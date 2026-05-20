import logging
from io import StringIO

from ..smt_backends.pysmt import *
import z3

from .utils import _string_to_script


def _has_quantifier(formula: FNode) -> bool:
  def walk(n: FNode) -> bool:
    if n.is_quantifier():
      return True
    return any(walk(a) for a in n.args())

  return walk(formula)


def _is_shared_array_pin(formula: FNode) -> bool:
  """Detect ``(= before-memory-X after-memory-X)`` pins from :func:`.array_subst`.

  These are appended just before ``check-sat`` and must not be replayed by
  positional index from Z3's processed assert list (Z3 may drop, merge, or
  reorder ground facts and would pair the wrong formulas).
  """
  if not formula.is_equals():
    return False
  left, right = formula.arg(0), formula.arg(1)
  if not (left.is_symbol() and right.is_symbol()):
    return False
  ln, rn = left.symbol_name(), right.symbol_name()
  if not (ln.startswith("before-memory-") and rn.startswith("after-memory-")):
    return False
  return ln.removeprefix("before-") == rn.removeprefix("after-")


def simplify_z3(smt_script: script.SmtLibScript, args=[]) -> script.SmtLibScript:
  match args:
    case []:
      tactic = z3.Repeat(
        z3.Then(
          "propagate-values",
          "elim-term-ite",
          "propagate-ineqs",
          "solve-eqs",
          "ctx-simplify",
        )
      )
    case [t]:
      tactic = z3.Tactic(t)
    case [*t]:
      tactic = z3.Then(*t)

  s = tactic.solver()
  conv = Z3Converter(get_env(), s.ctx)

  prefix: list = []
  assert_slots: list[tuple[str, script.SmtLibCommand]] = []
  suffix: list = []
  in_suffix = False
  output: list = []

  for cmd in smt_script:
    if in_suffix:
      suffix.append(cmd)
      continue
    match cmd.name:
      case "set-info" | "set-logic" | "set-option" | "declare-fun" | "get-model" | "get-unsat-core" | "echo":
        prefix.append(cmd)
      case "assert":
        if _has_quantifier(cmd.args[0]):
          assert_slots.append(("quant", cmd))
        elif _is_shared_array_pin(cmd.args[0]):
          assert_slots.append(("pin", cmd))
        else:
          assert_slots.append(("ground", cmd))
          s.add(conv.convert(cmd.args[0]))
      case "check-sat":
        s.check()
        processed = _string_to_script(s.sexpr()).commands
        ground_out: list[script.SmtLibCommand] = []
        for c in processed:
          if c.name == "assert" and not c.args[0].is_true():
            ground_out.append(c)
        output = list(prefix)
        gi = 0
        for kind, orig in assert_slots:
          if kind in ("quant", "pin"):
            output.append(orig)
          elif gi < len(ground_out):
            output.append(ground_out[gi])
            gi += 1
          else:
            logging.warning(
              "z3-replay: fewer Z3 ground asserts than expected; "
              "keeping original for %s",
              orig,
            )
            output.append(orig)
        extra = len(ground_out) - gi
        while gi < len(ground_out):
          output.append(ground_out[gi])
          gi += 1
        if extra > 0:
          logging.info(
              "z3-replay: appended %d extra Z3 ground assert(s) after replay",
              extra,
          )
        output.append(cmd)
        in_suffix = True
      case _:
        assert False, f"unexpected command: {cmd.name}"

  res = script.SmtLibScript()
  res.commands = output + suffix
  return res
