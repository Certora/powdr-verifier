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
          if kind == "quant":
            output.append(orig)
          else:
            output.append(ground_out[gi])
            gi += 1
        output.extend(ground_out[gi:])
        output.append(cmd)
        in_suffix = True
      case _:
        assert False, f"unexpected command: {cmd.name}"

  res = script.SmtLibScript()
  res.commands = output + suffix
  return res
