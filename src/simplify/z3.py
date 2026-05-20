from io import StringIO

from ..smt_backends.pysmt import *
import z3

from .utils import _string_to_script


def _is_shared_array_pin(formula: FNode) -> bool:
  """Detect ``(= before-memory-X after-memory-X)`` pins from :func:`.array_subst`.

  Used by tests and call sites that need to recognize these equalities.
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
        s.add(conv.convert(cmd.args[0]))
      case "check-sat":
        s.check()
        processed = _string_to_script(s.sexpr()).commands
        new_asserts = [
          c for c in processed
          if c.name == "assert" and not c.args[0].is_true()
        ]
        output = list(prefix) + new_asserts + [cmd]
        in_suffix = True
      case _:
        assert False, f"unexpected command: {cmd.name}"

  res = script.SmtLibScript()
  res.commands = output + suffix
  return res
