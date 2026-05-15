"""Shared helpers for the skolem-map simplifier.

Pure utilities used by :mod:`.skolem` and the per-contributor modules
(:mod:`.skolem_derived`, :mod:`.skolem_names`,
:mod:`.skolem_rules`):

* :func:`emit_pin_setinfo` - verifier-side serialization of a single
  ``Equals(var, expr)`` pin as a ``(set-info :prefix-N ...)`` command.
* :func:`load_setinfo_pins` - simplifier-side counterpart that reads
  every entry of a given prefix back as an ``FNode``.
* :func:`split_equation` - canonical ``Equals(var, expr) -> (var, expr)``
  splitter used by every contributor that consumes pin equations.
"""

import functools
import io

from pysmt.smtlib.parser import Tokenizer

from ..smt.utils import *


def emit_pin_setinfo(prefix: str, idx: int, equation: FNode) -> script.SmtLibCommand:
    """Build a ``(set-info :{prefix}{idx} <smtlib-equation>)`` command.

    The equation is serialized to SMT-LIB without daggification (no
    ``let`` bindings) and stored as the attribute value verbatim.
    pysmt's command printer wraps the string in ``|...|`` (quoted-symbol
    syntax) on emission and the parser strips the wrapper on read, so
    the round-trip is transparent as long as the serialized form does
    not itself contain literal ``|`` characters - which it never does
    for arithmetic / equality terms.
    """
    return script.SmtLibCommand(
        name="set-info",
        args=[f":{prefix}{idx}", equation.to_smtlib(daggify=False)],
    )


def _collect_forall_qvars(smt_script: script.SmtLibScript) -> dict[str, FNode]:
    """Gather every forall-bound qvar declared anywhere in the script.

    Pins emitted by the verifier may reference variables that only live
    inside a ``forall`` (they are not free in the top-level formula and
    thus have no ``declare-fun``); we still need them in the parser
    cache so :func:`_parse_equation` can resolve them.
    """
    out: dict[str, FNode] = {}

    def visit(node: FNode):
        if node.is_quantifier():
            for q in node.quantifier_vars():
                if q.is_symbol():
                    out[q.symbol_name()] = q
        for a in node.args():
            visit(a)

    for cmd in smt_script:
        if cmd.name == "assert":
            visit(cmd.args[0])
    return out


def _build_parser_with_cache(smt_script: script.SmtLibScript) -> SmtLibParser:
    """Make a parser whose symbol cache mirrors the script's symbols.

    Includes both top-level ``declare-fun``s and any forall-bound qvars
    so embedded pin equations can refer to either. UF (function-typed)
    symbols are bound to pysmt's ``_function_call_helper`` partial, the
    same way ``_cmd_declare_fun`` would have bound them when parsing a
    fresh script - otherwise the parser raises ``Unknown function`` on
    ``(uf_mod_inv x)`` because a bare ``Symbol`` is not callable.
    """
    parser = SmtLibParser()
    for cmd in smt_script:
        if cmd.name != "declare-fun":
            continue
        sym = cmd.args[0]
        if not sym.is_symbol():
            continue
        if sym.symbol_type().is_function_type():
            parser.cache.bind(
                sym.symbol_name(),
                functools.partial(parser._function_call_helper, sym),
            )
        else:
            parser.cache.bind(sym.symbol_name(), sym)
    for name, sym in _collect_forall_qvars(smt_script).items():
        parser.cache.bind(name, sym)
    return parser


def _parse_equation(parser: SmtLibParser, value: str) -> FNode | None:
    """Parse a set-info value back into an ``FNode`` equation.

    The value is the raw SMT-LIB serialization; pysmt has already
    stripped any ``|...|`` quoted-symbol wrapper on parse-in, so we can
    feed it straight to the tokenizer. A trailing space is appended so
    the pysmt tokenizer does not silently drop the final atom when the
    value happens to be a bare symbol or numeral (its generator only
    yields a token after seeing a separator).
    """
    if not value:
        return None
    try:
        tok = Tokenizer(io.StringIO(value + " "), interactive=False)
        return parser.get_expression(tok)
    except Exception as e:
        logging.warning(f"skolem: failed to parse pin value {value!r}: {e}")
        return None


def load_setinfo_pins(
    smt_script: script.SmtLibScript, prefix: str
) -> list[FNode]:
    """Return all pin equations carried by ``:{prefix}N`` set-info entries.

    Entries whose value cannot be parsed are skipped with a warning.
    """
    parser = _build_parser_with_cache(smt_script)
    out: list[FNode] = []
    for cmd in smt_script:
        if cmd.name != "set-info":
            continue
        keyword = cmd.args[0]
        if not keyword.startswith(f":{prefix}"):
            continue
        eq = _parse_equation(parser, cmd.args[1])
        if eq is not None:
            out.append(eq)
    return out


def split_equation(eq: FNode) -> tuple[FNode, FNode] | None:
    """Split an ``Equals(var, expr)`` pin equation into ``(var, expr)``.

    Returns ``None`` for non-equality nodes; falls back to
    ``(arg(1), arg(0))`` if the qvar happens to live on the right.
    """
    if not eq.is_equals():
        return None
    a, b = eq.arg(0), eq.arg(1)
    if a.is_symbol():
        return a, b
    if b.is_symbol():
        return b, a
    return None
