"""Translate mumei contract expressions into Lean 4 ``Prop`` source.

This is the *initial* (v1) translator used by ``scripts/ingest_cert.py``
to turn a mumei atom's ``requires`` / ``ensures`` strings into Lean
theorem statements. It deliberately handles a small, well-documented
subset:

* arithmetic comparisons: ``>``, ``>=``, ``<``, ``<=``, ``==``, ``!=``
* logical connectives:    ``&&`` (∧), ``||`` (∨), ``!`` (¬, prefix only)
* arithmetic operators:   ``+``, ``-``, ``*``, ``/``, ``%``
* integer / boolean literals, identifiers (including ``result``)
* parentheses

Anything outside this subset is preserved verbatim and emitted as a
Lean fragment that almost certainly will not type-check; the generated
theorem then carries a ``-- TODO: unproven`` marker which
``MumeiLean.unproven`` makes greppable.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import List, Set

# Tokens we recognise. Order matters: longer prefixes must come first
# so e.g. ``>=`` is not split into ``>`` + ``=``.
_TOKEN_RE = re.compile(
    r"""
    \s+                          |  # whitespace
    (?P<NUM>\d+)                 |  # integer literal
    (?P<BOOL>\btrue\b|\bfalse\b) |  # boolean literal
    (?P<ID>[A-Za-z_][A-Za-z0-9_]*) |  # identifier
    (?P<OP>
        ==|!=|>=|<=|&&|\|\||
        [+\-*/%<>!()]
    )
    """,
    re.VERBOSE,
)

# Identifiers that should NOT be quantified — they are either Lean
# keywords/standard names or mumei built-ins handled inline.
_RESERVED_IDENTS: Set[str] = {
    "true", "false",
    "result",  # bound separately as the theorem's return-value parameter
    # Lean keywords we never want to over-bind even if the contract uses
    # them as identifier names (it should not, but defensively).
    "Type", "Prop", "fun", "let", "do", "match", "with", "by",
}

# Operator translation: token text → Lean token text.
_OP_TRANSLATION = {
    "&&": "∧",
    "||": "∨",
    "==": "=",
    "!=": "≠",
    "!":  "¬",
    # passthrough for the rest
    ">=": "≥",
    "<=": "≤",
}


@dataclass
class TranslationResult:
    """Outcome of translating a single contract string."""

    lean_expr: str
    """Lean source fragment representing the contract as a ``Prop``."""

    identifiers: List[str]
    """Free identifiers referenced by the contract (excluding reserved)."""

    is_trivial: bool
    """``True`` if the source contract was empty / ``true`` /
    semantically a no-op. Trivial contracts produce ``True`` in Lean."""

    is_partial: bool
    """``True`` if the translator encountered tokens it could not fully
    handle (e.g. function calls, indexing). The caller should mark the
    generated theorem as ``-- TODO: unproven``."""


def _extract_identifiers(tokens: List[tuple]) -> List[str]:
    seen: List[str] = []
    for kind, text in tokens:
        if kind != "ID":
            continue
        if text in _RESERVED_IDENTS:
            continue
        if text not in seen:
            seen.append(text)
    return seen


def _tokenize(source: str) -> List[tuple]:
    """Return a list of ``(kind, text)`` tuples for ``source``.

    Whitespace is dropped. Unrecognised characters are folded into a
    synthetic ``UNK`` token so the caller can flag them.
    """
    pos = 0
    tokens: List[tuple] = []
    while pos < len(source):
        m = _TOKEN_RE.match(source, pos)
        if not m or m.end() == pos:
            tokens.append(("UNK", source[pos]))
            pos += 1
            continue
        if m.lastgroup is None:
            # whitespace
            pos = m.end()
            continue
        tokens.append((m.lastgroup, m.group(m.lastgroup)))
        pos = m.end()
    return tokens


def translate_contract(source: str) -> TranslationResult:
    """Translate a single mumei contract string to a Lean ``Prop``.

    The translator is deliberately *token-level*: it does not build a
    typed AST. This is enough for the initial scope (arithmetic
    comparisons + boolean connectives) and keeps the surface area
    auditable.
    """
    stripped = (source or "").strip()
    if stripped == "" or stripped == "true":
        return TranslationResult(
            lean_expr="True",
            identifiers=[],
            is_trivial=True,
            is_partial=False,
        )
    if stripped == "false":
        return TranslationResult(
            lean_expr="False",
            identifiers=[],
            is_trivial=False,
            is_partial=False,
        )

    tokens = _tokenize(stripped)
    is_partial = any(kind == "UNK" for kind, _ in tokens)

    pieces: List[str] = []
    for kind, text in tokens:
        if kind == "OP":
            pieces.append(_OP_TRANSLATION.get(text, text))
        elif kind == "BOOL":
            pieces.append("True" if text == "true" else "False")
        else:
            pieces.append(text)

    # Re-join with single spaces; Lean is whitespace-tolerant.
    lean_expr = " ".join(pieces)
    return TranslationResult(
        lean_expr=lean_expr,
        identifiers=_extract_identifiers(tokens),
        is_trivial=False,
        is_partial=is_partial,
    )
