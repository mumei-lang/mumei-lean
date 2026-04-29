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
from typing import List, Set, Tuple

# Tokens we recognise. Order matters: longer prefixes must come first
# so e.g. ``>=`` is not split into ``>`` + ``=``.
_TOKEN_RE = re.compile(
    r"""
    \s+                          |  # whitespace
    (?P<NUM>\d+)                 |  # integer literal
    (?P<BOOL>\btrue\b|\bfalse\b) |  # boolean literal
    (?P<KW>\bforall\b)           |  # quantifier keyword (PR 3)
    (?P<ID>[A-Za-z_][A-Za-z0-9_]*) |  # identifier
    (?P<OP>
        ==|!=|>=|<=|&&|\|\||
        [+\-*/%<>!()\[\],]
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


def contains_identifier(source: str, name: str) -> bool:
    """Return ``True`` iff ``source`` contains an identifier *token*
    that is exactly ``name``.

    Unlike a plain ``name in source`` substring test, this respects
    token boundaries: ``contains_identifier("results > 0", "result")``
    is ``False`` and so is ``contains_identifier("no_result > 0",
    "result")``.
    """
    if not name:
        return False
    for kind, text in _tokenize(source or ""):
        if kind == "ID" and text == name:
            return True
    return False


def _find_matching(
    tokens: List[tuple], start: int, open_tok: str, close_tok: str
) -> int:
    """Return the index of the closing ``close_tok`` matching ``tokens[start]``.

    ``tokens[start]`` must be ``("OP", open_tok)``. Returns ``-1`` if no
    matching close is found (caller should treat this as a partial
    translation failure).
    """
    depth = 0
    for j in range(start, len(tokens)):
        kind, text = tokens[j]
        if kind != "OP":
            continue
        if text == open_tok:
            depth += 1
        elif text == close_tok:
            depth -= 1
            if depth == 0:
                return j
    return -1


def _split_top_level(
    tokens: List[tuple], start: int, end: int
) -> List[List[tuple]]:
    """Split ``tokens[start:end]`` by top-level ``,`` tokens.

    Top-level meaning the comma is not nested inside ``()``/``[]``.
    """
    out: List[List[tuple]] = [[]]
    depth = 0
    for j in range(start, end):
        kind, text = tokens[j]
        if kind == "OP" and text in ("(", "["):
            depth += 1
            out[-1].append(tokens[j])
        elif kind == "OP" and text in (")", "]"):
            depth -= 1
            out[-1].append(tokens[j])
        elif kind == "OP" and text == "," and depth == 0:
            out.append([])
        else:
            out[-1].append(tokens[j])
    return out


def _emit_tokens(tokens: List[tuple]) -> Tuple[str, bool]:
    """Token-level emit pass with ``forall(..)`` and ``arr[i]`` rewrites.

    Returns ``(lean_source, is_partial)``. ``is_partial`` is True when
    we encountered an UNK token, an unmatched bracket, or a malformed
    ``forall`` (wrong number of arguments).
    """
    pieces: List[str] = []
    is_partial = any(kind == "UNK" for kind, _ in tokens)
    i = 0
    n = len(tokens)
    while i < n:
        kind, text = tokens[i]

        # forall(var, start, end, body) → (∀ var : Int, start ≤ var → var < end → body)
        if (
            kind == "KW"
            and text == "forall"
            and i + 1 < n
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            parts = _split_top_level(tokens, i + 2, close)
            if len(parts) != 4:
                # Malformed — fall back to verbatim.
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            var_tokens, start_tokens, end_tokens, body_tokens = parts
            if (
                len(var_tokens) != 1
                or var_tokens[0][0] != "ID"
            ):
                # Bound variable must be a single identifier.
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            var_name = var_tokens[0][1]
            start_src, p1 = _emit_tokens(start_tokens)
            end_src, p2 = _emit_tokens(end_tokens)
            body_src, p3 = _emit_tokens(body_tokens)
            pieces.append(
                f"(∀ {var_name} : Int, {start_src} ≤ {var_name} → "
                f"{var_name} < {end_src} → ({body_src}))"
            )
            is_partial = is_partial or p1 or p2 or p3
            i = close + 1
            continue

        # id[expr] → (id (expr))
        if (
            kind == "ID"
            and i + 1 < n
            and tokens[i + 1] == ("OP", "[")
        ):
            close = _find_matching(tokens, i + 1, "[", "]")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            inner_src, p = _emit_tokens(tokens[i + 2 : close])
            # Wrap the index in its own parens: in Lean 4, function
            # application binds tighter than arithmetic, so without
            # the inner parens ``arr[i + 1]`` would emit ``(arr i + 1)``
            # which Lean parses as ``((arr i) + 1)`` — wrong.
            pieces.append(f"({text} ({inner_src}))")
            is_partial = is_partial or p
            i = close + 1
            continue

        if kind == "OP":
            pieces.append(_OP_TRANSLATION.get(text, text))
        elif kind == "BOOL":
            pieces.append("True" if text == "true" else "False")
        elif kind == "KW":
            # `forall` reaching here means it was not followed by `(` —
            # leave the literal in and flag as partial.
            pieces.append(text)
            is_partial = True
        else:
            pieces.append(text)
        i += 1

    return " ".join(pieces), is_partial


def translate_contract(source: str) -> TranslationResult:
    """Translate a single mumei contract string to a Lean ``Prop``.

    The translator is deliberately *token-level*: it does not build a
    typed AST. This is enough for the initial scope (arithmetic
    comparisons + boolean connectives + bounded ``forall`` quantifiers
    and array-access ``arr[i]`` Function applications).
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
    lean_expr, is_partial = _emit_tokens(tokens)
    # Free identifiers are everything except reserved names AND the
    # bound variables of any ``forall``. The latter are still reported
    # as ID tokens by ``_extract_identifiers`` because we don't track
    # binder scope here; Lean will simply shadow them inside the
    # quantifier body, so emitting them as ``variable`` declarations
    # would be wrong. Filter explicit forall-bound names out.
    bound: Set[str] = set()
    i = 0
    while i < len(tokens):
        if (
            tokens[i] == ("KW", "forall")
            and i + 1 < len(tokens)
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close != -1:
                parts = _split_top_level(tokens, i + 2, close)
                if (
                    len(parts) == 4
                    and len(parts[0]) == 1
                    and parts[0][0][0] == "ID"
                ):
                    bound.add(parts[0][0][1])
        i += 1
    free = [name for name in _extract_identifiers(tokens) if name not in bound]
    return TranslationResult(
        lean_expr=lean_expr,
        identifiers=free,
        is_trivial=False,
        is_partial=is_partial,
    )
