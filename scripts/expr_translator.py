"""Translate mumei contract expressions into Lean 4 ``Prop`` source.

This is the translator used by ``scripts/ingest_cert.py``
to turn a mumei atom's ``requires`` / ``ensures`` strings into Lean
theorem statements. It deliberately handles a small, well-documented
subset:

* arithmetic comparisons: ``>``, ``>=``, ``<``, ``<=``, ``==``, ``!=``
* logical connectives:    ``&&`` (∧), ``||`` (∨), ``!`` (¬, prefix only)
* arithmetic operators:   ``+``, ``-``, ``*``, ``/``, ``%``
* integer / boolean literals, identifiers (including ``result``)
* parentheses
* bounded ``forall(..)``, ``arr[i]`` access, and known calls:
  ``len``, ``abs``, ``min``, ``max``

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
#
# The translator's call / array-access / comma handling lives in the
# translation phase rather than the lexer: the lexer keeps ``(``,
# ``)``, ``[``, ``]``, ``,`` as plain ``OP`` tokens and the
# ``_emit_tokens`` walker pattern-matches ``ID (`` / ``ID [`` /
# ``forall (`` to drive the rewrites added by the bridge translator.
_TOKEN_RE = re.compile(
    r"""
    \s+                          |  # whitespace
    (?P<NUM>\d+)                 |  # integer literal
    (?P<BOOL>\btrue\b|\bfalse\b) |  # boolean literal
    (?P<KW>\bforall\b)           |  # bounded quantifier keyword
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
    # Mumei built-ins handled inline by ``_emit_tokens``. Listing them
    # keeps ``_extract_identifiers`` from binding them as theorem
    # parameters if they show up as bare ID tokens.
    "forall", "len", "abs", "min", "max",
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

_KNOWN_FUNCTIONS = {
    "len": "mumei_len",
    "abs": "mumei_abs",
    "min": "min",
    "max": "max",
}

_KNOWN_FUNCTION_ARITY = {
    "len": 1,
    "abs": 1,
    "min": 2,
    "max": 2,
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

    array_identifiers: List[str]
    """Subset of ``identifiers`` that appear in ``arr[i]`` array-access
    position. These must be typed as ``Int → Int`` (not ``Int``) when
    emitted as theorem parameters, because the translator lowers
    ``arr[i]`` to Lean function application ``(arr (i))``."""


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
    """Token-level emit pass with ``forall(..)``, known calls, ``arr[i]``,
    and unknown function-call rewrites.

    Returns ``(lean_source, is_partial)``. ``is_partial`` is True when
    we encountered an UNK token, an unmatched bracket, a malformed
    ``forall`` (wrong number of arguments), or a function call that is
    not one of the known built-ins (``len`` / ``abs`` / ``min`` / ``max``) — the
    generated theorem then carries a ``-- TODO: unproven`` marker.
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
                f"{var_name} < {end_src} → {body_src})"
            )
            is_partial = is_partial or p1 or p2 or p3
            i = close + 1
            continue

        # id[expr] → ``id.get! <nat-index>``. Lean 4's ``List.get!``
        # takes a ``Nat`` index, but the surrounding mumei contract
        # binds variables (and the ``forall(i, lo, hi, …)`` quantifier)
        # at type ``Int``. We bridge the gap by emitting an ``.toNat``
        # conversion on identifier / compound indices; numeric literals
        # are left bare so Lean's polymorphic numeric literal elaboration
        # can pick the right ``Nat`` instance directly.
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
            inner_tokens = tokens[i + 2 : close]
            inner_src, p = _emit_tokens(inner_tokens)
            num_only = (
                len(inner_tokens) == 1 and inner_tokens[0][0] == "NUM"
            )
            id_only = (
                len(inner_tokens) == 1 and inner_tokens[0][0] == "ID"
            )
            if num_only:
                # ``arr[5]`` → ``arr.get! 5`` (literal, infers as ``Nat``).
                pieces.append(f"{text}.get! {inner_src}")
            elif id_only:
                # ``arr[i]`` → ``arr.get! i.toNat``. Method-call binding
                # is tighter than function application in Lean, so the
                # parens around ``i.toNat`` are unnecessary.
                pieces.append(f"{text}.get! {inner_src}.toNat")
            else:
                # ``arr[i + 1]`` → ``arr.get! (i + 1).toNat``. The outer
                # parens are required for ``.toNat`` to bind to the
                # whole compound expression rather than just the last
                # token.
                pieces.append(f"{text}.get! ({inner_src}).toNat")
            is_partial = is_partial or p
            i = close + 1
            continue

        # Known calls lower into Lean helper / standard functions:
        # ``len(arr)`` → ``(mumei_len arr)``, ``abs(x)`` → ``(mumei_abs x)``,
        # ``min(a, b)`` → ``(min a b)``, ``max(a, b)`` → ``(max a b)``.
        # Unknown calls are emitted verbatim and marked partial.
        if (
            kind == "ID"
            and i + 1 < n
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            arg_parts = _split_top_level(tokens, i + 2, close)
            arg_srcs: List[str] = []
            for ap in arg_parts:
                src, p = _emit_tokens(ap)
                arg_srcs.append(src)
                is_partial = is_partial or p
            if text in _KNOWN_FUNCTIONS:
                expected_arity = _KNOWN_FUNCTION_ARITY[text]
                if len(arg_parts) != expected_arity or any(not ap for ap in arg_parts):
                    pieces.append(f"{text} ({', '.join(arg_srcs)})")
                    is_partial = True
                else:
                    pieces.append(f"({_KNOWN_FUNCTIONS[text]} {' '.join(arg_srcs)})")
            else:
                pieces.append(f"{text} ({', '.join(arg_srcs)})")
                is_partial = True
            i = close + 1
            continue

        if kind == "OP":
            pieces.append(_OP_TRANSLATION.get(text, text))
        elif kind == "BOOL":
            pieces.append("True" if text == "true" else "False")
        elif kind == "KW":
            # ``forall`` reaching here means the keyword was
            # not followed by ``(`` — leave the literal in and flag as
            # partial so the generated theorem carries a TODO marker.
            pieces.append(text)
            is_partial = True
        else:
            # Bare ``len`` / ``abs`` / ``min`` / ``max`` (without a
            # following ``(``) cannot be lowered to a Lean helper call
            # and would reference an undeclared name. Flag as partial so
            # the generated theorem carries a ``-- TODO: unproven``
            # marker rather than silently emitting broken Lean.
            if kind == "ID" and text in _KNOWN_FUNCTIONS:
                is_partial = True
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
            array_identifiers=[],
        )
    if stripped == "false":
        return TranslationResult(
            lean_expr="False",
            identifiers=[],
            is_trivial=False,
            is_partial=False,
            array_identifiers=[],
        )

    tokens = _tokenize(stripped)
    lean_expr, is_partial = _emit_tokens(tokens)
    # Collect identifiers that appear in ``arr[i]`` position. These need
    # ``List Int`` typing in the rendered theorem signature so that
    # ``arr.get! i`` type-checks.
    array_idents: List[str] = []
    for j, (kind, text) in enumerate(tokens):
        # ``arr[i]``
        if (
            kind == "ID"
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "[")
        ):
            if text in _RESERVED_IDENTS:
                # Reserved names like ``result`` cannot be re-typed as
                # ``List Int`` (``render_theorem`` binds them as the
                # scalar return value). Flag as partial so the generated
                # theorem carries a ``-- TODO: unproven`` marker rather
                # than silently emitting ill-typed Lean.
                is_partial = True
            elif text not in array_idents:
                array_idents.append(text)
    # Type-conflict guard: an identifier passed to a scalar known call
    # (``len`` / ``abs`` / ``min`` / ``max``, all ``Int → Int`` or
    # ``Int → Int → Int``) that *also* appears in ``arr[i]`` position
    # would be typed as ``List Int`` by the renderer, producing a Lean
    # type error. Flag such contracts as partial so they carry a
    # ``-- TODO: unproven`` marker instead of silently emitting
    # ill-typed Lean.
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in _KNOWN_FUNCTIONS
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            for ap in _split_top_level(tokens, j + 2, close):
                for ak, at in ap:
                    if ak == "ID" and at in array_idents:
                        is_partial = True
                        break
    # Stand-alone commas outside known function calls / ``forall(..)`` /
    # ``arr[..]`` are not part of the supported surface; mark such
    # contracts as partial so the generated theorem still carries the
    # ``-- TODO: unproven`` triage marker.
    if not is_partial:
        depth = 0
        allowed_comma_depths: List[int] = []
        bracket_depth = 0
        for j, (kind, text) in enumerate(tokens):
            if kind == "OP" and text == "(":
                depth += 1
            elif kind == "OP" and text == ")":
                while allowed_comma_depths and allowed_comma_depths[-1] >= depth:
                    allowed_comma_depths.pop()
                depth -= 1
            elif kind == "OP" and text == "[":
                bracket_depth += 1
            elif kind == "OP" and text == "]":
                bracket_depth -= 1
            elif (
                (
                    (kind == "KW" and text == "forall")
                    or (kind == "ID" and text in _KNOWN_FUNCTIONS)
                )
                and j + 1 < len(tokens)
                and tokens[j + 1] == ("OP", "(")
            ):
                close = _find_matching(tokens, j + 1, "(", ")")
                if close != -1:
                    allowed_comma_depths.append(depth + 1)
            elif kind == "OP" and text == ",":
                inside_allowed_call = (
                    bool(allowed_comma_depths) and depth >= allowed_comma_depths[-1]
                )
                if not inside_allowed_call and bracket_depth == 0:
                    is_partial = True
                    break
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
    # Scope-awareness guard: ``bound`` is a flat set so an ID shared
    # between a forall's binder and a free occurrence outside that
    # forall would be silently dropped from ``free``, producing Lean
    # that references an undeclared name. Detect any such collision
    # and flag the contract as partial rather than emit broken output.
    if bound:
        scope_stack: List[tuple] = []  # (close_index, bound_name)
        for j, (kind, text) in enumerate(tokens):
            while scope_stack and scope_stack[-1][0] <= j:
                scope_stack.pop()
            if (
                kind == "KW"
                and text == "forall"
                and j + 1 < len(tokens)
                and tokens[j + 1] == ("OP", "(")
            ):
                close = _find_matching(tokens, j + 1, "(", ")")
                if close != -1:
                    parts = _split_top_level(tokens, j + 2, close)
                    if (
                        len(parts) == 4
                        and len(parts[0]) == 1
                        and parts[0][0][0] == "ID"
                    ):
                        scope_stack.append((close, parts[0][0][1]))
            elif kind == "ID" and text in bound:
                if not any(name == text for _, name in scope_stack):
                    is_partial = True
                    break
    return TranslationResult(
        lean_expr=lean_expr,
        identifiers=free,
        is_trivial=False,
        is_partial=is_partial,
        array_identifiers=[a for a in array_idents if a in free],
    )
