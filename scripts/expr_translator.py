"""Translate mumei contract expressions into Lean 4 ``Prop`` source.

This is the translator used by ``scripts/ingest_cert.py``
to turn a mumei atom's ``requires`` / ``ensures`` strings into Lean
theorem statements. It deliberately handles a small, well-documented
subset:

* arithmetic comparisons: ``>``, ``>=``, ``<``, ``<=``, ``==``, ``!=``
* logical connectives:    ``&&`` (∧), ``||`` (∨), ``!`` (¬, prefix only)
* arithmetic operators:   ``+``, ``-``, ``*``, ``/``, ``%``
* integer / boolean / string literals, identifiers (including ``result``)
* parentheses
* bounded ``forall(..)``, unbounded ``forall`` / ``exists`` quantifiers,
  ``if .. then .. else ..``, ``match`` expressions,
  ``arr[i]`` access, and known calls:
  ``len``, ``abs``, ``min``, ``max``, ``old``, ``starts_with``, ``ends_with``,
  ``contains``, ``not_contains``, ``sum``, ``count``

Anything outside this subset is preserved verbatim and emitted as a
Lean fragment that almost certainly will not type-check; the generated
theorem then carries a ``-- TODO: unproven`` marker which
``MumeiLean.unproven`` makes greppable.
"""
from __future__ import annotations

import re
from dataclasses import dataclass
from typing import Optional, List, Set, Tuple

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
    (?P<STR>"(?:\\.|[^"\\])*") |  # string literal
    (?P<NUM>\d+)                 |  # integer literal
    (?P<BOOL>\btrue\b|\bfalse\b) |  # boolean literal
    (?P<KW>\bforall\b|\bexists\b|\bif\b|\bthen\b|\belse\b|\bmatch\b) |  # keywords
    (?P<ID>[A-Za-z_][A-Za-z0-9_]*) |  # identifier
    (?P<OP>
        ==|!=|>=|<=|&&|\|\||=>|
        [+\-*/%<>!()\[\]{},:]
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
    "forall", "exists", "len", "abs", "min", "max", "old",
    "starts_with", "ends_with", "contains", "not_contains", "sum", "count",
    "if", "then", "else", "match", "_",
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
    "old": "old_",
    "starts_with": "mumei_starts_with",
    "ends_with": "mumei_ends_with",
    "contains": "mumei_contains",
    "not_contains": "mumei_not_contains",
    "sum": "mumei_sum",
    "count": "mumei_count",
}

_KNOWN_FUNCTION_ARITY = {
    "len": 1,
    "abs": 1,
    "min": 2,
    "max": 2,
    "old": 1,
    "starts_with": 2,
    "ends_with": 2,
    "contains": 2,
    "not_contains": 2,
    "sum": 2,
    "count": 2,
}

_QUANTIFIER_KEYWORDS = {"forall", "exists"}

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

    string_identifiers: List[str]
    """Subset of ``identifiers`` that are passed to string predicates
    such as ``starts_with`` / ``ends_with``. The renderer types these
    identifiers as ``String`` instead of the scalar ``Int`` default."""


def _extract_identifiers(tokens: List[tuple]) -> List[str]:
    seen: List[str] = []
    i = 0
    while i < len(tokens):
        kind, text = tokens[i]
        if (
            kind == "ID"
            and text == "old"
            and i + 1 < len(tokens)
            and tokens[i + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, i + 1, "(", ")")
            if close != -1:
                parts = _split_top_level(tokens, i + 2, close)
                if (
                    len(parts) == 1
                    and len(parts[0]) == 1
                    and parts[0][0][0] == "ID"
                ):
                    old_name = f"old_{parts[0][0][1]}"
                    if old_name not in seen:
                        seen.append(old_name)
                    i = close + 1
                    continue
        if kind != "ID":
            i += 1
            continue
        if text in _RESERVED_IDENTS:
            i += 1
            continue
        if text not in seen:
            seen.append(text)
        i += 1
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
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
            out[-1].append(tokens[j])
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
            out[-1].append(tokens[j])
        elif kind == "OP" and text == "," and depth == 0:
            out.append([])
        else:
            out[-1].append(tokens[j])
    return out


def _find_top_level_arrow(tokens: List[tuple]) -> int:
    depth = 0
    for idx, (kind, text) in enumerate(tokens):
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif kind == "OP" and text == "=>" and depth == 0:
            return idx
    return -1


def _if_else_tail_is_supported(tokens: List[tuple]) -> bool:
    depth = 0
    for kind, text in tokens:
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif depth == 0 and (
            (kind == "KW" and text != "match")
            or (kind == "OP" and text in {"&&", "||", "==", "!=", ">=", "<=", ">", "<"})
        ):
            return False
    return True


def _find_quantifier_colon(tokens: List[tuple], start: int, end: int) -> int:
    depth = 0
    for j in range(start, end):
        kind, text = tokens[j]
        if kind == "OP" and text in ("(", "[", "{"):
            depth += 1
        elif kind == "OP" and text in (")", "]", "}"):
            depth -= 1
        elif kind == "OP" and text == ":" and depth == 0:
            return j
    return -1


def _parse_unbounded_quantifier(
    tokens: List[tuple], start: int
) -> Optional[Tuple[str, int, List[tuple]]]:
    if start + 2 >= len(tokens):
        return None
    if tokens[start][0] != "KW" or tokens[start][1] not in _QUANTIFIER_KEYWORDS:
        return None
    var_kind, var_name = tokens[start + 1]
    if var_kind != "ID":
        return None
    colon_idx = _find_quantifier_colon(tokens, start + 2, len(tokens))
    if colon_idx == -1:
        return None
    body_start = colon_idx + 1
    if body_start >= len(tokens):
        return None
    return var_name, body_start, tokens[body_start:]


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

        # if cond then a else b → if cond then a else b
        if kind == "KW" and text == "if":
            depth = 0
            then_idx = -1
            else_idx = -1
            j = i + 1
            while j < n:
                tk, tt = tokens[j]
                if tk == "OP" and tt in ("(", "["):
                    depth += 1
                elif tk == "OP" and tt in (")", "]"):
                    depth -= 1
                elif tk == "KW" and tt == "then" and depth == 0:
                    then_idx = j
                    break
                j += 1
            if then_idx != -1:
                depth = 0
                j = then_idx + 1
                while j < n:
                    tk, tt = tokens[j]
                    if tk == "OP" and tt in ("(", "["):
                        depth += 1
                    elif tk == "OP" and tt in (")", "]"):
                        depth -= 1
                    elif tk == "KW" and tt == "else" and depth == 0:
                        else_idx = j
                        break
                    j += 1
            if then_idx == -1 or else_idx == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            cond_src, p1 = _emit_tokens(tokens[i + 1 : then_idx])
            then_src, p2 = _emit_tokens(tokens[then_idx + 1 : else_idx])
            else_src, p3 = _emit_tokens(tokens[else_idx + 1 :])
            pieces.append(f"if {cond_src} then {then_src} else {else_src}")
            is_partial = is_partial or p1 or p2 or p3
            if i != 0 or not _if_else_tail_is_supported(tokens[else_idx + 1 :]):
                is_partial = True
            i = n
            continue

        # match x { 0 => a, 1 => b, _ => c } →
        #   match x with | 0 => a | 1 => b | _ => c
        if kind == "KW" and text == "match":
            brace_idx = -1
            depth = 0
            j = i + 1
            while j < n:
                tk, tt = tokens[j]
                if tk == "OP" and tt in ("(", "["):
                    depth += 1
                elif tk == "OP" and tt in (")", "]"):
                    depth -= 1
                elif tk == "OP" and tt == "{" and depth == 0:
                    brace_idx = j
                    break
                j += 1
            if brace_idx == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            close = _find_matching(tokens, brace_idx, "{", "}")
            if close == -1:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            scrutinee_src, p_scrutinee = _emit_tokens(tokens[i + 1 : brace_idx])
            arm_parts = _split_top_level(tokens, brace_idx + 1, close)
            arm_srcs: List[str] = []
            match_partial = p_scrutinee or close != n - 1
            for arm in arm_parts:
                arrow_idx = _find_top_level_arrow(arm)
                if arrow_idx == -1:
                    match_partial = True
                    continue
                pattern_tokens = arm[:arrow_idx]
                value_tokens = arm[arrow_idx + 1 :]
                if not pattern_tokens or not value_tokens:
                    match_partial = True
                    continue
                pattern_src = " ".join(text for _kind, text in pattern_tokens)
                value_src, p_value = _emit_tokens(value_tokens)
                arm_srcs.append(f"| {pattern_src} => {value_src}")
                match_partial = match_partial or p_value
            if not arm_srcs:
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            pieces.append(f"(match {scrutinee_src} with {' '.join(arm_srcs)})")
            is_partial = is_partial or match_partial
            i = n if close == n - 1 else close + 1
            continue

        # forall var: body / exists var: body →
        #   (∀ var : Int, body) / (∃ var : Int, body)
        if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
            parsed = _parse_unbounded_quantifier(tokens, i)
            if parsed is not None:
                var_name, _body_start, body_tokens = parsed
                body_src, p = _emit_tokens(body_tokens)
                symbol = "∀" if text == "forall" else "∃"
                pieces.append(f"({symbol} {var_name} : Int, {body_src})")
                is_partial = is_partial or p
                i = n
                continue

        # forall(var, start, end, body) →
        #   (∀ var : Int, start ≤ var → var < end → body)
        # exists(var, body) → (∃ var : Int, body)
        # exists(var, start, end, body) →
        #   (∃ var : Int, start ≤ var ∧ var < end ∧ body)
        if (
            kind == "KW"
            and text in _QUANTIFIER_KEYWORDS
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
            is_bounded_forall = text == "forall" and len(parts) == 4
            is_unbounded_exists = text == "exists" and len(parts) == 2
            is_bounded_exists = text == "exists" and len(parts) == 4
            if not (is_bounded_forall or is_unbounded_exists or is_bounded_exists):
                # Malformed — fall back to verbatim.
                pieces.append(text)
                is_partial = True
                i += 1
                continue
            var_tokens = parts[0]
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
            if is_unbounded_exists:
                body_src, p = _emit_tokens(parts[1])
                pieces.append(f"(∃ {var_name} : Int, {body_src})")
                is_partial = is_partial or p
            else:
                start_tokens, end_tokens, body_tokens = parts[1], parts[2], parts[3]
                start_src, p1 = _emit_tokens(start_tokens)
                end_src, p2 = _emit_tokens(end_tokens)
                body_src, p3 = _emit_tokens(body_tokens)
                if text == "forall":
                    pieces.append(
                        f"(∀ {var_name} : Int, {start_src} ≤ {var_name} → "
                        f"{var_name} < {end_src} → {body_src})"
                    )
                else:
                    pieces.append(
                        f"(∃ {var_name} : Int, {start_src} ≤ {var_name} ∧ "
                        f"{var_name} < {end_src} ∧ {body_src})"
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
                elif text == "old":
                    old_arg = arg_parts[0]
                    if len(old_arg) == 1 and old_arg[0][0] == "ID":
                        pieces.append(f"old_{old_arg[0][1]}")
                    else:
                        pieces.append(f"old_ ({arg_srcs[0]})")
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
            pieces.append(text)
            # Keywords reaching here are malformed in the supported surface
            # (for example ``forall`` without ``(`` or a stray ``then``).
            is_partial = True
        elif kind == "STR":
            pieces.append(text)
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
            string_identifiers=[],
        )
    if stripped == "false":
        return TranslationResult(
            lean_expr="False",
            identifiers=[],
            is_trivial=False,
            is_partial=False,
            array_identifiers=[],
            string_identifiers=[],
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
    # ``sum(arr, n)`` / ``count(arr, val)``: the first argument is a
    # ``List Int`` in the Lean helper signatures (``mumei_sum`` /
    # ``mumei_count``), so identifiers appearing there must be typed as
    # ``List Int`` — not the scalar ``Int`` default that
    # ``render_theorem`` would otherwise emit. Without this pass the
    # generated theorem would reference ``mumei_sum arr n`` with
    # ``arr : Int``, which is a Lean type error.
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in ("sum", "count")
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            parts = _split_top_level(tokens, j + 2, close)
            if not parts or not parts[0]:
                continue
            first_arg = parts[0]
            if len(first_arg) == 1 and first_arg[0][0] == "ID":
                name = first_arg[0][1]
                if name in _RESERVED_IDENTS:
                    is_partial = True
                elif name not in array_idents:
                    array_idents.append(name)
            else:
                # Non-trivial first argument (e.g. a nested call) cannot
                # be re-typed at the parameter level; flag as partial so
                # the generated theorem carries a ``-- TODO: unproven``
                # marker.
                is_partial = True
    string_idents: List[str] = []
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in ("starts_with", "ends_with", "contains", "not_contains")
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            for ap in _split_top_level(tokens, j + 2, close):
                for ak, at in ap:
                    if (
                        ak == "ID"
                        and at not in _RESERVED_IDENTS
                        and at not in string_idents
                    ):
                        string_idents.append(at)
    scalar_call_idents: List[str] = []
    # Type-conflict guard: an identifier passed to a scalar known call
    # (e.g. ``len`` / ``abs`` / ``min`` / ``max``) that *also* appears in
    # ``arr[i]`` position
    # or string-predicate position would be typed non-``Int`` by the
    # renderer, producing a Lean type error. Flag such contracts as partial
    # so they carry a ``-- TODO: unproven`` marker instead of silently emitting
    # ill-typed Lean.
    for j, (kind, text) in enumerate(tokens):
        if (
            kind == "ID"
            and text in ("len", "abs", "min", "max", "sum", "count")
            and j + 1 < len(tokens)
            and tokens[j + 1] == ("OP", "(")
        ):
            close = _find_matching(tokens, j + 1, "(", ")")
            if close == -1:
                continue
            arg_parts = _split_top_level(tokens, j + 2, close)
            # ``sum`` / ``count`` take a ``List Int`` first argument, so
            # identifiers there are legitimately non-scalar and must not
            # trip the scalar-vs-array conflict guard below.
            if text in ("sum", "count"):
                arg_parts_to_scan = arg_parts[1:]
            else:
                arg_parts_to_scan = arg_parts
            for ap in arg_parts_to_scan:
                for ak, at in ap:
                    if ak == "ID" and at not in _RESERVED_IDENTS:
                        if at not in scalar_call_idents:
                            scalar_call_idents.append(at)
                        if at in array_idents or at in string_idents:
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
        brace_depth = 0
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
            elif kind == "OP" and text == "{":
                brace_depth += 1
            elif kind == "OP" and text == "}":
                brace_depth -= 1
            elif (
                (
                    (kind == "KW" and text in _QUANTIFIER_KEYWORDS)
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
                if not inside_allowed_call and bracket_depth == 0 and brace_depth == 0:
                    is_partial = True
                    break
    # Free identifiers are everything except reserved names AND the
    # bound variables of any quantifier. The latter are still reported
    # as ID tokens by ``_extract_identifiers`` because we don't track
    # binder scope here; Lean will simply shadow them inside the
    # quantifier body, so emitting them as ``variable`` declarations
    # would be wrong. Filter explicit quantifier-bound names out.
    bound: Set[str] = set()
    i = 0
    while i < len(tokens):
        kind, text = tokens[i]
        if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
            parsed_unbounded = _parse_unbounded_quantifier(tokens, i)
            if parsed_unbounded is not None:
                bound.add(parsed_unbounded[0])
            elif i + 1 < len(tokens) and tokens[i + 1] == ("OP", "("):
                close = _find_matching(tokens, i + 1, "(", ")")
                if close != -1:
                    parts = _split_top_level(tokens, i + 2, close)
                    valid_arity = len(parts) == 4 or (text == "exists" and len(parts) == 2)
                    if (
                        valid_arity
                        and len(parts[0]) == 1
                        and parts[0][0][0] == "ID"
                    ):
                        bound.add(parts[0][0][1])
        i += 1
    free = [name for name in _extract_identifiers(tokens) if name not in bound]
    for ident in string_idents:
        if ident in array_idents:
            is_partial = True
    # Scope-awareness guard: ``bound`` is a flat set so an ID shared
    # between a quantifier's binder and a free occurrence outside that
    # quantifier would be silently dropped from ``free``, producing Lean
    # that references an undeclared name. Detect any such collision
    # and flag the contract as partial rather than emit broken output.
    if bound:
        scope_stack: List[tuple] = []  # (close_index, bound_name)
        for j, (kind, text) in enumerate(tokens):
            while scope_stack and scope_stack[-1][0] <= j:
                scope_stack.pop()
            if kind == "KW" and text in _QUANTIFIER_KEYWORDS:
                parsed_unbounded = _parse_unbounded_quantifier(tokens, j)
                if parsed_unbounded is not None:
                    scope_stack.append((len(tokens), parsed_unbounded[0]))
                elif j + 1 < len(tokens) and tokens[j + 1] == ("OP", "("):
                    close = _find_matching(tokens, j + 1, "(", ")")
                    if close != -1:
                        parts = _split_top_level(tokens, j + 2, close)
                        valid_arity = len(parts) == 4 or (
                            text == "exists" and len(parts) == 2
                        )
                        if (
                            valid_arity
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
        string_identifiers=[s for s in string_idents if s in free],
    )


_IDENT_PATTERN = r"[A-Za-z_][A-Za-z0-9_]*"


def _fragment_translation(source: str) -> tuple[str, list[str], bool]:
    tokens = _tokenize(source.strip())
    lean_expr, is_partial = _emit_tokens(tokens)
    return lean_expr, _extract_identifiers(tokens), is_partial


def _merge_identifiers(groups: list[list[str]]) -> list[str]:
    merged: list[str] = []
    for group in groups:
        for ident in group:
            if ident not in merged:
                merged.append(ident)
    return merged


def _known_body_pattern(source: str) -> Optional[TranslationResult]:
    conditional_abs = re.fullmatch(
        rf"if\s+({_IDENT_PATTERN})\s*>=\s*0\s+then\s+\1\s+else\s+(?:-\s*\1|0\s*-\s*\1)",
        source,
    )
    if conditional_abs:
        var_name = conditional_abs.group(1)
        return TranslationResult(
            lean_expr=f"if {var_name} ≥ 0 then {var_name} else - {var_name}",
            identifiers=[var_name],
            is_trivial=False,
            is_partial=False,
            array_identifiers=[],
            string_identifiers=[],
        )

    saturating_abs = re.fullmatch(
        rf"if\s+({_IDENT_PATTERN})\s*==\s*(.+?)\s+then\s+(.+?)\s+else\s+if\s+\1\s*>=\s*0\s+then\s+\1\s+else\s+(?:-\s*\1|0\s*-\s*\1)",
        source,
    )
    if saturating_abs:
        var_name, min_src, max_src = saturating_abs.groups()
        min_lean, min_ids, min_partial = _fragment_translation(min_src)
        max_lean, max_ids, max_partial = _fragment_translation(max_src)
        return TranslationResult(
            lean_expr=(
                f"if {var_name} = {min_lean} then {max_lean} "
                f"else if {var_name} ≥ 0 then {var_name} else 0 - {var_name}"
            ),
            identifiers=_merge_identifiers([[var_name], min_ids, max_ids]),
            is_trivial=False,
            is_partial=min_partial or max_partial,
            array_identifiers=[],
            string_identifiers=[],
        )

    saturating_lower_bound = re.fullmatch(
        rf"if\s+({_IDENT_PATTERN})\s*<\s*(.+?)\s+then\s+(.+?)\s+else\s+\1",
        source,
    )
    if saturating_lower_bound:
        var_name, min_src, saturated_src = saturating_lower_bound.groups()
        if re.sub(r"\s+", "", min_src) != re.sub(r"\s+", "", saturated_src):
            return None
        min_lean, min_ids, min_partial = _fragment_translation(min_src)
        return TranslationResult(
            lean_expr=f"if {var_name} < {min_lean} then {min_lean} else {var_name}",
            identifiers=_merge_identifiers([[var_name], min_ids]),
            is_trivial=False,
            is_partial=min_partial,
            array_identifiers=[],
            string_identifiers=[],
        )

    return None


def translate_body(body_expr: str) -> TranslationResult:
    """Translate a mumei atom body expression to a Lean term.

    The supported body surface intentionally mirrors the simple term
    subset used in contracts: arithmetic, conditionals, known pure
    calls, and compact ``match x { ... }`` arms. Empty or unsupported
    bodies are marked partial so callers can fall back to the legacy
    theorem shape.
    """
    stripped = (body_expr or "").strip()
    if not stripped:
        return TranslationResult(
            lean_expr="",
            identifiers=[],
            is_trivial=False,
            is_partial=True,
            array_identifiers=[],
            string_identifiers=[],
        )
    known = _known_body_pattern(stripped)
    if known is not None:
        return known
    result = translate_contract(stripped)
    if "=>" in stripped and "=>" not in result.lean_expr:
        result.is_partial = True
    return result
