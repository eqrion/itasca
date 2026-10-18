"""Small lexical reader for build checks, not a Lean type checker.

Skip nested comments and retain strings as single tokens so source-looking
text inside comments/literals cannot satisfy import or declaration checks.
"""
from dataclasses import dataclass
from collections.abc import Iterator


@dataclass(frozen=True)
class Token:
    kind: str
    value: str


def tokens(source: str, *, rust_docs: bool = False) -> Iterator[Token]:
    i = 0
    while i < len(source):
        if source[i].isspace() or source[i] == "\ufeff":
            i += 1
        elif source.startswith("--", i):
            end = source.find("\n", i + 2)
            i = len(source) if end == -1 else end + 1
        elif source.startswith("/-", i):
            start = i
            i += 2
            depth = 1
            while depth:
                if i == len(source):
                    raise ValueError("Unterminated Lean block comment")
                if source.startswith("/-", i):
                    depth += 1
                    i += 2
                elif source.startswith("-/", i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            # Aeneas identifies opaque functions from the local crate in a
            # generated documentation header instead of a rust_fun attribute.
            # Preserve only that outer header when explicitly requested; text
            # nested inside another comment or a string remains inert.
            if rust_docs and source.startswith("/-- [", start):
                end = source.find("]:\n", start + 5, i)
                if end != -1 and "\n" not in source[start + 5:end]:
                    yield Token("rust_doc", source[start + 5:end])
        elif source[i] == "«":
            end = source.find("»", i + 1)
            if end == -1:
                raise ValueError("Unterminated Lean quoted identifier")
            yield Token("ident", source[i + 1:end])
            i = end + 1
        elif source[i] == "'" and i + 2 < len(source) and source[i + 2] == "'":
            yield Token("char", source[i + 1])
            i += 3
        elif source.startswith("'\\", i):
            end = source.find("'", i + 3)
            if end == -1 or "\n" in source[i:end]:
                raise ValueError("Unterminated Lean character literal")
            yield Token("char", source[i + 1:end])
            i = end + 1
        else:
            # Lean raw strings use r"...", r#"..."#, and so on.
            raw_end = i + 1
            if source[i] == "r":
                while raw_end < len(source) and source[raw_end] == "#":
                    raw_end += 1
            if source[i] == "r" and raw_end < len(source) and source[raw_end] == '"':
                closing = '"' + source[i + 1:raw_end]
                end = source.find(closing, raw_end + 1)
                if end == -1:
                    raise ValueError("Unterminated Lean raw string")
                yield Token("string", source[raw_end + 1:end])
                i = end + len(closing)
            elif source[i] == '"':
                start = i + 1
                i += 1
                while i < len(source) and source[i] != '"':
                    i += 2 if source[i] == "\\" else 1
                if i >= len(source):
                    raise ValueError("Unterminated Lean string")
                yield Token("string", source[start:i])
                i += 1
            elif source[i].isalpha() or source[i] == "_":
                start = i
                i += 1
                while i < len(source) and (source[i].isalnum() or source[i] in "_'!?"):
                    i += 1
                yield Token("ident", source[start:i])
            else:
                yield Token("symbol", source[i])
                i += 1


def header_imports(source: str) -> list[str]:
    """Read only the real header; declarations/quotations are never imports.

Recognizes module/prelude and [public] [meta] import [all] Module.Name, the
header grammar of the pinned Lean. Whitespace/comments may separate tokens.
The later Lean build remains responsible for full syntax/type checking.
"""
    stream = iter(tokens(source))
    token = next(stream, None)
    if token == Token("ident", "module"):
        token = next(stream, None)
    if token == Token("ident", "prelude"):
        token = next(stream, None)
    imports = []
    while token is not None:
        if token == Token("ident", "public"):
            token = next(stream, None)
        if token == Token("ident", "meta"):
            token = next(stream, None)
        if token != Token("ident", "import"):
            break
        token = next(stream, None)
        if token == Token("ident", "all"):
            token = next(stream, None)
        if token is None or token.kind != "ident":
            raise ValueError("Expected module name after Lean import")
        parts = [token.value]
        token = next(stream, None)
        while token == Token("symbol", "."):
            token = next(stream, None)
            if token is None or token.kind != "ident":
                raise ValueError("Incomplete Lean import name")
            parts.append(token.value)
            token = next(stream, None)
        imports.append(".".join(parts))
    return imports
