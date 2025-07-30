#!/usr/bin/env python3
import sys
import re

directive_re = re.compile(r'^(%)(ifdef|ifndef|if|elseif)\b(.*)$')


def extract_macros(expr: str) -> list[str]:
    """
    Extract all macro identifiers from the given expression string.
    Identifiers match C-style names: start with letter or underscore,
    followed by letters, digits, or underscores.
    """
    return re.findall(r"\b[A-Za-z_][A-Za-z0-9_]*\b", expr)


def main():
    """
    Read lines from stdin, collect all unique macros from %ifdef, %ifndef, %if, and %elseif directives,
    then print each macro and the total count.
    """
    macros: set[str] = set()
    for line in sys.stdin:
        m = directive_re.match(line)
        if not m:
            continue
        directive = m.group(2)
        rest = m.group(3).strip()

        if directive in ('ifdef', 'ifndef'):
            if rest:
                macros.add(rest)
        else:  # 'if' or 'elseif'
            for macro in extract_macros(rest):
                macros.add(macro)

    # Print sorted list of unique macros
    for macro in sorted(macros):
        print(macro)

    # Print total count
    print(f"\nTotal unique macros: {len(macros)}")


if __name__ == '__main__':
    main()
