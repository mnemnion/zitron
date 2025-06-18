#!/usr/bin/env python3

import sys
import os
import re


def normalize_basename(filename):
    parts = filename.split(".")
    if len(parts) > 2:
        return parts[0] + "." + parts[-1]
    return filename


def main():
    if len(sys.argv) != 2:
        print(f"Usage: {sys.argv[0]} path/to/file", file=sys.stderr)
        sys.exit(1)

    path = sys.argv[1]
    basename = normalize_basename(os.path.basename(path))

    line_re = re.compile(r'^#line\s+(\d+)\s+"([^"]+)"')

    with open(path, 'r', encoding='utf-8') as f:
        for lineno, line in enumerate(f, start=1):
            m = line_re.match(line)
            if m:
                declared_line = int(m.group(1))
                declared_file = normalize_basename(
                    os.path.basename(m.group(2)))
                if declared_file == basename:
                    expected = lineno + 1
                    if declared_line == expected:
                        print(f"Line {lineno}: Ok")
                    else:
                        delta = declared_line - expected
                        print(f"Line {lineno}: want {expected}, got {
                              declared_line} ({delta:+d})")


if __name__ == "__main__":
    main()
