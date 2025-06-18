#!/usr/bin/env python3

import sys
import re

rule_re = re.compile(r'^\s*~~~\s+(\w+)\s+\((\d+)\)')


def parse(path):
    result = []
    with open(path) as f:
        for line in f:
            line = line.rstrip('\n')
            if m := rule_re.match(line):
                name = m.group(1)
                result.append((name, line))
    return result


def main(full_path, maybe_missing_path):
    full = parse(full_path)
    maybe_missing = parse(maybe_missing_path)

    iter_missing = iter(maybe_missing)
    try:
        m_name, m_line = next(iter_missing)
    except StopIteration:
        m_name, m_line = None, None

    left_width = max(len(line) for _, line in full)

    for f_name, f_line in full:
        if m_name == f_name:
            print(f"{f_line:<{left_width}}    {m_line}")
            try:
                m_name, m_line = next(iter_missing)
            except StopIteration:
                m_name, m_line = None, None
        else:
            print(f"{f_line:<{left_width}}    ")


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: match_by_dominant.py full.txt partial.txt")
        sys.exit(1)
    main(sys.argv[1], sys.argv[2])
