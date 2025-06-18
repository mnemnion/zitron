#!/usr/bin/env python3

import sys
from collections import defaultdict


def extract_key(line):
    parts = line.split()
    return parts[1] if len(parts) > 1 else ''


def read_and_group(path):
    with open(path) as f:
        lines = [line.rstrip('\n') for line in f if line.strip()]
    groups = defaultdict(list)
    for line in lines:
        groups[extract_key(line)].append(line)
    return groups


def main(f1, f2):
    a_groups = read_and_group(f1)
    b_groups = read_and_group(f2)

    all_keys = sorted(set(a_groups) | set(b_groups))

    left_width = max((len(line) for lines in a_groups.values()
                     for line in lines), default=0)

    for key in all_keys:
        a_lines = a_groups.get(key, [])
        b_lines = b_groups.get(key, [])
        max_len = max(len(a_lines), len(b_lines))
        for i in range(max_len):
            left = a_lines[i] if i < len(a_lines) else ''
            right = b_lines[i] if i < len(b_lines) else ''
            print(f"{left:<{left_width}}    {right}")


if __name__ == '__main__':
    if len(sys.argv) != 3:
        print("Usage: compare_rules.py file1.txt file2.txt")
        sys.exit(1)
    main(sys.argv[1], sys.argv[2])
