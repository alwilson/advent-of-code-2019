#!/usr/bin/env python3

from typing import List, Tuple

with open('./input.txt') as fd:
    wire1 = [(x[0], int(x[1:])) for x in fd.readline().split(',')]
    wire2 = [(x[0], int(x[1:])) for x in fd.readline().split(',')]


def walk_the_wire(wire: List[Tuple[str, int]]) -> List[Tuple[int, int]]:
    path = [(0, 0)]
    for w in wire:
        last = path[-1]
        if w[0] == 'R':
            path += [(last[0] + (x + 1), last[1]) for x in range(0, w[1])]
        if w[0] == 'L':
            path += [(last[0] - (x + 1), last[1]) for x in range(0, w[1])]
        if w[0] == 'U':
            path += [(last[0], last[1] + (x + 1)) for x in range(0, w[1])]
        if w[0] == 'D':
            path += [(last[0], last[1] - (x + 1)) for x in range(0, w[1])]
    return path[1:]


path1 = walk_the_wire(wire1)
path2 = walk_the_wire(wire2)

intersection = set(path1) & set(path2)

manhattans = [abs(x) + abs(y) for x, y in intersection]
print(min(manhattans))
