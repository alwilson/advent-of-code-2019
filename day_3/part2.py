#!/usr/bin/env python3

from typing import List, Tuple

with open('./input.txt') as fd:
    wire1 = [(x[0], int(x[1:])) for x in fd.readline().split(',')]
    wire2 = [(x[0], int(x[1:])) for x in fd.readline().split(',')]


def walk_the_wire(wire: List[Tuple[str, int]]) -> List[Tuple[int, int, int]]:
    path = [(0, 0, 0)]
    for w in wire:
        last = path[-1]
        if w[0] == 'R':
            path += [(last[0] + (x + 1), last[1], last[2] + (x + 1)) for x in range(0, w[1])]
        if w[0] == 'L':
            path += [(last[0] - (x + 1), last[1], last[2] + (x + 1)) for x in range(0, w[1])]
        if w[0] == 'U':
            path += [(last[0], last[1] + (x + 1), last[2] + (x + 1)) for x in range(0, w[1])]
        if w[0] == 'D':
            path += [(last[0], last[1] - (x + 1), last[2] + (x + 1)) for x in range(0, w[1])]
    return path[1:]


path1 = walk_the_wire(wire1)
path2 = walk_the_wire(wire2)


def path_no_dups(path):
    path_dict = {}
    path_no_dups = []
    for p in path:
        point = (p[0], p[1])
        if point not in path_dict.keys():
            path_dict[point] = p
            path_no_dups.append(p)
    return path_no_dups


path1_no_dups = path_no_dups(path1)
path2_no_dups = path_no_dups(path2)

paths = path1_no_dups + path2_no_dups
paths_dict = {}
wire_delays = []
for p in paths:
    point = (p[0], p[1])
    if point not in paths_dict.keys():
        paths_dict[point] = p
    else:
        wire_delays.append(paths_dict[point][2] + p[2])

wire_delays.sort()
print(wire_delays[0])
