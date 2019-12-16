#!/usr/bin/env python3

from typing import Dict, Tuple
import time


def print_screen(screen: Dict):
    xs = [c[0] for c in screen.keys()]
    ys = [c[1] for c in screen.keys()]

    print('\033[{};{}H'.format(0, 0))
    for y in range(min(ys), max(ys) + 1):
        for x in range(min(xs), max(xs) + 1):
            if (x, y) in screen:
                c = screen[(x, y)]
                if c == '\n':
                    continue
                if isinstance(c, str):
                    print(c, end='')
                else:
                    print(c % 10, end='')
            else:
                print(' ', end='')
        print()


maze = {}  # type: Dict[Tuple[int, int], str]
y = 0
oxygen_edge = {}
for line in open('./maze_output.txt'):
    # line = line.strip()
    x = 0
    for c in line:
        maze[(x, y)] = c
        if c == 'O':
           oxygen_edge[(x, y)] = True
        x += 1
    y += 1

minutes = 0
while len(oxygen_edge.keys()):
    # print(f'pre oxygen edges: {len(oxygen_edge.keys())}')
    # print(oxygen_edge.keys())
    for oxy in list(oxygen_edge.keys()):
        next_locs = [(oxy[0], oxy[1] + 1),
                     (oxy[0], oxy[1] - 1),
                     (oxy[0] + 1, oxy[1]),
                     (oxy[0] - 1, oxy[1])]
        for next_loc in next_locs:
            if next_loc in maze and maze[next_loc] == '.':
                oxygen_edge[next_loc] = True
                maze[next_loc] = 'E'
        maze[oxy] = 'O'
        del oxygen_edge[oxy]
    minutes += 1
    print_screen(maze)
    print(f'oxygen edges: {len(oxygen_edge.keys())}')
    print(f'minutes elapsed: {minutes}')
    # FIXME This minute is off by one minute... why?
    time.sleep(0.05)
