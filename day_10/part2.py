#!/usr/bin/env python3

import pprint as pp
import math
from typing import Dict, Tuple
import numpy as np

asteroids = {}  # type: Dict[Tuple[int, int]]
y = 0
for line in open('./input.txt'):
    line = line.strip()
    x = 0
    for c in line:
        if c == '#':
            asteroids[(x, y)] = True
        x += 1

    y += 1

original = asteroids.copy()
# results = []
# for ast in asteroids.keys():
#     los = original.copy()
#     los.pop(ast)
#     # print(f'ax: {ast[0]} ay: {ast[1]}')
#     for other_ast in los.copy().keys():
#         if other_ast not in los:
#             continue
#         ax = ast[0]
#         ay = ast[1]
#         # print(f'\tox: {other_ast[0]} oy: {other_ast[1]}')
#         x = other_ast[0] - ast[0]
#         y = other_ast[1] - ast[1]
#         # print(f'\tx: {x} y: {y}')
#         gcd = math.gcd(x, y)
#         x //= gcd
#         y //= gcd
#         i = 1
#         first_found = False
#         xi = x
#         yi = y
#         # print(f'\txi: {xi} yi: {yi}')
#         while max(abs(ax + xi), abs(ax + yi)) < 100:
#             # print(f'\t\tx: {ax + xi} y: {ay + yi}')
#             if (ax + xi, ay + yi) in los:
#                 if not first_found:
#                     first_found = True
#                 else:
#                     popped = los.pop((ax + xi, ay + yi))
#                     # print(f'\t\t\tpopped: {popped}')
#             i += 1
#             xi = x * i
#             yi = y * i
#     results.append((len(los.keys()), ast))

# laser = max(results)[1]
laser = (30, 34)
# laser = (29, 35)
print(f'starting at: {laser}')

xs = [c[0] for c in original.keys()]
ys = [c[1] for c in original.keys()]

for y in range(min(ys), max(ys) + 1):
    for x in range(min(xs), max(xs)+1):
        if laser == (x, y):
            print('*', end='')
        elif (x, y) in original:
            print('#', end='')
        else:
            print('.', end='')
    print()

los = original.copy()
los.pop(laser)
angles = []
for ast in los:
    xdiff = ast[0] - laser[0]
    ydiff = laser[1] - ast[1]
    angles.append((np.arctan2(ydiff, xdiff), ast))

angles.sort()
# pp.pprint(angles)

def walk(start_ang, stop_ang):
    targets = []
    for ang in angles:
        if start_ang >= ang[0] > stop_ang:
            targets.append(ang)
    while len(targets) > 0:
        next_ang = max(targets)[0]
        detected = []
        for t_idx, t in enumerate(targets.copy()):
            if t[0] == next_ang:
                detected.append(targets.pop())
        if len(detected) == 0:
            start_ang = max(targets)


walk(math.pi/2, 0)

# walk(math.pi, math.pi)
# walk(math.pi/2, math.pi/2)
# walk(0, 0)
# walk(-math.pi/2, -math.pi/2)
# walk(-math.pi, -math.pi)

# pp.pprint(angles)


