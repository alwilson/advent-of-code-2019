#!/usr/bin/env python3

import pprint as pp
import math
from typing import Dict, Tuple

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
results = []
for ast in asteroids.keys():
    los = original.copy()
    los.pop(ast)
    print(f'ax: {ast[0]} ay: {ast[1]}')
    for other_ast in los.copy().keys():
        if other_ast not in los:
            continue
        ax = ast[0]
        ay = ast[1]
        print(f'\tox: {other_ast[0]} oy: {other_ast[1]}')
        x = other_ast[0] - ast[0]
        y = other_ast[1] - ast[1]
        print(f'\tx: {x} y: {y}')
        gcd = math.gcd(x, y)
        x //= gcd
        y //= gcd
        i = 1
        first_found = False
        xi = x
        yi = y
        print(f'\txi: {xi} yi: {yi}')
        while max(abs(ax + xi), abs(ax + yi)) < 100:
            # print(f'\t\tx: {ax + xi} y: {ay + yi}')
            if (ax + xi, ay + yi) in los:
                if not first_found:
                    first_found = True
                else:
                    popped = los.pop((ax + xi, ay + yi))
                    # print(f'\t\t\tpopped: {popped}')
            i += 1
            xi = x * i
            yi = y * i
    results.append((len(los.keys()), ast))

print(max(results))

