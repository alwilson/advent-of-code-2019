#!/usr/bin/env python3

import collections
from typing import List
from itertools import combinations

import pprint as pp
import numpy as np

class point(object):
    __slots__ = ['x', 'y', 'z']
    def __init__(self, x, y, z):
        self.x = x
        self.y = y
        self.z = z

class moon(object):
    __slots__ = ['pos', 'vel']
    def __init__(self, pos, vel):
        self.pos = pos  # type: point
        self.vel = vel  # type: point

# point = collections.namedtuple('point', 'x y z')
# moon = collections.namedtuple('moon', 'pos vel')

steps = 0
moons = []  # type: List[moon]
moons.append(moon(pos=point(x=0, y=4, z=0),      vel=point(x=0, y=0, z=0)))
moons.append(moon(pos=point(x=-10, y=-6, z=-14), vel=point(x=0, y=0, z=0)))
moons.append(moon(pos=point(x=9, y=-16, z=-3),   vel=point(x=0, y=0, z=0)))
moons.append(moon(pos=point(x=6, y=-1, z=2),     vel=point(x=0, y=0, z=0)))

# moons.append(moon(pos=point(x=-1, y=0, z=2), vel=point(x=0, y=0, z=0)))
# moons.append(moon(pos=point(x=2, y=-10, z=-7), vel=point(x=0, y=0, z=0)))
# moons.append(moon(pos=point(x=4, y=-8, z=8), vel=point(x=0, y=0, z=0)))
# moons.append(moon(pos=point(x=3, y=5, z=-1), vel=point(x=0, y=0, z=0)))

# moons.append(moon(pos=point(x=-8, y=-10, z=0), vel=point(x=0, y=0, z=0)))
# moons.append(moon(pos=point(x=5, y=5, z=10), vel=point(x=0, y=0, z=0)))
# moons.append(moon(pos=point(x=2, y=-7, z=3),   vel=point(x=0, y=0, z=0)))
# moons.append(moon(pos=point(x=9, y=-8, z=-3),  vel=point(x=0, y=0, z=0)))


def add_vel(moons: List[moon]):
    for m in moons:
        m.pos.x += m.vel.x
        m.pos.y += m.vel.y
        m.pos.z += m.vel.z

def calc_grav(moons: List[moon]):
    visited = {}
    for a in moons:
        for b in moons:
            if a != b and (a,b) not in visited and (b,a) not in visited:
                visited[(a,b)] = True
                visited[(b,a)] = True
                if a.pos.x > b.pos.x:
                    diff = 1
                elif a.pos.x == b.pos.x:
                    diff = 0
                else:
                    diff = -1
                a.vel.x += -diff
                b.vel.x += diff

                if a.pos.y > b.pos.y:
                    diff = 1
                elif a.pos.y == b.pos.y:
                    diff = 0
                else:
                    diff = -1
                a.vel.y += -diff
                b.vel.y += diff

                if a.pos.z > b.pos.z:
                    diff = 1
                elif a.pos.z == b.pos.z:
                    diff = 0
                else:
                    diff = -1
                a.vel.z += -diff
                b.vel.z += diff

def calc_energy(moons: List[moon]):
    energy = 0
    for m in moons:
       energy += (abs(m.pos.x) + abs(m.pos.y) + abs(m.pos.z)) * (abs(m.vel.x) + abs(m.vel.y) + abs(m.vel.z))
    print(f'Total Energy: {energy}')
    return energy

def print_stuff(moons: List[moon]):
    print(f'After {steps} steps')
    for m in moons:
        print(f'pos=<x={m.pos.x:3}, y={m.pos.y:3}, z={m.pos.z:3}>, vel=<x={m.vel.x:3}, y={m.vel.y:3}, z={m.vel.z:3}>')

def step(moons: List[moon]):
    calc_grav(moons)
    add_vel(moons)


def hashm(moons: List[moon]):
    hash = ''
    for m in moons:
        hash += str(m.pos.x) # + str(m.pos.y) + str(m.pos.z)
        hash += str(m.vel.x) # + str(m.vel.y) + str(m.vel.z)
    # print(hash)
    return hash

# print(np.lcm.reduce([286332, 161428, 54224]))
# print(np.lcm.reduce([286332, 161428, 54224]))
# print(np.lcm.reduce([286332, 54224, 161428]))
print(np.lcm.reduce([286332, 96236, 161428]))
# 96236 161428 286332
# print(np.lcm.reduce([18, 28, 44]))
# print(np.lcm.reduce([4702, 5898, 2028]))
exit(0)

states = {}
steps = 0
states[hashm(moons)] = [steps]
while True:
#for i in range(10):
    if steps % 1000000 == 0:
        print_stuff(moons)
        # calc_energy(moons)
    step(moons)
    steps += 1
    hashm_ret = hashm(moons)
    if hashm_ret in states:
        states[hashm_ret].append(steps)
        print(f'repeated after {steps} steps with {hashm_ret}')
        break
    # states[hashm_ret] = [steps]
# steps = 1000
# print_stuff(moons)
#calc_energy(moons)
# pp.pprint(states)

# x is 286332
# y is 161428
# z is 54224
