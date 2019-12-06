#!/usr/bin/env python3

with open('./input.txt') as fd:
    orbits = [tuple(reversed(line.strip().split(')'))) for line in fd]
    orbit_dict = dict(orbits)
    sum_orbits = 0
    o = 'YOU'
    you_orbits = set()
    while orbit_dict[o] in orbit_dict:
        o = orbit_dict[o]
        you_orbits.add(o)

    o = 'SAN'
    san_orbits = set()
    while orbit_dict[o] in orbit_dict:
        o = orbit_dict[o]
        san_orbits.add(o)

    print(len(san_orbits))
    print(len(you_orbits))
    diff = san_orbits.symmetric_difference(you_orbits)
    print(len(diff))
