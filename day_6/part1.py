#!/usr/bin/env python3

with open('./input.txt') as fd:
    orbits = [tuple(reversed(line.strip().split(')'))) for line in fd]
    orbit_dict = dict(orbits)
    sum_orbits = 0
    for o in orbit_dict.keys():
        num_orbits = 1
        while orbit_dict[o] in orbit_dict:
            num_orbits += 1
            o = orbit_dict[o]
        sum_orbits += num_orbits
    print(sum_orbits)


