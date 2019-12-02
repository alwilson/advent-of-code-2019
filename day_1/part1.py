#!/usr/bin/env python3

def calc_fuel(x: int) -> int:
    return int(x / 3) - 2

with open('./input.txt') as fd:
    fuel_l = [calc_fuel(int(line)) for line in fd]
    print(fuel_l)

    sum = 0
    for fuel in fuel_l:
        sum += fuel
    print(sum)
