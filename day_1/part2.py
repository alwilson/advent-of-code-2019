#!/usr/bin/env python3

def calc_fuel(x: int) -> int:
    return int(x / 3) - 2

with open('./input.txt') as fd:
    fuel_l = [calc_fuel(int(line)) for line in fd]
    print(fuel_l)

    fuel_sum = 0
    for fuel in fuel_l:
        print(f'module initial fuel: {fuel}')
        fuel_module = fuel
        more_fuel = calc_fuel(fuel)
        while more_fuel > 0:
            print(f'more fuel: {more_fuel}')
            fuel_module += more_fuel
            more_fuel = calc_fuel(more_fuel)
        fuel_sum += fuel_module
        print(f'fuel total so far: {fuel_sum}')

    print(f'end total: {fuel_sum}')
