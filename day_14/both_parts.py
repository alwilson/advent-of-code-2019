#!/usr/bin/env python3

# Notes:
#  - This may be a naive approach to solving with Z3, but it works!
#  - Each reaction is converted into an assertion


import z3
from typing import Dict, List

s = z3.Solver()

fuel = None
names = {}  # type: Dict[str, List[z3.Int]]
sums = {}  # type: Dict[str, z3.Int]


def get_name(n: str) -> z3.Int:
    """ Create a unique variable for each input chemical """
    if n in names:
        name_int = z3.Int(n + '_' + str(len(names[n])))
        names[n].append(name_int)
        return name_int
    else:
        names[n] = [z3.Int(n + '_0')]
        return names[n][0]


def get_sum(n: str) -> z3.Int:
    """ Find/create sum variable for a given chemical """
    if n not in sums:
        sums[n] = z3.Int(n + '_sum')
    return sums[n]


for line in open('input.txt'):
    left_right = line.strip().split('=>')
    num_name = left_right[1].strip().split(' ')
    rnum = int(num_name[0])
    rname = num_name[1]
    lnum_names = []
    for left in left_right[0].split(','):
        left = left.strip()
        num_name = left.split(' ')
        num = int(num_name[0])
        name = num_name[1]
        lnum_names.append((num, name))

    # Constrain each input to be equal to the sum of the output
    for lnum_name in lnum_names:
        lnum = z3.IntVal(lnum_name[0])
        lname = get_name(lnum_name[1])
        rname_sum = get_sum(rname)
        rnum_int = z3.IntVal(rnum)
        s.add(lname == lnum * (rname_sum / rnum_int + z3.If(rname_sum % rnum_int != 0, 1, 0)))

for name in names.keys():
    s.add(get_sum(name) == z3.Sum(names[name]))

### PART 1 ###

before_fuel = s.assertions()  # Save off model before constraining fuel for part 2. push/pop hangs the solver here. Why?
s.add(get_sum('FUEL') == 1)

# print(s.assertions())

# Check if we found a solution or not
result = s.check()
if result == z3.sat:
    m = s.model()
    ore = m[get_sum('ORE')].as_long()  # Grab the ore value from the model
    print(f'Part 1: ore = {ore}')
else:
    print(result)


### PART 2 ###

# Binary search by starting at 1, then double until ore is over 1 Trillion
fuel = 1
prev_fuel = 0
last_good = 0
while True:
    s = z3.Solver()
    s.add(before_fuel)
    s.add(get_sum('FUEL') == fuel)
    result = s.check()
    if result == z3.sat:
        m = s.model()
        ore = m[get_sum('ORE')].as_long()  # Grab the ore value from the model
        rem = 1000000000000 - ore

        if rem < 0:  # Over 1 Trillion ore used!
            prev_fuel = fuel
            fuel = (fuel + last_good) // 2
        else:  # Under 1 Trillion ore used.
            last_good = fuel
            if prev_fuel == 0:
                fuel *= 2
            else:
                new_fuel = (fuel + prev_fuel) // 2
                if fuel == new_fuel:
                    print(f'Part 2: max fuel for 1 Trillion ore = {fuel}')
                    break
                else:
                    fuel = new_fuel
    else:  # Unsat or Unknown
        print(result)
        break
