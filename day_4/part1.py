#!/usr/bin/env python3

import z3

s = z3.Solver()

# Wow, BitVec is orders than Int, even with constraints on each variable
pw = z3.BitVec('pw', 32)
digits = [z3.BitVec(f'd_{x}', 32) for x in range(0, 6)]

for x in range(0, 6):
    s.add(z3.And(digits[x] >= 0, digits[x] <= 9))

for x in range(0, 5):
    s.add(digits[x+1] >= digits[x])

s.add(z3.Or([digits[x] == digits[x+1] for x in range(0, 5)]))

# 347312-805915
s.add(pw == z3.Sum([digits[5-x] * 10**x for x in range(0, 6)]))
s.add(z3.And(pw >= 347312, pw <= 805915))

num_passwords = 0
while True:
    if s.check() == z3.sat:
        num_passwords += 1
        m = s.model()
        # print(f'pw = {m[pw]}')
        s.add(pw != m[pw])
    else:
        print(f'number of passwords: {num_passwords}')
        break
