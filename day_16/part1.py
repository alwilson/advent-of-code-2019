#!/usr/bin/env python3

from typing import List

signal_chars = open('input.txt').readline().strip()

signal = []  # type: List[int]
for s in signal_chars:
    signal.append(int(s))


pat = [0, 1, 0, -1]

for run in range(100):
    print(f'run: {run}')
    next_sig = []  # type: List[int]
    #print(signal)
    for c_idx, c in enumerate(signal):
        idx_pat = [pat[0]] * (c_idx + 1) + [pat[1]] * (c_idx + 1) + [pat[2]] * (c_idx + 1) + [pat[3]] * (c_idx + 1)
        idx_pat = idx_pat[1:] + [idx_pat[0]]
        # print(idx_pat)
        value = 0
        for s_idx, s in enumerate(signal):
            #print(f'{s}*{idx_pat[s_idx % len(idx_pat)]} + ', end='')
            value += s * idx_pat[s_idx % len(idx_pat)]
        value = abs(value) % 10
        #print(f'0 = {value}')
        next_sig += [value]
    signal = next_sig
print(signal[:8])
