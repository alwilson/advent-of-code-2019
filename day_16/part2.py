#!/usr/bin/env python3

from typing import List

signal_chars = open('input.txt').readline().strip()

signal = []  # type: List[int]
for s in signal_chars:
    signal.append(int(s))

big_signal = []  # type: List[int]
for _ in range(10000):
    big_signal += signal

# Calculate offset and prune signal
start = sum([s * 10 ** s_idx for s_idx, s in enumerate(reversed(signal[:7]))])
signal = big_signal[start:]
print(f'signal size: {len(signal)}')

# The pattern [0, 1, 0, -1] at large offsets doesn't matter like in part2
# This assumes that the pattern is all zeros up til the first offset number, and 1 till the end of the pattern
# *** That assumption may not be 100% correct for all input ***
for run in range(100):
    print(f'run: {run}')
    total = sum(signal)
    next_sig = []  # type: List[int]
    next_sig.append(abs(total) % 10)
    for c_idx, c in enumerate(signal[:-1]):
        total -= c
        next_sig.append(abs(total) % 10)
    signal = next_sig
print(signal[:8])
