#!/usr/bin/env python3

from typing import Dict
import pprint as pp


memory = {}  # type: Dict[int, int]


def get_mem(x: int) -> int:
    if x not in memory:
        memory[x] = 0
        return 0
    else:
        return memory[x]


with open('./input.txt') as fd:
    instrs = [int(x) for x in fd.readline().split(',')]
    for i in range(0, len(instrs)):
        memory[i] = instrs[i]
    memory[1] = 12
    memory[2] = 2
    pp.pprint(memory)

    pc = 0
    while instrs[pc] != 99:  # Halt
        if instrs[pc] == 1:  # Add
            memory[instrs[pc+3]] = get_mem(instrs[pc+1]) + get_mem(instrs[pc+2])
            print(f'add  {instrs[pc+1]} {instrs[pc+2]} {instrs[pc+3]}')
            pc += 4
        elif instrs[pc] == 2:  # Multiply
            memory[instrs[pc+3]] = get_mem(instrs[pc+1]) * get_mem(instrs[pc+2])
            print(f'mult {instrs[pc+1]} {instrs[pc+2]} {instrs[pc+3]}')
            pc += 4
        else:
            print('unknown instruction!')
    pp.pprint(memory)
    print('end')
