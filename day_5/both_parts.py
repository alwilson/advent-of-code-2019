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
    instrs += [0, 0, 0, 0, 0]
    for i in range(0, len(instrs)):
        memory[i] = instrs[i]

    pc = 0
    outputs = []
    while (get_mem(pc) % 100) != 99:  # Halt
        instr = get_mem(pc)
        opcode = instr % 100
        param1 = (instr // 100) % 10
        p1 = get_mem(pc + 1)
        param2 = (instr // 1000) % 10
        p2 = get_mem(pc + 2)
        param3 = (instr // 10000) % 10
        p3 = get_mem(pc + 3)
        print(f'[{pc:4}] ({instr:05} {param1} {param2} {param3}): ', end='')
        if opcode == 1:  # Add
            memory[p3] = (p1 if param1 else get_mem(p1)) + (p2 if param2 else get_mem(p2))
            print(f'add   {p1:5} {p2:5} {p3:5} = {memory[p3]:5}')
            pc += 4
        elif opcode == 2:  # Multiply
            memory[p3] = (p1 if param1 else get_mem(p1)) * (p2 if param2 else get_mem(p2))
            print(f'mult  {p1:5} {p2:5} {p3:5} = {memory[p3]:5}')
            pc += 4
        elif opcode == 3:  # Input
            memory[p1] = 5
            print(f'in    {p1:5} 5')
            pc += 2
        elif opcode == 4:  # Output
            output = p1 if param1 else get_mem(p1)
            print(f'out   {p1:5} {output:5}')
            outputs.append(output)
            pc += 2
        elif opcode == 5:  # Jump If True
            if (p1 if param1 else get_mem(p1)) != 0:
                pc = (p2 if param2 else get_mem(p2))
            else:
                pc += 3
            print(f'jmpt  {p1:5} {p2:5} -> {pc:5}')
        elif opcode == 6:  # Jump If False
            if (p1 if param1 else get_mem(p1)) == 0:
                pc = (p2 if param2 else get_mem(p2))
            else:
                pc += 3
            print(f'jmpf  {p1:5} {p2:5}')
        elif opcode == 7:  # Less Than
            if (p1 if param1 else get_mem(p1)) < (p2 if param2 else get_mem(p2)):
                memory[p3] = 1
            else:
                memory[p3] = 0
            print(f'less  {p1:5} {p2:5} {p3:5}')
            pc += 4
        elif opcode == 8:  # Less Than
            if (p1 if param1 else get_mem(p1)) == (p2 if param2 else get_mem(p2)):
                memory[p3] = 1
            else:
                memory[p3] = 0
            print(f'equal {p1:5} {p2:5} {p3:5}')
            pc += 4
        else:
            print('unknown instruction!')
    print('end')
    print(outputs)
