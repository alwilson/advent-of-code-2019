#!/usr/bin/env python3

from typing import Dict, List
import pprint as pp
import z3
import sys


# Notes
# - BitVec is used everywhere since Int types/sorts are unbounded and harder search than a 32-bit bit vector
# - This solution attempts to describe updates

# Assumptions to keep SMT solution simple
# - Operations will not update opcode locations
# - Operations will not change opcode locations to the halt or 99 opcode
# Both assumptions appear to be correct for my program, are they correct for all version?!?!

# Dictionary of memory location updates, this is used to generate the chain of opcode dependencies
memory = {}  # type: Dict[int, List]

# Generate a new BitVec before each operation, this represents the next value at this memory location
def gen_new_mem(x: int) -> int:
    if x not in memory:
        memory[x] = [z3.BitVecVal(0, 32)]
    else:
        memory[x].append(z3.BitVec(f'mem_{x}_{len(memory[x])}', 32))


with open('./input.txt') as fd:
    s = z3.Solver()
    instrs = [int(x) for x in fd.readline().split(',')]
    # Initialize memory, except at the input locations
    for i in range(0, len(instrs)):
        if i != 1 and i != 2:
            memory[i] = [z3.BitVecVal(instrs[i], 32)]

    # Constrain memory locations 1 and 2 to be between 0 and 99
    mem_1 = z3.BitVec(f'mem_1', 32)
    memory[1] = [mem_1]
    s.add(z3.And(mem_1 >= 0, mem_1 < 100))

    mem_2 = z3.BitVec(f'mem_2', 32)
    memory[2] = [mem_2]
    s.add(z3.And(mem_2 >= 0, mem_2 < 100))

    # At each add/mult instruction create a memory location update, then stop at the halt instruction
    # The assumptions mentioned before are important here
    pc = 0
    while instrs[pc] != 99:  # Halt
        if instrs[pc] == 1:  # Add
            print(f'add {instrs[pc+1]} {instrs[pc+2]} {instrs[pc+3]}')
            # Find and save the latest updates to each src location
            src1 = memory[instrs[pc+1]][-1]
            src2 = memory[instrs[pc+2]][-1]
            # Now generate a new update for this location
            gen_new_mem(instrs[pc+3])
            s.add(memory[instrs[pc+3]][-1] == src1 + src2)
            pc += 4
        elif instrs[pc] == 2:  # Multiply
            print(f'mult {instrs[pc+1]} {instrs[pc+2]} {instrs[pc+3]}')
            # Find and save the latest updates to each src location
            src1 = memory[instrs[pc+1]][-1]
            src2 = memory[instrs[pc+2]][-1]
            # Now generate a new update for this location
            gen_new_mem(instrs[pc+3])
            s.add(memory[instrs[pc+3]][-1] == src1 * src2)
            pc += 4
    print('end')

    # Constrain the last update to memory location 0 to the problem statement
    # Mine was 19690720
    s.add(memory[0][-1] == sys.argv[1])

    pp.pprint(s.assertions())

    if s.check() == z3.sat:
        print('sat')
        m = s.model()
        print(f'mem[0]: {m[memory[0][-1]]}')
        print(f'mem[1]: {m[mem_1]}')
        print(f'mem[2]: {m[mem_2]}')
    else:
        print('unsat')
