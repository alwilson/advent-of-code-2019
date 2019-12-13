#!/usr/bin/env python3

from typing import Dict
import pprint as pp
from itertools import permutations

import queue
import threading

import tracemalloc


class program(threading.Thread):
    def __init__(self, threadID, name, state, q_in, q_out):
        threading.Thread.__init__(self)
        self.threadID = threadID
        self.name = name
        self.state = state
        self.q_in = q_in
        self.q_out = q_out


    def run(self):
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
            state_mode = True
            while (get_mem(pc) % 100) != 99:  # Halt
                instr = get_mem(pc)
                opcode = instr % 100
                param1 = (instr // 100) % 10
                p1 = get_mem(pc + 1)
                param2 = (instr // 1000) % 10
                p2 = get_mem(pc + 2)
                param3 = (instr // 10000) % 10
                p3 = get_mem(pc + 3)
                print(f'{self.name}: ', end='')
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
                    if state_mode:
                        num = self.state
                        state_mode = False
                    else:
                        print(f'waiting on {self.q_in}')
                        num = self.q_in.get(block=True)
                    memory[p1] = num
                    print(f'in    {p1:5} {num}')
                    pc += 2
                elif opcode == 4:  # Output
                    output = p1 if param1 else get_mem(p1)
                    print(f'out   {p1:5} {output:5}')
                    self.q_out.put(output)
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
            else:
                print(f'[{pc:4}]              : end')
            #q.task_done()
            #print(outputs)
            #return outputs[-1]
            #return final_output


tracemalloc.start()

phase_perms = permutations([5, 6, 7, 8, 9])
results = []
for phases in list(phase_perms):
    phases = list(phases)
    qs = []
    for p in phases:
        qs.append(queue.Queue())
    qs[-1].put(0)
    for q in qs:
        pp.pprint(list(q.queue))
    threads = []
    print(f'phases: {phases}')
    for p_idx, p in enumerate(phases):
        print(f'creating {p} at {p_idx}')
        t = program(p_idx, f'Thread-{p_idx}', p, qs[p_idx-1], qs[p_idx])
        threads.append(t)

    for t in threads:
        print(f'starting {t.name}')
        t.start()


    print('waiting')
    for t in threads:
        print(f'joining {t.name} ==============')
        t.join()

    print('checking Qs')
    for q in qs:
        pp.pprint(list(q.queue))
    results.append(list(qs[-1].queue)[0])
print(max(results))

snapshot = tracemalloc.take_snapshot()
top_stats = snapshot.statistics('lineno')

print("[ Top 10 ]")
for stat in top_stats[:10]:
    print(stat)

