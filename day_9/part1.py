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
        relative_base = 0

        def get_mem(x: int) -> int:
            if x not in memory:
                memory[x] = 0
                return 0
            else:
                return memory[x]

        def param_arg(p: int, param: int):
            if param == 0:
                return get_mem(p)
            elif param == 1:
                return p
            elif param == 2:
                return get_mem(relative_base + p)

        def set_mem(p: int, param: int, num: int):
            if param == 2:
                memory[relative_base + p] = num
            else:
                memory[p] = num

        with open('./input.txt') as fd:
            instrs = [int(x) for x in fd.readline().split(',')]
            instrs += [0, 0, 0, 0, 0]
            for i in range(0, len(instrs)):
                memory[i] = instrs[i]

            pc = 0
            outputs = []
            state_mode = True
            iters = 0
            while (get_mem(pc) % 100) != 99:  # and iters < 10:  # Halt
                iters += 1
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
                    num = param_arg(p1, param1) + param_arg(p2, param2)
                    set_mem(p3, param3, num)
                    print(f'add   {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 2:  # Multiply
                    num = param_arg(p1, param1) * param_arg(p2, param2)
                    set_mem(p3, param3, num)
                    print(f'mult  {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 3:  # Input
                    if state_mode:
                        num = self.state
                        state_mode = False
                    else:
                        print(f'waiting on {self.q_in}')
                        num = self.q_in.get(block=True)
                    set_mem(p1, param1, num)
                    print(f'in    {p1:5} {num}')
                    pc += 2
                elif opcode == 4:  # Output
                    output = param_arg(p1, param1)
                    print(f'out   {p1:5} {output:5}')
                    self.q_out.put(output)
                    outputs.append(output)
                    pc += 2
                elif opcode == 5:  # Jump If True
                    if param_arg(p1, param1) != 0:
                        pc = param_arg(p2, param2)
                    else:
                        pc += 3
                    print(f'jmpt  {p1:5} {p2:5} -> {pc:5}')
                elif opcode == 6:  # Jump If False
                    if param_arg(p1, param1) == 0:
                        pc = param_arg(p2, param2)
                    else:
                        pc += 3
                    print(f'jmpf  {p1:5} {p2:5}')
                elif opcode == 7:  # Less Than
                    if param_arg(p1, param1) < param_arg(p2, param2):
                        set_mem(p3, param3, 1)
                    else:
                        set_mem(p3, param3, 0)
                    print(f'less  {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 8:  # Less Than
                    if param_arg(p1, param1) == param_arg(p2, param2):
                        set_mem(p3, param3, 1)
                    else:
                        set_mem(p3, param3, 0)
                    print(f'equal {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 9:
                    relative_base += param_arg(p1, param1)
                    pc += 2
                    print(f'relb  {p1:5} -> {relative_base}')
                else:
                    print('unknown instruction!')
            else:
                print(f'[{pc:4}]              : end')
            #q.task_done()
            #print(outputs)
            #return outputs[-1]
            #return final_output

q_in = queue.Queue()
q_out = queue.Queue()

t = program(0, f'Thread-{0}', 2, q_in, q_out)
t.start()
t.join()

pp.pprint(list(q_in.queue))
pp.pprint(list(q_out.queue))
# phase_perms = permutations([5, 6, 7, 8, 9])
# results = []
# for phases in list(phase_perms):
#     phases = list(phases)
#     qs = []
#     for p in phases:
#         qs.append(queue.Queue())
#     qs[-1].put(0)
#     for q in qs:
#         pp.pprint(list(q.queue))
#     threads = []
#     print(f'phases: {phases}')
#     for p_idx, p in enumerate(phases):
#         print(f'creating {p} at {p_idx}')
#         t = program(p_idx, f'Thread-{p_idx}', p, qs[p_idx-1], qs[p_idx])
#         threads.append(t)
#
#     for t in threads:
#         print(f'starting {t.name}')
#         t.start()
#
#
#     print('waiting')
#     for t in threads:
#         print(f'joining {t.name} ==============')
#         t.join()
#
#     print('checking Qs')
#     for q in qs:
#         pp.pprint(list(q.queue))
#     results.append(list(qs[-1].queue)[0])
# print(max(results))
#
# snapshot = tracemalloc.take_snapshot()
# top_stats = snapshot.statistics('lineno')
#
# print("[ Top 10 ]")
# for stat in top_stats[:10]:
#     print(stat)

