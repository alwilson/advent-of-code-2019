#!/usr/bin/env python3

from typing import Dict
import pprint as pp
from itertools import permutations

import queue
import threading

from random import randint

import tracemalloc

import sys
import os
import readchar
import time


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
            state_mode = False
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
                #print(f'{self.name}: ', end='')
                #print(f'[{pc:4}] ({instr:05} {param1} {param2} {param3}): ', end='')
                if opcode == 1:  # Add
                    num = param_arg(p1, param1) + param_arg(p2, param2)
                    set_mem(p3, param3, num)
                    #print(f'add   {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 2:  # Multiply
                    num = param_arg(p1, param1) * param_arg(p2, param2)
                    set_mem(p3, param3, num)
                    #print(f'mult  {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 3:  # Input
                    if state_mode:
                        num = self.state
                        state_mode = False
                    else:
                        num = self.q_in.get(block=True)
                        if num == 99:
                            return
                    set_mem(p1, param1, num)
                    #print(f'in    {p1:5} {num}')
                    pc += 2
                elif opcode == 4:  # Output
                    output = param_arg(p1, param1)
                    #print(f'out   {p1:5} {output:5}')
                    self.q_out.put(output)
                    outputs.append(output)
                    pc += 2
                elif opcode == 5:  # Jump If True
                    if param_arg(p1, param1) != 0:
                        pc = param_arg(p2, param2)
                    else:
                        pc += 3
                    #print(f'jmpt  {p1:5} {p2:5} -> {pc:5}')
                elif opcode == 6:  # Jump If False
                    if param_arg(p1, param1) == 0:
                        pc = param_arg(p2, param2)
                    else:
                        pc += 3
                    #print(f'jmpf  {p1:5} {p2:5}')
                elif opcode == 7:  # Less Than
                    if param_arg(p1, param1) < param_arg(p2, param2):
                        set_mem(p3, param3, 1)
                    else:
                        set_mem(p3, param3, 0)
                    #print(f'less  {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 8:  # Less Than
                    if param_arg(p1, param1) == param_arg(p2, param2):
                        set_mem(p3, param3, 1)
                    else:
                        set_mem(p3, param3, 0)
                    #print(f'equal {p1:5} {p2:5} {p3:5}')
                    pc += 4
                elif opcode == 9:
                    relative_base += param_arg(p1, param1)
                    pc += 2
                    #print(f'relb  {p1:5} -> {relative_base}')
                else:
                    print('unknown instruction!')
            else:
                # print(f'[{pc:4}]              : end')
                # print(f'iters: {iters}')
                q_out.put(99)
            # q_out.task_done()
            # q_in.task_done()

grid = {}

def get_grid(x):
    if x not in grid:
        return 0
    else:
        return grid[x][0]

def paint_grid(x, color):
    if x not in grid:
        grid[x] = (color, 1)
    else:
        grid[x] = (color, grid[x][1] + 1)

def print_screen(screen: Dict):
    xs = [c[0] for c in screen.keys()]
    ys = [c[1] for c in screen.keys()]

    print('\033[{};{}H'.format(0, 0))
    for y in range(min(ys), max(ys) + 1):
        for x in range(min(xs), max(xs) + 1):
            if (x, y) in screen:
                c = screen[(x, y)]
                if isinstance(c, str):
                    print(c, end='')
                else:
                    print(c % 10, end='')
            else:
                print(' ', end='')
        print()


q_in = queue.Queue()
q_out = queue.Queue()

t = program(0, f'Thread-{0}', 2, q_in, q_out)
t.start()

screen = {}
loc = (0, 0)
screen[loc] = 'S'
move = 1
oxy = None
while True:
    move = randint(1, 4)
    if move == 1:
        next_loc = (loc[0], loc[1] + 1)
    elif move == 2:
        next_loc = (loc[0], loc[1] - 1)
    elif move == 3:
        next_loc = (loc[0] + 1, loc[1])
    elif move == 4:
        next_loc = (loc[0] - 1, loc[1])

    # tries = 4
    # while next_loc in screen and tries > 0:
    #     move = randint(1, 4)
    #     tries -= 1

    # if move == 1:
    #     next_loc = (loc[0], loc[1] + 1)
    # elif move == 2:
    #     next_loc = (loc[0], loc[1] - 1)
    # elif move == 3:
    #     next_loc = (loc[0] + 1, loc[1])
    # elif move == 4:
    #     next_loc = (loc[0] - 1, loc[1])

    q_in.put(move)


    output = q_out.get()
    if output == 0:
        screen[next_loc] = '#'
    elif output == 1:
        #if loc != (0, 0):
        # if next_loc != (0, 0):
        # screen[loc] = '.'
        if next_loc not in screen:
            screen[next_loc] = '.'
            print_screen(screen)
            if oxy is not None:
                print(f'oxygen at {oxy}')
        # if next_loc not in screen:
        #     screen[next_loc] = screen[loc] + 1
        loc = next_loc
    elif output == 2:
        screen[next_loc] = 'E'
        print_screen(screen)
        loc = next_loc
        oxy = next_loc
        if oxy is not None:
            print(f'oxygen at {oxy}')
        # if next_loc not in screen:
        #     screen[next_loc] = screen[loc] + 1
        # screen[loc] = '.'
        # screen[next_loc] = 'O'
        # loc = next_loc
        # print_screen(screen)
        # q_in.put(99)
        # t.join()
        # print(f'shortest path? {screen[next_loc]}')
        # break



