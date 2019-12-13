#!/usr/bin/env python3

from typing import Dict
import pprint as pp
from itertools import permutations

import queue
import threading

import tracemalloc

import sys
import readchar

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
            memory[0] = 2

            pc = 0
            outputs = []
            state_mode = False
            iters = 0
            while (get_mem(pc) % 100) != 99:  # and iters < 10:  # Halt
                if memory[2666] > 20:
                    # memory[2665] = 0
                    memory[2666] = 1
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
                        num = 0
                        #print(f'waiting on {self.q_in}')
                        #num = self.q_in.get(block=True)
                        #print(f'pressed {num}')
                        #for i in range(8):
                            #print(f'mem[{i}]: {memory[2660+i]}')
                        #if memory[2666] > 20:
                            #memory[2665] = 0
                        #    memory[2666] = 1
                        #num = input('command: ')
                        #num = int(num)
                        #print(f'pressed {num}')
                        #num -= 2
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

    for y in range(min(ys), max(ys) + 1):
        for x in range(min(xs), max(xs) + 1):
            if (x, y) in screen:
                c = screen[(x, y)]
                char = '.'
                if c == 1:
                    char = '|'
                elif c == 2:
                    char = '#'
                elif c == 3:
                    char = 'T'
                elif c == 4:
                    char = 'o'
                print(char, end='')
            else:
                print('.', end='')
        print()


q_in = queue.Queue()
q_out = queue.Queue()

t = program(0, f'Thread-{0}', 2, q_in, q_out)
t.start()

start = (0, 0)  # type: Tuple[int, int]
dirc = 0
paint_grid(start, 0)

screen = {}
ball_dir = 1
pball = (-1, -1)
ball = (-1, -1)
paddle = (-1, -1)
last_action = None
scores = []
while True: # t.is_alive():

    # if last_action == 0:
    #     print_screen(screen)
    #     q_in.put(0)
    #     last_action = 1


    output = q_out.get()
    if output == 99:
        print('x')
        break
    x = output

    output = q_out.get()
    if output == 99:
        print('y')
        break
    y = output

    output = q_out.get()
    if output == 99:
        print('output')
        break
    tile_id = output

    if x == -1 and y == 0:
        print(f'FINAL SCORE: {output}')
        scores.append(output)

    screen[(x, y)] = tile_id
    # # print(f'({x}, {y}) = {tile_id}')
    # if tile_id == 4:
    #     print(f'> ({x}, {y}) = {tile_id}')
    #     pball = ball
    #     ball = (x, y)
    #     if pball != (-1, -1):
    #         ball_dir = ball[0] - pball[0]
    #         ball_dir = ball_dir // abs(ball_dir) if ball_dir != 0 else 0
    # if tile_id == 3:
    #     print(f'> ({x}, {y}) = {tile_id}')
    #     paddle = (x, y)

    # if ball != (-1, -1) and paddle != (-1, -1) and (tile_id == 4 or tile_id == 3) and q_in.empty():
    #     dist = ball[0] - paddle[0]
    #     diff = dist // abs(dist) if dist != 0 else 0
    #     print_screen(screen)
    #     print(f'dist: {dist} ball dir: {ball_dir} paddle dir: {diff}')
    #     # if ball_dir == 0:
    #     #     diff = 0
    #     if dist + ball_dir == 0:
    #         diff = 0
    #     q_in.put(diff)
    #     if diff == 0:
    #         last_action = 0
    #     print(f'ball: {ball} paddle: {paddle})')
    #     print(f'put in: {diff}')
    #     pp.pprint(list(q_in.queue))

    print_screen(screen)
    # 2668
    #print(list(screen.values()).count(2)*8)

print_screen(screen)
print(scores)

#print(list(screen.values()).count(2))

# pp.pprint(list(q_in.queue))
# pp.pprint(list(q_out.queue))
