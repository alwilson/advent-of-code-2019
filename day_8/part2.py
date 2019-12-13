#!/usr/bin/env python3

import numpy as np
import pprint as pp
from typing import List

w = 25
h = 6

img_str = open('./input.txt').readline()
img = []
for c in img_str:
    img.append(int(c))

layers = np.array(img).reshape(-1, h, w)
for row in range(h):
    for x in range(w):
        i = 0
        while layers[i][row][x] == 2:
            i += 1
        print('#' if layers[i][row][x] == 1 else ' ', end='')
    print()

