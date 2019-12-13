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

layers = np.array(img).reshape(-1, h*w)
num_zeros = [(list(l).count(0), l_idx) for l_idx, l in enumerate(layers)]
layer_w_max_zeros = layers[min(num_zeros)[1]]
max_1s_x_2s = list(layer_w_max_zeros).count(1) * list(layer_w_max_zeros).count(2)
pp.pprint(max_1s_x_2s)
