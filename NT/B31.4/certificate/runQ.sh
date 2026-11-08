#!/bin/bash
for p in 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17; do ./rudq $p 10000000 | tail -2; done > Q_scan_1e7.txt 2>&1
