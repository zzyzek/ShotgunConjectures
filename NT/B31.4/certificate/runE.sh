#!/bin/bash
for p in 12 14 16 18 20 22 24; do ./rud $p 0 300000000; done > E_scan_3e8.txt 2>&1
