#!/usr/local/bin/sage -python
import sys

from genus import write_all_of_sig_between

write_all_of_sig_between(int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))