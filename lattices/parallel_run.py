from genus import write_all_of_sig_between_genera_basic
import multiprocessing
from multiprocessing import Pool
from functools import reduce

min_rank = 1
max_rank = 5
num_cpus = 32
ranks = range(min_rank,max_rank+1)
sigs = [[(r - n_minus, n_minus) for n_minus in range(r//2+1)] for r in ranks]
all_sigs = reduce(lambda x,y : x+y, sigs)
def calculate(func, args):
    result = func(*args)
    return '%s says that %s%s = %s' % (
        multiprocessing.current_process().name,
        func.__name__, args, result
        )

tasks = [[(write_all_of_sig_between_genera_basic, (sig[0], sig[1], 100*i+1, 100*(i+1))) for i in range(10)] for sig in all_sigs]
all_tasks = reduce(lambda x,y : x + y, tasks)
my_pool = Pool(num_cpus)
results = [my_pool.apply_async(calculate, t) for t in all_tasks]
my_pool.close()