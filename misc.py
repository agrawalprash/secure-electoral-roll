import time
from hashlib import sha256
from collections.abc import Iterable
import gmpy2

from globals import CALLDEPTH


def sz(base64_input):
    """ Return size in bytes of base64 encoded input. 

    Ref: https://blog.aaronlenoir.com/2017/11/10/get-original-length-from-base-64-string/
    """

    b_padded = base64_input.split(str.encode(":"))[1]
    pad_size = b_padded.count(str.encode("="))
    b_len_without_pad = len(b_padded)-4
    byte_len = (b_len_without_pad *3)/4 +(3-pad_size)-1
    return byte_len

def statusstr(status):
    return "(ok)" if status else "(not ok)"

def expand_scientific_notation(numstr):
    was_neg = False
    if not ("e" in numstr):
        return numstr
    if numstr.startswith('-'):
        numstr = numstr[1:]
        was_neg = True 
    str_vals = str(numstr).split('e')
    coef = float(str_vals[0])
    exp = int(str_vals[1])
    return_val = ''
    if int(exp) > 0:
        return_val += str(coef).replace('.', '')
        return_val += ''.join(['0' for _ in range(0, abs(exp - len(str(coef).split('.')[1])))])
    elif int(exp) < 0:
        return_val += '0.'
        return_val += ''.join(['0' for _ in range(0, abs(exp) - 1)])
        return_val += str(coef).replace('.', '')
    if was_neg:
        return_val='-'+return_val
    return return_val

def fmt(num):
    num_truncated_precision = f'{num:.2}'
    return expand_scientific_notation(num_truncated_precision)

def pprint(*x):
    print("%s" % ("    " * CALLDEPTH), *x)

def bin(x):
    if isinstance(x, Iterable):
        res = b""
        for elem in x:
            res += bin(elem)
    else:
        res = gmpy2.to_binary(x)
    return res

def hash_gmpy2(x):
    xb = bin(x)
    return gmpy2.mpz(sha256(xb).hexdigest(), 16)

def retval(f):
    def retval_f(*args, **kwargs):
        ret = f(*args, **kwargs)
        print("    " * (CALLDEPTH-1), "%s retval: %s" % (f.__name__, ret))
        return ret

    retval_f.__name__ = f.__name__
    return retval_f

class timer:
    def __init__(self, name, report_subtimers=None):
        self.name = name
        self.subtimers = []
        global TIMERS
        TIMERS[name] = self
        self.report_subtimers = report_subtimers if report_subtimers is not None else []

    def __enter__(self):
        self.start = time.perf_counter()
        global CURRENT
        global CALLDEPTH
        if len(CURRENT.subtimers) == 0:
            print("%s" % ("    " * (CALLDEPTH-1)), CURRENT.name)    
        CURRENT.subtimers += [self]
        CURRENT, self._oldcurrent = self, CURRENT
        CALLDEPTH += 1
        return self

    def __exit__(self, exc_type, exc_value, exc_traceback):
        self.end = time.perf_counter()
        self.time = self.end - self.start
        global CURRENT
        CURRENT = self._oldcurrent
        
        global CALLDEPTH
        for report_subtimer in self.report_subtimers:
            report_time = 0.0
            subtimers = get_subtimers(self, report_subtimer)
            for subtimer in subtimers:
                report_time += subtimer.time
            pprint("%s total time: %s s" % (report_subtimer, fmt(report_time)))
        CALLDEPTH -= 1
        pprint("%s time: %s s" % (self.name, fmt(self.time)))

def timed(f, *a, **kw):
    def timed_f(*args, **kwargs):
        with timer(f.__name__, *a, **kw) as t:
            ret = f(*args, **kwargs)
        return ret

    timed_f.__name__ = f.__name__
    return timed_f

def get_subtimers(timer, prefix):
    subtimers = []
    for subtimer in timer.subtimers:
        if subtimer.name.startswith(prefix):
            subtimers.append(subtimer)
        else:
            subtimers += get_subtimers(subtimer, prefix)
    return subtimers

TIMERS = {}
CURRENT = timer("main")
