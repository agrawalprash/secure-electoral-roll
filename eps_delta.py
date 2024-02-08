from matplotlib import pyplot
from numpy import linspace
from math import comb, pow
import time
import csv
import sys

memo = {}

def hyp_exact(n, f, alpha, k):
    """ Return the probability of selecting exactly k bad items when alpha items are randomly selected without replacement from an urn 
    containing n items of which f are bad. """

    return comb(f, k) * comb(n-f, alpha-k) / comb(n, alpha)

def memoized_hyp_exact(n, f, alpha, k):
    """ A version of hyp that memorizes previous responses. """

    if (n,f,alpha,k) not in memo:
        memo[(n,f,alpha,k)] = hyp_exact(n, f, alpha, k)
    return memo[(n,f,alpha,k)] 

def hyp(n, f, alpha, d):
    """ Given that from an urn containing n items of which f are special, alpha are selected randomly without replacement. Also, given that 
    the probability of detecting a selected special item is d. Return the probability of not detecting any special item at all, given by the 
    following expression: sum_{k=0}^{\alpha} hyp_exact(n, f, alpha, k) (1-d)^k. 
    """

    if d == 1:
        return memoized_hyp_exact(n, f, alpha, 0)
    
    else:
        sum = 0
        for k in range(alpha):
            sum += memoized_hyp_exact(n,f,alpha,k) * pow(1-d, k)
        return sum

###### Calculation of epsilon and delta #################
    
# Here, for simplicity, we assume n_s = n_d = n, alpha_s = alpha_d = alpha, f_s = f_d = f and N_s = N = 2 n_s .


def eps1(n, alpha, f):
    return 2 * (hyp(n, alpha, int(f/2), 1.0/3) ** 2)

def eps2(N, alpha, f):
    return 2 * (hyp(N+f, alpha, int(f/2), 1) ** 2)

def eps(N,n,alpha,f):
    return max(eps1(n,alpha,f), eps2(N,alpha,f))

def delta1(n, alpha):
    return 1 - (hyp(n,alpha,1,1) ** 2) * ((1-alpha/n) ** 2)

def delta2(n, alpha):
    return 1 - hyp(n,alpha,2,1) * (1 - 2*alpha/n)

def delta3(n, alpha):
    return 1 - hyp(n,alpha,1,1) ** 2

def delta(n,alpha):
    return max(delta1(n,alpha), delta2(n,alpha), delta3(n,alpha))

def gen_eps_delta(N, n, f, fname):
    alphaarr = linspace(100, 3000, num=50, dtype=int)
    eps1arr, eps2arr, epsarr = [], [], []
    delta1arr, delta2arr, delta3arr, deltaarr = [], [], [], []
    with open(fname, 'w') as csvfile:
        writer = csv.writer(csvfile)
        for alpha in alphaarr:
            start = time.time()

            print("alpha:", alpha)
            
            eps1val = eps1(n, alpha, f)
            print("eps1val:", eps1val)
            eps2val = eps2(N, alpha, f)
            print("eps2val:", eps2val)
            epsval = max(eps1val, eps2val)
            print("epsval:", epsval)

            delta1val = delta1(n, alpha)
            print("delta1val:", delta1val)
            delta2val = delta2(n, alpha)
            print("delta2val:", delta2val)
            delta3val = delta3(n, alpha)
            print("delta3val:", delta3val)
            deltaval = max(delta1val, delta2val, delta3val)
            print("deltaval:", deltaval)

            eps1arr.append(eps1val)
            eps2arr.append(eps2val)
            epsarr.append(epsval)

            delta1arr.append(delta1val)
            delta2arr.append(delta2val)
            delta3arr.append(delta3val)
            deltaarr.append(deltaval)

            writer.writerow([alpha, eps1val, eps2val, epsval, delta1val, delta2val, delta3val, deltaval])

            end = time.time()
            print("Time:", end-start, "seconds")

def analyse_eps_delta(fname):
    alphaarr = []
    eps1arr, eps2arr, epsarr = [], [], []
    delta1arr, delta2arr, delta3arr, deltaarr = [], [], [], []
    with open(fname) as csvfile:
        reader = csv.reader(csvfile)
        for row in reader:
            alpha, eps1val, eps2val, epsval, delta1val, delta2val, delta3val, deltaval = row
            alphaarr.append(int(alpha))
            eps1arr.append(float(eps1val))
            eps2arr.append(float(eps2val))
            epsarr.append(float(epsval))
            delta1arr.append(float(delta1val))
            delta2arr.append(float(delta2val))
            delta3arr.append(float(delta3val))
            deltaarr.append(float(deltaval))

    for i in range(len(alphaarr)):
        if epsarr[i] < 0.001:
            print('alpha for eps<0.001:', alphaarr[i])
            print('delta at this alpha:', deltaarr[i])
            break

    # pyplot.plot(alphaarr, eps1arr, label="$\epsilon_1(n,\alpha,f)$")
    # pyplot.plot(alphaarr, eps2arr, label="$\epsilon_2(N,\alpha,f)$")
    pyplot.plot(alphaarr, epsarr, label="$\epsilon(N,n,\alpha,f)$")
    # pyplot.plot(alphaarr, delta1arr, label="$\delta_1(n,\alpha)$")
    # pyplot.plot(alphaarr, delta2arr, label="$\delta_2(n,\alpha)$")
    # pyplot.plot(alphaarr, delta3arr, label="$\delta_3(n,\alpha)$")
    pyplot.plot(alphaarr, deltaarr, label="$\delta(n,\alpha)$")
    pyplot.plot(alphaarr, [0.001 for alpha in alphaarr])
    pyplot.legend()
    pyplot.xlabel("alpha, the number of verifications")
    pyplot.title("Probability of not detecting a bad item, when probability of detection d=1/3")
    pyplot.show()

if __name__ == "__main__":
    n = 10000
    N = 2*n
    f = int(0.01*n)
    fname = "eps_delta_n%s_f%s.csv" % (n,f)
    if sys.argv[1] == "1":
        start = time.time()
        gen_eps_delta(N, n, f, fname)
        end = time.time()
        print("Total data generation time:", end - start, "seconds")
    if sys.argv[2] == "1":
        analyse_eps_delta(fname)