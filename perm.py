import random

def gen_rand_perm(n):
    firstn = range(n)
    pi = random.sample(firstn, len(firstn))
    reverse_pi =[0]*len(pi)
    for i in range(len(pi)):
        dest = pi[i]
        reverse_pi[dest] = i
    return pi, reverse_pi

def permute(items, perm):
    items_perm = zip(items, perm)
    all_items, perm = zip(*items_perm)
    permuted_all_items = [all_items[perm[i]] for i in range(len(all_items))]
    return permuted_all_items