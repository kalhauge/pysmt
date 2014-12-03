
def pairwise(iterable):
    a, b = tee(iterable)
    next(b, None)
    return zip(a, b)

