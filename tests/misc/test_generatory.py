
def basea(x):
    yield 2*x

def baseb():
    yield 3
    yield 4

def combinator():
    for x in [1,2,3]:
        yield from basea(x)
    #yield from (basea(x) for x in [1,2,3])
    yield from baseb()

for x in combinator():
    print(x)