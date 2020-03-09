def numbers():
    i = 1
    while i<50:
        yield i
        i += 1

def squares():
    for i in numbers():
        yield i*i

for s in squares():
    print s