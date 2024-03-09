def add1(x : int) -> int:
  return (x + 1)

y = input_int()
g : Callable[([int], int,)] = (lambda x: (x - y))
f = (add1 if input_int() == 0 else g)
print(f(41))