#!/usr/bin/env python3



import functools
def timeout_generator(func):
    "generator decorator: add a timeout argument"
    import multiprocessing, queue
    from pytictoc import TicToc
    def run(func, args, kwargs, q):
        for x in func(*args, **kwargs): q.put(x)
        q.put(NotImplemented)
        # q.close() # not working
    @functools.wraps(func)
    def wrapper(*args, timeout=float("inf"), **kwargs):
        tictoc_total = TicToc()
        tictoc_total.tic()
        if timeout is None: timeout = float("inf")
        if timeout<=0: raise TimeoutError(f"{func.__name__}: timeout is negative")
        q = multiprocessing.Queue()
        p = multiprocessing.Process(target=run, args=[func, args, kwargs, q], daemon=True)
        p.start()
        while True:
            try:
                t = timeout-tictoc_total.tocvalue()
                if t<=0: raise queue.Empty()
                if t==float("inf"): t=None
                ans = q.get(timeout=t)
            except queue.Empty:
                p.terminate()
                p.join()
                raise TimeoutError(f"{func.__name__}: interrupted")
            except (ValueError, OSError):
                p.join(); return
            else:
                if ans is NotImplemented: p.join(); return
                yield ans
    return wrapper