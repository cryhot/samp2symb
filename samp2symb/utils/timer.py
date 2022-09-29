#!/usr/bin/env python3
"""Author: Jean-Raphaël Gaglione"""
import time
import functools
import contextlib

default_timer = time.perf_counter
# default_timer = time.clock

class Timer(contextlib.ContextDecorator):

    def __init__(self):
        self.__total_elapsed = 0
        self.__session_start = None

    def __now(self):
        return default_timer()


    def running(self):
        """Return `True` if the timer is activated."""
        return self.__session_start is not None

    @property
    def elapsed(self):
        """Total elapsed time wile the timer was activated."""
        if self.running():
            session_elapsed = self.__now() - self.__session_start
        else:
            session_elapsed = 0
        return self.__total_elapsed + session_elapsed

    def resume(self):
        """Activate the timer."""
        if not self.running():
            self.__session_start = self.__now()
        return self

    def start(self):
        """Same as `resume` but raises an error if already activated."""
        # if self.running() or self.__total_elapsed > 0:
        if self.running():
            raise RuntimeError("Timer already running.")
        return self.resume()

    def stop(self):
        """Desactivate the timer."""
        self.__total_elapsed = self.elapsed
        self.__session_start = None
        return self

    def reset(self):
        """Reset the total elapsed time to zero. The timer stay activated if it was already running."""
        self.__total_elapsed = 0
        if self.running():
            self.__session_start = self.__now()
        return self


    def __enter__(self):
        """
            Timer can be used as a context manager.

            >>> with Timer() as t:
            >>>     ...
            >>> print(t.elapsed)
        """
        self.start()
        return self
    def __exit__(self, *args):
        """.. seealso:: __enter__()"""
        self.stop()

    # def __call__(self, func):
    #     """
    #         Timer objects can be used as a decorator, and time will be incremented each time the function is called.

    #         >>> @timer
    #         >>> def foo(*args, **kwargs):
    #         >>>     ...
    #     """
    #     @functools.wraps(func)
    #     def wrapper(*args, **kwargs):
    #         with self:
    #             return func(*args, **kwargs)
    #     return wrapper

    @property
    @contextlib.contextmanager
    def include(self):
        """
            Ensure that the code calculation time is included in the measured time.

            >>> with timer.include():
            >>>     ...

            >>> @timer.include()
            >>> def foo(*args, **kwargs):
            >>>     ...
        """
        if not self.running():
            self.start()
            yield self
            self.stop()
        else:
            yield self

    @property
    @contextlib.contextmanager
    def exclude(self):
        """
            Ensure that the code calculation time is excluded from the measured time.

            >>> with timer.exclude:
            >>>     ...

            >>> @timer.exclude
            >>> def foo(*args, **kwargs):
            >>>     ...
        """
        if self.running():
            self.stop()
            yield self
            self.start()
        else:
            yield self

    def __float__(self):
        return float(self.elapsed)
    def __bool__(self):
        """A timer has a boolean value of `False` after complete reset."""
        return self.running() or self.elapsed
    def __repr__(self):
        return "{!s}[{:.3f}s{}]".format(
            self.__class__.__name__,
            self.elapsed,
            "..." if self.running() else "",
        )
    def __str__(self):
        # return "{:.3f}".format(
        #     self.elapsed
        # )
        return repr(self)


class Timers(list, contextlib.ContextDecorator):
    """Group of several timers"""
    def __init__(self, *timers):
        super().__init__(timers)
    @property
    def elapsed(self):
        return tuple(timer.elapsed for timer in self)
    def resume(self):
        for timer in self: timer.resume()
        return self
    def start(self):
        for timer in self: timer.start()
        return self
    def stop(self):
        for timer in self: timer.stop()
        return self
    def reset(self):
        for timer in self: timer.reset()
        return self
    def __enter__(self):
        return tuple(timer.__enter__() for timer in self)
    def __exit__(self, *args):
        for timer in self: timer.__exit__()
    @property
    @contextlib.contextmanager
    def include(self):
        with contextlib.ExitStack() as stack:
            yield tuple(stack.enter_context(timer.include) for timer in self)
    @property
    @contextlib.contextmanager
    def exclude(self):
        with contextlib.ExitStack() as stack:
            yield tuple(stack.enter_context(timer.exclude) for timer in self)
    
    

class TimeKeeper():
    "Logs different timers"

    def __init__(self) -> None:
        self.timers = dict()

    def Timer(self, name):
        return self.timers.setdefault(name, Timer())
    def Timers(self, *names):
        return Timers(*(self.Timer(name) for name in names))
    def __getitem__(self, key):
        if key == slice(None): return Timers(*self.timers.values())
        if isinstance(key, tuple): return self.Timers(*key)
        return self.Timer(key)
    
    @property
    def elapsed(self):
        """Dictionnary of all logged timers elapsed times."""
        return {name:timer.elapsed for name,timer in self.timers.items()}
    

