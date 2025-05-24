import argparse
import importlib
import inspect
import pathlib
import sys

from z3 import *

class IntegerProxy:
    def __init__(self, term):
        self.term = term

    def __int_binop(self, other, op):
        if isinstance(other, int):
            other = IntegerProxy(other)
        if isinstance(other.term, int) and isinstance(self.term, int):
            return IntegerProxy(op(self.term, other.term))
        return IntegerProxy(simplify(op(self.term, other.term)))

    def __int_unop(self, op):
        if isinstance(self.term, int):
            return IntegerProxy(op(self.term))
        return IntegerProxy(simplify(op(self.term)))

    def __bool_binop(self, other, op):
        if isinstance(other, int):
            other = IntegerProxy(other)
        if isinstance(other.term, int) and isinstance(self.term, int):
            return BoolProxy(op(self.term, other.term))
        return BoolProxy(simplify(op(self.term, other.term)))

    def __add__(self, other): return self.__int_binop(
        other, lambda a, b: a + b)

    def __sub__(self, other): return self.__int_binop(
        other, lambda a, b: a - b)

    def __mul__(self, other): return self.__int_binop(
        other, lambda a, b: a * b)

    def __floordiv__(self, other): return self.__int_binop(
        other, lambda a, b: a // b)

    def __truediv__(self, other): return self.__int_binop(
        other, lambda a, b: a // b)

    def __pow__(self, other): return self.__int_binop(
        other, lambda a, b: a ** b)

    def __mod__(self, other): return self.__int_binop(
        other, lambda a, b: a % b)

    def __eq__(self, other): return self.__bool_binop(
        other, lambda a, b: a == b)

    def __ne__(self, other): return self.__bool_binop(
        other, lambda a, b: a != b)

    def __lt__(self, other): return self.__bool_binop(
        other, lambda a, b: a < b)

    def __gt__(self, other): return self.__bool_binop(
        other, lambda a, b: a > b)

    def __le__(self, other): return self.__bool_binop(
        other, lambda a, b: a <= b)
    def __ge__(self, other): return self.__bool_binop(
        other, lambda a, b: a >= b)

    def __radd__(self, other): return self.__add__(other)
    def __rsub__(self, other): return self.__sub__(other)
    def __rmul__(self, other): return self.__mul__(other)
    def __rfloordiv__(self, other): return self.__div__(other)
    def __rtruediv__(self, other): return self.__truediv__(other)
    def __rpow__(self, other): return self.__pow__(other)
    def __rmod__(self, other): return self.__mod__(other)
    def __neg__(self): return self.__int_unop(lambda a: -a)
    def __pos__(self): return self.__int_unop(lambda a: a)


class BoolProxy:
    def __init__(self, term):
        self.term = term

    def __bool_op(self, other, op):
        if isinstance(other, bool):
            other = BoolProxy(other)
        if isinstance(other.term, bool) and isinstance(self.term, bool):
            return BoolProxy(op(self.term, other.term))
        return BoolProxy(simplify(op(self.term, other.term)))

    def __and__(self, other): return self.__bool_op(
        other, lambda a, b: a and b)

    def __or__(self, other): return self.__bool_op(other, lambda a, b: a or b)

    def __bool__(self):
        if isinstance(self.term, bool):
            return self.term
        global terms, conditions
        s = Solver()
        s.add(And(*(conditions + [self.term])))
        true_cond = True if s.check() == sat else False

        s = Solver()
        s.add(And(*(conditions + [simplify(Not(self.term))])))
        false_cond = True if s.check() == sat else False

        if true_cond and not false_cond:
            return True
        if false_cond and not true_cond:
            return False

        if len(terms) > len(conditions):
            branch = terms[len(conditions)]
            conditions.append(
                self.term if branch else simplify(Not(self.term)))
            return branch

        if len(terms) >= 10:
            raise DepthException()

        terms.append(True)
        conditions.append(self.term)
        return True


class DepthException(Exception):
    pass


def run(fn, args):
    global terms, conditions
    terms = []
    models = []
    while True:
        conditions = []
        try:
            result = fn(*args)
        except DepthException:
            pass
        except Exception:
            pass

        s = Solver()
        s.add(And(*conditions))
        s.check()
        models.append(s.model())

        while len(terms) > 0 and not terms[-1]:
            terms.pop()
        if len(terms) == 0:
            break
        terms[-1] = False

    return models


conditions = {}
terms = []

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description='Generate test data using \
        symbolic execution.')
    parser.add_argument('-t', '--target', required=True,
                        help="the target file to symbolically execute")
    args = parser.parse_args()

    target = args.target

    target_path = pathlib.Path(target).resolve()
    sys.path.insert(0, str(target_path.parent))
    mod = importlib.import_module(target_path.stem)
    results = {}
    for name, fn in inspect.getmembers(mod, inspect.isfunction):
        if fn.__module__ != mod.__name__:
            continue
        argnames = fn.__code__.co_varnames[:fn.__code__.co_argcount]
        args = [IntegerProxy(Int(argname)) for argname in argnames]
        models = run(fn, args)
        results[name] = []
        for model in models:
            result = {}
            for argname, arg in zip(argnames, args):
                try:
                    result[argname] = model.evaluate(arg.term).as_long()
                except:
                    result[argname] = 0
            results[name].append(result)