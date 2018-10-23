import ast
from functools import partial
from types import FunctionType, CodeType
from collections import Iterator
from toolz.compatibility import iteritems, map
from toolz import assoc

from .utils import transitive_get as walk
from .variable import Var, var, isvar
from .dispatch import dispatch

################
# Reificiation #
################

def print_code_type(c):
        print("consts", c.co_consts)
        print("names", c.co_names)
        print("varnames", c.co_varnames)
        print("name", c.co_name)
        print("freevars", c.co_freevars)
        print("cellvars", c.co_cellvars)

@dispatch(FunctionType, dict)
def _reify(f, s):
    # Since we cannot modify the bytecode of a function, we'll have to create
    # a new function based on the bytecode from the original function.
    # The constants used in the function are located in f.__code__.co_consts
    # See: https://stackoverflow.com/questions/33348067/modifying-python-bytecode
    code = f.__code__
    if code.co_freevars:
        return f
    reified_constants = reify(code.co_consts, s)
    print("Reifying function {}")
    print_code_type(code)
    new_byte_code = CodeType(
        code.co_argcount,
        code.co_kwonlyargcount,
        code.co_nlocals,
        code.co_stacksize,
        code.co_flags,
        code.co_code,
        reified_constants,
        code.co_names,
        code.co_varnames,
        code.co_filename,
        code.co_name,
        code.co_firstlineno,
        code.co_lnotab,   # In general, You should adjust this
        code.co_freevars,
        code.co_cellvars
    )
    print_code_type(new_byte_code)

    new_f = lambda: 123
    new_f.__code__ = new_byte_code
    return new_f

@dispatch(Iterator, dict)
def _reify(t, s):
    return map(partial(reify, s=s), t)
    # return (reify(arg, s) for arg in t)

@dispatch(tuple, dict)
def _reify(t, s):
    return tuple(reify(iter(t), s))

@dispatch(list, dict)
def _reify(t, s):
    return list(reify(iter(t), s))

@dispatch(dict, dict)
def _reify(d, s):
    return dict((k, reify(v, s)) for k, v in d.items())

@dispatch(object, dict)
def _reify(o, s):
    if not isinstance(o, ast.AST):
        return o  # catch all, just return the object

    if hasattr(o, '__slots__'):
        return _reify_object_slots(o, s)
    else:
        return _reify_object_dict(o, s)

def _reify_object_dict(o, s):
    obj = type(o).__new__(type(o))
    d = reify(o.__dict__, s)
    if d == o.__dict__:
        return o
    obj.__dict__.update(d)
    return obj

def _reify_object_slots(o, s):
    attrs = [getattr(o, attr) for attr in o.__slots__]
    new_attrs = reify(attrs, s)
    if attrs == new_attrs:
        return o
    else:
        newobj = object.__new__(type(o))
        for slot, attr in zip(o.__slots__, new_attrs):
            setattr(newobj, slot, attr)
    return newobj

def reify(e, s):
    """ Replace variables of expression with substitution

    >>> x, y = var(), var()
    >>> e = (1, x, (3, y))
    >>> s = {x: 2, y: 4}
    >>> reify(e, s)
    (1, 2, (3, 4))

    >>> e = {1: x, 3: (y, 5)}
    >>> reify(e, s)
    {1: 2, 3: (4, 5)}
    """
    if isvar(e):
        return reify(s[e], s) if e in s else e
    return _reify(e, s)

###############
# Unification #
###############

@dispatch(FunctionType, FunctionType, dict)
def _unify(u, v, s):
    if u.__code__ != v.__code__:
        return False
    return s

seq = tuple, list, Iterator

@dispatch(seq, seq, dict)
def _unify(u, v, s):
    if len(u) != len(v):
        return False
    for uu, vv in zip(u, v):  # avoiding recursion
        s = unify(uu, vv, s)
        if s is False:
            return False
    return s

@dispatch((set, frozenset), (set, frozenset), dict)
def _unify(u, v, s):
    i = u & v
    u = u - i
    v = v - i
    return _unify(sorted(u), sorted(v), s)


@dispatch(dict, dict, dict)
def _unify(u, v, s):
    if len(u) != len(v):
        return False
    for key, uval in iteritems(u):
        if key not in v:
            return False
        s = unify(uval, v[key], s)
        if s is False:
            return False
    return s


@dispatch(object, object, dict)
def _unify(u, v, s):
    return False  # catch all


@dispatch(object, object, dict)
def unify(u, v, s):  # no check at the moment
    """ Find substitution so that u == v while satisfying s

    >>> x = var('x')
    >>> unify((1, x), (1, 2), {})
    {~x: 2}
    """
    u = walk(u, s)
    v = walk(v, s)
    if u == v:
        return s
    if isvar(u):
        return assoc(s, u, v)
    if isvar(v):
        return assoc(s, v, u)
    return _unify(u, v, s)


@dispatch(object, object)
def unify(u, v):
    return unify(u, v, {})
