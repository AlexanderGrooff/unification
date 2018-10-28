import ast
from functools import partial
from types import FunctionType, CodeType
from collections import Iterator
from toolz.compatibility import iteritems, map
from toolz import assoc
from codetransformer import Code, CodeTransformer, instructions, \
    pattern
from codetransformer.instructions import Instruction
from inspect import signature

from .utils import transitive_get as walk
from .variable import Var, var, isvar
from .dispatch import dispatch

################
# Reificiation #
################

def replace_logicvar_with_val(f, logicvar_name, val):
    class ReplaceLogicVar(CodeTransformer):
        @pattern(instructions.LOAD_GLOBAL)
        def _replace_logicvar(self, loadlogicvar):
            if loadlogicvar.arg == logicvar_name:
                yield instructions.LOAD_CONST(val).steal(loadlogicvar)
            else:
                yield loadlogicvar

    transformer = ReplaceLogicVar()
    return transformer(f)

@dispatch(FunctionType, dict)
def _reify(f, s):
    shadow_dict = {}
    for global_name in f.__code__.co_names:
        try:
            logicvar = f.__globals__[global_name]
            if not isvar(logicvar):
                continue
            reified_v = reify(logicvar, s)
            shadow_dict[global_name] = reified_v
        except (IndexError, KeyError):
            pass

    for logicvar, val in shadow_dict.items():
        f = replace_logicvar_with_val(f, logicvar, val)
    return f


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

seq = tuple, list, Iterator

@dispatch(Instruction, Instruction, dict)
def _unify(u, v, s):
    if u.uses_name:
        return assoc(s, var(u.arg), v.arg)
    if v.uses_name:
        return assoc(s, var(v.arg), u.arg)
    return s

@dispatch(FunctionType, FunctionType, dict)
def _unify(u, v, s):
    print("Unifying {} to {}".format(u, v))
    if signature(u) != signature(v):
        return False
    c_v = Code.from_pyfunc(u)
    c_u = Code.from_pyfunc(v)

    if len(c_v.instrs) == len(c_u.instrs):
        print("Same amount of instructions, directly correlating instructions")
        return _unify(c_v.instrs, c_u.instrs, s)
    print("Instructions dont match, returning s")
    return s

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

