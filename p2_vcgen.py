"""
CS292C Homework 2 — Problem 2: Hoare Logic VCG for IMP (30 points)
===================================================================
Implement weakest-precondition-based verification condition generation
for a simple IMP language, using Z3 to discharge the VCs.

Part (a): Compute wp using your VCG and analyze preconditions with Z3.
          NOTE: Part (a) depends on Part (b). Implement Part (b) first, then come back to Part (a).
Part (b): Implement wp() and verify() below.
Part (c): Discover loop invariants for three programs.
Part (d): Find and fix a bug in a provided invariant.
"""

from z3 import *
from dataclasses import dataclass
from typing import Union

# ============================================================================
# IMP Abstract Syntax Tree
# ============================================================================

@dataclass
class IntConst:
    value: int

@dataclass
class Var:
    name: str

@dataclass
class BinOp:
    """op ∈ {'+', '-', '*'}"""
    op: str
    left: 'AExp'
    right: 'AExp'

AExp = Union[IntConst, Var, BinOp]

@dataclass
class BoolConst:
    value: bool

@dataclass
class Compare:
    """op ∈ {'<', '<=', '>', '>=', '==', '!='}"""
    op: str
    left: AExp
    right: AExp

@dataclass
class ImpNot:
    expr: 'BExp'

@dataclass
class ImpAnd:
    left: 'BExp'
    right: 'BExp'

@dataclass
class ImpOr:
    left: 'BExp'
    right: 'BExp'

BExp = Union[BoolConst, Compare, ImpNot, ImpAnd, ImpOr]

@dataclass
class Assign:
    var: str
    expr: AExp

@dataclass
class Seq:
    s1: 'Stmt'
    s2: 'Stmt'

@dataclass
class If:
    cond: BExp
    then_branch: 'Stmt'
    else_branch: 'Stmt'

@dataclass
class While:
    cond: BExp
    invariant: 'BExp'
    body: 'Stmt'

@dataclass
class Assert:
    cond: BExp

@dataclass
class Assume:
    cond: BExp

Stmt = Union[Assign, Seq, If, While, Assert, Assume]

# ============================================================================
# IMP AST → Z3 Translation
# ============================================================================

_z3_vars: dict[str, ArithRef] = {}

def z3_var(name: str) -> ArithRef:
    if name not in _z3_vars:
        _z3_vars[name] = Int(name)
    return _z3_vars[name]

def aexp_to_z3(e: AExp) -> ArithRef:
    match e:
        case IntConst(v):   return IntVal(v)
        case Var(name):     return z3_var(name)
        case BinOp('+', l, r): return aexp_to_z3(l) + aexp_to_z3(r)
        case BinOp('-', l, r): return aexp_to_z3(l) - aexp_to_z3(r)
        case BinOp('*', l, r): return aexp_to_z3(l) * aexp_to_z3(r)
        case _: raise ValueError(f"Unknown AExp: {e}")

def bexp_to_z3(e: BExp) -> BoolRef:
    match e:
        case BoolConst(v):   return BoolVal(v)
        case Compare(op, l, r):
            lz, rz = aexp_to_z3(l), aexp_to_z3(r)
            return {'<': lz < rz, '<=': lz <= rz, '>': lz > rz,
                    '>=': lz >= rz, '==': lz == rz, '!=': lz != rz}[op]
        case ImpNot(inner):  return Not(bexp_to_z3(inner))
        case ImpAnd(l, r):   return And(bexp_to_z3(l), bexp_to_z3(r))
        case ImpOr(l, r):    return Or(bexp_to_z3(l), bexp_to_z3(r))
        case _: raise ValueError(f"Unknown BExp: {e}")

def z3_substitute_var(formula: ExprRef, var_name: str, replacement: ArithRef) -> ExprRef:
    """Replace every occurrence of z3 variable `var_name` with `replacement`."""
    return substitute(formula, (z3_var(var_name), replacement))


# ============================================================================
# Part (b): Weakest Precondition + VCG — 12 pts
# ============================================================================

side_vcs: list[tuple[str, BoolRef]] = []


def _vc_valid(phi: BoolRef) -> bool:
    s = Solver()
    s.add(Not(phi))
    return s.check() == unsat


def wp(stmt: Stmt, Q: BoolRef) -> BoolRef:
    """
    Compute the weakest precondition of `stmt` w.r.t. postcondition `Q`.
    For while loops, append side VCs to the global `side_vcs` list.
    """
    global side_vcs

    match stmt:
        case Assign(var, expr):
            return z3_substitute_var(Q, var, aexp_to_z3(expr))

        case Seq(s1, s2):
            return wp(s1, wp(s2, Q))

        case If(cond, s1, s2):
            c = bexp_to_z3(cond)
            return And(
                Implies(c, wp(s1, Q)),
                Implies(Not(c), wp(s2, Q)),
            )

        case While(cond, inv, body):
            I = bexp_to_z3(inv)
            c = bexp_to_z3(cond)
            body_wp = wp(body, I)
            side_vcs.append(
                ("preservation", Implies(And(I, c), body_wp))
            )
            side_vcs.append(
                ("postcondition", Implies(And(I, Not(c)), Q))
            )
            return I

        case Assert(cond):
            return And(bexp_to_z3(cond), Q)

        case Assume(cond):
            return Implies(bexp_to_z3(cond), Q)

        case _:
            raise ValueError(f"Unknown statement: {stmt}")


def verify(pre: BExp, stmt: Stmt, post: BExp, label: str = "Program"):
    """
    Verify the Hoare triple {pre} stmt {post}.
    Clears side_vcs, computes wp, checks pre → wp and each side VC.
    """
    global side_vcs
    side_vcs = []

    pre_z3 = bexp_to_z3(pre)
    post_z3 = bexp_to_z3(post)

    w = wp(stmt, post_z3)
    main_vc = Implies(pre_z3, w)

    print(f"=== {label} ===")
    main_ok = _vc_valid(main_vc)
    print(f"  main VC (pre → wp): {'OK' if main_ok else 'FAIL'}")

    all_ok = main_ok
    for name, vc in side_vcs:
        ok = _vc_valid(vc)
        print(f"  side VC [{name}]: {'OK' if ok else 'FAIL'}")
        all_ok = all_ok and ok

    print(f"  Overall: {'VERIFIED' if all_ok else 'NOT VERIFIED'}")
    print()


# ============================================================================
# Test Programs for Part (b) — verify your VCG works on these
# ============================================================================

def test_swap():
    """{ x == a ∧ y == b }  t:=x; x:=y; y:=t  { x == b ∧ y == a }"""
    pre = ImpAnd(Compare('==', Var('x'), Var('a')),
                 Compare('==', Var('y'), Var('b')))
    stmt = Seq(Assign('t', Var('x')),
               Seq(Assign('x', Var('y')), Assign('y', Var('t'))))
    post = ImpAnd(Compare('==', Var('x'), Var('b')),
                  Compare('==', Var('y'), Var('a')))
    verify(pre, stmt, post, "Swap")


def test_abs():
    """{ true }  if x<0 then r:=0-x else r:=x  { r >= 0 ∧ (r==x ∨ r==0-x) }"""
    pre = BoolConst(True)
    stmt = If(Compare('<', Var('x'), IntConst(0)),
              Assign('r', BinOp('-', IntConst(0), Var('x'))),
              Assign('r', Var('x')))
    post = ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                  ImpOr(Compare('==', Var('r'), Var('x')),
                        Compare('==', Var('r'), BinOp('-', IntConst(0), Var('x')))))
    verify(pre, stmt, post, "Absolute Value")


# ============================================================================
# Part (c): Invariant Discovery — 8 pts
#
# For each program below, replace the `???` invariant with a correct one.
# [EXPLAIN] in a comment how you found each invariant and why it works.
# ============================================================================

# [EXPLAIN] For invariants I follow a general rule which is what equation in the loop holds at all times and then add one more than what the conditional is.
# So, this is r = i * b & i <= a
# This works because for i=0, r=0 this holds. Then if you add the guard of and i < a. 
# Then the wp(stmt, I) is just r = i * b & i + 1 <= a. You know that i < a. so i + 1 <= a
# Also, the post-condition is met because its r = i * b & i = a so r = a * b
def test_mult():
    """C1: multiplication by repeated addition."""
    pre = Compare('>=', Var('a'), IntConst(0))
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('*', Var('i'), Var('b'))),
        Compare('<=', Var('i'), Var('a')),
    )
    body = Seq(Assign('r', BinOp('+', Var('r'), Var('b'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', IntConst(0)),
                   While(Compare('<', Var('i'), Var('a')), inv, body)))
    post = Compare('==', Var('r'), BinOp('*', Var('a'), Var('b')))
    verify(pre, stmt, post, "C1: Multiplication by Addition")


# [EXPLAIN] For invariants I follow a general rule which is what equation in the loop holds at all times and then add one more than what the conditional is.
# So, this is r = n + i & i <= m
# This works because for i=0, r=n this holds. Then if you add the guard of and i < m.
# Then the wp(stmt, I) is just r = n + i & i + 1 <= m. You know that i < m. so i + 1 <= m
# Also, the post-condition is met because its r = n + i & i = m so r = n + m
def test_add():
    """Program C2 — Addition by loop."""
    pre = ImpAnd(Compare('>=', Var('n'), IntConst(0)),
                 Compare('>=', Var('m'), IntConst(0)))
    inv = ImpAnd(
        Compare('==', Var('r'), BinOp('+', Var('n'), Var('i'))),
        Compare('<=', Var('i'), Var('m'))
    )
    body = Seq(Assign('r', BinOp('+', Var('r'), IntConst(1))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(0)),
               Seq(Assign('r', Var('n')),
                   While(Compare('<', Var('i'), Var('m')), inv, body)))
    post = Compare('==', Var('r'), BinOp('+', Var('n'), Var('m')))
    verify(pre, stmt, post, "C2: Addition by Loop")


# [EXPLAIN] For invariants I follow a general rule which is what equation in the loop holds at all times and then add one more than what the conditional is.
# So, this is 2 * s = i * (i - 1) & i <= n + 1
# This works because for i=1, s=0 this holds. Then if you add the guard of and i <= n.
# Then the wp(stmt, I) is just 2 * s = i * (i - 1) & i + 1 <= n + 1. You know that i <= n. so i + 1 <= n + 1
# Also, the post-condition is met because its 2 * s = i * (i - 1) & i = n + 1 so 2 * s = n * (n + 1)
def test_sum():
    """Program C3 — Sum of 1..n."""
    pre = Compare('>=', Var('n'), IntConst(1))
    inv = ImpAnd(
        Compare(
            '==',
            BinOp('*', IntConst(2), Var('s')),
            BinOp('*', Var('i'), BinOp('-', Var('i'), IntConst(1))),
        ),
        Compare('<=', Var('i'), BinOp('+', Var('n'), IntConst(1))),
    )
    body = Seq(Assign('s', BinOp('+', Var('s'), Var('i'))),
               Assign('i', BinOp('+', Var('i'), IntConst(1))))
    stmt = Seq(Assign('i', IntConst(1)),
               Seq(Assign('s', IntConst(0)),
                   While(Compare('<=', Var('i'), Var('n')), inv, body)))
    post = Compare('==', BinOp('*', IntConst(2), Var('s')),
                   BinOp('*', Var('n'), BinOp('+', Var('n'), IntConst(1))))
    verify(pre, stmt, post, "C3: Sum of 1..n")


# ============================================================================
# Part (d): Find the Bug — 4 pts
#
# The invariant below is WRONG (too weak). Your VCG should report failure.
# 1. Run it — which side VC fails?
# 2. [EXPLAIN] Give a concrete state where the invariant holds but the
#    postcondition does not.
# 3. Fix the invariant and re-verify.
# ============================================================================

def test_buggy_div():
    """
    Integer division with a BUGGY invariant.
      { x >= 0 ∧ y > 0 }
      q := 0; r := x;
      while r >= y  invariant (q * y + r == x)  do    ← TOO WEAK!
        r := r - y;  q := q + 1;
      { q * y + r == x ∧ 0 <= r ∧ r < y }

    The invariant q * y + r == x is correct but INCOMPLETE.
    It is missing a crucial conjunct. Find it.
    """
    pre = ImpAnd(Compare('>=', Var('x'), IntConst(0)),
                 Compare('>', Var('y'), IntConst(0)))

    inv_buggy = Compare(
        '==',
        BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
        Var('x'),
    )

    body = Seq(Assign('r', BinOp('-', Var('r'), Var('y'))),
               Assign('q', BinOp('+', Var('q'), IntConst(1))))
    stmt_buggy = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_buggy, body)))

    post = ImpAnd(Compare('==',
                       BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')),
                       Var('x')),
                  ImpAnd(Compare('>=', Var('r'), IntConst(0)),
                         Compare('<', Var('r'), Var('y'))))

    verify(pre, stmt_buggy, post, "Buggy Division (should FAIL)")

    # [EXPLAIN] e.g. x=5, y=3: invariant holds for q=2, r=-1 since q*y+r=x, but post needs r>=0.

    inv_fixed = ImpAnd(
        Compare('==', BinOp('+', BinOp('*', Var('q'), Var('y')), Var('r')), Var('x')),
        Compare('>=', Var('r'), IntConst(0)),
    )
    stmt_fixed = Seq(Assign('q', IntConst(0)),
                     Seq(Assign('r', Var('x')),
                         While(Compare('>=', Var('r'), Var('y')),
                               inv_fixed, body)))

    verify(pre, stmt_fixed, post, "FIXED")
    print("FIXED: Verified")


# ============================================================================
# Part (a): WP Derivation via Z3 — 6 pts
#
# Build the following program as an IMP AST:
#   x := x + 1;
#   if x > 0 then y := x * 2 else y := 0 - x;
# Postcondition: { y > 0 }
#
# 1. Call wp() to get the weakest precondition. Print the Z3 formula.
# 2. Use Z3 to check whether each of the following is a valid precondition:
#    - { x >= 0 }
#    - { x >= -1 }
#    - { x == -1 }
#    For each, print whether it's valid and add a comment explaining why.
# ============================================================================

def test_wp_derivation():
    """Part (a): Use your VCG to compute wp, then check candidate preconditions."""
    print("=== Part (a): WP Derivation ===")

    stmt = Seq(
        Assign('x', BinOp('+', Var('x'), IntConst(1))),
        If(
            Compare('>', Var('x'), IntConst(0)),
            Assign('y', BinOp('*', Var('x'), IntConst(2))),
            Assign('y', BinOp('-', IntConst(0), Var('x'))),
        ),
    )
    post = Compare('>', Var('y'), IntConst(0))

    wp_result = wp(stmt, bexp_to_z3(post))
    print(f"  wp = {wp_result}")

    candidates = [
        ("x >= 0",  z3_var('x') >= 0), #[EXPLAIN]: Valid — wp simplifies to x != -1 and x >= 0 is strictly stronger (it excludes -1).
        ("x >= -1", z3_var('x') >= -1), #[EXPLAIN]: Invalid — x >= -1 includes x = -1, which makes x+1 = 0, hitting the else branch where y = 0, violating y > 0.
        ("x == -1", z3_var('x') == -1), #[EXPLAIN]: Invalid — x = -1 makes x+1 = 0, so the else branch sets y = 0 - 0 = 0, which doesn't satisfy y > 0.
    ]
    for name, pre in candidates:
        s = Solver()
        s.add(Not(Implies(pre, wp_result)))
        result = s.check()
        valid = (result == unsat)
        print(f"  {name}: {'VALID' if valid else 'INVALID'}")

    print()


# ============================================================================
if __name__ == "__main__":
    print("=" * 60)
    print("Part (b): VCG Correctness Tests")
    print("=" * 60)
    test_swap()
    test_abs()

    print("=" * 60)
    print("Part (a): WP Derivation via Z3")
    print("=" * 60)
    test_wp_derivation()

    print("=" * 60)
    print("Part (c): Invariant Discovery")
    print("=" * 60)
    test_mult()
    test_add()
    test_sum()

    print("=" * 60)
    print("Part (d): Find the Bug")
    print("=" * 60)
    test_buggy_div()
