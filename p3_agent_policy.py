"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5.

    TODO: Implement this. You need to think about:
    1. How to express "viewers may ONLY do X" (everything else is denied).
    2. How R4 overrides R3 for admins.
    3. Whether you need a closed-world assumption (if not explicitly
       allowed, it's denied).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    r1 = And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r)))
    r2 = And(role(u) == DEVELOPER, 
        Or(
          t == FILE_READ,
          And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
          And(t == NETWORK_FETCH, in_sandbox(r))  
        ),
    )
    r3 = And(
        role(u) == ADMIN,
        Or(
            t == FILE_READ, 
            t == FILE_WRITE, 
            And(t == SHELL_EXEC, Not(is_sensitive(r))),
            And(t == NETWORK_FETCH, in_sandbox(r))
        ),
    )
    
    axiom = ForAll([u, t, r], allowed(u, t, r) == Or(r1, r2, r3))
    constraints = [axiom]


    # TODO: Encode R1–R5
    # Hint: Start with a default-deny rule, then add exceptions.

    return constraints


def make_policy_without_r4():
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    r1 = And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r)))
    r2 = And(role(u) == DEVELOPER,
        Or(
          t == FILE_READ,
          And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
          And(t == NETWORK_FETCH, in_sandbox(r))
        ),
    )
    r3 = And(
        role(u) == ADMIN,
        Or(
            t == FILE_READ,
            t == FILE_WRITE,
            t == SHELL_EXEC,
            And(t == NETWORK_FETCH, in_sandbox(r))
        ),
    )

    axiom = ForAll([u, t, r], allowed(u, t, r) == Or(r1, r2, r3))
    return [axiom]


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(*policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.

    TODO: Implement each query.
    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    extra_1 = And(
        role(u) == DEVELOPER, 
        allowed(u, FILE_WRITE, r),
        is_sensitive(r),
        owner(r) != u, 
        in_sandbox(r)
    )
    query("Can a developer write to a sensitive file they don't own, in the sandbox?", policy, extra_1)
    #[EXPLAIN] This is the second rule, where if its in a sandbox a developer can write to it. 

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    extra_2 = And(
        role(u) == ADMIN, 
        allowed(u, NETWORK_FETCH, r),
        Not(in_sandbox(r))
    )
    query("Q2: Can an admin network_fetch a resource outside the sandbox?", policy, extra_2)
    #[EXPLAIN] This is the fifth rule where network_fetch can only be used for sandboxed resources

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    extra_3 = And(
        is_sensitive(r),
        allowed(u, SHELL_EXEC, r)
    )
    query("Is there ANY role that can shell_exec on a sensitive resource?", policy, extra_3)
    #[EXPLAIN] This is the fourth rule where nobody can shell_exec on sensitive resources

    policy_no_r4 = make_policy_without_r4()
    extra_4 = And(
        role(u) == ADMIN,
        is_sensitive(r),
        allowed(u, SHELL_EXEC, r),
    )
    query("Q4: without R4 — can an admin shell_exec on a sensitive resource?", policy_no_r4, extra_4)
    #[EXPLAIN] Without R4 the admin branch allows shell_exec on sensitive resources too, so Q4 is SAT and the model shows that dangerous action.


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    TODO:
    1. Add rule R6 to the policy.
    2. Model a 2-step trace:
       - Step 1: developer calls shell_exec on resource r1
         (r1 is non-sensitive and in sandbox — allowed by R6)
         Side-effect: this command changes resource r2 from sensitive to
         non-sensitive (e.g., modifying an access-control config)
       - Step 2: developer calls shell_exec on resource r2
         (r2 is NOW non-sensitive — was it allowed before? is it allowed now?)
    3. The twist: r2's sensitivity changes BETWEEN steps. Encode this by
       using two copies of is_sensitive (before and after).
    4. Check if the developer can effectively access a previously-sensitive resource.
    5. [EXPLAIN] in a comment: Propose and implement a fix.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    # Hint: Use is_sensitive_before and is_sensitive_after as two separate
    # functions, or use a time-indexed model.

    is_sensitive_before = Function('is_sensitive_before', Resource, BoolSort())
    is_sensitive_after  = Function('is_sensitive_after',  Resource, BoolSort())

    u  = Const('u',  User)
    r1 = Const('r1', Resource)  # the sandbox resource the dev shell_execs first
    r2 = Const('r2', Resource)  # the previously-sensitive target the attack unlocks

    # R6 at step 1: developer shell_execs r1 using the BEFORE state of is_sensitive.
    step1_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_before(r1)),
        in_sandbox(r1),
    )

    # R6 at step 2: developer shell_execs r2 using the AFTER state of is_sensitive
    # (step 1 mutated r2's flag from sensitive → non-sensitive).
    step2_allowed = And(
        role(u) == DEVELOPER,
        Not(is_sensitive_after(r2)),
        in_sandbox(r2),
    )

    attack = And(
        r1 != r2,
        is_sensitive_before(r2),       # r2 used to be sensitive (R4 should protect it)
        Not(is_sensitive_after(r2)),   # but step 1 stripped that flag
        step1_allowed,
        step2_allowed,
    )

    s = Solver()
    s.add(attack)
    res = s.check()
    print(f"  Escalation reachable? → {res}")
    if res == sat:
        print(f"    Model: {s.model()}")
    print()

    # Fix: sensitivity is monotone — once sensitive, always sensitive.
    r = Const('r', Resource)
    fix = ForAll([r], Implies(is_sensitive_before(r), is_sensitive_after(r)))

    s2 = Solver()
    s2.add(attack, fix)
    res2 = s2.check()
    print(f"  With monotone-sensitivity fix → {res2}")
    if res2 == unsat:
        print("  ESCALATION BLOCKED")
    print()

    # [EXPLAIN] R6 only checks the current is_sensitive flag, so step 1's mutation
    # can clear that flag and let step 2 shell_exec a previously-sensitive resource.
    # The fix asserts is_sensitive is monotone (it can only become MORE restricted),
    # which makes is_sensitive_before(r2) ∧ ¬is_sensitive_after(r2) unsatisfiable.


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
