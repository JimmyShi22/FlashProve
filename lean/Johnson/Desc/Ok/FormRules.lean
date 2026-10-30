-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/FormRules.lean: a rule for every form of round whose count is a function of the
entry's own numbers, and the test that no entry that stands in a plan is without a test: `everyOk
M`: comparisons of natural numbers. It runs: it imports no Mathlib, Cb or ThirdParty module. It
imports two files of lean/Johnson/Bridge/ that run too, PlanRulesNat.lean and PlanFiveNat.lean (and
through them PlanOkNat.lean, the planner and the format): these three bear that folder's mark, and
hold numbers of coding theory as bare arithmetic. This file holds none: it hands a table and a
radius on to `recordRule`, unread.

In one paragraph. No entry that is there is without a test. Five of the seven
plans are held whole against the planner's records. In the two others, the first chain's plan of a
proof file and of a key file, the entries of nine names are held against the records by `planOk`;
every other entry has the form of its name, at a cap that no record enters. What is absent from
these two plans, how many entries of a name there are, in which order (but that `planOk` reads the
name and the answers of the entry behind a «SEND seed»), and that a block's own count is under its
form's cap, nobody asks here. So spend it with `h : configure l x cfg bits = .ok M` beside it: then
records and plans come of one call of the planner, and nothing can be absent, laid
twice, renamed or moved: `configure_plans` (OnBytes/Plan/PlanListsConfigure.lean) and
`configure_proofPlans` (OnBytes/Plan/PlanListsProof.lean) say that each of the seven plans is what
the planner's own routine makes at M's records (a proof file's first plan: at these and at x's
sub-proofs); `planned_made` (OnBytes/Model/Fit/PlanTestsPlanned.lean) gives such an h for the M that
the port's `planned` makes. The doors of absence are doors of the test alone, not of the pair.

What it asks. (1) A proof file and a key file have three plans each. (2) `fiveOk M`
(Johnson/Bridge/PlanFiveNat.lean; within it `planOk M`). (3) Of each of the two first plans: every
entry has one of `planOk`'s nine names, or a name that has a rule here, and passes at its rule: so
an entry under a name that has no price makes the test say no. (4) `setWorkOk M`
(Johnson/Bridge/PlanOkNat.lean): `planOk` and `fiveOk` take the bits of work of a test's «CS» and
«BASE» off its own entry «BASE», and those of a first chain's «LOC» off the entry: here they are
held against the setting's, chain by chain.

The rules. Each takes what is drawn off the entry itself, and says which other numbers must be 0.
  Nine field names («PSC epsilon», «PSC round», «LINE», «ZERO», «JOIN», «LKP», «LKP shift», and «LIN
    zeta», «LINK phi», which at stored plans stand in the five whole plans alone): the entry draws m
    field elements, 1 ≤ m ≤ 2^16, none bound to be other than 0, and nothing else; no work. The
    count is a cap: 2^61 q^(m - 1): it bounds degree times q^(m - 1) for every degree up to 2^61.
    The comparison passes at every such entry: what is tested is the form. Among these names the
    name says nothing: one can stand for another.
  «BAT-sigma»: one field element; the count is the entry's rows less one: the one degree that an
    entry holds. The rows are held against no record; below two rows the count is 0.
  «PSC Y»: one element other than 0 and nothing else; no work; a cap: 2^60, of q - 1.
  Forms at which nothing is drawn («PSC values», «REPLY», «SEND answer», «SPLIT», «SEAL»): 0.
  «RNG», in a proof file's first plan alone: matrix entries alone, at most 2^28, a multiple of n and
    at least n, n the setting's number of combinations on a request's chain; the setting's work.
    An entry of the matrix is a pair of bits, so there are 4^entries matrices; the count is these
    over 2^n. The comparison says n + work ≥ 128: at n = 128 without work the room is 0. The count
    is one instance's: the planner's price has the setting's instances as a factor, and n their
    logarithm more (1 and 0 at the stored settings).
  «RECORD», as the first entry of a key file's first plan alone: the seed of the stored table's
    record: `recordRule`, which lies in Johnson/Bridge/PlanFiveNat.lean, since its count has a
    code's list in it; this one rule reads a record: the table's. It is no round of a chain.

Limits. A yes says nothing of a block: it holds counts. That a form's block has at most its rule's
count of bad verifier messages is each block's own law; for «RNG» it is other files'
(the laws of the smallness test's kind, K8).
No theorem says yes at any plan. Which kind a description gives a round is not read: the
theorems ask seeds where a seed is drawn, else neither seeds nor sealed. An entry's bytes, roots and
answers are not read. The columns of «RNG» are held against no record. What `planOk` leaves open in
the two first plans stays open: the rows of their «BAT», the coordinates and messages of a «SEND
seed» outside the code switches, how many such seeds there are. The names are those of a census of
stored plans. The limits of Johnson/Bridge/PlanFiveNat.lean and PlanOkNat.lean hold, among them that
the counts of bad fold points lean on files adapted from ArkLib and Mathlib (lean/LIMITS.md, L15).
The cost: a rule's guard caps what the entry draws before a power of it is taken; no definition here
or in Johnson/Bridge/PlanFiveNat.lean has a recursion of its own over a plan's entries. No sum over
rounds.

-/
import Johnson.Bridge.PlanRulesNat
import Johnson.Bridge.PlanFiveNat

set_option autoImplicit false

namespace Johnson.Desc.Ok
open OnBytes OnBytes.Params Johnson.Bridge.OkNat

/-- A field form: the entry draws m field elements, 1 ≤ m ≤ 2^16 (the guard), and the slot asks:
none of them bound to be other than 0, no position, no matrix entry, no work; the rows are the
entry's own. The count is a cap, 2^61 q^(m - 1) of the q^m points: whoever has a count «degree times
q^(m - 1)» with a degree of at most 2^61 is under it. -/
def fieldRule (name : String) : Rule :=
  ⟨name, fun e => decide (1 ≤ e.drawE) && decide (e.drawE ≤ 2 ^ 16),
    fun e => ⟨name, false, e.drawE, 0, 0, 0, 0, 0, fun y => y.rows,
      fun y => 2 ^ 61 * q ^ (y.drawE - 1)⟩⟩

/-- The batching of rows by the powers of one field element: of the q elements at most rows - 1 are
bad, the rows being the entry's own. -/
def sigmaRule : Rule :=
  ⟨"BAT-sigma", fun _ => true,
    fun _ => ⟨"BAT-sigma", false, 1, 0, 0, 0, 0, 0, fun y => y.rows, fun y => y.rows - 1⟩⟩

/-- One field element other than 0 and nothing else, without work. The count is a cap: 2^60 of the
q - 1 elements. -/
def unitRule (name : String) : Rule :=
  ⟨name, fun _ => true, fun _ => ⟨name, false, 1, 1, 0, 0, 0, 0, fun _ => 0, fun _ => 2 ^ 60⟩⟩

/-- Nothing is drawn; the count 0. -/
def zeroRule (name : String) : Rule := ⟨name, fun _ => true, fun _ => zeroSlot name⟩

/-- The matrix of the smallness test, at n combinations and w bits of work. The guard: at most 2^28
matrix entries, a multiple of n, at least n. The slot: matrix entries alone. An entry is a pair of
bits: 4^entries matrices; the count: these over 2^n, the share 2^-n of the planner's `planRng`. -/
def rngRule (n w : Nat) : Rule :=
  ⟨"RNG", fun e => decide (1 ≤ n) && decide (e.trits ≤ 2 ^ 28) && Nat.beq (e.trits % n) 0 &&
      decide (n ≤ e.trits),
    fun e => ⟨"RNG", false, 0, 0, 0, 0, e.trits, w, fun _ => 0, fun y => 4 ^ y.trits / 2 ^ n⟩⟩

/-- The names under `fieldRule`. -/
def fieldNames : List String :=
  ["PSC epsilon", "PSC round", "LINE", "ZERO", "JOIN", "LKP", "LKP shift", "LIN zeta", "LINK phi"]

/-- The names under `zeroRule`. -/
def zeroNames : List String := ["PSC values", "REPLY", "SEND answer", "SPLIT", "SEAL"]

/-- The rules that read no record and no setting. -/
def formRules : List Rule :=
  fieldNames.map fieldRule ++ [sigmaRule, unitRule "PSC Y"] ++ zeroNames.map zeroRule

/-- A proof file's first plan: these, and «RNG» at the setting's numbers on a request's chain. -/
def proofRules (s : Setting) : List Rule :=
  formRules ++ [rngRule (rngCombinations s .request) (s.workOf .small .request)]

/-- A key file's first plan: these, and «RECORD» at the stored table x.T and the radius x.e. -/
def keyRules (x : Point) : List Rule := recordRule x :: formRules

/-- The key file's stored table at the planner's radius. -/
def keyTable (M : Configured) : Point := ⟨M.sized.key.once.table, tableRad M, 0, 0⟩

/-- The two first chains' plans: every entry is of the nine names or passes at its rule; «RECORD»
stands nowhere in a key file's first plan but as its first entry. -/
def firstPlansOk (M : Configured) : Bool :=
  rulesOk nineNames (proofRules M.sized.proof.set) (entriesAt M.proof 0) &&
    rulesOk nineNames (keyRules (keyTable M)) (entriesAt M.key 0) &&
    ((entriesAt M.key 0).drop 1).all fun e => e.name != "RECORD"

/-- A proof file and a key file have three plans each. -/
def sevenOk (M : Configured) : Bool := Nat.beq M.proof.length 3 && Nat.beq M.key.length 3

/-- **THE TEST: no entry that stands in one of the seven plans is without a test**, and the bits of
work of the nine tests and of the first chain's «LOC» are the setting's (`setWorkOk`,
Johnson/Bridge/PlanOkNat.lean). -/
def everyOk (M : Configured) : Bool := sevenOk M && fiveOk M && firstPlansOk M && setWorkOk M

end Johnson.Desc.Ok

#print axioms Johnson.Desc.Ok.everyOk
