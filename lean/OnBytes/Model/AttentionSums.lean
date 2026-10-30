-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionSums.lean: the two kinds of sumcheck of the attention sub-proof.

Both kinds are masked sumchecks (OnBytes/Model/Psc.lean); the protocol's pages call them
zero-knowledge. This file follows the verifier's steps and claims nothing about hiding. The prover
sends the sum of a hiding polynomial, and the verifier draws the element that joins that polynomial
to the claim. Then come the rounds over the variables, one round in a further variable, and the end
values, each under a mask. No round tests an equation. A run leaves one affine form that must be 0.
This form is the row of the sumcheck. The caller adds the row to the claims of the sub-proof. It
must also tie down each end value. For most end values it adds a claim that says which value of
which committed matrix the end value is. An end value can instead enter the start of a later
sumcheck, or a claim that ties it to another end value. The statement of each kind stands at the
head of its section.

What the caller must do first. Before it begins a run, it must have received every hidden value that
the form start names and every message that the summand depends on (for the sumcheck of products:
the weights and the maps). It must also have made every draw that the summand depends on. Only the
first of these is tested: pscBegin refuses a form that names a slot that is still free. The order of
the other messages and draws is tested neither here nor in OnBytes/Model/Psc.lean.

The file follows verifier/src/vf_sumcheck_attention.h: sc3Slots, sc3In, sc3A, sc3B, sc3Row, scdIn.
scdRow has no routine there: the C++ caller makes that row itself. OnBytes/Model/AttentionHeard.lean
explains the terms of the attention files.

Main definitions: sc3Slots, Sc3, sc3In, sc3A, sc3B, sc3Row, Scd, scdIn, scdRow, sumsNames.

This file holds no theorem. It claims neither soundness nor hiding.
-/
import OnBytes.Model.Psc

namespace OnBytes.Attention

/-! ## The sumcheck of products

The statement of the sumcheck of products is
  start = sum over b and x of W_b(x) A_b(x) B_b(x)
for nb pairs of maps (A_b, B_b) in nv variables. The weights W_b are public. The polynomial of a
round has degree 3. The end values are A_0, B_0, A_1, B_1 and so on at the point of the challenges.

The next paragraph holds of both kinds of sumcheck.
Slots. Each scalar that a sub-proof sends has a number, its slot (OnBytes/Model/Hide.lean). A run
takes the next free slots: one for the sum of the hiding polynomial, one for each coefficient sent,
and one for each end value.
-/

/-- The number of slots that a sumcheck of products takes: 1 for the sum of the hiding polynomial,
3 for each of the nv rounds, 2 for the round in the further variable, and 2 for each of the nb pairs
of maps. -/
def sc3Slots (nv nb : Nat) : Nat := Model.sumcheckSlots .sum3 nv (2 * nb) 2

/-- A sumcheck of products: what has been received of it so far. -/
structure Sc3 where
  /-- the challenges of the rounds over the variables, in the order of the rounds -/
  r : Array E := #[]
  /-- the slot of the first end value -/
  sEnd : Nat := 0
  /-- the number of pairs of maps -/
  nb : Nat := 0
  /-- the state of the masked sumcheck -/
  p : Model.Psc := default
  /-- the row. Until sc3Row has made it, it is the form 0, a claim that always holds: a caller must
  run sc3Row before it adds the row -/
  rowU : Model.Aff := Model.Aff.ofConst zeroE
  deriving Inhabited

/-- Runs n rounds of degree 3. r holds the challenges of the rounds before them. Returns all
challenges and the new state. -/
def sc3Rounds : Nat → Model.Psc → Array E → Model.SubM (Array E × Model.Psc)
  | 0, p, r => pure (r, p)
  | n + 1, p, r => do
    let x ← Model.roundIn .sum3 p
    sc3Rounds n x.2 (r.push x.1)

/-- Receives the messages of a sumcheck of products with nv variables and nb pairs of maps. start
is the form that the sum must equal. -/
def sc3In (nv nb : Nat) (start : Model.Aff) : Model.SubM Sc3 := do
  let p0 ← Model.pscBegin start
  let x ← sc3Rounds nv p0 #[]
  let e ← Model.pscEnds x.2 2 (2 * nb)
  pure { r := x.1, sEnd := e.1, nb := nb, p := e.2 }

/-- The hidden end value of the map A_b. -/
def sc3A (o : Sc3) (b : Nat) : Model.Aff := Model.Aff.slot (o.sEnd + 2 * b)

/-- The hidden end value of the map B_b. -/
def sc3B (o : Sc3) (b : Nat) : Model.Aff := Model.Aff.slot (o.sEnd + (2 * b + 1))

/-- The summand at the point of the challenges, on the scalars that were shown for the end values.
It is the sum of W[b] times what was shown for A_b times what was shown for B_b. The arguments after
W are the number of pairs of maps that are still to be added, the first of them, and the sum of the
pairs before it. -/
def sc3Shown (o : Sc3) (W : Array E) : Nat → Nat → E → Model.SubM E
  | 0, _, s => pure s
  | n + 1, b, s => do
    let x ← Model.SubM.shown (o.sEnd + 2 * b)
    let y ← Model.SubM.shown (o.sEnd + (2 * b + 1))
    sc3Shown o W n (b + 1) (addE s (mulE (mulE (W.getD b zeroE) x) y))

/-- Makes the row of a sumcheck of products. W[b] is the weight W_b at the point of the challenges.
Refuses as internal-sc3 unless there is one weight for each pair of maps. The C++ verifier appends
the sumcheck's name, for example internal-sc3-e. Returns the run with its row set. -/
def sc3Row (o : Sc3) (W : Array E) : Model.SubM Sc3 := do
  Model.mustAs "internal-sc3" (W.size == o.nb)
  let s0 ← sc3Shown o W o.nb 0 zeroE
  let x ← Model.pscRow o.p s0
  pure { o with p := x.2, rowU := x.1 }

/-! ## The sumcheck by degrees

The statement of the sumcheck by degrees is
  start = sum over x of a summand that its caller fixes.
Every round has a degree of its own. The caller computes the summand at the point of the challenges
and passes it to scdRow.
-/

/-- A sumcheck by degrees: what has been received of it so far. -/
structure Scd where
  /-- the challenges of the rounds over the variables, in the order of the rounds -/
  r : Array E := #[]
  /-- the slot of the first end value -/
  sEnd : Nat := 0
  /-- the state of the masked sumcheck -/
  p : Model.Psc := default
  /-- the row. Until scdRow has made it, it is the form 0, a claim that always holds: a caller must
  run scdRow before it adds the row -/
  rowU : Model.Aff := Model.Aff.ofConst zeroE
  deriving Inhabited

/-- Runs one round for each member of the list, of that degree. r holds the challenges of the
rounds before them. Returns all challenges and the new state. -/
def scdRounds : List Nat → Model.Psc → Array E → Model.SubM (Array E × Model.Psc)
  | [], p, r => pure (r, p)
  | d :: ds, p, r => do
    let x ← Model.roundIn .nodes p zeroE d
    scdRounds ds x.2 (r.push x.1)

/-- Receives the messages of a sumcheck by degrees. degrees holds the degree of each round.
degreeInY is the degree of the round in the further variable. n is the number of end values. start
is the form that the sum must equal. The run takes as many slots as
Model.sumcheckSlotsDegrees degrees n degreeInY says. -/
def scdIn (degrees : List Nat) (degreeInY n : Nat) (start : Model.Aff) : Model.SubM Scd := do
  let p0 ← Model.pscBegin start
  let x ← scdRounds degrees p0 #[]
  let e ← Model.pscEnds x.2 degreeInY n
  pure { r := x.1, sEnd := e.1, p := e.2 }

/-- Makes the row of a sumcheck by degrees. s0 is the summand at the point of the challenges, which
the caller has computed on the scalars that were shown for the end values. Returns the run with its
row set. -/
def scdRow (o : Scd) (s0 : E) : Model.SubM Scd := do
  let x ← Model.pscRow o.p s0
  pure { o with p := x.2, rowU := x.1 }

/-- The names under which this file's tests fail. A name must be listed here to be printed:
proofRefusalName in OnBytes/Model/VerifyStages.lean passes on listed names only. A test without a
name, such as those that OnBytes/Model/Psc.lean writes with SubM.must and SubM.get, fails as refused
(unnamed in OnBytes/Iop/Ground.lean). -/
def sumsNames : List String := ["internal-sc3"]

end OnBytes.Attention
