-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/K8Claims.lean: the smallness test's CLAIMS half as fields of a block
(Johnson/Desc/Block.lean): the run of claims, and two runs behind the batching: the one
writing that the equations' text leaves to it, and the tests on the batched sums.

  `K8Part`: the part of the carried record that this half reads and writes: the smallness test's
    record, the sub-proof's list of tables (read alone), the sub-proof's state.
  `k8Claims`: for `Block.claims`: one named run, "K8.equations": from the number that the run is
    handed and the part, to the list of claims (`equations`, Equations.lean) and the part behind
    it; a refusal bears the name of the test that refused.
  `k8LsTail`: for `Block.after`: "K8.lsTail": the coefficients on the block's own masking values,
    read off the ledger behind the adding (`verify-on-bytes`'s OnBytes/Model/Tail.lean:1094).
  `k8Tests nU`: for `Block.after`, behind it: "K8.tests": the tests on the batched sums and the
    rows' weights (`testsP`, SelfRows.lean).
  `k8PartP`: where the part lies in the first chain's carried record S
    (Johnson/Desc/First/State.lean), as a `Part` (Johnson/Desc/Lens.lean): there inside a link
    alone; for `Block.liftPart k8PartP.get? k8PartP.set`.
THE NUMBER OF CLAIMS IN FRONT OF THE LIST is the ledger's own count (the claims added so far) plus
the number that the run is handed (the claims gathered in this call and not yet added): so it is
right where a link's claims are all gathered first, and where they are gathered and added cut by
cut, if each cut is added before the next is gathered. It is a claim's number as `verify-on-bytes`
counts it, IF the link's runs are gathered in the order in which that program adds its claims: its
ledger belongs to one link and counts from 0 there (at a link's end it asks that the count is the
plan's number of that link's claims: OnBytes/Model/Attention.lean:156, Head.lean:329,
Layer.lean:633). By reading; not run.
THE DIGITS' LOOKUP's OWN CLAIMS ARE NOT THIS RUN's: the lookup's block lays them (its run "objects")
and pays their owed mark. TWO DEMANDS ON THE DRIVER, which this run cannot see kept: that run is
gathered right before this one, so that its claims are counted in front; and its claims are not
added until this run has been called, or the test of Tail.lean:1046-1047 refuses an honest proof
(Equations.lean's head says why). A DEMAND ON whoever gathers both lists: that the lookup's run
lays `lookRows tl` claims (Tail.lean:1053): this run sees the heard rows alone, and asks it of them.
NOT ASKED IN THIS FORM, by name: "only the smallness test's equations, the digits' lookup's own
among them, lay weights on the masking values in its window": `verify-on-bytes` asks it by two tests
in time (Tail.lean:1046-1047; :1158-1159 against lsTail), which go blind together where a link's
claims are gathered before any is added: the first still stands in `equations` and is idle on an
empty ledger. A test on the list of claims would ask it: no claim but this run's and the digits'
lookup's names a slot in the window.
Limits: definitions alone. HTailF2, HFun and Fork here, and what
Equations.lean and SelfRows.lean call by name, are `verify-on-bytes`'s.

-/
import Johnson.Desc.First.TailClaims.Equations
import Johnson.Desc.First.TailClaims.SelfRows
import Johnson.Desc.First.Parts

set_option autoImplicit false

namespace VerifiableInference.Desc.First.TailClaims

open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First

/-- The part of the carried record that the smallness test's claims half reads and writes. -/
structure K8Part where
  /-- the smallness test's record -/
  tl : HTailF2
  /-- the sub-proof's list of tables: read alone -/
  funs : Array HFun
  /-- the sub-proof's state; the ledger lies in it -/
  F : Fork

/-- For `Block.claims`. -/
def k8Claims : List (String × (Nat → K8Part → Except String (List Claim × K8Part))) :=
  [("K8.equations", fun front p =>
    (equations (p.F.nClaim + front) p.tl p.funs p.F).map fun x =>
      (x.2.2, { p with tl := x.1, F := x.2.1 }))]

/-- For `Block.after`. -/
def k8LsTail : String × (K8Part → Except String K8Part) :=
  ("K8.lsTail", fun p =>
    .ok { p with tl := { p.tl with lsTail := p.F.LS.extract p.tl.slotA p.tl.slotB } })

/-- For `Block.after`, behind `k8LsTail`: the smallness test's sixteen tests on the sums, with the
rows' weights set between them (`testsP`, SelfRows.lean). nU: the plan's lengths of the vectors U1
to U3 at this place. A refusal bears the guard's own name. -/
def k8Tests (nU : Array Nat) : String × (K8Part → Except String K8Part) :=
  ("K8.tests", fun p => (testsP nU p.tl p.F).map fun F => { p with F := F })

/-- Where the part lies in the first chain's carried record. The list of tables is read and not laid
back. -/
def k8PartP : Part S K8Part :=
  ⟨fun s => (tlForkP.get? s).bind fun x => (S.funs? s).map fun funs => ⟨x.1, funs, x.2⟩,
   fun s p => tlForkP.set s (p.tl, p.F)⟩

end VerifiableInference.Desc.First.TailClaims
