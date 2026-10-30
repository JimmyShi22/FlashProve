-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/P2At.lean: the numbers of a place of the kind K2 (`K2.P2`,
Johnson/Top/H0/Tw/K2C/Kind.lean) against a record of Row.lean: the two entries that the block
declares are the plan's two entries at the record.

Reading.lean asks of the two written rounds that they have the PLAN's two entries (`K2Wr`). A block
of the description declares its own entries, made of its place's numbers (`K2.rounds p`). Here the
two are tied by one equation of lists, which can be evaluated. Definitions, and theorems with their
proofs.

Main names:
  `P2At r p`: the declared entries are the plan's. `p2AtB`: the same as a test.
  `P2At.logN`, `P2At.positions`: so the place's range of positions and their number are the
    record's.
  `k2Wr_of`: written rounds with the block's declared entries and the kinds of the entries' names
    meet `K2Wr`.
  `p2Of`, `p2Of_at`: numbers of a place made of a record meet `P2At`: so it is not empty.

Limits: that the numbers which a lot lays at a place of a made plan meet `P2At` at the place's
record is not shown. `p2Of` fills the fields that no entry reads (name, place, the trees read and
the like) with letters. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Reading
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Maker OnBytes.Tie.Pv.Switch

/-- **The block's declared entries are the plan's two entries at the record.** -/
def P2At (r : SwRow) (p : K2.P2) : Prop :=
  (K2.rounds p).map (·.entry) = r.specs.map fun y => (y.round r.set .request).entry

/-- The same as a test. -/
def p2AtB (r : SwRow) (p : K2.P2) : Bool :=
  decide ((K2.rounds p).map (·.entry) = r.specs.map fun y => (y.round r.set .request).entry)

theorem p2At_of {r : SwRow} {p : K2.P2} (h : p2AtB r p = true) : P2At r p := by
  unfold p2AtB at h
  unfold P2At
  exact of_decide_eq_true h

theorem P2At.logN {r : SwRow} {p : K2.P2} (h : P2At r p) : p.logN = r.g.main.logN :=
  congrArg (fun l : List Fmt.Entry => (l.getD 1 { name := "" }).logN) h

theorem P2At.positions {r : SwRow} {p : K2.P2} (h : P2At r p) :
    p.positions = baseCount r.set .request r.g :=
  congrArg (fun l : List Fmt.Entry => (l.getD 1 { name := "" }).poss) h

/-- **Written rounds with the block's declared entries meet `K2Wr`.** -/
theorem k2Wr_of {r : SwRow} {p : K2.P2} (h : P2At r p) {d₁ d₂ : RDT}
    (he : [d₁, d₂].map (·.entry) = (K2.rounds p).map (·.entry))
    (hk : ∀ d ∈ [d₁, d₂], Fmt.kindOf d.entry.name = some d.kind) : K2Wr r d₁ d₂ := by
  have e := he.trans h
  have e1 : d₁.entry = ((sendSeed r.set r.o r.roots).round r.set .request).entry :=
    congrArg (fun l : List Fmt.Entry => l.getD 0 { name := "" }) e
  have e2 : d₂.entry = ((locRound r.set .request r.g (24 * (r.set.samples * r.o.length)) 0
      (r.set.samples * r.o.length)).round r.set .request).entry :=
    congrArg (fun l : List Fmt.Entry => l.getD 1 { name := "" }) e
  exact ⟨e1, hk d₁ (by simp), e2, hk d₂ (by simp)⟩

/-- Numbers of a place made of a record; q: the fields that no entry reads. -/
def p2Of (r : SwRow) (q : K2.P2) : K2.P2 :=
  { q with
    work₁ := r.set.workOf .sample .request
    roots := r.roots
    seeds := r.set.samples * (largestCube r.o + 1)
    nonZero := r.set.samples
    work₂ := r.set.workOf .query .request
    answers := r.set.samples * r.o.length
    positions := baseCount r.set .request r.g
    logN := r.g.main.logN }

theorem p2Of_at (r : SwRow) (q : K2.P2) : P2At r (p2Of r q) := rfl

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2Wr_of
#print axioms VerifiableInference.Desc.First.K2Caller.p2Of_at
