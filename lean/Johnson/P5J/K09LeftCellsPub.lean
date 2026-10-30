-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K09LeftCellsPub.lean: K9's LAW AT THE 25 LINKS, AT THE CLOSED CONSTANT: THREE OF THE
SEVEN PREMISES ON PUBLIC DATA OF `AtMgA.left_cells` (K09LeftCells.lean beside this file): hp, hpl
AND h3. Closed facts by Lean's kernel on written lists, and theorems. A law file; no running text
imports it.
  `batchPlaceB e m`, `batch_place_full`, `batch_place_bent`   BY THE KERNEL: the written list of
                    places has, at the batching's number of link m, a place that bears the link m,
                    at all 25; a corollary, no control: that place bears the link m + 1 at no m.
  `batch_place`       hp | hpl: ∃ p, At.ps[batchAt fullLinks At.ps m]? = some p ∧ p.link = some m.
  `momentsB n`, `moments_full`, `moments_tight`   BY THE KERNEL: every link of the written shape of
                    a request has at most three moments; THE CONTROL: "at most two" fails.
  `AtMgA.left_moments`  h3: from the head: ∀ L, Zp.first.shape.link[m]? = some L → reqMoments L ≤ 3:
                    in scope the first chain's shape is the written one (first_written_in_scope,
                    request_shape_written).

Limits. The four other premises on public data (hT1, hT2, hB, hZ) are not treated. At
OnBytes.secondHashFunction. The full size alone. Nothing on soundness or on hiding.

-/
import Johnson.P5J.K09LeftCells
import Johnson.Goal.Numbers.RequestWritten
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open OnBytes OnBytes.Model OnBytes.Params
open OnBytes.Maker (WholeD)
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.LinkJoin (batchAt)
open VerifiableInference.Desc.ReqLit (shapeFull)

/-- The place at the batching's number of link m bears the link m + e. -/
def batchPlaceB (e m : ℕ) : Bool :=
  (At.ps[batchAt fullLinks At.ps m]?).any fun p => p.link == some (m + e)

set_option maxRecDepth 1000000 in
theorem batch_place_full : (List.range 25).all (batchPlaceB 0) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A corollary of batch_place_full (one place bears one link). It would hold over no place at all
too: so it is no control. Nothing uses it. -/
theorem batch_place_bent : (List.range 25).any (batchPlaceB 1) = false := by decide +kernel

/-- **hp | hpl.** -/
theorem batch_place {m : ℕ} (hm : m < 25) :
    ∃ p, At.ps[batchAt fullLinks At.ps m]? = some p ∧ p.link = some m := by
  have a := List.all_eq_true.1 batch_place_full m (List.mem_range.2 hm)
  unfold batchPlaceB at a
  cases e : At.ps[batchAt fullLinks At.ps m]? with
  | none =>
    rw [e] at a
    cases a
  | some p =>
    rw [e] at a
    exact ⟨p, rfl, by simpa using a⟩

/-- Every link of the written shape has at most n moments. -/
def momentsB (n : ℕ) : Bool := shapeFull.link.all fun L => decide (reqMoments L ≤ n)

set_option maxRecDepth 1000000 in
theorem moments_full : momentsB 3 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The control. -/
theorem moments_tight : momentsB 2 = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Desc.First.Look.Place}

/-- **h3.** -/
theorem AtMgA.left_moments (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (m : ℕ) :
    ∀ L, Zp.first.shape.link[m]? = some L → reqMoments L ≤ 3 := by
  have e : Zp.first.shape = shapeFull :=
    (PlanWritten.Joined.first_written_in_scope h.scope h.laid.pub
      (pins_of_laid h.scope h.laid).1).2.2.1.trans PlanWritten.request_shape_written
  intro L hL
  rw [e] at hL
  exact of_decide_eq_true (List.all_eq_true.1 moments_full L (List.mem_of_getElem? hL))

end P5J

#print axioms P5J.batch_place_full
#print axioms P5J.batch_place_bent
#print axioms P5J.batch_place
#print axioms P5J.moments_full
#print axioms P5J.moments_tight
#print axioms P5J.AtMgA.left_moments
