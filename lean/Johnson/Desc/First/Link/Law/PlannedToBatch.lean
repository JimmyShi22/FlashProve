-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/PlannedToBatch.lean: FROM THE APPROXIMATE RANGE PROOF's DRAW TO THE
LINK's BATCHING, AT THE PROOF FILE's SEAT: EVERY READING OF THAT PROOF's STRUCTURE IN THE VERIFIER's
STATE THAT READS NEITHER THE DRAWN MATRIX NOR THE FOUR FIELDS THAT THE LOOKUP ON THE DIGITS LAYS
HAS,
AT EVERY STATE REACHED AT THE BATCHING's NUMBER, THE VALUE THAT IT HAS AT THE STATES REACHED AT THE
DRAW's NUMBER. General in the reading. Theorems. No text already in the library turns.

Why. The link's table asks, at the state in front of the batching, tests on the planned fields of
the structure (the arrays' index, the number of matrices, the symbol arrays' numbers, the matrices,
the pieces …). `k8LaidOwn` (Johnson/P1K8R/FrontAtSeat.lean) has seven of them IN FRONT OF
THE DRAW, at the link's own planned value; `staysAt_open` (Johnson/P1K8R/WideAtSeat.lean) says
what the entries behind the draw leave.

  `KeepsDraw g`: g reads neither cfF nor cfFirst. `hear_leaves_read`: the draw's block leaves
    `readTl g` (by `drawn_of_yes`, Johnson/Desc/First/K8/TieRides.lean).
  `stretch_leaves`: in scope, at `IM.Open … secondHashFunction`, at each (l, i, n) of the written list
    `stretches`: the entries of the numbers 14 l + i + 2 … 14 l + i + 2 + n leave `readTl g`.
  `planned_to_batch`: **so: readTl g = v at every state reached at 14 l + i + 2 ⊢ readTl g = v at
    every state reached at 14 l + i + 3 + n**, which is the batching's entry's number
    (`batch_behind`). `Reach`: by the sub-protocols' own steps; `RchAt` gives it (`rchAt_raw`).
Limits. The premise at the draw's number is shown here of no reading. The batching's own step and
the runs behind it are not treated. In scope, at secondHashFunction alone. Nothing on soundness.

-/
import Johnson.P1K8R.WideAtSeat
import Johnson.Desc.First.K8.TieRides
import Johnson.Desc.First.Link.Law.ReachLeaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open Inst.Model
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (readTl Keeps4 approximateRangeProofDrawKind atS drawn_of_yes putTl_tl)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile (Cl)

/-- A reading that the draw does not turn. -/
def KeepsDraw {α : Type} (g : HTailF2 → α) : Prop :=
  ∀ (tl : HTailF2) (mm : Array Int) (f : Array Nat), g { tl with cfF := mm, cfFirst := f } = g tl

theorem hear_leaves_read {Cl' α : Type} {g : HTailF2 → α} (hd : KeepsDraw g) (p : First.K8.Par) :
    (approximateRangeProofDrawKind (Cl := Cl') atS p).Leaves (readTl g) := by
  intro s rs gs s' h
  obtain ⟨tl, mm, f, ht, rfl⟩ := drawn_of_yes p s s' rs gs h
  unfold readTl
  rw [putTl_tl s tl _ ht, ht]
  exact congrArg some (hd tl mm f)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem stretch_leaves (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ P1K8S.stretches) {α : Type} (g : HTailF2 → α) (h4 : Keeps4 g) (hd : KeepsDraw g) :
    ∀ j, 14 * x.1 + x.2.1 + 2 ≤ j → j < 14 * x.1 + x.2.1 + 2 + (x.2.2 + 1) →
      ∀ b, c.blocksInOrder[j]? = some b → b.Leaves (readTl g) := by
  intro j h1 h2 b hb
  by_cases hj : j = 14 * x.1 + x.2.1 + 2
  · subst hj
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
    have hp : (l, if l = 24 then 5 else 4) ∈ P1K8S.places := List.mem_map.2 ⟨l, hl, rfl⟩
    obtain ⟨_, b0, Xl, _, _, hf, _, _, hs, _⟩ := P1K8S.sitsAt_open hS hR O _ hp
    obtain rfl : b0 = b := Option.some.inj (hf.symm.trans hb)
    exact P1K8S.leaves_of_under hs.under (hear_leaves_read hd _)
  · refine (P1K8S.staysAt_open hS hR O x hx).2 (j - (14 * x.1 + x.2.1 + 3)) (by omega) b ?_ _ g h4
    rw [show 14 * x.1 + x.2.1 + 3 + (j - (14 * x.1 + x.2.1 + 3)) = j by omega]
    exact hb

/-- **FROM THE DRAW's NUMBER TO THE BATCHING's.** -/
theorem planned_to_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {x : ℕ × ℕ × ℕ}
    (hx : x ∈ P1K8S.stretches) {α : Type} (g : HTailF2 → α) (h4 : Keeps4 g) (hd : KeepsDraw g)
    (v : ProofFile.InstPub → Option α)
    (h0 : ∀ a, Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 2) a → readTl g a.2 = v a.1) :
    ∀ a, Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * x.1 + x.2.1 + 3 + x.2.2) a →
      readTl g a.2 = v a.1 := by
  intro a h
  rw [show 14 * x.1 + x.2.1 + 3 + x.2.2 = 14 * x.1 + x.2.1 + 2 + (x.2.2 + 1) by omega] at h
  exact reach_carries 0 c.blocksInOrder (ProofFile.startS Z) (readTl g) _ _
    (stretch_leaves hS hR O hx g h4 hd) v h0 a h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.hear_leaves_read
#print axioms VerifiableInference.Desc.LinkJoin.stretch_leaves
#print axioms VerifiableInference.Desc.LinkJoin.planned_to_batch
