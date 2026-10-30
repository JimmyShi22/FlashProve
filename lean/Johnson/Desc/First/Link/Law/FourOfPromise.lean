-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-

Johnson/Desc/First/Link/Law/FourOfPromise.lean: THE CLAUSES «four» AND «ents4» OF A LINK's Ok (`OkCore`, OkOne.lean beside this file) AT EVERY STATE THAT IS REACHED IN FRONT OF THE BATCHING, AT ALL 25 LINKS OF THE IOP AS
WRITTEN IN LEAN, IN THE GOALS' SCOPE: **WITH THE PREMISE hLed OF FourAtBatch.lean GONE**: in its place hB: AT THAT SAME STATE a ledger is open and has its sizes: which the table's promise says there (the public item «ledger m»).
Theorems.

Why. FourAtBatch.lean's theorems ask the ledger's sizes at every state reached IN FRONT OF the lookup on the digits (hLed): of such a state one has «reached» and no more, and nobody has the sizes along «reached». But no text
between turns an array's length: so the sizes are pulled back from the state in front of the batching. A reached state has no one predecessor: so the pull is made INSIDE the proof, at the very predecessor that it takes, from
the very accept that it reads.

What is said.
  `four_raw_of`: l < 25; c' reached right behind the digits' seated sub-protocol; hp; hB at c' ⊢ what was heard, the ledger, and the two bodies (as `four_raw_at`).
  `four_of_promise`: **l < 24; c' reached at 14 l + 9; hp; hB at c' ⊢ `OkCore`'s clauses four and ents4, to the letter, at `fixed9 φ c'`.**
  `four_of_promise_head`: **the same at the head's link: c' reached at 347**: the sizes are pulled back over the merge, then over the digits.
BY: `sizes_behind_digits` (SizesDigits.lean: off `decide_sameLen`, Johnson/Top/H/Keep/PadSizes.lean, and `quietAt_sizesS`) · `merge_pulls` (SizesBack.lean) · FourBehindDigits.lean ·
FourAtBatch.lean's `piece_digits`, `merge_leaves_tl`.

Limits. hp follows from one accepting run (`IM.planOk_of_run`). hB is a premise: the promise's, at the batching's own border. The premises are not shown to be satisfiable. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SizesDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Q : Type} {start : Q → S}

/-- **RIGHT BEHIND THE DIGITS' SEATED SUB-PROTOCOL, FROM THE SIZES AT THAT SAME STATE.** -/
theorem four_raw_of (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 25) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + IM.k3Ix l true + 2 + 1) (z, c'))
    (hB : ∃ G', c'.fork? = some G' ∧ Sized G') :
    ∃ g G, c'.tl?.bind (·.heard) = some g ∧ c'.fork? = some G ∧ Sized G ∧
      (∀ tl, ∀ cl ∈ four8 tl g, cl.form.ents = #[]) ∧
      ∀ H, _root_.Fo.Later G H → ∀ tl, ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled H x.1 := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l hl true
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s _ rs gs).1 hd).1
  have hOk : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 l rfl h7
  obtain ⟨G₀, hG₀, hz₀⟩ :=
    (sizes_behind_digits _ _ _ _ _ _ b' l e3 hOk rfl hpc s rs gs _ hd').pulls hB
  exact four_behind_digits _ _ _ _ _ _ b' e3 hOk l rfl hpc s _ rs gs hd' hG₀ hz₀

/-- **AT 24 LINKS: IN FRONT OF THE BATCHING: WITHOUT hLed.** -/
theorem four_of_promise (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {l : ℕ} (hl : l < 24) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start (14 * l + 9) (z, c'))
    (hB : ∃ G', c'.fork? = some G' ∧ Sized G')
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    (∀ v tlb g, (fixed9 φ c').2 = some v → (π (fixed9 φ c').1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g, (π (fixed9 φ c').1).1 = some tlb → tlb.heard = some g →
        ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  have e : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  obtain ⟨g, G, h1, h2, hz, h3, h4⟩ := four_raw_of (start := start) hS hR O hp
    (by omega : l < 25) (z := z) (c' := c') (by rw [e]; exact h) hB
  exact four_fixed π φ u hπ h1 h2 hz h3 (h4 G (_root_.Fo.Later.refl G))

/-- **AT THE HEAD's LINK: IN FRONT OF THE BATCHING (347): WITHOUT hLed.** -/
theorem four_of_promise_head (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {z : Q} {c' : S}
    (h : Reach 0 c.blocksInOrder start 347 (z, c')) (hB : ∃ G', c'.fork? = some G' ∧ Sized G')
    {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α) (u : HTailF2)
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) :
    (∀ v tlb g, (fixed9 φ c').2 = some v → (π (fixed9 φ c').1).1 = some tlb →
      tlb.heard = some g → Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g, (π (fixed9 φ c').1).1 = some tlb → tlb.heard = some g →
        ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  obtain ⟨z', s, s'', b₀, e, hr, hb, hy⟩ := reach_pred (k := 346) h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  obtain ⟨Lk, b, e1, e2, hla, -⟩ := IM.k11_of hS hR O
  have h3 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by decide) 8] at h3
  obtain rfl : b = b₀ := Option.some.inj (h3.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hm : headMergeDecide _ s rs = .ok _ := ((IM.k11_yes hla _ _ _ _).1 hd).1
  obtain ⟨g, G, a1, a2, az, a3, a4⟩ := four_raw_of (start := start) hS hR O hp (l := 24)
    (by decide) (z := z) (c' := s) hr (merge_pulls _ hm hB)
  obtain ⟨t1, G', t2, t3⟩ := merge_leaves_tl hm a2
  exact four_fixed π φ u hπ (by rw [t1]; exact a1) t2 (t3.sized az) a3
    (a4 G' ⟨t3.next, t3.ns, t3.keep⟩)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.four_raw_of
#print axioms VerifiableInference.Desc.LinkJoin.four_of_promise
#print axioms VerifiableInference.Desc.LinkJoin.four_of_promise_head
