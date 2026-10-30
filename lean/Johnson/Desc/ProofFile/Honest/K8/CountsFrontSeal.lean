-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/CountsFrontSeal.lean: THE SMALLNESS TEST: THE SENTENCE
`CountsFront` OF THE ITEM "totalB" (Johnson/Desc/ProofFile/Honest/K9/TotalFront.lean) FROM THAT
FILE's OWN GATHERING OF THE LIBRARY's LAWS AT A LINK (`SealLaw`) AND THE
KIND's SEAT: two of the four premises of `counts_front`
(Johnson/Desc/ProofFile/Honest/K8/CountsFrontK8.lean) ARE PAID: `NumRun` is the field numRun of
`SealLaw`; `NumDraw` holds outright, by that house's `draw_num`
(Johnson/Desc/ProofFile/Honest/K9/DrawNum.lean). Corollaries; none of the library's goals.

  **`numDraw`**   NumDraw p u, at every place and every u: a yes of the draw holds that the
                   batching's part is there
  **`counts_front_seal`**   SealLaw sub l Lk p φ Ok nU u π tmOf lenOf → K8At Lk w.1 pW → (w.1 =
                   .head → FoldOnce Lk p T b) → CountsFront Lk p T b w
  `counts_front_alone`   the same with `K8At` out of the seat: k8Entry w.1 ∈ Lk.order, the hearing
                   block at that entry laid alone over K8.whole pW
Limits. `SealLaw` is a premise. AT THE HEAD `FoldOnce`
STAYS: no line of the run tests that count. Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.K8AtSeat
import Johnson.Desc.ProofFile.Honest.K9.DrawNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open ProofFile.Honest.K9 (CountsFront SealLaw draw_num k8Entry drawnOne)

/-- **The draw leaves the three numbers**, with no premise on the state. -/
theorem numDraw (p : Desc.K9.Where) (u : HTailF2) : NumDraw p u := by
  intro s x t₁ h
  cases ha : Desc.K9.atS.get? s with
  | some a => exact draw_num u p s t₁ x a ha h
  | none =>
    obtain ⟨s₀, hs₀, -⟩ := VerifiableInference.Desc.bind_ok (x := Desc.K9.atS.part s) h
    unfold Desc.K9.Lens.part Desc.K9.there at hs₀
    rw [ha] at hs₀
    exact nomatch hs₀

section
variable {α : Type} {sub : First.ModelPart} {l : ℕ} {Lk : Link S Claim} {p : Desc.K9.Where} {φ : S → α}
  {Ok : α × Option K9L.Pub9 → Prop} {nU : Array ℕ} {u : HTailF2}
  {π : α → Option HTailF2 × Option (Array HFun)}
  {tmOf : ℕ × String → ℕ → α × Option K9L.Pub9 → K9L.Bound Cb.Gl.E → List (ℕ × Cb.Gl.E)}
  {lenOf : ℕ × String → α × Option K9L.Pub9 → ℕ}
  {V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Claim V W X Pb) (b : Nat)

/-- **The counts but the first, from the gathered laws and the seat.** -/
theorem counts_front_seal (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf)
    (w : Desc.K9.SegSort × Nat × Desc.K9.TWhere) (pW : K8.ParW) (hK : K8At Lk w.1 pW)
    (hF : w.1 = .head → FoldOnce Lk p T b) : CountsFront Lk p T b w :=
  counts_front Lk p T b u w pW A.numRun (numDraw p u) hK hF

/-- The same, with the seat's facts in the place of `K8At`. -/
theorem counts_front_alone (A : SealLaw sub l Lk p φ Ok nU u π tmOf lenOf)
    (w : Desc.K9.SegSort × Nat × Desc.K9.TWhere) (pW : K8.ParW) {blk : Block S Claim}
    {name : String} {a : Place} (ho : k8Entry w.1 ∈ Lk.order)
    (hb : Lk.hear[(k8Entry w.1).1]? = some blk)
    (la : IM.LaidAlone ProofFile.sameReply blk (K8.whole pW) name a)
    (hF : w.1 = .head → FoldOnce Lk p T b) : CountsFront Lk p T b w :=
  counts_front_seal T b A w pW (k8At_of_alone ho hb la) hF

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.numDraw
#print axioms ProofFile.Honest.K8.counts_front_seal
#print axioms ProofFile.Honest.K8.counts_front_alone
