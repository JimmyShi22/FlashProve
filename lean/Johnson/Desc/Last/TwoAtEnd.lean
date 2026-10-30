-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/TwoAtEnd.lean: THE TWO TESTS THAT `ownSitsB V` ASKS OF A REACHED STATE (the book's places are the listed
seats; the statement's oracle messages have the listed shapes), ASKED AT THE FIRST CHAIN'S LAST STATE ALONE. Statements with
their proofs.

Why. `ownSitsB_at_promise_count` (Johnson/Desc/Last/CountAtEnd.lean) asks the two tests of EVERY state of the family at
border 357. Their payers hold them at the end. The last sub-protocol leaves the state as it is (`IM.at_357`): so a fact
at border 358 goes back to border 357. THE SAME MOVE AS `ownSitsB_last_end` (not in this library):
here at this file's own letters.

Main names (namespace `VerifiableInference.Desc.Last`).
  `WithAtEnd Q Rc`: a family of reached states, cut at border 358, with a fact Q on the state beside it at borders 357, 358.
  `handsBack_withAtEnd`: in scope: where Rc hands back (`ToldDesc.HandsBack`), so does `WithAtEnd Q Rc`.
  **`ownSitsB_at_promise_end`**: `ownSitsB_at_promise_count` WITH hTwo (every state at 357) TURNED INTO hEnd:
    ∀ z s, Rc 358 (z, s) → s.failed = none → seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true.
  At the foot an example: the first of the two, in hEnd's letters, off `Meaning.K2.five_at_end` (Johnson/IMR/EndFive.lean).

What stays a premise. hI · hII · hsp · `PlanSits` · hNum · hEnd.
Limits. Letters throughout. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.CountAtEnd
import Johnson.IMR.EndFive

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Last
open OnBytes
open VerifiableInference.Desc.First (Item Pub ModelPart Numbers Meaning openSets)
open VerifiableInference.Desc.Sound (ocEnd)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open ToldDesc (HandsBack PlanSits)
open Johnson.Desc.First.Walk.Tied (Reach)

/-- A family of reached states, cut at border 358, with a fact on the state beside it at the last two borders. -/
def WithAtEnd {Pp : Type} (Q : First.S → Prop) (Rc : ℕ → Pp × First.S → Prop) :
    ℕ → Pp × First.S → Prop :=
  fun k q => Rc k q ∧ k ≤ 358 ∧ (357 ≤ k → Q q.2)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A fact at the last border goes back over the seal.** -/
theorem handsBack_withAtEnd (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc) (Q : First.S → Prop) :
    HandsBack c.blocksInOrder (WithAtEnd Q Rc) := by
  intro k z s h
  obtain ⟨h0, hk, h7⟩ := h
  obtain ⟨s₀, b, ft, rs, cols, m, r0, hb0, y0⟩ := hb k z s h0
  refine ⟨s₀, b, ft, rs, cols, m, ⟨r0, by omega, fun h6 => ?_⟩, hb0, y0⟩
  obtain rfl : k = 357 := by omega
  show Q s₀
  rw [← IM.at_357 hS hR O hb0 y0]
  exact h7 (by omega)

/-- **`ownSitsB` inside the first table's last promise, the two tests asked at the last state alone.** -/
theorem ownSitsB_at_promise_end (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {Pp P₀ W : Type} {Rc : ℕ → Pp × First.S → Prop} (hb : HandsBack c.blocksInOrder Rc)
    (g : Pp × First.S → P₀ × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁) (N₁ : Numbers)
    (Mg₁ : Meaning P₀ W) (links : List ModelPart) (ps : List Place) {L : Laid} {M : List OracleShape}
    {V : OwnSeats} {idx nW : ℕ}
    (hI : Item.pinI ∈ (openSets links ps (First.start links))[ps.length]?.getD [])
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC idx x.2)
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits L M V idx nW)
    (hNum : N₁.msgsAt none = nW + wMsgs Z)
    (hEnd : ∀ z s, Rc 358 (z, s) → s.failed = none → seatsCarriedB L s.book = true ∧
      msgShapesB M s.st = true) :
    ∀ q y, ocEnd g N₁ Mg₁ links ps q y → Rc 358 q → (g q).2.failed = none →
      ownSitsB V (g q).2 = true := by
  rintro ⟨z, s⟩ y hoc hr hm
  have hm' : s.failed = none := by
    rw [hg] at hm
    exact hm
  have ht := hEnd z s hr hm'
  exact ownSitsB_at_promise_count hS hR O
    (handsBack_withAtEnd hS hR O hb
      (fun s => seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true))
    g hg N₁ Mg₁ links ps hI hII hsp T hNum (fun _ _ h2 _ => h2.2.2 (Nat.le_refl _)) (z, s) y hoc
    ⟨hr, Nat.le_refl _, fun _ => ht⟩ hm

/-- The first of the two tests, in hEnd's letters at the family that a run makes, off the five facts at the
end (`Meaning.K2.five_at_end`, Johnson/IMR/EndFive.lean). -/
example (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true)
    (D : ∀ z : ProofFile.InstPub, IM.SendDebts 0 Z.first.codes (K12.Door.snAt Z Bs.G₀ IM.placesW) Z Bs.G₀ c
      (ProofFile.startS Z z))
    (hB : K12.Door.sendsAreB Z.made.proof.1 358 (K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    {L : Laid} (hL : K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L) :
    ∀ z s, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 (z, s) → s.failed = none →
      seatsCarriedB L s.book = true := by
  intro z s hr hm
  have hr' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length (z, s) := by
    rw [flat_358 hS hR O]
    exact hr
  exact (Meaning.K2.five_at_end hS O hp D hB hL (z, s) hr' hm).2.2.2.2

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.handsBack_withAtEnd
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_promise_end
