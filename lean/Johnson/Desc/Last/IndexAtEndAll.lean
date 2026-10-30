-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/IndexAtEndAll.lean: TWO PREMISES OF `ownSitsB_at_end`
(Johnson/Desc/Last/IndexAtEnd.lean) MET: at the full size's written list of segments, and at the
composed meaning. Statements with their proofs.

Main names (namespace `VerifiableInference.Desc.Last`).
  `mgAll_indexIs`: the composed meaning's test at the item indexIs is `K13.indexIsC` at the number
    `𝔇.pubD.N.indexNo` (hII, at idx := that number).
  `pinI_open_full`: the item pinI is open at the first chain's last border, at `P5J.fullLinks` and
    its written list of places (hI): `last_pins_full` (Johnson/Desc/Last/ShapeDoorClosed.lean, by
    Lean's kernel), whose list `Sound.linksFull` is that list by unfolding.
  **`ownSitsB_at_end_mgAll`**: `ownSitsB_at_end` at these two, and at the description's term
    `Desc.K14.Law.descZ` with both later seats by name.

What stays a premise. hsp; hCount (border 356); hTwo (border 357); and `PlanSits L M V
𝔇.pubD.N.indexNo nW`: THE FIVE TESTS ON THE PLAN AT THE MEANING'S OWN NUMBER: a closed test once the
letters are filled; evaluated by nobody at that term yet.
Limits. 𝔇, Mg, N₁, V, L, M, nW are letters. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.IndexAtEnd
import Johnson.Desc.Last.ShapeDoorClosed
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.Sound.AtDescPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Flat OnBytes.Maker KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning Numbers Pub Item openSets flatPlacesOf pubAll_indexIs)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open ToldDesc (PlanSits)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- The composed meaning's test at the item "indexIs". -/
theorem mgAll_indexIs (a : P × First.S) :
    (mgAll 𝔇 Mg).pub .indexIs a = K13.indexIsC 𝔇.pubD.N.indexNo a.2 := by
  rw [mgAll_pub, pubAll_indexIs]

/-- The item pinI is open at the first chain's last border, at the full size's written lists. -/
theorem pinI_open_full :
    Item.pinI ∈ (openSets P5J.fullLinks (flatPlacesOf P5J.fullLinks true)
      (First.start P5J.fullLinks))[(flatPlacesOf P5J.fullLinks true).length]?.getD [] :=
  last_pins_full.1

/-- **`ownSitsB` at the first chain's last reached state, inside the first table's last promise, at
the composed meaning and the full size's written lists.** -/
theorem ownSitsB_at_end_mgAll {Pl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : Chain First.S ProofFile.Cl} {Np : H2U.Places4} (hS : VerifierAndGoals.InScope Pl = true)
    (hR : VerifierAndGoals.readFiles Pl = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pl.pol lay Pl.KL F Z Bs base c (_root_.Desc.K14.Law.seatZ Z Np)
      (_root_.Desc.K14.Law.secondAt Z Np))
    (g : ProofFile.InstPub × First.S → P × First.S) (hg : ∀ q s₁, (g (q, s₁)).2 = s₁) (N₁ : Numbers)
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) (T : PlanSits L M V 𝔇.pubD.N.indexNo nW)
    (hCount : ∀ z s₁, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 356 (z, s₁) →
      s₁.failed = none → s₁.st.oracles.size = nW)
    (hTwo : ∀ z s₂, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true ∧
      nW < s₂.st.oracles.size ∧ s₂.book.place.size = s₂.st.oracles.size) :
    ∀ q y, ocEnd g N₁ (mgAll 𝔇 Mg) P5J.fullLinks (flatPlacesOf P5J.fullLinks true) q y →
      EndAt₁ (_root_.Desc.K14.Law.descZ OnBytes.secondHashFunction Z Np (_root_.Desc.K14.Law.secondAt Z Np) c)
        q →
      (g q).2.failed = none → ownSitsB V (g q).2 = true :=
  ownSitsB_at_end hS hR O g hg N₁ (mgAll 𝔇 Mg) P5J.fullLinks (flatPlacesOf P5J.fullLinks true)
    pinI_open_full (mgAll_indexIs 𝔇 Mg) hsp T hCount hTwo

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.mgAll_indexIs
#print axioms VerifiableInference.Desc.Last.pinI_open_full
#print axioms VerifiableInference.Desc.Last.ownSitsB_at_end_mgAll
