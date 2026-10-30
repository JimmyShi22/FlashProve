-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/OwnSitsBools.lean: no soundness is claimed.
ownSitsB at the first chain's last reached state (OwnSitsLast.lean), with its premise on the state behind W's sending (BehindM4) brought down to two fields of FoldFacts (Johnson/Desc/First/FoldFacts.lean: seatsCarried · msgShapes: tests with code, Johnson/Desc/K12/Door/), one count, and five tests on the plan.
  PlanSits L M V idx nW   the five tests on the plan: idx < nW · the listed seats at idx | nW are V.index | V.w · the listed shapes there are V.indexShape | V.wShape · planSitsB · planSits_iff
  **behindM4_of_bools**   on one state: seatsCarriedB L s.book · msgShapesB M s.st · «W's number is nW» · nW lies in the book and in the statement · PlanSits ⇒ BehindM4 V idx s
  **ownSitsB_last_bools** in the goals' scope, general in the family Rc (HandsBack c.blocksInOrder Rc): Rc 358 (z, s) ⇒ ownSitsB V s = true, under: hsp · hRow (at 356: one row on the table, on the message idx alone, with a mask entry) · hCount (at 356: the statement holds nW messages) · hTwo (at 357: the two tests accept, the statement holds more than nW messages, and the book has as many places as the statement has messages) · PlanSits.
    «W's number is nW» is w_fresh_atM4 with hCount.
Left, by name. hsp: left to kind K13's files · hRow: FoldFacts' oneRow | pileMasks at 356 · hCount | hTwo: FoldFacts' seatsCarried | msgShapes at 357 and the counts along the fold (seats_at_cut, Johnson/IMR/SendsFold.lean) · PlanSits: a test with code on the public parameters: not evaluated here.
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.OwnSitsLast
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.K12.Door.MsgShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Last (OwnSeats ownSitsB w_fresh_atM4)
open VerifiableInference.Desc.K13.Law (OnLedger linAt)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB place_of_seats msgShapesB msgShape_at)

/-- **The five tests on the plan.** -/
structure PlanSits (L : Laid) (M : List OracleShape) (V : OwnSeats) (idx nW : ℕ) : Prop where
  elder : idx < nW
  seatI : L.places[idx]? = some V.index
  seatW : L.places[nW]? = some V.w
  shapeI : M[idx]? = some V.indexShape
  shapeW : M[nW]? = some V.wShape

/-- The same as a test with code. -/
def planSitsB (L : Laid) (M : List OracleShape) (V : OwnSeats) (idx nW : ℕ) : Bool :=
  decide (idx < nW) && decide (L.places[idx]? = some V.index) &&
    decide (L.places[nW]? = some V.w) && decide (M[idx]? = some V.indexShape) &&
    decide (M[nW]? = some V.wShape)

theorem planSits_iff (L : Laid) (M : List OracleShape) (V : OwnSeats) (idx nW : ℕ) :
    planSitsB L M V idx nW = true ↔ PlanSits L M V idx nW := by
  unfold planSitsB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩,
    fun h => ⟨⟨⟨⟨h.elder, h.seatI⟩, h.seatW⟩, h.shapeI⟩, h.shapeW⟩⟩

/-- **On one state.** -/
theorem behindM4_of_bools {L : Laid} {M : List OracleShape} {V : OwnSeats} {idx nW : ℕ} {s : S}
    (hS : seatsCarriedB L s.book = true) (hM : msgShapesB M s.st = true)
    (hw : ∀ l, linAt s = some l → l.w = nW) (bW : nW < s.book.place.size)
    (oW : nW < s.st.oracles.size) (T : PlanSits L M V idx nW) : BehindM4 V idx s where
  pI := by rw [place_of_seats hS idx (Nat.lt_trans T.elder bW)]; exact T.seatI
  pW := fun l hl => by rw [hw l hl, place_of_seats hS nW bW]; exact T.seatW
  sI := by rw [msgShape_at hM idx (Nat.lt_trans T.elder oW)]; exact T.shapeI
  sW := fun l hl => by rw [hw l hl, msgShape_at hM nW oW]; exact T.shapeW

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the first chain's last reached state, from two of FoldFacts' tests, one count and the
tests on the plan.** -/
theorem ownSitsB_last_bools (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Pp : Type}
    {Rc : ℕ → Pp × S → Prop} (hb : HandsBack c.blocksInOrder Rc) {z : Pp} {s : S} (h : Rc 358 (z, s))
    (hsp : (K13.whereOf Z).lin.ownSplitNeeded = false) {L : Laid} {M : List OracleShape}
    {V : OwnSeats} {idx nW : ℕ} (T : PlanSits L M V idx nW)
    (hRow : ∀ s₁, Rc 356 (z, s₁) → ∃ r, s₁.rows = [r] ∧ OnLedger idx r ∧ r.masks ≠ [])
    (hCount : ∀ s₁, Rc 356 (z, s₁) → s₁.st.oracles.size = nW)
    (hTwo : ∀ s₂, Rc 357 (z, s₂) → seatsCarriedB L s₂.book = true ∧
      msgShapesB M s₂.st = true ∧ nW < s₂.st.oracles.size ∧
      s₂.book.place.size = s₂.st.oracles.size) :
    ownSitsB V s = true := by
  obtain ⟨s₂, b₂, f2, R2, c2, m2, r2, hb2, y2⟩ := hb 357 z s h
  obtain ⟨s₁, b₁, f1, R1, c1, m1, r1, hb1, y1⟩ := hb 356 z s₂ r2
  obtain ⟨w, hw, ⟨rs', gs, hd⟩, -, -⟩ := IM.at_356 hS hR O hb1 y1
  obtain rfl : s = s₂ := IM.at_357 hS hR O hb2 y2
  obtain ⟨msg, -, rfl⟩ := (K13.Law.wAt_is _ _ _ w).1 hw
  obtain ⟨q₁, q₂, hd2⟩ := atM4_two hd
  obtain ⟨k1, k2, k3, k4⟩ := hTwo _ r2
  have hc := hCount _ r1
  refine ownSitsB_atM4 hd hsp ⟨hRow _ r1, by rw [hc]; exact T.elder⟩
    (behindM4_of_bools k1 k2 (fun l hl => (w_fresh_atM4 hd2 l hl).trans hc) (by rw [k4]; exact k3)
      k3 T)

end

end ToldDesc

#print axioms ToldDesc.planSits_iff
#print axioms ToldDesc.behindM4_of_bools
#print axioms ToldDesc.ownSitsB_last_bools
