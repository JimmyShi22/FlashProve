-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/Numbers.lean: THE NUMBERS OF THE MEMBERS OF THE PROOF FILE's OWN FIRST CHAIN,
AS NUMERALS. The laws on that chain's members spell the list in two ways and a member's number in
several (by a link's number of hearing sub-protocols; by a search in the table of places; by a
kind's own index). Here each spelling is brought to 14 l + ‹a numeral›, and to a numeral at the
head's link, so that the laws can be read at one table's own numbers and "no member is counted
twice" can be read off the statements. Small laws; the search in the table of places is run by
Lean's kernel at 25 links.

  `first_is`: (F0T o Zp Np cF).first = cF: the two spellings of the list are one. No premise.
  `flat_len`: UNDER THE HEAD (P5J.AtMgA, Johnson/P5J/MgAtAll.lean): cF.blocksInOrder has 358 members.
  `hear_at`: under the head, l < 25: the link's number of hearing sub-protocols is 9 at l = 24, else
    7.
  `batch_no` (m < 25): batchAt fullLinks P5J.At.ps m = 14 m + 9, and 347 at m = 24.
  `close_no`: LPFK10.ixK10 l = 14 l + 12, and 350 at l = 24.
  `k1_no`, `k3_no`, `k8_no`: IM.k1Ix l digits, IM.k3Ix l digits, k8No (subAt l) as numerals.
  **`numbers_at`**: under the head, at a link l < 24 and its L: six spellings, each as 14 l +
    ‹numeral›: the batching 9 · behind the batching 10 · the one equation 11 · the closing 12 · shut
    13 · cleared 14. **`numbers_head`**: at l = 24: these six as 347 … 352, and 14 · 24 + 1 = 337
    ("laid": closed arithmetic).

Limits. Numbers alone. close_no, k1_no, k3_no and k8_no hold at every l, beyond 24 too, where no
link stands. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.BehindAtHead
import Johnson.IMR.EndFive
import Johnson.IMR.FrameSeat
import Johnson.IMR.K1Scope
import Johnson.IMR.K3Seat
import Johnson.LPFK10R.SitsAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.LinkJoin (batchAt)
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T fullLinks)

/-! ## 1 No premise -/

theorem first_is (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) :
    (F0T o Zp Np cF).first = cF := rfl

theorem batch_no :
    ∀ m < 25, batchAt fullLinks P5J.At.ps m = if m = 24 then 347 else 14 * m + 9 := by
  decide +kernel

theorem close_no (l : Nat) : LPFK10.ixK10 l = if l = 24 then 350 else 14 * l + 12 := by
  unfold LPFK10.ixK10
  rw [IM.hear_len_at]
  split
  · rename_i h
    rw [h]
  · rfl

theorem k1_no (l : Nat) (digits : Bool) :
    IM.k1Ix l digits = if l = 24 then (if digits then 6 else 4) else (if digits then 5 else 3) := by
  unfold IM.k1Ix
  by_cases h : l = 24 <;> cases digits <;> simp [h]

theorem k3_no (l : Nat) (digits : Bool) :
    IM.k3Ix l digits = if l = 24 then (if digits then 7 else 2) else (if digits then 6 else 1) := by
  unfold IM.k3Ix
  by_cases h : l = 24 <;> cases digits <;> simp [h]

theorem k8_no (l : Nat) : k8No (subAt l) = if l = 24 then 5 else 4 := by
  unfold subAt
  split
  · rfl
  · split <;> rfl

/-! ## 2 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem flat_len (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : cF.blocksInOrder.length = 358 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.flat_358 h.scope O

theorem hear_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 25)
    {L : Link S ProofFile.Cl} (hL : cF.links[l]? = some L) :
    L.hear.length = if l = 24 then 9 else 7 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, fs, -, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨Lk, f, -, -, -, eL, hn, -⟩ := hall l hl
  obtain rfl : Lk = L := Option.some.inj (eL.symm.trans hL)
  exact hn

/-- **The spellings at a link in front of the head's.** -/
theorem numbers_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {l : Nat} (hl : l < 24)
    {L : Link S ProofFile.Cl} (hL : cF.links[l]? = some L) :
    14 * l + L.hear.length + 2 = 14 * l + 9 ∧
      batchAt fullLinks P5J.At.ps l + 1 = 14 * l + 10 ∧
      14 * l + L.hear.length + 4 + 0 = 14 * l + 11 ∧
      LPFK10.ixK10 l = 14 * l + 12 ∧
      14 * l + L.hear.length + 4 + 2 = 14 * l + 13 ∧
      14 * l + L.hear.length + 7 = 14 * l + 14 := by
  have e := hear_at h (by omega : l < 25) hL
  rw [if_neg (by omega)] at e
  have b := batch_no l (by omega)
  rw [if_neg (by omega)] at b
  have c := close_no l
  rw [if_neg (by omega)] at c
  rw [e, b, c]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The spellings at the head's link.** -/
theorem numbers_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : Link S ProofFile.Cl}
    (hL : cF.links[24]? = some L) :
    14 * 24 + 1 = 337 ∧ 14 * 24 + L.hear.length + 2 = 347 ∧
      batchAt fullLinks P5J.At.ps 24 + 1 = 348 ∧
      14 * 24 + L.hear.length + 4 + 0 = 349 ∧
      LPFK10.ixK10 24 = 350 ∧
      14 * 24 + L.hear.length + 4 + 2 = 351 ∧
      14 * 24 + L.hear.length + 7 = 352 := by
  have e := hear_at h (by omega : 24 < 25) hL
  rw [if_pos rfl] at e
  have b := batch_no 24 (by omega)
  rw [if_pos rfl] at b
  have c := close_no 24
  rw [if_pos rfl] at c
  rw [e, b, c]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.first_is
#print axioms Johnson.AtFull.Shape.batch_no
#print axioms Johnson.AtFull.Shape.close_no
#print axioms Johnson.AtFull.Shape.k1_no
#print axioms Johnson.AtFull.Shape.k3_no
#print axioms Johnson.AtFull.Shape.k8_no
#print axioms Johnson.AtFull.Shape.flat_len
#print axioms Johnson.AtFull.Shape.hear_at
#print axioms Johnson.AtFull.Shape.numbers_at
#print axioms Johnson.AtFull.Shape.numbers_head
