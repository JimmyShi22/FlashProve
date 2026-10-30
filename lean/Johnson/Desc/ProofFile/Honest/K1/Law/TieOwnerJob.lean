-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieOwnerJob.lean: K1's SHARE OF OwnerHolds (TieMatOwners.lean): at a message of
a job of the shared sending, under the record K1Seated, where the job's data answers the packed cells at the laid places.

  ownerHolds_job       the general law
  ownerHolds_opening   at the first segment's opening, by first_val


NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatOwners
import Johnson.Desc.ProofFile.Honest.K1.Law.FirstIsPacked
import Johnson.Desc.ProofFile.Honest.K1.Law.TieMatFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem)
open OnBytes.HonestTrace (Sz packedCells)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (shapeAt Rows)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Tr' X P Cells' Tok : Type}
  {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {own₀ : X} {sort : K1Sort}
  {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- OwnerHolds at a shorter list of challenges holds at a longer one. -/
theorem OwnerHolds.mono {L : Letters Bk Cl W₀ Rc ProofFile.Inst Tr' X P Cells' Tok MsgT}
    {wit : Local W₀ Rc ProofFile.Inst Tr' → PlaceIn ProofFile.Inst} {Sz₀ : Sz} {n N₁ N₂ l₀ ν₀ : ℕ} {a : ReqArray}
    (h : N₁ ≤ N₂) (H : OwnerHolds L wit Sz₀ n N₁ l₀ ν₀ a) : OwnerHolds L wit Sz₀ n N₂ l₀ ν₀ a :=
  fun k w hd hv hN => H k w hd hv (Nat.le_trans h hN)

/-- **OwnerHolds at a message of a job.** hVal: at the laid places the job's data answers the packed
cells, at what had been heard. hRoom: they lie in the message's main rows, off the pad. -/
theorem ownerHolds_job {J : SendJob (PlaceIn ProofFile.Inst) X}
    (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) (Sz₀ : Sz) {n l₀ ν₀ : ℕ} {a : ReqArray}
    (hn : n < J.P.sent.size) (hans : (shapeAt J.P n).answers ≠ 0)
    (hVal : ∀ w (hd : List Fmt.Drawn) i c rp, laidAt a i c = some rp →
      c < (Sz₀.packedShape l₀ ν₀).2 → i < (Sz₀.packedShape l₀ ν₀).1 →
      J.data (wit w) { heard := hd, own := own₀, seen := .bare [] } n rp.1 rp.2 =
        some (.inl (packedCells Sz₀ (wit w).R.cells.cell l₀ ν₀ i c)))
    (hRoom : ∀ i c rp, laidAt a i c = some rp → c < (Sz₀.packedShape l₀ ν₀).2 →
      i < (Sz₀.packedShape l₀ ν₀).1 → rp.1 < (shapeAt J.P n).mainRows ∧
      rp.2 < (J.P.codes.base.getD (shapeAt J.P n).code default).ell ∧
      (rp.1, rp.2) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell (shapeAt J.P n)) :
    OwnerHolds L wit Sz₀ (arr (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2)
      (L.thread.front + roundsTo L.bs b) l₀ ν₀ a := by
  intro k w hd hv hN i c rp hrp hc hi
  obtain ⟨hr, hj, hp⟩ := hRoom i c rp hrp hc hi
  obtain ⟨cut, hcut⟩ := R.cut k
  have e := R.msgs n hn k w hd hv hN false rp.1 rp.2 _
    (msgTxt_some 0 wit J own₀ n k cut hcut w (hd.take (L.thread.front + roundsTo L.bs b)) false rp.1 rp.2)
  have hv' := hVal w (hd.take (L.thread.front + roundsTo L.bs b)) i c rp hrp hc hi
  show L.Q.msg _ k w (hd.take (L.Q.fixedMsg _)) false rp.1 rp.2 = _
  rw [e]
  show Rows.main (rowsLaid J own₀ cut (wit w) (hd.take (L.thread.front + roundsTo L.bs b)) n)
    ((shapeAt J.P n).mainDeg == 3) rp.1 rp.2 = _
  unfold Rows.main rowsLaid
  by_cases h3 : ((shapeAt J.P n).mainDeg == 3) = true
  · rw [if_pos h3, main_data_e J.P J.ride _ cut n rp.1 rp.2 h3 hr hj hans hp, hv']
  · have h3' : ((shapeAt J.P n).mainDeg == 3) = false := by simpa using h3
    rw [if_neg h3, main_data_f J.P J.ride _ cut n rp.1 rp.2 h3' hr hj hans hp, hv']

/-- **OwnerHolds at the first segment's opening.** -/
theorem ownerHolds_opening {Sz₀ : Sz} {Z : Pub} {G : Ground} {gp : _root_.Desc.Plain.GPar} {first : ℕ}
    (R₀ : K1Seated L b blk wit
      (placeJob (K1.firstPar G.first gp) first (firstFold G.first) (lotData Sz₀ Z G)) own₀ sort arr
      seats₀ ms rad) {n ν : ℕ} {a : ReqArray}
    (hn : n < (K1.firstPar G.first gp).sent.size) (hans : (shapeAt (K1.firstPar G.first gp) n).answers ≠ 0)
    (t1 : firstSeat G.first.shape 0 ⟨firstAddr, n⟩ = some (0, a.message))
    (hfit : msgFits G.first.codes G.first.shape G.first.layout 0 a.message = true)
    (ha : a ∈ (G.first.layout.link.getD 0 []).filter fun y => y.message == a.message)
    (hmu : labelNo a.name = some ν) (hz : (cellsVals Sz₀).size 0 a.name = some (Sz₀.packedShape 0 ν))
    (hRoom : ∀ i c rp, laidAt a i c = some rp → c < (Sz₀.packedShape 0 ν).2 →
      i < (Sz₀.packedShape 0 ν).1 → rp.1 < (shapeAt (K1.firstPar G.first gp) n).mainRows ∧
      rp.2 < ((K1.firstPar G.first gp).codes.base.getD (shapeAt (K1.firstPar G.first gp) n).code default).ell ∧
      (rp.1, rp.2) ∉ padInMain ((K1.firstPar G.first gp).codes.base.getD
        (shapeAt (K1.firstPar G.first gp) n).code default).ell (shapeAt (K1.firstPar G.first gp) n)) :
    OwnerHolds L wit Sz₀
      (arr (seatAtMember L.bs b (K1.firstPar G.first gp) n).1 (seatAtMember L.bs b (K1.firstPar G.first gp) n).2)
      (L.thread.front + roundsTo L.bs b) 0 ν a :=
  ownerHolds_job R₀ Sz₀ hn hans
    (fun w hd _ _ _ hrp hc hi => first_val Sz₀ Z G (wit w).x (wit w).R hd t1 hfit ha hrp hmu hz ⟨hi, hc⟩)
    hRoom

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.ownerHolds_job
#print axioms ProofFile.Honest.K1.ownerHolds_opening
