-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CellsAtBatch.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN
BLOCKS REACH IN FRONT OF A SEGMENT's BATCHING, AT ALL 25 SEGMENTS: EACH MATRIX's NUMBER OF ROWS OF
CELLS IS SMALL: (m + 2) / 3 ≤ 2 ^ 64: THE SECOND FIELD OF `TieFront`
(Johnson/Desc/K8/Honest/TieWords.lean); SO, WITH `drawn_at_batch` (Johnson/P1K8R/DrawAtBatch.lean),
`TieFront` WHOLE. UNDER THE SCOPE, THE FILES READ AND IM.Open. Lemmas; none of the library's goals.
No prover stands in them; nothing on completeness, soundness or hiding. Why. A piece of the lookup
on the digits is mz columns wide; its keys lie among the call's, whose numbers have 63 bits at most;
and a matrix's rows of cells are columns of the digits' array's low half.

  **`mz_le_of_tests`**   on plain data, from Fo.ZTests
      (OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsRun.lean) and "there is a combination": mz ≤ 2 ^ 63:
      DgP.TailOK's rows (there is a piece) and pc (it is mz wide; its width times its rows is 2 ^ b)
      (OnBytes/Tie/Pv/Lookup/Digits/PortLaws.lean); Fo.PieceOK's bn (b ≤ n) (Ends/FoTailKf.lean); t8
      (n ≤ 63)
  `cells_of_cols`   a matrix ends at or before mz: DgP.dgP_col_le (Digits/PortCols.lean)
  **`cells_at_batch`**   `tests_at_built` (Johnson/P1K8R/StaticAtBuilt.lean) and IM.k8_tau_128
      (Johnson/K8Q14R/TauAt.lean) at the built segment; `apart_at_batch` (ApartAtBatch.lean) at the
      state; mz crosses by LinkJoin.planned_at_batch at `piecesView` (PublicAtBatch.lean)
  **`tieFront_at_batch`**   `TieFront tl`, all four fields
Limits. The bound is far from sharp. Nothing on whether any state is reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.DrawAtBatch
import Johnson.P1K8R.StaticAtBuilt
import Johnson.P1K8R.PublicAtBatch
import Johnson.P1K8R.ApartAtBatch
import Johnson.Desc.First.Link.Law.OkAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **The digits' array's low half has 2 ^ 63 columns at most.** -/
theorem mz_le_of_tests {t : HTailF2} {Fc : Fork} (T : Fo.ZTests t t Fc) (h : 0 < t.tau) :
    t.mz ≤ 2 ^ 63 := by
  have K := DgP.tailOK_of_test T.t1
  have h0 : 0 < t.f9.NC := by
    rw [K.nc]
    norm_num
  have hs := K.rows 0 h0 0 h
  unfold DgP.pieceAt at hs
  rw [List.find?_isSome] at hs
  obtain ⟨p, hp, -⟩ := hs
  obtain ⟨c1, c2, c3, -, -⟩ := K.pc 0 h0 p hp
  have ok := Fo.pieceOK_of_test (T.t2 0 (by norm_num)) p hp
  have hb : p.b ≤ 63 := le_trans ok.bn (T.t8 0 (by norm_num))
  have hR : 0 < p.Rp := by
    rcases Nat.eq_zero_or_pos p.Rp with e | e
    · rw [e, Nat.mul_zero] at c3
      exact absurd c3 (Nat.ne_of_lt (Nat.two_pow_pos _))
    · exact e
  have hCP : p.CP ≤ 2 ^ p.b := by
    rw [← c3]
    exact Nat.le_mul_of_pos_right _ hR
  rw [← c1]
  exact le_trans c2 (le_trans hCP (Nat.pow_le_pow_right (by norm_num) hb))

/-- So each matrix's number of rows of cells is small. -/
theorem cells_of_cols {tl : HTailF2} (hC : DgP.colsTest tl = true) (hz : tl.mz ≤ 2 ^ 63) :
    ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64 := by
  intro nu hnu
  have e := DgP.dgP_col_le hC (tl.NM - nu - 1) nu (by omega)
  have e' : tl.off.getD nu 0 + (tl.mats.getD nu {}).m ≤ tl.mz := e
  have h63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have h64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  rw [h63] at hz
  rw [h64]
  omega

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING: THE SECOND FIELD OF `TieFront`.** -/
theorem cells_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) :
    ∀ nu, nu < tl.NM → ((tl.mats.getD nu {}).m + 2) / 3 ≤ 2 ^ 64 := by
  have hx : (l, (if l = 24 then 5 else 4), (if l = 24 then 3 else 2)) ∈ P1K8S.stretches :=
    List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩
  have e : 14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2) =
      14 * l + (if l = 24 then 11 else 9) := by
    split_ifs <;> omega
  have h' : Reach 0 c.blocksInOrder (ProofFile.startS Z)
      (14 * l + (if l = 24 then 5 else 4) + 3 + (if l = 24 then 3 else 2)) (z, s) := by
    rw [e]
    exact h
  have v : piecesView tl = piecesView Xl.tl :=
    LinkJoin.of_readTl (LinkJoin.planned_at_batch planned_pieces hS hR O hx e3 (z, s) h') tl ht
  have v5 : tl.mz = Xl.tl.mz := congrArg (·.2.2.2.2.1) v
  have hTX : Xl.tl.tau = 128 := IM.k8_tau_128 hS hR O (by omega) e3
  have hz : Xl.tl.mz ≤ 2 ^ 63 :=
    mz_le_of_tests (tests_at_built hS O hl e3) (by rw [hTX]; norm_num)
  obtain ⟨t3, a3, -, hC⟩ := apart_at_batch hS hR O hl h
  rw [Option.some.inj (a3.symm.trans ht)] at hC
  exact cells_of_cols hC (by rw [v5]; exact hz)

/-- **`TieFront`, WHOLE, AT EVERY STATE REACHED IN FRONT OF A SEGMENT's BATCHING.** -/
theorem tieFront_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s))
    {tl : HTailF2} (ht : s.tl? = some tl) : TieFront tl := by
  obtain ⟨t, a, D, hT⟩ := drawn_at_batch hS hR O hl h
  rw [Option.some.inj (a.symm.trans ht)] at D hT
  exact tieFront_of_drawn hT (cells_at_batch hS hR O hl e3 h ht) D

end

end P1K8

#print axioms P1K8.mz_le_of_tests
#print axioms P1K8.cells_of_cols
#print axioms P1K8.cells_at_batch
#print axioms P1K8.tieFront_at_batch
