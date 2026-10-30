-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/JoinCoef.lean: THE SMALLNESS TEST: WHAT THE CLAIM ON THE LOOKUP's KEY VECTORS
(the first of the list "K8.equations") BEARS ON EACH ENTRY OF A PIECE's VIRTUAL ROW OF THE DIGITS'
ARRAY: INSIDE THE PIECE's COLUMNS ONE TERM; OUTSIDE NOTHING. Definitions and lemmas; none of the
library's goals. On claims and plain data: no ledger, no block, no prover; nothing on completeness,
soundness or hiding. BY VALUES.

  `joinClaim tl g`, `joinTerm tl g x i`, `joinTerm_in`   the claim (K9L.four8's first: `four8_zero`,
      Johnson/Desc/K8/Honest/DigitsLiveOf.lean); what piece x's run lays on column i of its virtual
      row; the same at column number cc of the piece
  `join_coef_sum`   the claim's coefficient on an entry (`coefOn`,
      Johnson/Desc/K8/Honest/FallCount.lean) is the sum of the terms of the pieces that cover it,
      WHERE THE FORM THAT THE LOOKUP HAS HEARD NAMES NO ENTRY
  `pair_key`, `key_of_row`   under `piecesLaid` (Johnson/Desc/K8/Honest/PiecesLaid.lean): each
      piece's array, virtual row, first column and number of columns; two pieces with one virtual
      row have the same columns
  **`join_coef_in`**, **`join_coef_out`**   the sentences of the title. THE STEPS OF THE FIRST ARE
      THOSE INSIDE THE PROOF OF `live_one` (DigitsLiveOf.lean), which ends in "not 0" and states no
      value
By: `coefOn_eq` (Johnson/Desc/K8/Honest/CoefCode.lean) · `entsE_none` (PlanesLiveOf.lean) ·
`runsE_sum`, `joinRuns_eq`, `addMul_ents`, `pair_lt` (DigitsLiveOf.lean) · `no_ent` (GoodOf.lean) ·
`pair_mem` (PublicOfPieces.lean) · `cover_of_laid` (PiecesLaid.lean). The library's laws on these
runs (Fo.joinRun_value, OnBytes/Tie/Pv/Lookup/Ends/FoTailJoinVal.lean; Fo.kf_piece, Fo.kf_ext,
FoTailKf.lean) go by sums in a world, not entry by entry.
Limits. Nothing on any weight of a ledger. What the lookup has heard, and `piecesLaid`, are
premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.NamesOff

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-- The claim on the lookup's key vectors: the first of the list "K8.equations". -/
def joinClaim (tl : HTailF2) (g : Forest.Heard) : Claim :=
  { form := Aff.ofConst (Fo.joinConst tl g) - g.cEnd, runs := (Fo.joinRuns tl g).toArray }

/-- What piece x's run lays on column i of its virtual row, by value. -/
def joinTerm (tl : HTailF2) (g : Forest.Heard) (x : Nat × OnBytes.Model.Piece) (i : Nat) :
    Cb.Gl.E :=
  -(Reading.gl.val (g.e.getD x.1 zeroE) *
      Reading.gl.val (eqOne ((g.zk.getD x.1 #[]).extract 0 ((tl.zOf x.1).call.n - x.2.b))
        (x.2.off / 2 ^ x.2.b))) *
    Reading.gl.val ((eqTab (Fo.joinZc tl g x.1 x.2)).getD (i - x.2.c0) zeroE)

/-- The term at column number cc of the piece. -/
theorem joinTerm_in (tl : HTailF2) (g : Forest.Heard) (x : Nat × OnBytes.Model.Piece) (cc : Nat) :
    joinTerm tl g x (x.2.c0 + cc) =
      -(Reading.gl.val (g.e.getD x.1 zeroE) *
          Reading.gl.val (eqOne ((g.zk.getD x.1 #[]).extract 0 ((tl.zOf x.1).call.n - x.2.b))
            (x.2.off / 2 ^ x.2.b))) *
        Reading.gl.val ((eqTab (Fo.joinZc tl g x.1 x.2)).getD cc zeroE) := by
  unfold joinTerm
  rw [Nat.add_sub_cancel_left]

/-- **What the claim bears on an entry**: the sum over the pieces that cover it: where the form
that the lookup has heard names no entry. -/
theorem join_coef_sum (tl : HTailF2) (g : Forest.Heard) (hc : g.cEnd.ents.isEmpty = true)
    (t r i : Nat) :
    coefOn (joinClaim tl g) t r i =
      (((joinPairs tl).filter fun x => pieceCovers x.2 t r i).map
        fun x => joinTerm tl g x i).sum := by
  rw [coefOn_eq]
  unfold coefE joinClaim
  have he : entsE (Aff.ofConst (Fo.joinConst tl g) - g.cEnd).ents.toList t r i = zeroE :=
    entsE_none _ _ _ _ fun x hx _ => by
      rcases addMul_ents _ _ _ x hx with h1 | ⟨y, hy, -, -, -⟩
      · simp [Aff.ofConst] at h1
      · exact absurd hy (no_ent _ hc y)
  rw [Reading.gl.add]
  show Reading.gl.val (entsE (Aff.ofConst (Fo.joinConst tl g) - g.cEnd).ents.toList t r i) +
      Reading.gl.val (runsE (Fo.joinRuns tl g).toArray.toList t r i) = _
  rw [he, Reading.gl.zero, zero_add, List.toList_toArray, runsE_sum, joinRuns_eq,
    List.filter_map, List.map_map]
  have hf : ((joinPairs tl).filter
      ((fun R => covers R t r i) ∘ fun x => Fo.joinRun tl g x.1 x.2)) =
      (joinPairs tl).filter fun x => pieceCovers x.2 t r i := rfl
  rw [hf]
  refine congrArg List.sum (List.map_congr_left fun x _ => ?_)
  show Reading.gl.val (subE zeroE (mulE (g.e.getD x.1 zeroE)
      (eqOne ((g.zk.getD x.1 #[]).extract 0 ((tl.zOf x.1).call.n - x.2.b))
        (x.2.off / 2 ^ x.2.b)))) *
    Reading.gl.val ((eqTab (Fo.joinZc tl g x.1 x.2)).getD (0 + (i - x.2.c0)) zeroE) = _
  unfold joinTerm
  rw [Reading.gl.sub, Reading.gl.zero, Reading.gl.mul, Nat.zero_add, zero_sub]

/-- Where the two calls' pieces lie as the plan lays them: each piece's key. -/
theorem pair_key (tl : HTailF2) (hL : piecesLaid tl = true) (x : Nat × OnBytes.Model.Piece)
    (hx : x ∈ joinPairs tl) : ∃ j, j < tl.zzBlocks ∧
      pieceKey x.2 = (tl.ix.ZZ, x.1 * tl.zzBlocks + j, x.1 * tl.mz, tl.mz) := by
  unfold piecesLaid at hL
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hL
  have hq := pair_lt tl x hx
  have hp := pair_mem tl x hx
  have h01 : x.1 = 0 ∨ x.1 = 1 := by omega
  rcases h01 with e | e
  · rw [e] at hp
    have hm : pieceKey x.2 ∈ tl.z1.pieces.toList.map pieceKey := List.mem_map_of_mem hp
    rw [hL.1] at hm
    obtain ⟨j, hj, ej⟩ := List.mem_map.1 hm
    exact ⟨j, List.mem_range.1 hj, by rw [← ej, e, Nat.zero_mul, Nat.zero_mul, Nat.zero_add]⟩
  · rw [e] at hp
    have hm : pieceKey x.2 ∈ tl.z2.pieces.toList.map pieceKey := List.mem_map_of_mem hp
    rw [hL.2] at hm
    obtain ⟨j, hj, ej⟩ := List.mem_map.1 hm
    exact ⟨j, List.mem_range.1 hj, by rw [← ej, e, Nat.one_mul, Nat.one_mul]⟩

/-- Two pieces with one virtual row have one key. -/
theorem key_of_row (tl : HTailF2) (hL : piecesLaid tl = true) (x y : Nat × OnBytes.Model.Piece)
    (hx : x ∈ joinPairs tl) (hy : y ∈ joinPairs tl) (h : y.2.row = x.2.row) :
    y.2.c0 = x.2.c0 ∧ y.2.Cp = x.2.Cp := by
  obtain ⟨j, hj, ej⟩ := pair_key tl hL x hx
  obtain ⟨k, hk, ek⟩ := pair_key tl hL y hy
  have qx := pair_lt tl x hx
  have qy := pair_lt tl y hy
  unfold pieceKey at ej ek
  simp only [Prod.mk.injEq] at ej ek
  have hq : y.1 = x.1 := by
    have h1 : y.1 * tl.zzBlocks + k = x.1 * tl.zzBlocks + j := by rw [← ek.2.1, ← ej.2.1, h]
    have hx01 : x.1 = 0 ∨ x.1 = 1 := by omega
    have hy01 : y.1 = 0 ∨ y.1 = 1 := by omega
    rcases hx01 with a | a <;> rcases hy01 with b | b <;> rw [a, b] at h1 <;> omega
  exact ⟨by rw [ek.2.2.1, ej.2.2.1, hq], by rw [ek.2.2.2, ej.2.2.2]⟩

/-- **Inside a piece's columns: one term.** -/
theorem join_coef_in (tl : HTailF2) (g : Forest.Heard) (hc : g.cEnd.ents.isEmpty = true)
    (hL : piecesLaid tl = true) (x : Nat × OnBytes.Model.Piece) (hx : x ∈ joinPairs tl) (cc : Nat)
    (hcc : cc < x.2.Cp) :
    coefOn (joinClaim tl g) tl.ix.ZZ x.2.row (x.2.c0 + cc) = joinTerm tl g x (x.2.c0 + cc) := by
  obtain ⟨j, hj, ej⟩ := pair_key tl hL x hx
  have qx := pair_lt tl x hx
  unfold pieceKey at ej
  simp only [Prod.mk.injEq] at ej
  have hcov : pieceCovers x.2 tl.ix.ZZ x.2.row (x.2.c0 + cc) = true :=
    decide_eq_true ⟨ej.1, rfl, Nat.le_add_right _ _, by omega⟩
  have hone : oneCover tl tl.ix.ZZ x.2.row (x.2.c0 + cc) = true := by
    have hD := cover_of_laid tl hL
    unfold digitsCover at hD
    simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true] at hD
    have hu : cc < tl.mz := by rw [← ej.2.2.2]; exact hcc
    have h01 : x.1 = 0 ∨ x.1 = 1 := by omega
    rcases h01 with a | a
    · rw [ej.2.1, ej.2.2.1, a, Nat.zero_mul, Nat.zero_mul, Nat.zero_add, Nat.zero_add]
      exact (hD j hj cc hu).1
    · rw [ej.2.1, ej.2.2.1, a, Nat.one_mul, Nat.one_mul]
      exact (hD j hj cc hu).2
  rw [join_coef_sum tl g hc]
  unfold oneCover at hone
  obtain ⟨y, hy⟩ := List.length_eq_one_iff.1 (beq_iff_eq.1 hone)
  have hm : x ∈ (joinPairs tl).filter fun x' => pieceCovers x'.2 tl.ix.ZZ x.2.row (x.2.c0 + cc) :=
    List.mem_filter.2 ⟨hx, hcov⟩
  rw [hy] at hm ⊢
  obtain rfl : x = y := List.mem_singleton.1 hm
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]

/-- **Outside a piece's columns, in its virtual row: nothing.** -/
theorem join_coef_out (tl : HTailF2) (g : Forest.Heard) (hc : g.cEnd.ents.isEmpty = true)
    (hL : piecesLaid tl = true) (x : Nat × OnBytes.Model.Piece) (hx : x ∈ joinPairs tl) (i : Nat)
    (hi : ¬ (x.2.c0 ≤ i ∧ i < x.2.c0 + x.2.Cp)) :
    coefOn (joinClaim tl g) tl.ix.ZZ x.2.row i = 0 := by
  rw [join_coef_sum tl g hc]
  have he : ((joinPairs tl).filter fun y => pieceCovers y.2 tl.ix.ZZ x.2.row i) = [] := by
    refine List.filter_eq_nil_iff.2 fun y hy hcov => hi ?_
    have k : y.2.tree = tl.ix.ZZ ∧ y.2.row = x.2.row ∧ y.2.c0 ≤ i ∧ i < y.2.c0 + y.2.Cp :=
      of_decide_eq_true hcov
    obtain ⟨e1, e2⟩ := key_of_row tl hL x y hx hy k.2.1
    rw [← e1, ← e2]
    exact k.2.2
  rw [he]
  rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.joinTerm_in
#print axioms VerifiableInference.Desc.First.K8.Honest.join_coef_sum
#print axioms VerifiableInference.Desc.First.K8.Honest.pair_key
#print axioms VerifiableInference.Desc.First.K8.Honest.key_of_row
#print axioms VerifiableInference.Desc.First.K8.Honest.join_coef_in
#print axioms VerifiableInference.Desc.First.K8.Honest.join_coef_out
