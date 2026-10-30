-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LinkedFew.lean: THE SMALLNESS TEST: THE COUNT FOR ITS TEST `selfLinked` ("no
weight on the reads' row or on the ties' row of the digits' array is 0":
Johnson/Desc/First/TailClaims/SelfTests.lean). Definitions with code, statements and proofs. No
prover. Lemmas; none of the library's goals.

ZZ: the digits' array; mz: the rows of cells of all matrices; the test asks the columns 0 .. 2 mz -
1 of both rows. off[mu], m: matrix mu's first row of cells and its number of them.
  `tiesLaid tl`   with code, on public numbers: ZZ is no matrix's array of symbols and not what a
      read's vector's array reads as; each matrix has rows of cells, as many as its shape says,
      within mz; the matrices' stretches [off, off + m) lie apart and cover 0 .. mz - 1
  **`readsLive tl`**   with code, ON THE CLOSED LIST OF TABLES, whose weights are made of challenges
      drawn in front: FOR EACH COLUMN x < 2 mz SOME READ OF THE LIST HAS A WEIGHT AT x THAT IS NOT
      THE WORD 0 (`readCoefE`, Johnson/Desc/K8/Honest/LinkedAt.lean). It does not ask that of every
      table
  `zzCol_val`, **`ties_at_row`**   under `tiesLaid`, the powers laid: what the ties and reads lay on
      column plane * mz + off[mu] + i of the ties' row: ONE MONOMIAL: theta ^ (the plan's number +
      the tie's first index + stepF * (i / 3)) * ((2^10)^plane * (2^20)^(i % 3))
  `tieRowTerms`, `tieRowTerms_ok`, `tieRowTerms_live`   with the plain claims' terms; 2 is not 0 in
      the field
  `tie_cut`, `reads_cut`   behind a yes of the list, in the letters of the data in front
  `linkedNo s`   the state holds data and a ledger at which `selfLinked` says no; `linkedCount tl`
      := 2 mz + the sum over the matrices of 2 m
  **`linked_few`**   IF tl passes both tests, g meets `Gathers` at s and d bounds the exponents:
      THEN at most linkedCount tl * d field elements are challenges at which batch says yes and,
      behind it, `selfLinked` says no
  `linked_from`   in the form `CountFrom` (Johnson/Desc/K8/Honest/CountFrom.lean)
By: `behind_total` (BehindTotal.lean) · `reads_at_row`, `tie_at_row`, `readsTerms_ok`,
`readsTerms_live` (LinkedAt.lean) · `range_pick` (TiesAt.lean) · eq_funs
(Johnson/Desc/First/TailClaims/EquationsOut.lean): a yes of the list: the list handed in is the
closed one · gl_two_ne_zero (Cb/Pv/Head/NormGl.lean).
Limits. `readsLive` IS A PREMISE ON CHALLENGES DRAWN IN FRONT: how often it fails is counted nowhere
here; that it can hold at a segment's list is not shown here. `Gathers` and `tiesLaid` are premises.
No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.LinkedAt
import Johnson.Desc.K8.Honest.CountFrom
import Johnson.Desc.First.TailClaims.EquationsOut
import Cb.Pv.Head.NormGl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- On public numbers. -/
def tiesLaid (tl : HTailF2) : Bool :=
  (tl.ix.U.getD 0 none).getD 0 != tl.ix.ZZ && (tl.ix.U.getD 2 none).getD 0 != tl.ix.ZZ &&
  ((List.range tl.NM).all fun mu =>
    tl.gtTree.getD mu 0 != tl.ix.ZZ && (tl.shp.getD mu {}).m == (tl.mats.getD mu {}).m &&
    decide (0 < (tl.mats.getD mu {}).m) &&
    decide (tl.off.getD mu 0 + (tl.mats.getD mu {}).m ≤ tl.mz) &&
    (List.range tl.NM).all fun nu => nu == mu ||
      decide (tl.off.getD nu 0 + (tl.mats.getD nu {}).m ≤ tl.off.getD mu 0) ||
      decide (tl.off.getD mu 0 + (tl.mats.getD mu {}).m ≤ tl.off.getD nu 0)) &&
  (List.range tl.mz).all fun x => (List.range tl.NM).any fun mu =>
    decide (tl.off.getD mu 0 ≤ x) && decide (x < tl.off.getD mu 0 + (tl.mats.getD mu {}).m)

/-- What `tiesLaid` says. -/
structure TiesLaid (tl : HTailF2) : Prop where
  u0 : (tl.ix.U.getD 0 none).getD 0 ≠ tl.ix.ZZ
  u2 : (tl.ix.U.getD 2 none).getD 0 ≠ tl.ix.ZZ
  gt : ∀ mu, mu < tl.NM → tl.gtTree.getD mu 0 ≠ tl.ix.ZZ
  fit : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).m = (tl.mats.getD mu {}).m
  pos : ∀ mu, mu < tl.NM → 0 < (tl.mats.getD mu {}).m
  within : ∀ mu, mu < tl.NM → tl.off.getD mu 0 + (tl.mats.getD mu {}).m ≤ tl.mz
  apart : ∀ mu, mu < tl.NM → ∀ nu, nu < tl.NM → nu ≠ mu →
    tl.off.getD nu 0 + (tl.mats.getD nu {}).m ≤ tl.off.getD mu 0 ∨
      tl.off.getD mu 0 + (tl.mats.getD mu {}).m ≤ tl.off.getD nu 0
  cover : ∀ x, x < tl.mz → ∃ mu, mu < tl.NM ∧ tl.off.getD mu 0 ≤ x ∧
    x < tl.off.getD mu 0 + (tl.mats.getD mu {}).m

theorem tiesLaid_spec (tl : HTailF2) (h : tiesLaid tl = true) : TiesLaid tl := by
  simp only [tiesLaid, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.any_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := h
  exact ⟨a1, a2, fun mu hm => (a3 mu hm).1.1.1.1, fun mu hm => (a3 mu hm).1.1.1.2,
    fun mu hm => (a3 mu hm).1.1.2, fun mu hm => (a3 mu hm).1.2,
    fun mu hm nu hn hne => by
      rcases (a3 mu hm).2 nu hn with (h | h) | h
      · exact absurd h hne
      · exact Or.inl h
      · exact Or.inr h,
    fun x hx => by
      obtain ⟨mu, hm, h1, h2⟩ := a4 x hx
      exact ⟨mu, hm, h1, h2⟩⟩

/-- On the closed list of tables. -/
def readsLive (tl : HTailF2) : Bool :=
  (List.range (2 * tl.mz)).all fun x =>
    (readsList tl tl.funs).any fun y => !isZeroE (readCoefE tl y x)

/-- The first column of a matrix's digits. -/
theorem zzCol_val (tl : HTailF2) (mu plane : Nat) (hmu : mu < tl.NM) (hp : plane ≤ 1)
    (hm : 0 < (tl.mats.getD mu {}).m) :
    (tl.zzCol mu plane 0).getD 0 = plane * tl.mz + tl.off.getD mu 0 := by
  unfold HTailF2.zzCol
  rw [if_pos (by rw [decide_eq_true hmu, decide_eq_true hp, decide_eq_true hm]; rfl)]
  rfl

/-- **What the ties and reads lay on a column of the ties' row: one monomial.** -/
theorem ties_at_row (tl : HTailF2) (F0 : Fork) (hP : Powered tl F0.theta) (funs : Array HFun)
    (hL : TiesLaid tl) (mu₀ plane i : Nat) (hmu : mu₀ < tl.NM) (hp : plane ≤ 1)
    (hi : i < (tl.mats.getD mu₀ {}).m) :
    (((List.range tl.NM).map (tieTerm Reading.gl
          (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu₀ 0 + i)) tl F0)).sum +
        sumFrom (readTerm Reading.gl
          (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu₀ 0 + i)) tl F0) 0
          (readsList tl funs)) -
      (((List.range tl.NM).map (tieTerm Reading.gl allZero tl F0)).sum +
        sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs)) =
      Reading.gl.val F0.theta ^
          (F0.planClaimsF + tl.eqFirst.getD mu₀ 0 + tl.stepF * (i / 3)) *
        (((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3)) := by
  have hm3 : ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).m ≤ 3 * (tl.shp.getD mu {}).mS := by
    intro mu hm
    have h1 := (hP.shape mu hm).2.2.2.2
    have h2 := hL.fit mu hm
    omega
  have hr : sumFrom (readTerm Reading.gl
        (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu₀ 0 + i)) tl F0) 0
        (readsList tl funs) =
      sumFrom (readTerm Reading.gl allZero tl F0) 0 (readsList tl funs) := by
    refine sumFrom_congr _ _ _ _ fun j z hz => ?_
    have hU : (tl.ix.U.getD z.1.tree none).getD 0 ≠ tl.ix.ZZ := by
      rcases tree_of_mem tl funs z hz with e | e
      · rw [e]
        exact hL.u0
      · rw [e]
        exact hL.u2
    unfold readTerm
    rw [readBracket_off tl F0 z _ _ _ (fun h => by
      have h2 : 2 * tl.zzBlocks = 2 * tl.zzBlocks + 1 := h.2
      omega) hU]
  have hw0 := hL.within mu₀ hmu
  have ht := range_pick (tieTerm Reading.gl
      (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu₀ 0 + i)) tl F0)
    (tieTerm Reading.gl allZero tl F0) mu₀ tl.NM hmu (fun mu hm hne => by
      have hd := tie_at_row tl F0.theta hP mu (plane * tl.mz + tl.off.getD mu₀ 0 + i) hm
        (hm3 mu hm) (hL.gt mu hm)
      rw [zzCol_val tl mu 0 hm (Nat.zero_le _) (hL.pos mu hm),
        zzCol_val tl mu 1 hm (Nat.le_refl _) (hL.pos mu hm), hL.fit mu hm] at hd
      have hw := hL.within mu hm
      have ha := hL.apart mu₀ hmu mu hm hne
      have hpc : plane = 0 ∨ plane = 1 := by omega
      rw [if_neg (by rcases hpc with rfl | rfl <;> omega),
        if_neg (by rcases hpc with rfl | rfl <;> omega)] at hd
      unfold tieTerm
      have hd' : tieBracket Reading.gl
          (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu₀ 0 + i)) tl mu =
          tieBracket Reading.gl allZero tl mu := by
        linear_combination hd
      rw [hd'])
  have hd := tie_at_row tl F0.theta hP mu₀ (plane * tl.mz + tl.off.getD mu₀ 0 + i) hmu
    (hm3 mu₀ hmu) (hL.gt mu₀ hmu)
  rw [zzCol_val tl mu₀ 0 hmu (Nat.zero_le _) (hL.pos mu₀ hmu),
    zzCol_val tl mu₀ 1 hmu (Nat.le_refl _) (hL.pos mu₀ hmu), hL.fit mu₀ hmu] at hd
  have ht' : tieTerm Reading.gl
        (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu₀ 0 + i)) tl F0 mu₀ -
      tieTerm Reading.gl allZero tl F0 mu₀ =
      Reading.gl.val F0.theta ^
          (F0.planClaimsF + tl.eqFirst.getD mu₀ 0 + tl.stepF * (i / 3)) *
        (((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3)) := by
    unfold tieTerm
    rw [← mul_sub, hd, pow_add]
    have hpc : plane = 0 ∨ plane = 1 := by omega
    rcases hpc with rfl | rfl
    · rw [if_pos (by omega), if_neg (by omega)]
      have e : 0 * tl.mz + tl.off.getD mu₀ 0 + i - (0 * tl.mz + tl.off.getD mu₀ 0) = i := by omega
      rw [e]
      ring
    · rw [if_neg (by omega), if_pos (by omega)]
      have e : 1 * tl.mz + tl.off.getD mu₀ 0 + i - (1 * tl.mz + tl.off.getD mu₀ 0) = i := by omega
      rw [e]
      ring
  rw [hr]
  linear_combination ht + ht'

/-- The terms of the weight of column plane * mz + off[mu] + i of the ties' row. -/
def tieRowTerms (a : Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R mu plane i : Nat) :
    List (ℕ × Cb.Gl.E) :=
  plainTerms a nf nb (tl.NM + R) ++
    [(n + firstOf tl mu + tl.stepF * (i / 3),
      ((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3))]

/-- A matrix's equations' indices, all of them, end in front of the reads'. -/
theorem firstOf_next (tl : HTailF2) (mu : Nat) (hmu : mu < tl.NM) :
    firstOf tl mu + tl.stepF * 2 ^ clog2 (tl.shp.getD mu {}).mS ≤ firstOf tl tl.NM := by
  unfold firstOf
  have h1 : ∑ nu ∈ Finset.range (mu + 1), tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS ≤
      ∑ nu ∈ Finset.range tl.NM, tl.stepF * 2 ^ clog2 (tl.shp.getD nu {}).mS :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 hmu)
  rw [Finset.sum_range_succ] at h1
  exact h1

theorem tieRowTerms_ok (a : Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R mu plane i d : Nat)
    (hcl : nf + (4 + (tl.NM + R)) + nb ≤ n) (hmu : mu < tl.NM)
    (hi : i / 3 < (tl.shp.getD mu {}).mS)
    (hd : n + (firstOf tl tl.NM + R * tl.stepF) ≤ d + 1) :
    K9L.TermsOk (tieRowTerms a tl n nf nb R mu plane i) d := by
  obtain ⟨p1, p2⟩ := plainTerms_ok a nf nb (tl.NM + R) d (by omega)
  have pb := plainTerms_lt a nf nb _ n hcl
  have h1 := firstOf_next tl mu hmu
  have h2 : (tl.shp.getD mu {}).mS ≤ 2 ^ clog2 (tl.shp.getD mu {}).mS := K9L.le_pow_clog2 _
  have h3 : tl.stepF * (i / 3 + 1) ≤ tl.stepF * 2 ^ clog2 (tl.shp.getD mu {}).mS :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : tl.stepF * (i / 3 + 1) = tl.stepF * (i / 3) + tl.stepF := Nat.mul_succ _ _
  have h5 := stepF_pos tl
  refine ⟨?_, ?_⟩
  · unfold tieRowTerms
    rw [List.map_append, List.nodup_append]
    refine ⟨p1, by simp, ?_⟩
    intro u hu v hv
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hu
    have b1 := pb y hy
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv
    omega
  · intro y hy
    unfold tieRowTerms at hy
    rcases List.mem_append.1 hy with hy | hy
    · exact p2 y hy
    · obtain rfl := List.mem_singleton.1 hy
      show n + firstOf tl mu + tl.stepF * (i / 3) ≤ d
      omega

theorem tieRowTerms_live (a : Nat → Cb.Gl.E) (tl : HTailF2) (n nf nb R mu plane i : Nat) :
    ∃ y ∈ tieRowTerms a tl n nf nb R mu plane i, y.2 ≠ 0 :=
  ⟨_, List.mem_append_right _ (List.mem_singleton.2 rfl),
    mul_ne_zero (pow_ne_zero _ (pow_ne_zero _ Cb.Pv.Head.gl_two_ne_zero))
      (pow_ne_zero _ (pow_ne_zero _ Cb.Pv.Head.gl_two_ne_zero))⟩

section
variable {n₀ : Nat} {tl tl' tl1 : HTailF2} {funs : Array HFun} {F₁ F₂ : Fork} {k8 : List Claim}

/-- **The ties' row, in the letters of the data in front.** -/
theorem tie_cut (geq : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (etl : tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid })
    (hP : Powered tl1 F₁.theta) (hL : tiesLaid tl = true) (mu plane i : Nat) (hmu : mu < tl.NM)
    (hp : plane ≤ 1) (hi : i < (tl.mats.getD mu {}).m) :
    (((List.range tl1.NM).map (tieTerm Reading.gl
          (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)) tl1 F₁)).sum +
        sumFrom (readTerm Reading.gl
          (oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)) tl1 F₁) 0
          (readsList tl1 funs)) -
      (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
        sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs)) =
      Reading.gl.val F₁.theta ^ (F₁.planClaimsF + firstOf tl mu + tl.stepF * (i / 3)) *
        (((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3)) := by
  have eL : tiesLaid tl1 = tiesLaid tl := same1 (fun u : HTailF2 => tiesLaid u) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eN : tl1.NM = tl.NM := same1 (fun u : HTailF2 => u.NM) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eM : (tl1.mats.getD mu {}).m = (tl.mats.getD mu {}).m :=
    same1 (fun u : HTailF2 => (u.mats.getD mu {}).m) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eW : oneAt tl1.ix.ZZ tl1.zzRowTies (plane * tl1.mz + tl1.off.getD mu 0 + i) =
      oneAt tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i) :=
    same1 (fun u : HTailF2 => oneAt u.ix.ZZ u.zzRowTies (plane * u.mz + u.off.getD mu 0 + i))
      geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eE : firstOf tl1 mu + tl1.stepF * (i / 3) = firstOf tl mu + tl.stepF * (i / 3) :=
    same1 (fun u : HTailF2 => firstOf u mu + u.stepF * (i / 3)) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have hmu1 : mu < tl1.NM := by rw [eN]; exact hmu
  have h := ties_at_row tl1 F₁ hP funs (tiesLaid_spec tl1 (by rw [eL]; exact hL)) mu plane i hmu1
    hp (by rw [eM]; exact hi)
  rw [eW, hP.eqFirst_val mu (Nat.le_of_lt (hP.lt_shp mu hmu1))] at h
  rw [h]
  have e2 : F₁.planClaimsF + (∑ nu ∈ Finset.range mu,
      tl1.stepF * 2 ^ clog2 (tl1.shp.getD nu {}).mS) + tl1.stepF * (i / 3) =
      F₁.planClaimsF + firstOf tl mu + tl.stepF * (i / 3) := by
    have e3 : (∑ nu ∈ Finset.range mu, tl1.stepF * 2 ^ clog2 (tl1.shp.getD nu {}).mS) =
      firstOf tl1 mu := rfl
    rw [e3]
    omega
  rw [e2]

/-- **The reads' row, in the letters of the data in front.** -/
theorem reads_cut (geq : equations n₀ tl funs F₁ = .ok (tl', F₂, k8))
    (etl : tl' = { tl1 with tieObj := tl'.tieObj, tiesOn := tl'.tiesOn, nX4Laid := tl'.nX4Laid })
    (hP : Powered tl1 F₁.theta) (hL : tiesLaid tl = true) (x : Nat) :
    (((List.range tl1.NM).map
          (tieTerm Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl1 F₁)).sum +
        sumFrom (readTerm Reading.gl (oneAt tl.ix.ZZ tl.zzRowReads x) tl1 F₁) 0
          (readsList tl1 funs)) -
      (((List.range tl1.NM).map (tieTerm Reading.gl allZero tl1 F₁)).sum +
        sumFrom (readTerm Reading.gl allZero tl1 F₁) 0 (readsList tl1 funs)) =
      K9L.termsSum (stepTerms (fun y => Reading.gl.val (readCoefE tl y x))
        (F₁.planClaimsF + firstOf tl tl.NM) tl.stepF 0 (readsList tl funs))
        (Reading.gl.val F₁.theta) := by
  have eL : tiesLaid tl1 = tiesLaid tl := same1 (fun u : HTailF2 => tiesLaid u) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eW : oneAt tl1.ix.ZZ tl1.zzRowReads x = oneAt tl.ix.ZZ tl.zzRowReads x :=
    same1 (fun u : HTailF2 => oneAt u.ix.ZZ u.zzRowReads x) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have hL1 := tiesLaid_spec tl1 (by rw [eL]; exact hL)
  have h := reads_at_row tl1 F₁ funs x hL1.gt hL1.u0 hL1.u2
  rw [eW, hP.eqFirst_val tl1.NM hP.NM_le_shp] at h
  rw [h]
  exact same1 (fun u : HTailF2 => K9L.termsSum (stepTerms
      (fun y => Reading.gl.val (readCoefE u y x)) (F₁.planClaimsF + firstOf u u.NM) u.stepF 0
      (readsList u funs)) (Reading.gl.val F₁.theta)) geq etl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)

end

/-- `selfLinked` says no at the state. -/
def linkedNo (s : S) : Bool :=
  match tlForkP.get? s with
  | some q => !selfLinked q.1 q.2
  | none => false

/-- How many polynomials the count takes. -/
def linkedCount (tl : HTailF2) : ℕ :=
  2 * tl.mz + ∑ mu ∈ Finset.range tl.NM, 2 * (tl.mats.getD mu {}).m

/-- **The count.** -/
theorem linked_few (p : K9.Where) (g : S → Except String (List Claim × S))
    (batch : S → List Fmt.RoundView → Except String S) (s : S) (tl : HTailF2) (F : Fork)
    (funs : Array HFun) (nf nb d : Nat) (a : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (hb : ∀ rs t, batch s rs = .ok t → (K9.batch K9.atS p g).decide s rs [] = .ok t)
    (hs : tlForkP.get? s = some (tl, F)) (hP : tiesLaid tl = true) (hL : readsLive tl = true)
    (hG : Gathers p g s tl funs nf nb a) (hd : F.planClaimsF + topOf tl funs ≤ d + 1) :
    Prob.cnt (fun x : Cb.Gl.E => askBehind batch linkedNo s [chiAt x] = true) ≤
      linkedCount tl * d := by
  have hT := tiesLaid_spec tl hP
  have root : ∀ x : Cb.Gl.E, askBehind batch linkedNo s [chiAt x] = true →
      (nf + (4 + (tl.NM + (readsList tl funs).length)) + nb ≤ F.planClaimsF ∧ funs = tl.funs ∧
        ∀ mu, mu < tl.NM → (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3) ∧
      ((∃ c ∈ Finset.range (2 * tl.mz),
          K9L.termsSum (readsTerms (fun j => a j tl.ix.ZZ tl.zzRowReads c) tl funs F.planClaimsF
            nf nb c) x = 0) ∨
        ∃ mu ∈ Finset.range tl.NM, ∃ plane ∈ Finset.range 2,
          ∃ i ∈ Finset.range (tl.mats.getD mu {}).m,
            K9L.termsSum (tieRowTerms
              (fun j => a j tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)) tl
              F.planClaimsF nf nb (readsList tl funs).length mu plane i) x = 0) := by
    intro x hx
    unfold askBehind at hx
    simp only [List.map_cons, List.map_nil] at hx
    cases hbt : batch s [⟨[], chiAt x⟩] with
    | error e =>
      rw [hbt] at hx
      exact absurd hx (by simp)
    | ok t' =>
      rw [hbt] at hx
      change linkedNo t' = true at hx
      obtain ⟨tl', G, F₁, F₂, k8, n₀, g₀, h1, geq, -, hθ, hpl, -, shG, hcnt, -, hcut⟩ :=
        behind_total p g batch s t' tl F funs nf nb a hb hs hG x hbt
      obtain ⟨tl0, hP0, -, etl0, -⟩ := hcut 0 0 0
      have hmS : ∀ mu, mu < tl.NM →
          (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3 := by
        intro mu hmu
        have e1 : tl0.NM = tl.NM := same1 (fun u : HTailF2 => u.NM) geq etl0
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        have e2 : ((tl0.shp.getD mu {}).mS = ((tl0.mats.getD mu {}).m + 2) / 3) =
            ((tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3) :=
          same1 (fun u : HTailF2 => (u.shp.getD mu {}).mS = ((u.mats.getD mu {}).m + 2) / 3)
            geq etl0
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        exact e2.mp (hP0.shape mu (by rw [e1]; exact hmu)).2.2.2.2
      refine ⟨⟨hcnt, eq_funs geq, hmS⟩, ?_⟩
      have eq3 : (tl'.ix.ZZ, tl'.zzRowReads, tl'.zzRowTies, tl'.mz) =
          (tl.ix.ZZ, tl.zzRowReads, tl.zzRowTies, tl.mz) :=
        eq_same (fun u : HTailF2 => (u.ix.ZZ, u.zzRowReads, u.zzRowTies, u.mz)) geq
          (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      obtain ⟨eZ, eR, eT, eM⟩ : tl'.ix.ZZ = tl.ix.ZZ ∧ tl'.zzRowReads = tl.zzRowReads ∧
          tl'.zzRowTies = tl.zzRowTies ∧ tl'.mz = tl.mz := by
        simpa only [Prod.mk.injEq] using eq3
      unfold linkedNo at hx
      rw [h1] at hx
      have hno : selfLinked tl' G = false := by simpa using hx
      unfold selfLinked at hno
      rw [eZ, eR, eT, eM] at hno
      -- a row whose test says no has a column at which the ledger's two values agree
      have row : ∀ r, noneZero (weightsOf G tl.ix.ZZ r) 0 (2 * tl.mz) = false →
          ∃ c, c < 2 * tl.mz ∧
            G.total Reading.gl (oneAt tl.ix.ZZ r c) - G.total Reading.gl allZero = 0 := by
        intro r hr
        obtain ⟨u, hu, hz⟩ := noneZero_no _ 0 _ (Or.inl (Nat.zero_le _)) hr
        rw [Nat.zero_add] at hz
        by_cases h0 : ((G.trees.getD tl.ix.ZZ {}).rows.getD r {}).L0 = 0
        · refine ⟨u, hu, ?_⟩
          rw [total_oneAt Reading.gl G _ _ _ h0, hz]
          exact Reading.gl.zero
        · exact ⟨0, Nat.lt_of_le_of_lt (Nat.zero_le _) hu,
            total_below Reading.gl G _ _ 0 (Nat.pos_of_ne_zero h0)⟩
      rcases Bool.and_eq_false_iff.1 hno with hr | hr
      · left
        obtain ⟨c, hc, hz⟩ := row _ hr
        refine ⟨c, Finset.mem_range.2 hc, ?_⟩
        obtain ⟨tl1, hP1, -, etl, hc1⟩ := hcut tl.ix.ZZ tl.zzRowReads c
        rw [hc1, reads_cut geq etl hP1 hP c, hθ, hpl] at hz
        unfold readsTerms plainTerms
        rw [termsSum_append, termsSum_append]
        exact hz
      · right
        obtain ⟨c, hc, hz⟩ := row _ hr
        obtain ⟨mu, plane, i, hmu, hp, hi, rfl⟩ : ∃ mu plane i, mu < tl.NM ∧ plane < 2 ∧
            i < (tl.mats.getD mu {}).m ∧ c = plane * tl.mz + tl.off.getD mu 0 + i := by
          by_cases hlow : c < tl.mz
          · obtain ⟨mu, hmu, c1, c2⟩ := hT.cover c hlow
            exact ⟨mu, 0, c - tl.off.getD mu 0, hmu, by omega, by omega, by omega⟩
          · obtain ⟨mu, hmu, c1, c2⟩ := hT.cover (c - tl.mz) (by omega)
            exact ⟨mu, 1, c - tl.mz - tl.off.getD mu 0, hmu, by omega, by omega, by omega⟩
        refine ⟨mu, Finset.mem_range.2 hmu, plane, Finset.mem_range.2 hp, i,
          Finset.mem_range.2 hi, ?_⟩
        obtain ⟨tl1, hP1, -, etl, hc1⟩ :=
          hcut tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)
        rw [hc1, tie_cut geq etl hP1 hP mu plane i hmu (by omega) hi, hθ, hpl] at hz
        unfold tieRowTerms plainTerms
        rw [termsSum_append, termsSum_append]
        have e1 : K9L.termsSum [(F.planClaimsF + firstOf tl mu + tl.stepF * (i / 3),
            ((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3))] x =
            x ^ (F.planClaimsF + firstOf tl mu + tl.stepF * (i / 3)) *
              (((2 : Cb.Gl.E) ^ 10) ^ plane * ((2 : Cb.Gl.E) ^ 20) ^ (i % 3)) := by
          simp [K9L.termsSum]
        rw [e1]
        exact hz
  by_cases hne : ∃ x : Cb.Gl.E, askBehind batch linkedNo s [chiAt x] = true
  · obtain ⟨x₀, hx₀⟩ := hne
    obtain ⟨⟨hcnt, hfuns, hmS⟩, -⟩ := root x₀ hx₀
    simp only [readsLive, List.all_eq_true, List.mem_range] at hL
    rw [← hfuns] at hL
    have hd' : F.planClaimsF + (firstOf tl tl.NM + (readsList tl funs).length * tl.stepF) ≤
        d + 1 := hd
    refine (Prob.cnt_le_add fun x hx => (root x hx).2).trans ?_
    have hA : Prob.cnt (fun x : Cb.Gl.E => ∃ c ∈ Finset.range (2 * tl.mz),
        K9L.termsSum (readsTerms (fun j => a j tl.ix.ZZ tl.zzRowReads c) tl funs F.planClaimsF
          nf nb c) x = 0) ≤ 2 * tl.mz * d := by
      refine (Prob.cnt_exists_mem_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => d) fun c hc => ?_).trans (by simp)
      exact K9L.count_terms Cb.Gl.E _ d (readsTerms_ok _ tl funs F.planClaimsF nf nb c d hcnt hd')
        (readsTerms_live _ tl funs F.planClaimsF nf nb c (hL c (Finset.mem_range.1 hc)))
    have hB : Prob.cnt (fun x : Cb.Gl.E => ∃ mu ∈ Finset.range tl.NM, ∃ plane ∈ Finset.range 2,
        ∃ i ∈ Finset.range (tl.mats.getD mu {}).m,
          K9L.termsSum (tieRowTerms
            (fun j => a j tl.ix.ZZ tl.zzRowTies (plane * tl.mz + tl.off.getD mu 0 + i)) tl
            F.planClaimsF nf nb (readsList tl funs).length mu plane i) x = 0) ≤
        (∑ mu ∈ Finset.range tl.NM, 2 * (tl.mats.getD mu {}).m) * d := by
      refine (Prob.cnt_exists_mem_le _ _).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun mu hmu => ?_
      refine (Prob.cnt_exists_mem_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => (tl.mats.getD mu {}).m * d) fun plane _ => ?_).trans
        (by simp [Nat.mul_assoc])
      refine (Prob.cnt_exists_mem_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => d) fun i hi => ?_).trans (by simp)
      exact K9L.count_terms Cb.Gl.E _ d
        (tieRowTerms_ok _ tl F.planClaimsF nf nb _ mu plane i d hcnt (Finset.mem_range.1 hmu)
          (by
            have h1 := hmS mu (Finset.mem_range.1 hmu)
            have h2 := Finset.mem_range.1 hi
            omega) hd')
        (tieRowTerms_live _ tl F.planClaimsF nf nb _ mu plane i)
    unfold linkedCount
    rw [Nat.add_mul]
    exact Nat.add_le_add hA hB
  · rw [Prob.cnt_false fun x hx => hne ⟨x, hx⟩]
    exact Nat.zero_le _

/-- In the form of a count, the test a letter. -/
theorem linked_from :
    CountFrom (fun tl _ => tiesLaid tl && readsLive tl) linkedNo linkedCount := by
  intro p g batch s tl F funs nf nb d a hb hs hok hG hd
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 hok
  exact linked_few p g batch s tl F funs nf nb d a hb hs h1 h2 hG hd

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tiesLaid_spec
#print axioms VerifiableInference.Desc.First.K8.Honest.zzCol_val
#print axioms VerifiableInference.Desc.First.K8.Honest.ties_at_row
#print axioms VerifiableInference.Desc.First.K8.Honest.tieRowTerms_ok
#print axioms VerifiableInference.Desc.First.K8.Honest.tieRowTerms_live
#print axioms VerifiableInference.Desc.First.K8.Honest.tie_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.reads_cut
#print axioms VerifiableInference.Desc.First.K8.Honest.linked_few
#print axioms VerifiableInference.Desc.First.K8.Honest.linked_from
