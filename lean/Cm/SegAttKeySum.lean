-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAttKeySum.lean: the key families 2M, 2D, 3W of the attention segment: those with sums of
products of cells. (What is required of a family, `AttKeyOK`, and the affine families:
Cm/SegAttKey.lean.)

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family (`Fam`, Cb/Req/ReqSpec.lean) has one value at each
vertex of a cube; a vertex beyond the index set is called dead.

Main names:
  `RE_eq`: for a position i < `DA.T`, `AttSeg.RE`, the part of key 3W with the sum over the places
    of a row, with that sum as one sum over positions (`AttSeg.rowSum_eq`).
  `fam2M`, `fam2D`: affine part - Σ_n query × key: the gap (`AttSeg.gp`) contains the score
    (`AttSeg.scV`), a sum over the 2^7 channels (a sum atom; both forms are 0 at a dead vertex and
    at an empty place of M).
  `fam3W`: ± (2 Σ_j weight × value + den - 2 den × out) + affine part (a sum atom over the 2^10
    positions; the weight's form is 0 at positions beyond the row's blocks; den × out is a product
    of two forms).
  `fam2M_ok`, `fam2D_ok`, `fam3W_ok`: each has `AttKeyOK`.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegAttKey

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset Ex
open Inst.Model.AttSeg (Raw Reg)

variable [scl : Scl]

/-! ## The keys, written out -/

section Eq
variable {R : Type} [CommRing R] (u0 : ℕ) (t : Raw → R)

theorem key2M_eq (b x : ℕ) :
    AttSeg.key2 (DU u0) t .M b x =
      (if DA.EmptyM x then (((DU u0).cutC : ℤ) : R)
          else
            AttSeg.mxV t b (DA.mG x) (DA.iM x) -
              ∑ n ∈ range DA.ch, AttSeg.qryV t b (DA.mG x) (DA.iM x) n *
                AttSeg.keyV t (DA.lamOf b) (DA.mG x) (DA.jM x) n) -
        AttSeg.rm t .M b x + 2 ^ 32 * AttSeg.flV t .M b x + 2 ^ 33 * AttSeg.wtV t .M b x := rfl

theorem key2D_eq (b x : ℕ) :
    AttSeg.key2 (DU u0) t .D b x =
      (AttSeg.mxV t b (DA.dG x) (DA.iD x) -
          ∑ n ∈ range DA.ch, AttSeg.qryV t b (DA.dG x) (DA.iD x) n *
            AttSeg.keyV t (DA.lamOf b) (DA.dG x) (DA.jD x) n +
          if DA.MaskedD x then ((AttSeg.Om (DU u0) : ℤ) : R) else 0) -
        AttSeg.rm t .D b x + 2 ^ 32 * AttSeg.flV t .D b x + 2 ^ 33 * AttSeg.wtV t .D b x := rfl

omit scl in
/-- for a position i < `DA.T`, RE with the accumulator as one sum over positions -/
theorem RE_eq (b h n : ℕ) {i : ℕ} (hi : i < DA.T) :
    AttSeg.RE (DU u0) t b h i n =
      2 * (∑ j ∈ range (DA.B * (i / DA.B + 1)),
            AttSeg.wtIJ DA t b h i j * AttSeg.valV t (DA.lamOf b) h j n) +
        AttSeg.denV t b h i - 2 * AttSeg.denV t b h i * AttSeg.outV t b h i n := by
  show 2 * AttSeg.rowSum DA t (fun j => AttSeg.valV t (DA.lamOf b) h j n) b h i + _ - _ = _
  rw [AttSeg.rowSum_eq DA t _ b h hi]

end Eq

variable {X F E : Type} [Field F] [Field E] [Algebra F E] (g u0 : ℕ) (tb : Tables) (Φ : IdxFmt F)

/-! ## 2M -/

def a2M (b x : ℕ) : CForm E :=
  (if DA.EmptyM x then cK ((((DU u0).cutC : ℤ) : E)) else cmx g b (DA.mG x) (DA.iM x)) -
    crm g .M b x + ((2 : E) ^ 32) • cfl g .M b x + ((2 : E) ^ 33) • cwt g .M b x
/-- the two factors of the score at (vertex B, channel n) -/
def q2M (B n : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lM ∧ ¬ DA.EmptyM (yOf DA.lM B) then
    cqry g (bOf DA.lM B) (DA.mG (yOf DA.lM B)) (DA.iM (yOf DA.lM B)) n
  else cK 0
def k2M (B n : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lM ∧ ¬ DA.EmptyM (yOf DA.lM B) then
    ckey g (DA.lamOf (bOf DA.lM B)) (DA.mG (yOf DA.lM B)) (DA.jM (yOf DA.lM B)) n
  else cK 0

def ex2M : Ex1 X E :=
  aff (live DA.lM (padA u0 tb 1) (a2M g u0)) -
    sumA (5 + DA.lM) DA.ln
      (aff0 (fun B' => q2M g (bOf DA.ln B') (yOf DA.ln B')) *
        aff0 fun B' => k2M g (bOf DA.ln B') (yOf DA.ln B'))

def fam2M : Cb.Fam X E := Ex1.fam (5 + DA.lM) (ex2M g u0 tb)

theorem fam2M_ok :
    AttKeyOK Φ g u0 tb 1 0 (DA.nb * 2 ^ DA.lM) (fam2M (X := X) (E := E) g u0 tb) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam2M
    rw [fam_val]
    unfold ex2M
    simp only [val1_sub, val1_aff, val1_sumA, val0_mul, val0_aff, val_live]
    rw [sum_dec DA.ln B fun B n => (q2M g B n).val A * (k2M g B n).val A, keyVec1]
    by_cases h : B < DA.nb * 2 ^ DA.lM
    · rw [if_pos h, if_pos h]
      refine Eq.trans ?_ (twoFam_fst h).symm
      refine Eq.trans ?_ (key2M_eq u0 (tAtt g A) _ _).symm
      by_cases he : DA.EmptyM (yOf DA.lM B)
      · simp [a2M, q2M, k2M, he]
      · have e : ∀ n, (q2M g B n).val A * (k2M g B n).val A
            = AttSeg.qryV (tAtt g A) (bOf DA.lM B) (DA.mG (yOf DA.lM B)) (DA.iM (yOf DA.lM B)) n *
                AttSeg.keyV (tAtt g A) (DA.lamOf (bOf DA.lM B)) (DA.mG (yOf DA.lM B))
                  (DA.jM (yOf DA.lM B)) n := fun n => by
          unfold q2M k2M
          rw [if_pos ⟨h, he⟩, if_pos ⟨h, he⟩, val_cqry, val_ckey]
        simp only [e]
        have e2 : (a2M g u0 (bOf DA.lM B) (yOf DA.lM B) : CForm E).val A =
            AttSeg.mxV (tAtt g A) (bOf DA.lM B) (DA.mG (yOf DA.lM B)) (DA.iM (yOf DA.lM B)) -
              AttSeg.rm (tAtt g A) .M (bOf DA.lM B) (yOf DA.lM B) +
              2 ^ 32 * AttSeg.flV (tAtt g A) .M (bOf DA.lM B) (yOf DA.lM B) +
              2 ^ 33 * AttSeg.wtV (tAtt g A) .M (bOf DA.lM B) (yOf DA.lM B) := by
          simp [a2M, he]
        rw [e2, if_neg he]
        show _ - ∑ n ∈ range DA.ch, _ = _
        ring
    · rw [if_neg h, if_neg h]
      have e : ∀ n, (q2M g B n : CForm E).val A * (k2M g B n).val A = 0 := fun n => by
        unfold q2M
        rw [if_neg fun hh => h hh.1, val_cK, zero_mul]
      simp only [e, sum_const_zero, sub_zero]
  wf := fam_wf Φ (All.sub (WF1.aff Φ _ _) (WF1.sumA Φ (All.mul (WF0.aff Φ _ _) (WF0.aff Φ _ _))))
  places := fam_places (All.sub (Pl1.aff fun B _ => pl_live (fun b hb x hx => by
      refine (((AllPl.ite (fun _ => AllPl.cK _) fun he => inAtt_cmx g hb (DA.mG_lt hx) (iM_lt he)).sub (inAtt_crm g hb hx)).add ((inAtt_cfl g hb hx).smul _)).add ((inAtt_cwt g hb hx).smul _)) B)
    (Pl1.sumA (All.mul
      (Pl0.aff fun B' _ =>
        AllPl.ite
          (fun hh => inAtt_cqry g (bOf_lt hh.1) (DA.mG_lt (yOf_lt _ _)) (iM_lt hh.2) (yOf_lt _ _))
          fun _ => AllPl.cK _)
      (Pl0.aff fun B' _ =>
        AllPl.ite (fun hh =>
            inAtt_ckey g (lam_lt (bOf_lt hh.1)) (DA.mG_lt (yOf_lt _ _)) (jM_lt hh.2) (yOf_lt _ _))
          fun _ => AllPl.cK _))))

/-! ## 2D -/

def a2D (b x : ℕ) : CForm E :=
  (cmx g b (DA.dG x) (DA.iD x) +
      if DA.MaskedD x then cK (((AttSeg.Om (DU u0) : ℤ) : E)) else cK 0) -
    crm g .D b x + ((2 : E) ^ 32) • cfl g .D b x + ((2 : E) ^ 33) • cwt g .D b x
def q2D (B n : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lD then cqry g (bOf DA.lD B) (DA.dG (yOf DA.lD B)) (DA.iD (yOf DA.lD B)) n
  else cK 0
def k2D (B n : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lD then
    ckey g (DA.lamOf (bOf DA.lD B)) (DA.dG (yOf DA.lD B)) (DA.jD (yOf DA.lD B)) n
  else cK 0

def ex2D : Ex1 X E :=
  aff (live DA.lD (padA u0 tb 1) (a2D g u0)) -
    sumA (5 + DA.lD) DA.ln
      (aff0 (fun B' => q2D g (bOf DA.ln B') (yOf DA.ln B')) *
        aff0 fun B' => k2D g (bOf DA.ln B') (yOf DA.ln B'))

def fam2D : Cb.Fam X E := Ex1.fam (5 + DA.lD) (ex2D g u0 tb)

theorem fam2D_ok :
    AttKeyOK Φ g u0 tb 1 (DA.nb * 2 ^ DA.lM) (DA.nb * 2 ^ DA.lD)
      (fam2D (X := X) (E := E) g u0 tb) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam2D
    rw [fam_val]
    unfold ex2D
    simp only [val1_sub, val1_aff, val1_sumA, val0_mul, val0_aff, val_live]
    rw [sum_dec DA.ln B fun B n => (q2D g B n).val A * (k2D g B n).val A, keyVec1]
    by_cases h : B < DA.nb * 2 ^ DA.lD
    · rw [if_pos h, if_pos h]
      refine Eq.trans ?_ (twoFam_snd h).symm
      refine Eq.trans ?_ (key2D_eq u0 (tAtt g A) _ _).symm
      have e : ∀ n, (q2D g B n).val A * (k2D g B n).val A =
          AttSeg.qryV (tAtt g A) (bOf DA.lD B) (DA.dG (yOf DA.lD B)) (DA.iD (yOf DA.lD B)) n *
            AttSeg.keyV (tAtt g A) (DA.lamOf (bOf DA.lD B)) (DA.dG (yOf DA.lD B))
              (DA.jD (yOf DA.lD B)) n := fun n => by
        unfold q2D k2D
        rw [if_pos h, if_pos h, val_cqry, val_ckey]
      simp only [e]
      have e2 : (a2D g u0 (bOf DA.lD B) (yOf DA.lD B) : CForm E).val A =
          (AttSeg.mxV (tAtt g A) (bOf DA.lD B) (DA.dG (yOf DA.lD B)) (DA.iD (yOf DA.lD B)) +
              if DA.MaskedD (yOf DA.lD B) then ((AttSeg.Om (DU u0) : ℤ) : E) else 0) -
            AttSeg.rm (tAtt g A) .D (bOf DA.lD B) (yOf DA.lD B) +
            2 ^ 32 * AttSeg.flV (tAtt g A) .D (bOf DA.lD B) (yOf DA.lD B) +
            2 ^ 33 * AttSeg.wtV (tAtt g A) .D (bOf DA.lD B) (yOf DA.lD B) := by
        simp [a2D]
      rw [e2]
      show _ - ∑ n ∈ range DA.ch, _ = _
      ring
    · rw [if_neg h, if_neg h]
      have e : ∀ n, (q2D g B n : CForm E).val A * (k2D g B n).val A = 0 := fun n => by
        unfold q2D
        rw [if_neg h, val_cK, zero_mul]
      simp only [e, sum_const_zero, sub_zero]
  wf := fam_wf Φ (All.sub (WF1.aff Φ _ _) (WF1.sumA Φ (All.mul (WF0.aff Φ _ _) (WF0.aff Φ _ _))))
  places := fam_places (All.sub (Pl1.aff fun B _ => pl_live (fun b hb x hx => by
      refine ((((inAtt_cmx g hb (DA.dG_lt hx) (iD_lt x)).add (AllPl.ite (fun _ => AllPl.cK _) fun _ => AllPl.cK _)).sub (inAtt_crm g hb hx)).add ((inAtt_cfl g hb hx).smul _)).add ((inAtt_cwt g hb hx).smul _)) B)
    (Pl1.sumA (All.mul
      (Pl0.aff fun B' _ =>
        AllPl.ite
          (fun hh => inAtt_cqry g (bOf_lt hh) (DA.dG_lt (yOf_lt _ _)) (iD_lt _) (yOf_lt _ _))
          fun _ => AllPl.cK _)
      (Pl0.aff fun B' _ =>
        AllPl.ite (fun hh =>
            inAtt_ckey g (lam_lt (bOf_lt hh)) (DA.dG_lt (yOf_lt _ _)) (jD_lt _) (yOf_lt _ _))
          fun _ => AllPl.cK _))))

/-! ## 3W -/

/-- the weight at the place that stands for the pair of positions (i, j),
j < `DA.B` (⌊i/`DA.B`⌋ + 1), as a form -/
def cwtIJ (b h i j : ℕ) : CForm E :=
  if j / DA.B < i / DA.B then
    cwt g .M b
      (DA.codeM h (DA.slotP (i / DA.B)) (DA.slotS (i / DA.B) (j / DA.B)) (i % DA.B) (j % DA.B))
  else cwt g .D b (DA.codeD h (i / DA.B) (i % DA.B) (j % DA.B))

omit scl in
@[simp] theorem val_cwtIJ (A : ℕ → ℕ → ℕ → E) (b h i j : ℕ) :
    (cwtIJ g b h i j : CForm E).val A = AttSeg.wtIJ DA (tAtt g A) b h i j := by
  simp [cwtIJ, AttSeg.wtIJ]

omit scl in
theorem inAtt_cwtIJ {b h i j : ℕ} (hb : b < DA.nb) (hh : h < DA.nG) (hi : i < DA.T) :
    InAtt g (cwtIJ g b h i j : CForm E) := by
  have hI : i / DA.B < DA.nBlk := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
  refine AllPl.ite (fun hJ => ?_) fun _ => ?_
  · have hs := DA.slot_of_blk hJ hI
    exact inAtt_cwt g hb
      (DA.codeM_lt hh hs.1 (lt_of_lt_of_le hs.2.1 (Nat.sub_le _ _))
        (Nat.mod_lt _ DA.B_pos) (Nat.mod_lt _ DA.B_pos))
  · exact inAtt_cwt g hb (DA.codeD_lt hh hI (Nat.mod_lt _ DA.B_pos) (Nat.mod_lt _ DA.B_pos))

/-- the parts (χ, h, i, n) of the inner index of a piece of 3W -/
def wX (y : ℕ) : ℕ := y / DA.ch / DA.T / DA.nG
def wH (y : ℕ) : ℕ := y / DA.ch / DA.T % DA.nG
def wI (y : ℕ) : ℕ := y / DA.ch % DA.T
def wN (y : ℕ) : ℕ := y % DA.ch

omit scl in
theorem wH_lt (y : ℕ) : wH y < DA.nG := Nat.mod_lt _ (by decide)
omit scl in
theorem wI_lt (y : ℕ) : wI y < DA.T := Nat.mod_lt _ (by decide)
omit scl in
theorem wN_lt (y : ℕ) : wN y < DA.ch := Nat.mod_lt _ (by decide)

/-- the factors of the accumulator at (vertex B, position j) -/
def wt3 (B j : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lW ∧ j < DA.B * (wI (yOf DA.lW B) / DA.B + 1) then
    cwtIJ g (bOf DA.lW B) (wH (yOf DA.lW B)) (wI (yOf DA.lW B)) j
  else cK 0
def vl3 (B j : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lW then
    cval g (DA.lamOf (bOf DA.lW B)) (wH (yOf DA.lW B)) j (wN (yOf DA.lW B))
  else cK 0
def den3 (B : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lW then cden g (bOf DA.lW B) (wH (yOf DA.lW B)) (wI (yOf DA.lW B)) else cK 0
def out3 (B : ℕ) : CForm E :=
  if B < DA.nb * 2 ^ DA.lW then
    cout g (bOf DA.lW B) (wH (yOf DA.lW B)) (wI (yOf DA.lW B)) (wN (yOf DA.lW B))
  else cK 0
/-- the affine rest -/
def rest3 (b y : ℕ) : CForm E :=
  if wX y = 0 then (-(2 : E) ^ 16) • cqh g b (wH y) (wI y) (wN y)
  else (2 : E) • cden g b (wH y) (wI y) - cK 1 - ((2 : E) ^ 16) • cqh' g b (wH y) (wI y) (wN y)
/-- the sign of RE -/
def sg3 : X → ℕ → E := fun _ B => if wX (yOf DA.lW B) = 0 then 1 else -1

def ex3W : Ex1 X E :=
  Ex.sc sg3 ((2 : E) •
          sumA (5 + DA.lW) DA.lT
            (aff0 (fun B' => wt3 g (bOf DA.lT B') (yOf DA.lT B')) *
              aff0 fun B' => vl3 g (bOf DA.lT B') (yOf DA.lT B')) +
        aff (den3 g) - (2 : E) • (aff (den3 g) * aff (out3 g))) +
    aff (live DA.lW (padA u0 tb 2) (rest3 g))

def fam3W : Cb.Fam X E := Ex1.fam (5 + DA.lW) (ex3W g u0 tb)

theorem fam3W_ok :
    AttKeyOK Φ g u0 tb 2 0 (DA.nb * 2 ^ DA.lW) (fam3W (X := X) (E := E) g u0 tb) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam3W
    rw [fam_val]
    unfold ex3W
    simp only [val1_add, val1_sub, val1_sc, val1_smul, val1_mul, val1_aff, val1_sumA,
      val0_mul, val0_aff, val_live]
    rw [sum_dec DA.lT B fun B j => (wt3 g B j).val A * (vl3 g B j).val A, keyVec2]
    by_cases h : B < DA.nb * 2 ^ DA.lW
    · rw [if_pos h, if_pos h]
      refine Eq.trans ?_ (twoFam_fst h).symm
      show _ = AttSeg.key3W (DU u0) (tAtt g A) (wX (yOf DA.lW B)) (bOf DA.lW B) (wH (yOf DA.lW B))
          (wI (yOf DA.lW B)) (wN (yOf DA.lW B))
      unfold AttSeg.key3W
      rw [RE_eq u0 (tAtt g A) _ _ _ (wI_lt _)]
      have e : ∀ j, (wt3 g B j).val A * (vl3 g B j).val A = if j < DA.B * (wI (yOf DA.lW B) / DA.B + 1) then
          AttSeg.wtIJ DA (tAtt g A) (bOf DA.lW B) (wH (yOf DA.lW B)) (wI (yOf DA.lW B)) j *
            AttSeg.valV (tAtt g A) (DA.lamOf (bOf DA.lW B)) (wH (yOf DA.lW B)) j (wN (yOf DA.lW B))
          else 0 := fun j => by
        unfold wt3 vl3
        by_cases hj : j < DA.B * (wI (yOf DA.lW B) / DA.B + 1)
        · rw [if_pos ⟨h, hj⟩, if_pos h, if_pos hj, val_cwtIJ, val_cval]
        · rw [if_neg fun hh => hj hh.2, if_neg hj, val_cK, zero_mul]
      simp only [e]
      have hle : DA.B * (wI (yOf DA.lW B) / DA.B + 1) ≤ 2 ^ DA.lT := by
        have h1 : wI (yOf DA.lW B) / DA.B < DA.nBlk :=
          Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact wI_lt _)
        have h2 : (2 : ℕ) ^ DA.lT = DA.B * DA.nBlk := by decide
        rw [h2]
        exact Nat.mul_le_mul_left _ h1
      rw [sum_range_ite hle]
      have e3 : (den3 g B : CForm E).val A =
          AttSeg.denV (tAtt g A) (bOf DA.lW B) (wH (yOf DA.lW B)) (wI (yOf DA.lW B)) := by
        unfold den3
        rw [if_pos h, val_cden]
      have e4 : (out3 g B : CForm E).val A =
          AttSeg.outV (tAtt g A) (bOf DA.lW B) (wH (yOf DA.lW B))
            (wI (yOf DA.lW B)) (wN (yOf DA.lW B)) := by
        unfold out3
        rw [if_pos h, val_cout]
      rw [e3, e4]
      unfold sg3 rest3
      by_cases hχ : wX (yOf DA.lW B) = 0
      · rw [if_pos hχ, if_pos hχ, if_pos hχ, val_smul, val_cqh]
        ring
      · rw [if_neg hχ, if_neg hχ, if_neg hχ, val_sub, val_sub, val_smul, val_smul,
          val_cK, val_cden, val_cqh']
        ring
    · rw [if_neg h, if_neg h]
      have e : ∀ j, (wt3 g B j : CForm E).val A * (vl3 g B j).val A = 0 := fun j => by
        unfold wt3
        rw [if_neg fun hh => h hh.1, val_cK, zero_mul]
      have e3 : (den3 g B : CForm E).val A = 0 := by
        unfold den3
        rw [if_neg h, val_cK]
      simp only [e, e3, sum_const_zero]
      ring
  wf := fam_wf Φ
    (All.add (All.sc _
        (All.sub (All.add (All.smul _ (WF1.sumA Φ (All.mul (WF0.aff Φ _ _) (WF0.aff Φ _ _))))
            (WF1.aff Φ _ _))
          (All.smul _ (All.mul (WF1.aff Φ _ _) (WF1.aff Φ _ _))))) (WF1.aff Φ _ _))
  places := by
    have hden : ∀ B, InAtt g (den3 g B : CForm E) := fun B =>
      AllPl.ite (fun hh => inAtt_cden g (bOf_lt hh) (wH_lt _) (wI_lt _)) fun _ => AllPl.cK _
    refine fam_places (All.add (All.sc _ (All.sub (All.add (All.smul _ (Pl1.sumA (All.mul
      (Pl0.aff fun B' _ =>
        AllPl.ite (fun hh => inAtt_cwtIJ g (bOf_lt hh.1) (wH_lt _) (wI_lt _)) fun _ => AllPl.cK _)
      (Pl0.aff fun B' _ => AllPl.ite (fun hh => inAtt_cval g (lam_lt (bOf_lt hh)) (wH_lt _) (by
        have h2 : (2 : ℕ) ^ DA.lT = DA.T := by decide
        exact h2 ▸ yOf_lt _ _) (wN_lt _)) fun _ => AllPl.cK _)))) (Pl1.aff fun B _ => hden B))
      (All.smul _
        (All.mul (Pl1.aff fun B _ => hden B)
          (Pl1.aff fun B _ =>
            AllPl.ite (fun hh => inAtt_cout g (bOf_lt hh) (wH_lt _) (wI_lt _) (wN_lt _))
              fun _ => AllPl.cK _)))))
      (Pl1.aff fun B _ =>
        pl_live (fun b hb y _ =>
          AllPl.ite (fun _ => (inAtt_cqh g hb (wH_lt _) (wI_lt _) (wN_lt _)).smul _)
        fun _ => (((inAtt_cden g hb (wH_lt _) (wI_lt _)).smul _).sub (AllPl.cK _)).sub ((inAtt_cqh' g hb (wH_lt _) (wI_lt _) (wN_lt _)).smul _)) B))

end Cm.Seg
