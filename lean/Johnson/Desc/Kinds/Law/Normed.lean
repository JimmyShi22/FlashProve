-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Normed.lean: THE LAW OF THE FINAL NORMALIZATION's SUMCHECK "normed": STATED AND PROVED.
"normed" (HeadNorm.lean: hear) is a masked sumcheck at the lookup's point zt of the reciprocal times the
weighted stream. Its claimed sum stands in the key remLow. THE STATEMENT (NormedStatement): the cells, the
mask entries, the ledger in front and the letters that come in stand in front of "there is a rule"; then: at
a hearing that returns, in a world whose slots hold the hidden scalars AT THE SUMCHECK's OWN NUMBERS (no other
number is asked: a world read off a later ledger serves), with normedForms' three forms 0, two
reads true below the lengths that the forms spend, and no bad draw: THE CLAIMED SUM's HIDDEN SCALAR IS THE TRUE
SUM (HeadNormLaw.lean: trueNormed): the last field of HeadOutLaw.lean's NormTrue.
THE RULE HAS A NAME (normedRule), and the law is said of it (normed_at): so that it can later be shown empty at an
honest run; the statement with "there is a rule" follows.
THE SUMCHECK IS NOT PROVED AGAIN: Law/SumLaw.lean's coreG, which is sound_hear at HeadParts.lean's
"sumcheck z n". Here: the two tables; that their product's sum at zt is trueNormed; that the second and third
form say that the end values are the tables' extensions at the challenges.
IMPORTED, NOT THIS FILE's: HeadNormLaw.lean, Law/NormProof.lean (recZ, str, rd_R's way);
P6/NormRowLaw.lean (Rlo_value, Rhi_value, sm_value), MaskedSumProducts.lean (isSum_product, product_at);
Law/Mle.lean (mle_idx, tot_pairs), Law/Ints.lean (sumZ_eq).
WHAT IT DOES NOT SAY. That the reads are true (the range check's); that the forms are 0 (the batching's and the
last equation's); time; how probable a bad draw is: lists are counted.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.SumLaw
import Johnson.Desc.Kinds.Law.NormKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Aff Fork Reading World)
open Norm (lt ls d lPd T S2)
open Came (val)

/-- The two reads that normedForms spend, each below the length spent. -/
structure NormedReads [Sizes] [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]
    (W : World K) (c : NCells) : Prop where
  row : ∀ j, j < NR → val W (FinalNorm.entry .rowAtNormed j)
    = rd (readAtN c (.row, .short (eq FinalNorm.normed.r)) j)
  stream : ∀ i, i < 5 * d / S2 → val W (FinalNorm.entry .streamAtNormed i)
    = rd (readAtN c (.stream, .long (eq FinalNorm.zl) (eq FinalNorm.normed.r)) i)

/-- What the law says of a rule. -/
def NormedAt [Sizes] [Policy] [Request] [Token] [FinalNorm.In] (c : NCells) (mask : Nat → E)
    (F0 : Fork) (bad : List Fmt.RoundView → List E) : Prop :=
  ∀ (F1 : Fork) (t : List Fmt.RoundView) (S : Sum) (W : World K) [Norm.Heard] [FinalNorm.Reads],
    (∀ j, F0.next ≤ j → j < Came.sEndG FinalNorm.zt 2 F0 + 2 →
      W.slot j = rd (hidden F1 mask j)) → Canonical t →
    sumcheck FinalNorm.zt 2 F0 t = some (S, F1, []) →
    let _ : FinalNorm.Heard := { normed := S }
    NormedReads W c → (∀ f, f ∈ FinalNorm.normedForms → val W f = 0) → NoBad bad t →
    val W FinalNorm.normed.claimed.var = rd (trueNormed c)

/-- **THE LAW OF "normed".** -/
def NormedStatement : Prop :=
  ∀ [Sizes] [Policy] [Request] [Token] [FinalNorm.In] (c : NCells) (mask : Nat → E) (F0 : Fork),
    WellLaid F0 → (FinalNorm.zt).size = lt → S2 ∣ d →
    (∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2)) →
    ∃ bad : List Fmt.RoundView → List E,
      (∀ h, (bad h).length ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1) ∧
      NormedAt c mask F0 bad

namespace Came

open OnBytes.Desc.First.P1 (mle tot ext1 IsSum)
open Part.MaskedSum (Var Call weightsOf)

/-! ## Sums -/

theorem spr_sum {n m : Nat} {u w : Nat → K} (k : Nat) (a : Nat → K) (g : Nat → Nat → Nat → K) :
    ((Finset.range k).sum fun l => a l * spr n m u w (g l))
      = spr n m u w fun x t => (Finset.range k).sum fun l => a l * g l x t := by
  unfold spr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  exact Finset.sum_congr rfl fun l _ => by ring

theorem spr_swap {n m : Nat} {u w : Nat → K} (g : Nat → Nat → K) :
    spr n m u w g = (Finset.range m).sum fun t => w t * (Finset.range n).sum fun x => u x * g x t := by
  unfold spr
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- Blocks of S entries under a block's weight and a weight inside the block. -/
theorem blocks_spr {S D m : Nat} (hS : 0 < S) (hd : S ∣ D) (u eh zl' w : Nat → K)
    (hU : ∀ i j, i < D / S → j < S → u (S * i + j) = eh i * zl' j) (g : Nat → Nat → K) :
    ((Finset.range (D / S)).sum fun i => eh i * (Finset.range S).sum fun j =>
        (Finset.range m).sum fun t => zl' j * w t * g (S * i + j) t)
      = spr D m u w g := by
  have hb := sum_blocks S (fun x => (Finset.range m).sum fun t => u x * w t * g x t) (D / S)
  rw [Nat.div_mul_cancel hd] at hb
  unfold spr
  rw [← hb]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hU i j (Finset.mem_range.1 hi) (Finset.mem_range.1 hj)]
  ring

/-- The reciprocal is linear in six digits. -/
theorem ledgerR (D : Nat → K) : Inst.Model.Ledger.Rlo D + ((2 ^ 24 : Nat) : K) * Inst.Model.Ledger.Rhi D
    = D 80 + 256 * D 81 + 256 ^ 2 * D 82 + 2 ^ 24 * (D 83 + 256 * D 84 + 256 ^ 2 * D 85) := by
  simp only [Inst.Model.Ledger.Rlo, Inst.Model.Ledger.Rhi, Inst.Model.Ledger.b256,
    Finset.sum_range_succ, Finset.sum_range_zero]
  push_cast
  ring

section Letters
variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In]

/-- The two tables: the reciprocal; the stream under the weights of the key remLow. -/
def AtN (c : NCells) : List Bool → K := fun b => ((recZ c (idxOf b) : Int) : K)
@[inherit_doc AtN] def BtN (c : NCells) : List Bool → K := fun b =>
  (Finset.range d).sum fun x => UN .remLow x * ((str c (idxOf b) x : Int) : K)

variable (c : NCells) (mask : Nat → E) (F0 : Fork)

/-- The summand, the further variable last. -/
def SmN : List K → K := fun rs =>
  mle ((vsG FinalNorm.zt).length + 1)
      (ext1 (vsG FinalNorm.zt).length (AtN c) (rd (mask (sEndG FinalNorm.zt 2 F0)))) rs *
    mle ((vsG FinalNorm.zt).length + 1)
      (ext1 (vsG FinalNorm.zt).length (BtN c) (rd (mask (sEndG FinalNorm.zt 2 F0 + 1)))) rs

def sigN : K := tot (weightsOf Reading.gl (vsG FinalNorm.zt)) fun b => AtN c b * BtN c b

theorem hSN : IsSum ((⟨1, vsG FinalNorm.zt, some ⟨2, 2⟩⟩ : Call).all.map (Var.wt Reading.gl))
    (SmN c mask F0) (sigN c) :=
  Part.MaskedSum.isSum_product Reading.gl 1 (vsG FinalNorm.zt) 2
    (fun v hv => by rw [vsG_d _ v hv]) _ _ _ _

theorem vsG_length (z : Point) : (vsG z).length = z.size := by
  unfold vsG
  rw [List.length_map, Array.length_toList]

/-- An extension at a point of lt coordinates, as a sum over the positions. -/
theorem mle_point (z : Point) (hz : z.size = lt) (g : Nat → K) :
    mle lt (fun b => g (idxOf b)) (z.toList.map rd)
      = (Finset.range T).sum fun t => rd (eq z t) * g t := by
  have h := mle_idx (z.toList.map rd) g
  rw [List.length_map, Array.length_toList, hz] at h
  rw [h]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [rd_eq, hz, if_pos (show t < 2 ^ lt from Finset.mem_range.1 ht)]

/-- The tables' product, summed at zt, is the true sum. -/
theorem sigN_eq (hzt : (FinalNorm.zt).size = lt) : sigN c = rd (trueNormed c) := by
  have hw : weightsOf Reading.gl (vsG FinalNorm.zt)
      = ((FinalNorm.zt).toList.map rd).map fun x => (1 - x, x) := by
    unfold weightsOf vsG
    simp only [List.map_map]
    rfl
  unfold sigN
  rw [hw, tot_pairs, List.length_map, Array.length_toList, hzt]
  have h := mle_point FinalNorm.zt hzt fun t => ((recZ c t : Int) : K) *
    (Finset.range d).sum fun x => UN .remLow x * ((str c t x : Int) : K)
  refine Eq.trans h ?_
  -- three classes that the called lemma carries and does not read
  letI : Norm.Heard := normHeardAt c #[]
  letI : FinalNorm.Heard := finalHeardAt c
  letI : FinalNorm.Reads := normReadsAtCells c
  rw [rd_trueNormed', spr_swap]
  refine Finset.sum_congr rfl fun t _ => ?_
  show rd (eq FinalNorm.zt t) * _ = WN t * _
  unfold WN
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  push_cast
  ring

/-- **THE RULE OF "normed", BY NAME**: Law/SumLaw.lean's rule at this sumcheck's summand: its sets are sound_hear_true's (Johnson/Desc/Part/MaskedSumTruth.lean),
empty at the truth (bEG_empty, bdG_empty). -/
def normedRule : List Fmt.RoundView → List E :=
  badG FinalNorm.zt 2 (by omega) (SmN c mask F0) (sigN c) (hSN c mask F0) mask F0

theorem normedRule_length (h : List Fmt.RoundView) : (normedRule c mask F0 h).length
    ≤ ((h.getLast?.map fun r => r.vals.length).getD 0) + 1 := badG_length _ _ _ _ _ _ _ _ h

end Letters

/-- **THE LAW OF "normed", AT ITS RULE BY NAME.** -/
theorem normed_at [Sizes] [Policy] [Request] [Token] [FinalNorm.In] (c : NCells) (mask : Nat → E)
    (F0 : Fork) (hWL : WellLaid F0) (hzt : (FinalNorm.zt).size = lt) (hd : S2 ∣ d)
    (hblock : ∀ x, x < d →
      FinalNorm.ew .remLow x = FinalNorm.ewh .remLow (x / S2) * eq FinalNorm.zl (x % S2)) :
    NormedAt c mask F0 (normedRule c mask F0) := by
  intro F1 t S W _ _ hWs hcan hsum _ hreads hforms hnb
  have hS2 : 0 < S2 := S2_posN
  have hr : S.r.size = lt := by rw [sum_r_size hsum, hzt]
  have hw1 : (Finset.range T).sum (fun t => rd (eq S.r t)) = 1 := by
    have h := sum_rd_eq S.r
    rwa [hr] at h
  -- the three forms
  have f1 : val W (S.left ((S.end_ 0).shown * (S.end_ 1).shown)) = 0 :=
    hforms _ (by simp [FinalNorm.normedForms]; left; rfl)
  have f2 : val W ((S.end_ 0).var
      - (OnBytes.Desc.First.P6.Row.ofDigits fun j => FinalNorm.entry .rowAtNormed j + off1).R) = 0 :=
    hforms _ (by simp [FinalNorm.normedForms]; right; left; rfl)
  have f3 : val W ((S.end_ 1).var - sumTo (d / S2) fun i => sumTo 5 fun l =>
      ((256 : E) ^ l * FinalNorm.ewh .remLow i) • FinalNorm.entry .streamAtNormed (l * d / S2 + i))
      = 0 :=
    hforms _ (by simp [FinalNorm.normedForms]; right; right; rfl)
  -- the first end value is the reciprocal's extension at the challenges
  have g2 : val W (S.end_ 0).var = mle lt (AtN c) (S.r.toList.map rd) := by
    rw [val_sub] at f2
    rw [sub_eq_zero.1 f2]
    have hD : ∀ j, j < NR → OnBytes.Desc.First.P6.dv Reading.gl W
        (fun j => FinalNorm.entry .rowAtNormed j + off1) j
        = (Finset.range T).sum fun t => rd (eq S.r t) * ((digZ c t j : Int) : K) := by
      intro j hj
      show val W (FinalNorm.entry .rowAtNormed j + off1) = _
      rw [val_add, val_natCast, hreads.row j hj]
      show rd (sumTo T fun t => eq S.r t * ofInt (c.cell .row j t)) + _ = _
      rw [rd_sumTo]
      have h128 : ((off1 : Nat) : K) = (Finset.range T).sum fun t => rd (eq S.r t) * ((off1 : Nat) : K) := by
        rw [← Finset.sum_mul, hw1, one_mul]
      rw [h128, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [rd_mul, rd_ofInt]
      unfold digZ off1
      push_cast
      ring
    show Aff.value Reading.gl W
      ((OnBytes.Desc.First.P6.Row.ofDigits fun j => FinalNorm.entry .rowAtNormed j + off1).Rlo
        + OnBytes.Desc.First.P6.sm (2 ^ 24)
          (OnBytes.Desc.First.P6.Row.ofDigits fun j => FinalNorm.entry .rowAtNormed j + off1).Rhi) = _
    rw [Aff.value_add, OnBytes.Desc.First.P6.sm_value, OnBytes.Desc.First.P6.Rlo_value,
      OnBytes.Desc.First.P6.Rhi_value, ledgerR,
      hD 80 (by unfold NR; omega), hD 81 (by unfold NR; omega), hD 82 (by unfold NR; omega),
      hD 83 (by unfold NR; omega), hD 84 (by unfold NR; omega), hD 85 (by unfold NR; omega)]
    have hm := mle_point S.r hr fun t => ((recZ c t : Int) : K)
    refine Eq.trans ?_ hm.symm
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hR := Inst.Model.Ledger.map_R (Int.castRingHom K) (digZ c t)
    simp only [eq_intCast] at hR
    unfold recZ
    rw [hR]
    have hl := ledgerR fun m => ((digZ c t m : Int) : K)
    unfold Inst.Model.Ledger.R
    have h24 : ((2 ^ 24 : Nat) : K) = 2 ^ 24 := by push_cast; rfl
    rw [h24] at hl
    rw [hl]
    ring
  -- the second is the weighted stream's
  have g3 : val W (S.end_ 1).var = mle lt (BtN c) (S.r.toList.map rd) := by
    rw [val_sub] at f3
    rw [sub_eq_zero.1 f3]
    have hm := mle_point S.r hr fun t =>
      (Finset.range d).sum fun x => UN .remLow x * ((str c t x : Int) : K)
    refine Eq.trans ?_ hm.symm
    rw [← spr_swap (u := UN .remLow) (w := fun t => rd (eq S.r t))
      (fun x t => ((str c t x : Int) : K))]
    have hstr : ∀ x t, ((str c t x : Int) : K)
        = (Finset.range 5).sum fun l => (256 : K) ^ l * ((c.stream (l * d + x) t : Int) : K) := by
      intro x t
      unfold str limbZ
      rw [sumZ_eq]
      push_cast
      rfl
    simp only [hstr]
    rw [← spr_sum 5 (fun l => (256 : K) ^ l) fun l x t => ((c.stream (l * d + x) t : Int) : K)]
    rw [val_sumTo]
    simp only [val_sumTo]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l hl => ?_
    have hl5 := Finset.mem_range.1 hl
    rw [← blocks_spr hS2 hd (UN .remLow) (fun i => rd (FinalNorm.ewh .remLow i))
      (fun j => rd (eq FinalNorm.zl j)) (fun t => rd (eq S.r t)) ?_
      (fun x t => ((c.stream (l * d + x) t : Int) : K)), Finset.mul_sum]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      have hdl : S2 ∣ l * d := Dvd.dvd.mul_left hd l
      have hidx : l * d / S2 + i < 5 * d / S2 := by
        obtain ⟨a, ha⟩ := hdl
        obtain ⟨b, hb⟩ := hd
        rw [ha, Nat.mul_div_cancel_left _ hS2]
        apply (Nat.le_div_iff_mul_le hS2).2
        have h1 : (i + 1) * S2 ≤ d / S2 * S2 := Nat.mul_le_mul_right _ hi'
        rw [Nat.div_mul_cancel ⟨b, hb⟩] at h1
        have h2 : l * d ≤ 4 * d := Nat.mul_le_mul_right d (by omega)
        have h3 : (a + i + 1) * S2 = S2 * a + (i + 1) * S2 := by ring
        rw [h3, ← ha]
        omega
      rw [val_smulE, rd_mul, rd_pow, rd_ofNat, hreads.stream _ hidx]
      show _ * rd (sumTo S2 fun j => sumTo T fun t =>
        eq FinalNorm.zl j * eq S.r t * ofInt (c.stream (S2 * (l * d / S2 + i) + j) t)) = _
      rw [rd_sumTo]
      have hin : ∀ j, rd (sumTo T fun t =>
          eq FinalNorm.zl j * eq S.r t * ofInt (c.stream (S2 * (l * d / S2 + i) + j) t))
          = (Finset.range T).sum fun t => rd (eq FinalNorm.zl j) * rd (eq S.r t)
            * ((c.stream (l * d + (S2 * i + j)) t : Int) : K) := by
        intro j
        rw [rd_sumTo]
        refine Finset.sum_congr rfl fun t _ => ?_
        have e : S2 * (l * d / S2 + i) + j = l * d + (S2 * i + j) := by
          rw [Nat.mul_add, Nat.mul_div_cancel' hdl, Nat.add_assoc]
        rw [rd_mul, rd_mul, rd_ofInt, e]
      simp only [hin]
      push_cast
      ring
    · intro i j hi hj
      have hlt : S2 * i + j < d := by
        have h1 : (i + 1) * S2 ≤ d / S2 * S2 := Nat.mul_le_mul_right _ hi
        rw [Nat.div_mul_cancel hd, Nat.add_mul, Nat.one_mul, Nat.mul_comm] at h1
        omega
      have h1 : (S2 * i + j) / S2 = i := by
        rw [Nat.mul_add_div hS2, Nat.div_eq_of_lt hj, Nat.add_zero]
      have h2 : (S2 * i + j) % S2 = j := by
        rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
      unfold UN
      rw [hblock _ hlt, rd_mul, h1, h2]
  have hres := coreG FinalNorm.zt 2 (by omega) (SmN c mask F0) (sigN c) (hSN c mask F0) mask F0 hWL W
    hWs hcan hsum ((S.end_ 0).shown * (S.end_ 1).shown) f1 (fun β hβ => by
      unfold SmN
      rw [Part.MaskedSum.product_at (vsG FinalNorm.zt).length _ _ _ _ _ _
        (by rw [List.length_map, Array.length_toList, hr, vsG_length, hzt]), rd_mul,
        hβ 0 (by omega), hβ 1 (by omega), vsG_length, hzt, ← g2, ← g3, Nat.add_zero]
      rfl) hnb
  rw [← sigN_eq c hzt]
  exact hres

/-- **THE LAW OF "normed".** -/
theorem normed_law : NormedStatement := fun c mask F0 hWL hzt hd hblock =>
  ⟨normedRule c mask F0, normedRule_length c mask F0, normed_at c mask F0 hWL hzt hd hblock⟩

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.normed_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.normed_law
