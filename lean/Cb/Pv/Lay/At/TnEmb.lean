-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/TnEmb.lean: the tensor claim on the embedding that the first group of layers adds, as a
pair of coefficients on the rows and on the columns of the committed matrix.

The claim reads the embedding's unit (Layout.uEmb) under two factors. On the vocabulary: for a token
v the sum of the equality weights of the positions that hold v. On the features: the equality weight
of the feature at a point of two parts, the blocks' coordinates pb and then the first ls coordinates
of pa. This file gives the two factors as descriptions (Inst/Model/LayoutSplit.lean), shows that
they fit, and concludes that the value of the claim's pair (tval in Cb/Pv/Lay/At/FootW.lean) is the
sum over blocks, places in a block and positions of the three equality weights times the embedding
of the position's token, in the form of Cb/Pv/Lay/EmbSide.lean.

Main names: psiOf, featPt, dsEmb, allOK_dsEmb, psi_sum, feat_weight, embTn, tenEmb, tenEmb_val.

The hypotheses: the width is nb blocks of 2^ls features, with nb at most 2^gB; the matrix has room
for all units. Nothing is asked of the tokens: at a position whose token is no word of the
vocabulary both sides have 0, since the library's embedding embR is 0 there.

Limits. That the programs' coefficients are these is not said.


-/
import Cb.Pv.Lay.At.TnSplit
import Cb.Pv.Lay.Routed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At

open Finset
open Inst.Model (Params entryW)
open Inst.Model.Layout (sOf units off rows first uEmb)
open Inst.Model.Layout.Tensor (FD AllOK matOf rows_fit sOf_le_of_le aligned_id)
open Inst.Model.FFSeg (embR)
open Blocks (eqN)

noncomputable section

variable {K : Type} [Field K]

/-- The factor on the vocabulary: the equality weights of the positions that hold the token v. -/
def psiOf (lT ls : ℕ) (pa : ℕ → K) (tok : ℕ → ℕ) (v : ℕ) : K :=
  ∑ p ∈ range (2 ^ lT), if tok p = v then eqN lT ls pa p else 0

/-- The point of the factor on the features: pb's first gB coordinates, then pa's. -/
def featPt (gB : ℕ) (pa pb : ℕ → K) (j : ℕ) : K := if j < gB then pb j else pa (j - gB)

/-- The descriptions of the two factors. -/
def dsEmb (lT ls gB : ℕ) (pa pb : ℕ → K) (tok : ℕ → ℕ) : List (FD K) :=
  [.whole (psiOf lT ls pa tok), .high (gB + ls) 0 (featPt gB pa pb) id]

/-- They fit the embedding's unit. -/
theorem allOK_dsEmb (P : Params) (lT ls gB nb : ℕ) (hd : P.d = nb * 2 ^ ls) (hnb : nb ≤ 2 ^ gB)
    (pa pb : ℕ → K) (tok : ℕ → ℕ) : AllOK (uEmb P).coords (dsEmb lT ls gB pa pb tok) := by
  refine ⟨rfl, ⟨rfl, ?_, aligned_id _ _⟩, trivial⟩
  show sOf P.d ≤ gB + ls
  rcases Nat.eq_zero_or_pos P.d with e | hp
  · rw [e]
    exact Nat.zero_le _
  · refine sOf_le_of_le hp ?_
    rw [hd, pow_add]
    exact Nat.mul_le_mul_right _ hnb

/-- A sum over the vocabulary under the first factor is a sum over the positions. A position whose
token is no word of the vocabulary adds nothing. -/
theorem psi_sum (lT ls V : ℕ) (pa : ℕ → K) (tok : ℕ → ℕ) (G : ℕ → K) :
    ∑ v ∈ range V, psiOf lT ls pa tok v * G v =
      ∑ p ∈ range (2 ^ lT), eqN lT ls pa p * if tok p < V then G (tok p) else 0 := by
  unfold psiOf
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun p _ => ?_
  by_cases ht : tok p < V
  · rw [if_pos ht, Finset.sum_eq_single (tok p)]
    · rw [if_pos rfl]
    · intro v _ hv
      rw [if_neg fun e => hv e.symm, zero_mul]
    · intro h0
      exact absurd (mem_range.mpr ht) h0
  · rw [if_neg ht, mul_zero]
    refine sum_eq_zero fun v hv => ?_
    rw [if_neg fun e => ht (by rw [e]; exact mem_range.mp hv), zero_mul]

/-- The second factor at the feature kh 2^ls + r. -/
theorem feat_weight (gB ls : ℕ) (pa pb : ℕ → K) (kh : ℕ) {r : ℕ} (hr : r < 2 ^ ls) :
    eqN (gB + ls) 0 (featPt gB pa pb) (kh * 2 ^ ls + r) = eqN gB 0 pb kh * eqN ls 0 pa r := by
  rw [Blocks.eqN_append' gB ls 0 (featPt gB pa pb) kh hr,
    eqN_congr' (off := 0) (off' := 0) (a := featPt gB pa pb) (a' := pb) (fun t ht => by
      unfold featPt
      rw [Nat.zero_add, if_pos ht]) kh,
    eqN_congr' (off := 0 + gB) (off' := 0) (a := featPt gB pa pb) (a' := pa) (fun t _ => by
      unfold featPt
      rw [Nat.zero_add, Nat.zero_add, if_neg (by omega), Nat.add_sub_cancel_left]) r]

/-- The functional of the claim on the embedding. -/
theorem embTn (P : Params) (k : ℕ) (W : ℕ → ℕ → K) (lT ls gB nb : ℕ) (hd : P.d = nb * 2 ^ ls)
    (pa pb : ℕ → K) (tok : ℕ → ℕ) :
    (⟨first P P.layers, uEmb P, (dsEmb lT ls gB pa pb tok).map FD.f⟩ :
        Inst.Model.TClaim K).Tn P k W =
      ∑ kh ∈ range nb, eqN gB 0 pb kh * ∑ r ∈ range (2 ^ ls), eqN ls 0 pa r *
        ∑ p ∈ range (2 ^ lT), eqN lT ls pa p * embR P k W (tok p) (kh * 2 ^ ls + r) := by
  have e0 : (⟨first P P.layers, uEmb P, (dsEmb lT ls gB pa pb tok).map FD.f⟩ :
        Inst.Model.TClaim K).Tn P k W =
      ∑ v ∈ range P.V, ∑ x ∈ range P.d, psiOf lT ls pa tok v *
        eqN (gB + ls) 0 (featPt gB pa pb) x * entryW P k W (first P P.layers) (uEmb P) [v, x] :=
    Inst.Model.TClaim.Tn_two P k W (first P P.layers) (uEmb P) ⟨P.V, .whole⟩ ⟨P.d, .high⟩ rfl _ _
  rw [e0, sum_comm, hd, Alg.sum_range_mul_add]
  refine sum_congr rfl fun kh hkh => ?_
  rw [mul_sum]
  refine sum_congr rfl fun r hr => ?_
  have hx : kh * 2 ^ ls + r < P.d := by
    rw [hd]
    have h1 : (kh + 1) * 2 ^ ls ≤ nb * 2 ^ ls := Nat.mul_le_mul_right _ (mem_range.mp hkh)
    have h2 := mem_range.mp hr
    rw [Nat.add_mul, Nat.one_mul] at h1
    omega
  have e1 : ∑ v ∈ range P.V, psiOf lT ls pa tok v *
        eqN (gB + ls) 0 (featPt gB pa pb) (kh * 2 ^ ls + r) *
        entryW P k W (first P P.layers) (uEmb P) [v, kh * 2 ^ ls + r] =
      ∑ v ∈ range P.V, psiOf lT ls pa tok v *
        (eqN (gB + ls) 0 (featPt gB pa pb) (kh * 2 ^ ls + r) *
          entryW P k W (first P P.layers) (uEmb P) [v, kh * 2 ^ ls + r]) :=
    sum_congr rfl fun v _ => mul_assoc _ _ _
  rw [e1, psi_sum lT ls P.V pa tok, feat_weight gB ls pa pb kh (mem_range.mp hr), mul_sum,
    mul_sum]
  refine sum_congr rfl fun p _ => ?_
  by_cases ht : tok p < P.V
  · have e2 : embR P k W (tok p) (kh * 2 ^ ls + r) =
        entryW P k W (first P P.layers) (uEmb P) [tok p, kh * 2 ^ ls + r] := by
      show (if tok p < P.V ∧ kh * 2 ^ ls + r < P.d then _ else 0) = _
      rw [if_pos ⟨ht, hx⟩]
      rfl
    rw [if_pos ht, e2]
    ring
  · have e2 : embR P k W (tok p) (kh * 2 ^ ls + r) = 0 := by
      show (if tok p < P.V ∧ kh * 2 ^ ls + r < P.d then _ else 0) = _
      rw [if_neg fun h => ht h.1]
    rw [if_neg ht, e2]
    ring

open Classical in
/-- The pair of the claim on the embedding. If the matrix has no room for the unit: zero. -/
def tenEmb (P : Params) (k h lT ls gB : ℕ) (pa pb : ℕ → K) (tok : ℕ → ℕ) :
    (Fin h → K) × ((Fin k → Bool) → K) :=
  if hr : off k (units P) (first P P.layers) + rows k (uEmb P) ≤ h
  then pairOf P k h _ _ (dsEmb lT ls gB pa pb tok) hr
  else (0, 0)

/-- The pair's value on the matrix. -/
theorem tenEmb_val (P : Params) (k h lT ls gB nb : ℕ) (hd : P.d = nb * 2 ^ ls) (hnb : nb ≤ 2 ^ gB)
    (pa pb : ℕ → K) (tok : ℕ → ℕ) (hH : off k (units P) (units P).length ≤ h) (W : ℕ → ℕ → K) :
    tval (tenEmb P k h lT ls gB pa pb tok) (matOf W) =
      ∑ kh ∈ range nb, eqN gB 0 pb kh * ∑ r ∈ range (2 ^ ls), eqN ls 0 pa r *
        ∑ p ∈ range (2 ^ lT), eqN lT ls pa p * embR P k W (tok p) (kh * 2 ^ ls + r) := by
  have hr := rows_fit k h (units P) _ _ (Inst.Model.Layout.Bridge.unit_emb P) hH
  unfold tenEmb
  rw [dif_pos hr, tval_pairOf P k h _ _ _ hr (allOK_dsEmb P lT ls gB nb hd hnb pa pb tok) W,
    embTn P k W lT ls gB nb hd pa pb tok]

end

end Cb.Pv.Lay.At
