-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysV.lean: the form of the segment V plus the matrix products in its keys.

The key of the family V is the low key of a rounding whose accumulator is an inner product of the
array a with a column of the weight matrix Wv. The verifier's form of the segment holds the part of
the key that is affine in the cells (Johnson/Road/FormsKeysA.lean, Fits.line_V). The accumulator is
left to a panel of the batched sumcheck. This file adds to the form's value the matrix products of
the keys, written on the library's own objects in the shape in which a row of that panel would hold
them: the factor 2^max(0, 16 - kv), times the sum over the channels j of the extension of a[lam, j]
times the sum over the segment's entries x of the weight of x times Wv[j][x]. The sum of the two is
the weighted sum of the extensions of the whole keys.

No panel of the verifier stands in a statement of this file. What the verifier's panel of the
segment V holds is said in Johnson/Road/FormsKeysPan.lean (panelV_spec): its A side and its rows'
weights are worth the first factor and the factor 2^max(0, 16 - kv) here.

Main theorems: acc_V, Fits.whole_V.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. That the sumcheck shows the panel's sum,
and that the weight claim which the panel leaves says what the B side stands for, is not touched.
The program does not import this file.
-/
import Johnson.Road.FormsKeysA

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Arr Fam LW key lin term mat len valU)

variable {K : Type} [Field K] [scl : Scl]

/-- The matrix products in the keys of the family V at layer l, summed under weights g: the factor
2^max(0, 16 - kv) times the sum over the channels j of the extension of a[l, j] times the column
sums of Wv under g. -/
theorem acc_V (D : Dim) (t : Cell → K) (w : ℕ → LW K) (g : ℕ → K) (u : ℕ → K) (l : ℕ) :
    wsum g D.lT u D.dkv (fun x i => mat D t w .V l x i) =
      Inst.Model.Site.scl (D.Pl l).kv
        (∑ j ∈ range D.d, valU D t .a l j u * ∑ x ∈ range D.dkv, g x * (w l).Wv j x) := by
  have e : ∀ x, Blocks.ext D.lT (fun i => mat D t w .V l x i) u =
      (2 : K) ^ Inst.Model.Site.dn (D.Pl l).kv *
        ∑ j ∈ range D.d, valU D t .a l j u * (w l).Wv j x := by
    intro x
    simp only [mat, Inst.Model.Site.scl_eq, Inst.Model.FFSeg.Av]
    rw [Blocks.ext_smul, Blocks.ext_sum]
    congr 1
    refine sum_congr rfl fun j _ => ?_
    have c : (fun i => Inst.Model.FFSeg.val t .a l j i * (w l).Wv j x) =
        fun i => (w l).Wv j x * Inst.Model.FFSeg.val t .a l j i := by
      funext i
      ring
    rw [c, Blocks.ext_smul]
    unfold valU
    ring
  unfold wsum
  simp only [e, Inst.Model.Site.scl_eq, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  refine sum_congr rfl fun x _ => ?_
  ring

variable {ρ : Reading K} {W : World K} {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K}

/-- The family V, whole: the value of the segment's form plus the matrix products of the keys,
written as a row of a panel would hold them, is the weighted sum of the extensions of the library's
keys. -/
theorem Fits.whole_V (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (lam : ℕ)
    (hlam : lam < D.nl) {ew wh : Array E} (hw : Wts ρ ew wh v.y.ls low D.dkv) {f : Aff}
    (h : v.line "V" lam ew wh = some f) :
    f.value ρ W + Inst.Model.Site.scl (D.Pl lam).kv
        (∑ j ∈ range D.d, valU D t .a lam j u * ∑ x ∈ range D.dkv, wt ρ ew x * (w lam).Wv j x) =
      ∑ x ∈ range (len D .V), ρ.val (ew.getD x zeroE) *
        Blocks.ext D.lT (fun i => key D t tb L0 w .V lam x i) u := by
  have e : ∀ x, x < D.dkv → ∀ i, key D t tb L0 w .V lam x i =
      lin D t tb L0 w .V lam x i + mat D t w .V lam x i := by
    intro x _ i
    rw [Inst.Model.FFSeg.key_eq]
    simp [term]
  show _ = wsum (wt ρ ew) D.lT u D.dkv (fun x i => key D t tb L0 w .V lam x i)
  rw [wsum_congr _ _ _ _ e, wsum_add, acc_V, F.line_V tb L0 w lam hlam hw h]
  rfl

#print axioms Fits.whole_V

end OnBytes.Road
