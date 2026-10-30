-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttRows58.lean: the public weights and the start forms of the last four sumchecks
of the attention sub-proof, in the library's words.

A sumcheck of products of the attention sub-proof (OnBytes/Model/AttentionSums.lean) starts from a
form and ends in a row. The verifier makes the row from the weights W_b at the point of the
challenges (OnBytes/Model/AttentionDivide.lean: valueOnIn, scoreAtIndexIn, bitsIn). The library has
these weights as polynomials in the point (Wb in Inst/Model/Att/Sums.lean). This file shows that the
verifier's numbers read as the library's polynomials at the verifier's point, and what the start
forms are worth.

Main theorems.
 - eqPair_value, eqPts_value: the verifier's equality polynomial of two points reads as the
   library's eqPt. eqPt_agree: eqPt reads the first coordinates of its points alone.
 - weightOn, weightScore, weightBits: the weights of the value product on the diagonal tiles, of the
   score at the index and of the bits are Wb at the steps s12 and s16, and bitWt with 4 bits.
 - weightedSum_value: a sum of forms under public weights. startScore, startKey: the start forms of
   the score at the index and of the key at the index.

What a theorem on a weight takes as given: the lengths of the points, and that the verifier's points
and batching weights are the library's, coordinate by coordinate.

What this file does not claim. The summand of the sumcheck for the key at the index is not treated.
Nothing is said about a run of the verifier: the theorems are on the expressions that the text of
the three routines passes to sc3Row and sc3In. Nothing is said about probabilities or hiding.


-/
import Johnson.Road.Rows.AttEnds58Proofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff)
open OnBytes.Attention (Shape PW eqPair eqPts timesW scaled weightedSum sc3B Sc3)
open Inst.Model.AttSeg (Dim Calls Pub Wb eqPt eq1 sh wp yg yI)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The equality polynomial of two points -/

/-- One factor. -/
theorem eqPair_value (x y : E) : ρ.val (eqPair x y) = eq1 (ρ.val x) (ρ.val y) := by
  unfold eqPair eq1
  rw [ρ.add, ρ.mul, ρ.mul, ρ.sub, ρ.sub, ρ.one]

/-- **The verifier's equality polynomial of two points reads as the library's.** -/
theorem eqPts_value (x y : Array E) :
    ρ.val (eqPts x y) = eqPt x.size (pt ρ x) (pt ρ y) := by
  unfold eqPts eqPt
  generalize x.size = n
  induction n with
  | zero => simp [ρ.one]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ρ.mul, ih,
      prod_range_succ, eqPair_value]
    rfl

/-- The library's equality polynomial of two points reads their first n coordinates alone. -/
theorem eqPt_agree {n : ℕ} {u u' v v' : ℕ → K} (hu : ∀ k < n, u k = u' k)
    (hv : ∀ k < n, v k = v' k) : eqPt n u v = eqPt n u' v' := by
  unfold eqPt
  exact prod_congr rfl fun k hk => by rw [hu k (mem_range.mp hk), hv k (mem_range.mp hk)]

/-- The equality polynomial of a point x and the part of r from a on, read in the library's
letters. -/
theorem eqPts_cut {x r : Array E} {a n : ℕ} {u : ℕ → K} (hx : x.size = n)
    (hr : a + n ≤ r.size) (hu : ∀ k < n, pt ρ x k = u k) :
    ρ.val (eqPts x (r.extract a (a + n))) = eqPt n u (sh (pt ρ r) a) := by
  rw [eqPts_value, hx]
  exact eqPt_agree hu fun k hk => pt_extract ρ r hr (by omega)

/-! ## The weights -/

/-- **The weight of pair b in the score at the index.** -/
theorem weightScore (D : Dim) (C : Calls) (p : Pub K) {om tg ti r : Array E} {b : ℕ}
    (hb : b < om.size) (htg : tg.size = D.lg) (hti : ti.size = D.lT)
    (hr : D.lT + D.lg ≤ r.size) (ho : ρ.val (om.getD b zeroE) = p.o b)
    (hg : ∀ k < D.lg, pt ρ tg k = p.tg k) (hi : ∀ k < D.lT, pt ρ ti k = p.ti k) :
    ρ.val ((scaled om (mulE (eqPts tg (r.extract D.lT (D.lT + D.lg)))
      (eqPts ti (r.extract 0 D.lT)))).getD b zeroE) = Wb D C p .s16 b (pt ρ r) := by
  unfold scaled
  rw [getD_map_lt om _ hb zeroE zeroE, ρ.mul, ρ.mul, ho, eqPts_cut ρ htg hr hg]
  have e : ρ.val (eqPts ti (r.extract 0 D.lT)) = eqPt D.lT p.ti (pt ρ r) := by
    have e0 := eqPts_cut ρ (r := r) (a := 0) hti (by omega) hi
    rw [Nat.zero_add] at e0
    rw [e0]
    exact eqPt_agree (fun _ _ => rfl) fun k _ => by
      show pt ρ r (0 + k) = pt ρ r k
      rw [Nat.zero_add]
  rw [e]
  show _ = p.o b * eqPt D.lg p.tg (sh (pt ρ r) D.lT) * eqPt D.lT p.ti (pt ρ r)
  ring

/-- **The weight of pair b in the bits of the index**, with the verifier's 4 bits for the number of
a bit. -/
theorem weightBits (D : Dim) (p : Pub K) {om5 tk tbg tbi r : Array E} {b : ℕ}
    (hb : b < om5.size) (htk : tk.size = 4) (htg : tbg.size = D.lg) (hti : tbi.size = D.lT)
    (hr : D.lT + D.lg + 4 ≤ r.size) (ho : ρ.val (om5.getD b zeroE) = p.o'' b)
    (hk : ∀ k < 4, pt ρ tk k = p.tk k) (hg : ∀ k < D.lg, pt ρ tbg k = p.tbg k)
    (hi : ∀ k < D.lT, pt ρ tbi k = p.tbi k) :
    ρ.val ((scaled om5 (mulE (mulE (eqPts tbi (r.extract 0 D.lT))
      (eqPts tbg (r.extract D.lT (D.lT + D.lg))))
      (eqPts tk (r.extract (D.lT + D.lg) (D.lT + D.lg + 4))))).getD b zeroE) =
      bitWt 4 D p b (pt ρ r) := by
  unfold scaled
  rw [getD_map_lt om5 _ hb zeroE zeroE, ρ.mul, ρ.mul, ρ.mul, ho,
    eqPts_cut ρ htg (by omega) hg, eqPts_cut ρ htk hr hk]
  have e : ρ.val (eqPts tbi (r.extract 0 D.lT)) = eqPt D.lT p.tbi (pt ρ r) := by
    have e0 := eqPts_cut ρ (r := r) (a := 0) hti (by omega) hi
    rw [Nat.zero_add] at e0
    rw [e0]
    exact eqPt_agree (fun _ _ => rfl) fun k _ => by
      show pt ρ r (0 + k) = pt ρ r k
      rw [Nat.zero_add]
  rw [e]
  unfold bitWt
  ring

/-- **The weight of pair b in the value product on the diagonal tiles.** -/
theorem weightOn (D : Dim) (C : Calls) (p : Pub K) {pwW : Array PW} {zgW zihi r : Array E} {b : ℕ}
    (hb : b < pwW.size) (hzg : zgW.size = D.lg) (hzi : zihi.size = D.lP + 1)
    (hr : D.lg + (D.lP + 1) ≤ r.size)
    (hw : ρ.val (pwW.getD b default).wp = wp D C p.z .w3 b)
    (hg : ∀ k < D.lg, pt ρ zgW k = yg D C p.z k)
    (hi : ∀ k < D.lP + 1, pt ρ zihi k = yI D C p.z k) :
    ρ.val ((timesW pwW (mulE (eqPts zgW (r.extract 0 D.lg))
      (eqPts zihi (r.extract D.lg (D.lg + (D.lP + 1)))))).getD b zeroE) =
      Wb D C p .s12 b (pt ρ r) := by
  unfold timesW
  rw [getD_map_lt pwW _ hb zeroE default, ρ.mul, ρ.mul, hw, eqPts_cut ρ hzi hr hi]
  have e : ρ.val (eqPts zgW (r.extract 0 D.lg)) = eqPt D.lg (yg D C p.z) (pt ρ r) := by
    have e0 := eqPts_cut ρ (r := r) (a := 0) hzg (by omega) hg
    rw [Nat.zero_add] at e0
    rw [e0]
    exact eqPt_agree (fun _ _ => rfl) fun k _ => by
      show pt ρ r (0 + k) = pt ρ r k
      rw [Nat.zero_add]
  rw [e]
  show _ = wp D C p.z .w3 b * eqPt D.lg (yg D C p.z) (pt ρ r) *
    eqPt (D.lP + 1) (yI D C p.z) (sh (pt ρ r) D.lg)
  ring

/-! ## The start forms -/

variable (W : World K)

/-- **A sum of forms under public weights.** -/
theorem weightedSum_value (n : ℕ) (w : Array E) (form : ℕ → Aff) :
    (weightedSum n w form).value ρ W =
      ∑ b ∈ range n, ρ.val (w.getD b zeroE) * (form b).value ρ W := by
  unfold weightedSum
  induction n with
  | zero => simp [Aff.value_ofConst, ρ.zero]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Aff.value_addMul, ih,
      sum_range_succ]

/-- The start form of the score at the index: the batch of the values sent for the row maxima. -/
theorem startScore (n sM6 : ℕ) (om : Array E) :
    (weightedSum n om fun b => Aff.slot (sM6 + b)).value ρ W =
      ∑ b ∈ range n, ρ.val (om.getD b zeroE) * W.slot (sM6 + b) := by
  rw [weightedSum_value]
  exact sum_congr rfl fun b _ => by rw [Aff.value_slot]

/-- The start form of the key at the index: the batch of the second end values of the score at the
index. -/
theorem startKey (n : ℕ) (om4 : Array E) (scF : Sc3) :
    (weightedSum n om4 (sc3B scF)).value ρ W =
      ∑ b ∈ range n, ρ.val (om4.getD b zeroE) * W.slot (scF.sEnd + (2 * b + 1)) := by
  rw [weightedSum_value]
  exact sum_congr rfl fun b _ => by
    rw [show (sc3B scF b).value ρ W = W.slot (scF.sEnd + (2 * b + 1)) from Aff.value_slot ρ W _]

end OnBytes.Road.Rows
