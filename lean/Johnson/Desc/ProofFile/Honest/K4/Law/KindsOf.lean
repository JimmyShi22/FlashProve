-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/KindsOf.lean: CONDITIONAL.

What is here. THE HYPOTHESIS `Kinds` (TripsOf.lean) AT A TOKEN POINT AND THE TOKENS' CORNERS, under
the point's equality weights: a form's value on the honest reads (Johnson/Road/K4/C/TermsOpen.lean:
`valAffQ_tok`); an entry of a weights' table (Johnson/Road/K4/C/TokTables.lean: `tok_tables`); the
gated products summed over the tokens under the point's weights (here); a constant form's value
(here); the weights' sum (the library's `sum_eqN_one`). And with it `TripsAt` (TermsTrips.lean) by
TripsWhole.lean. Statements and proofs.

  `val_const`   a constant form's value
  `gated_tok`   **the gated products under the point's weights**
  `kinds_of`   **`Kinds`**
  `tripsAt_at`   **`TripsAt`**

Limits. At the reading `Reading.gl`. Premises, on public data, on returns, and on the sizes of a
sampled point and of a table of the input's products: the verifier's list of tables is laid; every
family of that list is of a sort that `TokAsk` names; the structure that the forms read has the
plan's layout; the lookup's low coordinates are ls in number; the point has lt coordinates; there
are 2 ^ lt tokens, and at most so many by the structure that the rotation factor reads; THE TABLE OF
GATED PRODUCTS HAS A WHOLE NUMBER OF ROWS OF T ENTRIES; the reads are made at the point and at each
corner (for `tripsAt_at` the tokens' rows pay the corners'). For `tripsAt_at` besides: the public
test `triPlainB`; the tokens' rows are made; the products at the point are made at all values in the
place of the shown factors. No example of the premises together is known at the full size. From
`TermsPub` and the tokens' rows the premises of `tripsAt_at` follow by a theorem (TermsAll.lean's
`terms_tripsAt`). No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.TripsWhole
import Johnson.Road.K4.C.TokTables
import Johnson.Road.FormsKeysEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE maddE)
open OnBytes.Model (Reading Aff eqTab)
open OnBytes.Model.Layer (Env TableAsk TableAt layTables tableAsks)
open OnBytes.Road (pt eqTab_value sum_eqN_one)
open OnBytes.Road.K4.C (TokAsks valAffQ_tok valAffQ_some tok_tables tok_tables_plain gl_foldl_maddE
  range_sum)
open OnBytes.Desc.First.K4.Honest

/-- A constant form's value is the constant, on all reads. -/
theorem val_const (v : Env) (R : Reads) (slot : ℕ → E) (c x : E)
    (h : valAff? v R slot (Aff.ofConst c) = some x) : x = c := by
  rw [((valAffQ_some v R slot _ x).mp h).2]
  rfl

/-- **The gated products summed over the tokens under a point's equality weights** are the
combination, under these weights, of the gated products at the tokens. i: the row's number. -/
theorem gated_tok (S : Sides) {z : Array E} (hz : z.size = S.v.y.h.lt)
    (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hdiv : S.hh.size % S.v.y.T = 0) (i : ℕ) :
    Reading.gl.val ((S.gatedUnder (eqTab z)).getD i zeroE) =
      ∑ t ∈ Finset.range (2 ^ S.v.y.h.lt), Blocks.eqN S.v.y.h.lt 0 (pt Reading.gl z) t *
        Reading.gl.val (S.hh.getD (i * S.v.y.T + t) zeroE) := by
  have pos : 0 < S.v.y.T := by
    rw [hT]
    exact Nat.two_pow_pos _
  unfold Sides.gatedUnder
  dsimp only
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_map]
  by_cases hi : i < S.hh.size / S.v.y.T
  · rw [Array.getElem?_range, if_pos hi]
    show Reading.gl.val ((List.range S.v.y.T).foldl
      (fun s t => maddE s ((eqTab z).getD t zeroE) (S.hh.getD (i * S.v.y.T + t) zeroE)) zeroE) = _
    rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum, hT]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [eqTab_value Reading.gl z t (by rw [hz]; exact Finset.mem_range.mp ht), hz]
  · rw [Array.getElem?_eq_none (by rw [Array.size_range]; omega)]
    show Reading.gl.val zeroE = _
    rw [Reading.gl.zero]
    refine (Finset.sum_eq_zero fun t _ => ?_).symm
    have hge : S.hh.size ≤ i * S.v.y.T + t := by
      have h1 : S.hh.size / S.v.y.T ≤ i := Nat.le_of_not_lt hi
      have h2 : S.hh.size = S.v.y.T * (S.hh.size / S.v.y.T) := by
        have := Nat.div_add_mod S.hh.size S.v.y.T
        omega
      calc S.hh.size = S.v.y.T * (S.hh.size / S.v.y.T) := h2
        _ ≤ S.v.y.T * i := Nat.mul_le_mul_left _ h1
        _ = i * S.v.y.T := Nat.mul_comm _ _
        _ ≤ i * S.v.y.T + t := Nat.le_add_right _ _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hge]
    show _ * Reading.gl.val zeroE = 0
    rw [Reading.gl.zero, mul_zero]

variable {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **`Kinds` at a token point and the tokens' corners.** -/
theorem kinds_of (S : Sides)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r)
    (hk : TokAsks S.Q) (hy : S.v.y = S.Q.P.y) (hlow : S.zlow.size = S.v.y.ls) {z : Array E}
    (hz : z.size = S.v.y.h.lt) (hT : S.v.y.T = 2 ^ S.v.y.h.lt)
    (hTc : S.ce.v.y.T ≤ 2 ^ S.v.y.h.lt) (hdiv : S.hh.size % S.v.y.T = 0) {Rz : Reads}
    (hRz : S.readsTok z = some Rz) (Rt : ℕ → Reads)
    (hRt : ∀ t, t < 2 ^ S.v.y.h.lt → S.readsTok (bitsOf S.v.y.h.lt t) = some (Rt t)) :
    Kinds (2 ^ S.v.y.h.lt) (Blocks.eqN S.v.y.h.lt 0 (pt Reading.gl z))
      (fun a => valAff? S.v Rz (fun _ => zeroE) a)
      (fun t a => valAff? S.v (Rt t) (fun _ => zeroE) a) (S.weights (eqTab z))
      (fun t => S.weights (eqTab (bitsOf S.v.y.h.lt t)))
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE)
      (fun t lm yv => S.hh.getD (S.routedAt lm yv * S.v.y.T + t) zeroE) where
  form := by
    intro a x xt hx hxt
    obtain ⟨h1, h2⟩ := valAffQ_tok (Q := S.Q) (w := S.w) (fo := S.fo) (zlow := S.zlow) (z := z)
      (Rz := Rz) (Rt := Rt) hl hk (by rw [← hy]; exact hlow) (by rw [← hy]; exact hz) hRz
      (by rw [← hy]; exact hRt) hx
    rw [← hy] at h1 h2
    rw [h2]
    refine Finset.sum_congr rfl fun t ht => ?_
    have e := (h1 t (Finset.mem_range.mp ht)).symm.trans (hxt t (Finset.mem_range.mp ht))
    rw [Option.some.inj e]
  constz := fun c x h => val_const _ _ _ c x h
  constt := fun _ c x h => val_const _ _ _ c x h
  tab := fun a kk hi yv => tok_tables S hz hTc a kk hi yv
  gated := fun lm yv => gated_tok S hz hT hdiv _
  one := sum_eqN_one _ _

/-- **`TripsAt` at a token point.** -/
theorem tripsAt_at (S : Sides) {rows : TokRows} (hrows : tokenRows S = some rows)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r)
    (hk : TokAsks S.Q) (hy : S.v.y = S.Q.P.y) (hlow : S.zlow.size = S.v.y.ls)
    (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hTc : S.ce.v.y.T ≤ 2 ^ S.v.y.h.lt)
    (hdiv : S.hh.size % S.v.y.T = 0) (hB : triPlainB S = true) (z : Array E)
    (hz : z.size = S.v.y.h.lt) (Rz : Reads) (hRz : S.readsTok z = some Rz)
    (hmade : ∀ e : Array E, ∃ l, S.trips Rz (eqTab z)
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) e = some l) :
    ∃ idx, TripsAt S rows z idx :=
  tripsAt_of hrows hT hB z Rz hRz
    (fun Rt hRt => kinds_of S hl hk hy hlow hz hT hTc hdiv hRz Rt hRt)
    (fun a hcd et et' => tok_tables_plain S a hcd et et') hmade

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.val_const
#print axioms ProofFile.Honest.K4.gated_tok
#print axioms ProofFile.Honest.K4.kinds_of
#print axioms ProofFile.Honest.K4.tripsAt_at
