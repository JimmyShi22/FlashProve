-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TripShare.lean: CONDITIONAL.

What is here. One panel of the batched sumcheck's second pass: the sum of the products that the
honest side makes of it at a token point (`tripsOf`, Johnson/Desc/K4/Honest/Sides.lean) is the
library's share of the verifier's panel (`shareP`, Johnson/Road/FormsKeysPort.lean).

  `TripTies`   the ties
  `trip_tri`, `trip_plain`   the two kinds of a panel
  `trip_share`   **one panel**

Limits. At the reading `Reading.gl`. ALL TIES BETWEEN THE TWO SIDES ARE HYPOTHESES, gathered in
`TripTies`: the honest value of each of the panel's own forms is the form's value in the world Wo
(of no other form); the routed experts' never-sent vectors hv read as the honest function hh, inside
the panel's columns; the weight claims' vectors wv read as the honest tables of the weights, and 0
from the panel's number of columns on; a panel with the selector has as many rows as there are
routed experts; the panel's columns fit its bits. hv, wv, hh and Wo are variables. TripTiesOf.lean
pays the ties at chosen hv and wv, in every world in which the first of them holds; HvalOf.lean pays
that one in every world with the true entries. No example of the ties together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.PanelShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE mulE maddE)
open OnBytes.Model (Reading Aff World)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Road (shareP wtK rowW aRaw bRaw nRows sideK ov)
open OnBytes.Road.K4.C (gl_foldl_maddE range_sum)
open OnBytes.Desc.First.K4.Honest

/-- **The ties between the honest side's letters and the library's, at one panel of the second
pass.** -/
structure TripTies (S : OnBytes.Desc.First.K4.Honest.Sides) (val : Aff → Option E)
    (F : Array (Array E)) (hh : ℕ → ℕ → E) (Wo : World Cb.Gl.E) (hv wv : ℕ → ℕ → Cb.Gl.E)
    (b : SBlk) : Prop where
  /-- the honest value of a column factor's form is its value in the world -/
  valX : ∀ yv y, yv < b.ny → val (b.xx.getD yv {}) = some y →
    Reading.gl.val y = (b.xx.getD yv {}).value Reading.gl Wo
  /-- the like for a form of the A side -/
  valA : ∀ A i yv f y, b.A = some A → A i yv = some f → val f = some y →
    Reading.gl.val y = f.value Reading.gl Wo
  /-- the like for a form of the B side -/
  valB : ∀ B i yv f y, b.B = some B → B i yv = some f → val f = some y →
    Reading.gl.val y = f.value Reading.gl Wo
  /-- a panel with the selector has a row for each routed expert -/
  rows : b.tri = true → b.ni = S.v.y.h.NE
  /-- the columns fit the bits -/
  cols : b.ny ≤ 2 ^ b.wy
  /-- a never-sent vector that is the column factor of a panel with the selector -/
  hvT : b.tri = true → ∀ k, b.virt = some k → ∀ yv, yv < b.ny →
    hv k yv = Reading.gl.val (hh (k - 1) yv)
  /-- the one weight claim of a panel with the selector -/
  wvT : b.tri = true → ∀ v0, b.v0 = some v0 → ∀ i yv, i < b.ni → yv < 2 ^ b.wy →
    wv v0 (i * 2 ^ b.wy + yv) = if yv < b.ny then
      Reading.gl.val (at2 (F.getD v0 #[]) (S.kkOf v0) i yv) else 0
  /-- the weight claims of another panel, one for each row -/
  wvP : b.tri = false → ∀ v0, b.v0 = some v0 → ∀ i yv, i < b.ni → yv < 2 ^ b.wy →
    wv (v0 + i) yv = if yv < b.ny then
      Reading.gl.val (at2 (F.getD (v0 + i) #[]) (S.kkOf (v0 + i)) 0 yv) else 0

variable {S : OnBytes.Desc.First.K4.Honest.Sides} {val : Aff → Option E} {F : Array (Array E)}
  {hh : ℕ → ℕ → E} {Wo : World Cb.Gl.E} {hv wv : ℕ → ℕ → Cb.Gl.E} {b : SBlk}

/-- **A panel with the selector.** -/
theorem trip_tri (T : TripTies S val F hh Wo hv wv b) (htri : b.tri = true) {tr : Array Trip}
    (ht : tripsOf S val F hh b = some tr) :
    tripSum tr.toList = shareP Reading.gl Wo S.v.y hv wv b := by
  unfold tripsOf at ht
  simp only [htri, ↓reduceIte] at ht
  obtain ⟨v0, hv0, ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain ⟨cols, hc, ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain rfl := Option.some.inj ht
  unfold shareP nRows tripSum
  rw [if_pos htri, ← T.rows htri, Array.toList_map, Array.toList_range, List.map_map, range_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have hb : ∀ yv, yv < 2 ^ b.wy → bRaw Reading.gl Wo wv b i yv = if yv < b.ny then
      Reading.gl.val (at2 (F.getD v0 #[]) (S.kkOf v0) i yv) else 0 := by
    intro yv hy
    unfold bRaw
    rw [htri, hv0]
    exact T.wvT htri v0 hv0 i yv hi' hy
  rw [sum_cut T.cols _ fun yv h1 h2 => by rw [hb yv h2, if_neg (by omega), mul_zero]]
  show Reading.gl.val (mulE b.ec (b.wt.getD 0 zeroE)) * (Reading.gl.val (b.sl.getD i zeroE) *
    Reading.gl.val ((List.range b.ny).foldl (fun s yv => maddE s (cols.getD yv zeroE)
      (at2 (F.getD v0 #[]) (S.kkOf v0) i yv)) zeroE)) = _
  rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum, Reading.gl.mul]
  have e : ∑ yv ∈ Finset.range b.ny, aRaw Reading.gl Wo hv b i yv * bRaw Reading.gl Wo wv b i yv =
      ∑ yv ∈ Finset.range b.ny, Reading.gl.val (cols.getD yv zeroE) *
        Reading.gl.val (at2 (F.getD v0 #[]) (S.kkOf v0) i yv) := by
    refine Finset.sum_congr rfl fun yv hyv => ?_
    have hyv' := Finset.mem_range.mp hyv
    have ha : aRaw Reading.gl Wo hv b i yv = Reading.gl.val (cols.getD yv zeroE) := by
      have g := amapM_range_get _ hc hyv' zeroE
      unfold aRaw
      rw [htri]
      cases hk : b.virt with
      | some k =>
        simp only [hk] at g
        show hv k yv = _
        rw [T.hvT htri k hk yv hyv', Option.some.inj g]
      | none =>
        simp only [hk] at g
        show (if yv < b.ny then (b.xx.getD yv {}).value Reading.gl Wo else 0) = _
        rw [if_pos hyv', T.valX yv _ hyv' g]
    rw [ha, hb yv (lt_of_lt_of_le hyv' T.cols), if_pos hyv']
  rw [e]
  unfold rowW wtK
  rw [if_pos htri]
  ring

/-- **A panel with two factors.** -/
theorem trip_plain (T : TripTies S val F hh Wo hv wv b) (htri : b.tri = false) {tr : Array Trip}
    (ht : tripsOf S val F hh b = some tr) :
    tripSum tr.toList = shareP Reading.gl Wo S.v.y hv wv b := by
  unfold tripsOf at ht
  simp only [htri, Bool.false_eq_true, ↓reduceIte] at ht
  have hk : b.virt = none := by
    cases hv : b.virt with
    | none => rfl
    | some k =>
      rw [hv] at ht
      simp at ht
  rw [hk] at ht
  simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at ht
  obtain ⟨A, hA, ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain ⟨rows, hr, ht⟩ := Option.bind_eq_some_iff.mp ht
  obtain rfl := Option.some.inj ht
  have hr' : (Array.range b.ni).mapM
      (fun i => (Array.range b.ny).mapM (elemOfB S val F b A i)) = some rows := hr
  have hrs : rows.size = b.ni := amapM_range_size _ hr'
  have tl : ∀ (u : Array Trip) k, u.toList.getD k trip0 = u.getD k trip0 := fun u k => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  have tl2 : ∀ k, rows.toList.getD k #[] = rows.getD k #[] := fun k => by
    rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  unfold shareP nRows
  rw [if_neg (by rw [htri]; decide), Array.toList_flatMap, tripSum_flat, sum_by_number #[],
    Array.length_toList, hrs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  have gi := amapM_range_get _ hr' hi' #[]
  have his : (rows.getD i #[]).size = b.ny := amapM_range_size _ gi
  have haR : ∀ yv, aRaw Reading.gl Wo hv b i yv =
      if yv < b.ny then sideK Reading.gl Wo b.A i yv else 0 := by
    intro yv
    unfold aRaw
    rw [htri, hk]
  rw [tl2, sum_cut T.cols _ fun yv h1 _ => by rw [haR yv, if_neg (by omega), zero_mul]]
  show tripSum (rows.getD i #[]).toList = _
  unfold tripSum
  rw [sum_by_number trip0, Array.length_toList, his, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun yv hyv => ?_
  have hyv' := Finset.mem_range.mp hyv
  rw [tl]
  obtain ⟨f, a', c', e1, e2, e3, e4⟩ := elemOfB_open (amapM_range_get _ gi hyv' trip0)
  rw [e4]
  have eA : aRaw Reading.gl Wo hv b i yv = Reading.gl.val a' := by
    rw [haR yv, if_pos hyv', hA]
    show ov Reading.gl Wo (A i yv) = _
    rw [e1]
    exact (T.valA A i yv f a' hA e1 e2).symm
  have eB : bRaw Reading.gl Wo wv b i yv = Reading.gl.val c' := by
    unfold bRaw
    rw [htri, hk]
    revert e3
    cases h0 : b.v0 with
    | some v0 =>
      intro e3
      show wv (v0 + i) yv = _
      rw [T.wvP htri v0 h0 i yv hi' (lt_of_lt_of_le hyv' T.cols), if_pos hyv',
        Option.some.inj e3]
    | none =>
      cases hB : b.B with
      | none =>
        intro e3
        cases e3
      | some B =>
        intro e3
        obtain ⟨g, q1, q2⟩ := Option.bind_eq_some_iff.mp e3
        show (if yv < b.ny then sideK Reading.gl Wo (some B) i yv else 0) = _
        rw [if_pos hyv']
        show ov Reading.gl Wo (B i yv) = _
        rw [q1]
        exact (T.valB B i yv g _ hB q1 q2).symm
  rw [eA, eB]
  show Reading.gl.val (mulE b.ec (b.wt.getD i zeroE)) *
    (Reading.gl.val a' * Reading.gl.val c') = _
  rw [Reading.gl.mul]
  unfold rowW wtK
  rw [if_neg (by rw [htri]; decide)]
  ring

/-- **ONE PANEL OF THE SECOND PASS**: the sum of the honest side's products is the library's share.
CONDITIONAL: on the ties. -/
theorem trip_share (T : TripTies S val F hh Wo hv wv b) {tr : Array Trip}
    (ht : tripsOf S val F hh b = some tr) :
    tripSum tr.toList = shareP Reading.gl Wo S.v.y hv wv b := by
  cases htri : b.tri with
  | true => exact trip_tri T htri ht
  | false => exact trip_plain T htri ht

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.trip_tri
#print axioms ProofFile.Honest.K4.trip_plain
#print axioms ProofFile.Honest.K4.trip_share
