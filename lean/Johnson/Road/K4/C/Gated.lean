-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/Gated.lean: CONDITIONAL.

Not shown here. THAT THE HONEST SIDE's TENSORS READ AS THE LIBRARY's VALUES: TensorIs is a
hypothesis here. That the hypotheses can hold together: no example is known. That the point r is
what the verifier has heard: a hypothesis (hr), in the honest side's own term. That the cube's sizes
fit: a hypothesis (hfit). Nothing on a slot, a ledger or a mask. Nothing on soundness, on
completeness or on any other property. No property is claimed.

The end values of the two product layers of the gated products, as the honest side of the layers'
own rounds (sub-protocol K4) computes them (`jobGated`, `jobGated2`,
Johnson/Desc/K4/Honest/Gated.lean), read into the field, as extensions of the library's four maps
slV, upV, slV', upV' at the cells t. The right sides are typed after those of the fields lv1L, lv1R,
lv2L, lv2R of `Opened` (Johnson/Road/K4/W/Ground.lean); that the letters meet is said by no
statement of this file. These two functions of the honest side (makers, in these files' heads) value
no form on the honest side's reads: they read cells alone.

  `TensorIs Q w t A X`   the tensor X of the input's cells, read into the field, is the library's
      value of the array A at the cells t, at every layer, feature and token of the group.
  `GatedNums Q D`   twelve public numbers.
  `level_end`   an end value of a product layer's sumcheck is the extension of its table at the
      challenges laid as a point.
  `layerTab_at`   an entry of the table of minus a tensor.
  `tab1_read`, `tab2_read`, `gatedTabs_eq`, `gatedTabs2_eq`   the two layers' tables, entry by
      entry.
  `lv1_read`, `lv2_read`   the two end values of the first layer; of the second.
-/
import Johnson.Desc.K4.Honest.Gated
import Johnson.Desc.K4.Honest.Law.Cube
import Johnson.Road.FormsKeysKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Ten downFrom)
open Inst.Model.FFSeg (Dim Cell Arr val lF lFe slV upV slV' upV')
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (valuesAt_mle mle_ext pointOf_size)

/-- **The input's tensor reads as the library's value.** This defines a hypothesis; the definition
claims nothing. -/
def TensorIs (Q : K4Pub) (w : K4In) (t : Cell → Cb.Gl.E) (A : Arr) (X : Ten) : Prop :=
  ∀ ix j i, ix < Q.P.y.Lam → j < Q.P.y.h.f → i < Q.P.y.T →
    Reading.gl.val (tensorAt Q.P.y w.cell X ix j i) = val t A ix j i

/-- **Twelve public numbers.** This defines a hypothesis; the definition claims nothing. -/
structure GatedNums (Q : K4Pub) (D : Dim) : Prop where
  T : Q.P.y.T = 2 ^ D.lT
  Lam : Q.P.y.Lam = 2 ^ D.lL
  lL : 1 ≤ D.lL
  f : Q.P.y.h.f = 2 ^ lF D
  Pf : Q.P.y.Pf = 2 ^ lF D
  fe : Q.P.y.h.fe = 2 ^ lFe D
  Dfe : D.fe = 2 ^ lFe D
  ffe : lF D = lFe D + 1
  muH : Q.P.rd.muH = D.lL + lF D + D.lT
  muH2 : Q.P.rd.muH2 = D.lL - 1 + lFe D + D.lT
  lfe : Q.P.y.lfe = lFe D
  LamM : Q.P.y.LamM = 2 ^ (D.lL - 1)

/-- **An end value of a product layer's sumcheck**: the extension of table number e at the
challenges laid as a point. CONDITIONAL: on the sizes. -/
theorem level_end (mu : ℕ) (order : List ℕ) (rho : Array E) (tb : Tab × Tab) (rs : List E)
    (hfit : (levelJob mu order rho tb).cube.fits = true) (hrs : rs.length = mu) (e : ℕ) :
    Reading.gl.val (((levelJob mu order rho tb).ends rs).getD e zeroE) =
      ext mu (fun i => Reading.gl.val ((#[tb.1, tb.2].getD e #[]).getD i zeroE))
        (pt Reading.gl ((levelJob mu order rho tb).cube.pointOf rs)) := by
  have h1 : ((levelJob mu order rho tb).ends rs).getD e zeroE =
      ((levelJob mu order rho tb).cube.valuesAt rs).getD e zeroE := by
    show (((levelJob mu order rho tb).cube.valuesAt rs).toList).getD e zeroE = _
    simp [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?]
  have hs : ((levelJob mu order rho tb).cube.pointOf rs).size = mu :=
    pointOf_size (levelJob mu order rho tb).cube rs
  rw [h1, valuesAt_mle Reading.gl (levelJob mu order rho tb).cube hfit rs hrs e, mle_ext, hs]
  rfl

/-- An entry of the table of minus a tensor. -/
theorem layerTab_at (y : Lay) (cell : ℕ → ℕ → ℕ → F) (X : Ten) (mu stride width : ℕ)
    (lamOf : ℕ → ℕ) (first : ℕ) {i : ℕ} (hi : i < 2 ^ mu) (hx : i / y.T % stride < width) :
    (layerTab y cell X mu stride width lamOf first).getD i zeroE =
      negE (tensorAt y cell X (lamOf (i / y.T / stride)) (first + i / y.T % stride) (i % y.T)) := by
  unfold layerTab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hi]
  simp only [Option.getD_some, if_pos hx]

section Tops
variable {Q : K4Pub} {w : K4In} {t : Cell → Cb.Gl.E} {D : Dim} {ts tu : Ten}

/-- An entry of a table of the first product layer. -/
theorem tab1_read (N : GatedNums Q D) {A : Arr} {X : Ten} (S : TensorIs Q w t A X) {i : ℕ}
    (hi : i < 2 ^ (D.lL + lF D + D.lT)) :
    Reading.gl.val ((layerTab Q.P.y w.cell X Q.P.rd.muH Q.P.y.Pf Q.P.y.h.f id 0).getD i zeroE) =
      -val t A (i / D.T / 2 ^ lF D) (i / D.T % 2 ^ lF D) (i % D.T) := by
  have hT : Q.P.y.T = D.T := N.T
  have p1 : 0 < 2 ^ lF D := Nat.two_pow_pos _
  have p2 : 0 < D.T := Nat.two_pow_pos _
  have hx : i / Q.P.y.T % Q.P.y.Pf < Q.P.y.h.f := by
    rw [N.Pf, N.f]
    exact Nat.mod_lt _ p1
  rw [layerTab_at _ _ _ _ _ _ _ _ (by rw [N.muH]; exact hi) hx, gl_numerals.neg,
    S _ _ _ ?_ (by rw [Nat.zero_add]; exact hx) (by rw [hT]; exact Nat.mod_lt _ p2),
    Nat.zero_add, hT, N.Pf]
  · rfl
  · show i / Q.P.y.T / Q.P.y.Pf < Q.P.y.Lam
    rw [hT, N.Pf, N.Lam, Nat.div_div_eq_div_mul]
    refine Nat.div_lt_of_lt_mul ?_
    have e : D.T * 2 ^ lF D * 2 ^ D.lL = 2 ^ (D.lL + lF D + D.lT) := by
      show 2 ^ D.lT * 2 ^ lF D * 2 ^ D.lL = _
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega
    rw [e]
    exact hi

/-- An entry of a table of the second product layer. -/
theorem tab2_read (N : GatedNums Q D) {A : Arr} {X : Ten} (S : TensorIs Q w t A X) {i : ℕ}
    (hi : i < 2 ^ (D.lL - 1 + lFe D + D.lT)) :
    Reading.gl.val ((layerTab Q.P.y w.cell X Q.P.rd.muH2 Q.P.y.h.fe Q.P.y.h.fe
      (fun m => 2 * m + 1) Q.P.y.h.fe).getD i zeroE) =
      -val t A (2 * (i / D.T / 2 ^ lFe D) + 1) (D.fe + i / D.T % 2 ^ lFe D) (i % D.T) := by
  have hT : Q.P.y.T = D.T := N.T
  have p1 : 0 < 2 ^ lFe D := Nat.two_pow_pos _
  have p2 : 0 < D.T := Nat.two_pow_pos _
  have hx : i / Q.P.y.T % Q.P.y.h.fe < Q.P.y.h.fe := by
    rw [N.fe]
    exact Nat.mod_lt _ p1
  have hm : i / D.T / 2 ^ lFe D < 2 ^ (D.lL - 1) := by
    rw [Nat.div_div_eq_div_mul]
    refine Nat.div_lt_of_lt_mul ?_
    have e : D.T * 2 ^ lFe D * 2 ^ (D.lL - 1) = 2 ^ (D.lL - 1 + lFe D + D.lT) := by
      show 2 ^ D.lT * 2 ^ lFe D * 2 ^ (D.lL - 1) = _
      rw [← Nat.pow_add, ← Nat.pow_add]
      congr 1
      omega
    rw [e]
    exact hi
  have hL : 2 ^ D.lL = 2 * 2 ^ (D.lL - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, D.lL = k + 1 := ⟨D.lL - 1, by have := N.lL; omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  have hF : 2 ^ lF D = 2 * 2 ^ lFe D := by rw [N.ffe, Nat.pow_succ, Nat.mul_comm]
  rw [layerTab_at _ _ _ _ _ _ _ _ (by rw [N.muH2]; exact hi) hx, gl_numerals.neg,
    S _ _ _ ?_ ?_ (by rw [hT]; exact Nat.mod_lt _ p2), hT, N.fe, N.Dfe]
  · show 2 * (i / Q.P.y.T / Q.P.y.h.fe) + 1 < Q.P.y.Lam
    rw [hT, N.fe, N.Lam, hL]
    omega
  · rw [N.f, hF]
    rw [N.fe] at hx ⊢
    omega

/-- The two tables, where the layout has the two tensors. -/
theorem gatedTabs_eq (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    {tb : Tab × Tab} (htb : gatedTabs Q w = some tb) :
    tb = (layerTab Q.P.y w.cell ts Q.P.rd.muH Q.P.y.Pf Q.P.y.h.f id 0,
      layerTab Q.P.y w.cell tu Q.P.rd.muH Q.P.y.Pf Q.P.y.h.f id 0) := by
  unfold gatedTabs at htb
  dsimp only at htb
  rw [hts, htu] at htb
  exact (Option.some.inj htb).symm

/-- The second layer's two tables, where the layout has the two tensors. -/
theorem gatedTabs2_eq (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    {tb : Tab × Tab} (htb : gatedTabs2 Q w = some tb) :
    tb = (layerTab Q.P.y w.cell ts Q.P.rd.muH2 Q.P.y.h.fe Q.P.y.h.fe (fun m => 2 * m + 1)
        Q.P.y.h.fe,
      layerTab Q.P.y w.cell tu Q.P.rd.muH2 Q.P.y.h.fe Q.P.y.h.fe (fun m => 2 * m + 1)
        Q.P.y.h.fe) := by
  unfold gatedTabs2 at htb
  dsimp only at htb
  rw [hts, htu] at htb
  exact (Option.some.inj htb).symm

/-- **THE FIRST PRODUCT LAYER's TWO END VALUES.** p: the sampled values; rs: the layer's challenges
in the order of the rounds; r: these laid as a point. CONDITIONAL: on every hypothesis named. -/
theorem lv1_read (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D) (p : Pts)
    (rs : List E) (hrs : rs.length = Q.P.rd.muH) {tb : Tab × Tab} (htb : gatedTabs Q w = some tb)
    (hfit : (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) tb).cube.fits = true)
    {r : Array E} (hr : r = (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
      (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) tb).cube.pointOf rs) :
    Reading.gl.val ((((jobGated Q w p).map (·.ends rs)).getD []).getD 0 zeroE) =
        ext (D.lL + lF D + D.lT) (slV D t) (pt Reading.gl r) ∧
      Reading.gl.val ((((jobGated Q w p).map (·.ends rs)).getD []).getD 1 zeroE) =
        ext (D.lL + lF D + D.lT) (upV D t) (pt Reading.gl r) := by
  have etb := gatedTabs_eq hts htu htb
  have ej : ((jobGated Q w p).map (·.ends rs)).getD [] =
      (levelJob Q.P.rd.muH (orderRange Q.P.rd.muH)
        (downFrom p.rs (Q.P.y.h.ll + Q.P.y.lPf) ++ ztOf Q p) tb).ends rs := by
    unfold jobGated
    rw [htb]
    rfl
  rw [ej, hr]
  refine ⟨?_, ?_⟩
  · rw [level_end _ _ _ _ _ hfit hrs 0, N.muH]
    refine Blocks.ext_congr (fun i hi => ?_) _
    rw [etb]
    exact tab1_read N Ss hi
  · rw [level_end _ _ _ _ _ hfit hrs 1, N.muH]
    refine Blocks.ext_congr (fun i hi => ?_) _
    rw [etb]
    exact tab1_read N Su hi

/-- **THE SECOND PRODUCT LAYER's TWO END VALUES.** As lv1_read, at the layers with routed experts.
CONDITIONAL: on every hypothesis named. -/
theorem lv2_read (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D) (p : Pts)
    (rs : List E) (hrs : rs.length = Q.P.rd.muH2) {tb : Tab × Tab}
    (htb : gatedTabs2 Q w = some tb)
    (hfit : (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt) tb).cube.fits = true)
    {r : Array E} (hr : r = (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
      (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt) tb).cube.pointOf rs) :
    Reading.gl.val ((((jobGated2 Q w p).map (·.ends rs)).getD []).getD 0 zeroE) =
        ext (D.lL - 1 + lFe D + D.lT) (slV' D t) (pt Reading.gl r) ∧
      Reading.gl.val ((((jobGated2 Q w p).map (·.ends rs)).getD []).getD 1 zeroE) =
        ext (D.lL - 1 + lFe D + D.lT) (upV' D t) (pt Reading.gl r) := by
  have etb := gatedTabs2_eq hts htu htb
  have ej : ((jobGated2 Q w p).map (·.ends rs)).getD [] =
      (levelJob Q.P.rd.muH2 (orderRange Q.P.rd.muH2)
        (p.rhoM ++ downFrom p.rs Q.P.y.lfe ++ p.rt) tb).ends rs := by
    unfold jobGated2
    rw [htb]
    rfl
  rw [ej, hr]
  refine ⟨?_, ?_⟩
  · rw [level_end _ _ _ _ _ hfit hrs 0, N.muH2]
    refine Blocks.ext_congr (fun i hi => ?_) _
    rw [etb]
    exact tab2_read N Ss hi
  · rw [level_end _ _ _ _ _ hfit hrs 1, N.muH2]
    refine Blocks.ext_congr (fun i hi => ?_) _
    rw [etb]
    exact tab2_read N Su hi

end Tops

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.level_end
#print axioms OnBytes.Road.K4.C.layerTab_at
#print axioms OnBytes.Road.K4.C.tab1_read
#print axioms OnBytes.Road.K4.C.tab2_read
#print axioms OnBytes.Road.K4.C.gatedTabs_eq
#print axioms OnBytes.Road.K4.C.gatedTabs2_eq
#print axioms OnBytes.Road.K4.C.lv1_read
#print axioms OnBytes.Road.K4.C.lv2_read
