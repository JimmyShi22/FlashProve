-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/PlacesTiesOK.lean

Where the Lean verifier's layout functions return for a parameter file, the numbers at the file's
lines meet "Sz.Fit" and, with the returned lookups' kT, "Sz.OK".

The ties of Johnson/HonestTrace/PlacesTies.lean at the numbers "Sz.ofHdr" keep "Sz.OK" and "Sz.Fit"
as premises. This file shows both from the tests that the functions of the Lean verifier under
OnBytes/Model/ have made where they return, and states the two ties again without them.

Main definitions and theorems. "Return" means: the function's value is ".ok" of something.
* "tests_of_layout", "tests_of_config", "planeCols_of_layout", "planeCols_of_headLayout",
  "lmb_of_fill": what "Layer.layout", "Attention.config", "Head.layout", "Attention.fill" have
  tested or set where they return.
* "fit_ofHdr": "Sz.Fit" at "Sz.ofHdr", if "Layer.layout" (at "layerShape"), "Attention.config" and,
  for some group, "Attention.group" return.
* "ok_ofHdr": "Sz.OK" at "Sz.ofHdr", if besides "Head.layout" (at "headShape") returns and
  "Forest.planeCols" returns for every segment of the proof at a lookup with that segment's kT.
* "lookNo", "planes_ofHdr": the last premise holds at the returned lookups' kT, if "Attention.group"
  returns for every group.
* "place_eq_addrA_of_returns", "place_eq_placeOf_of_returns": the ties to "L5.addrA" and "placeOf"
  with premises on what returns alone (and, for the layers, "Switches" and profile 4).

Limits. The limits of Johnson/HonestTrace/PlacesTies.lean hold here too: "placeOf" and "L5.addrA"
are functions of this library beside the Lean verifier. That "Attention.group" returns for every
group is a premise; this file does not draw it from "Attention.config returns", which calls it for
each group. No theorem of this file shows that the functions return for some file. Profile 4 is the
parameter file's line prof 20.

Not claimed: that a prover lays its cells at these places; that a verifier accepts anything.

-/
import Johnson.Road.FormsKeysQK
import Johnson.HonestTrace.PlacesTies

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (Forest.Shape)
open OnBytes.Model.Layer (layout layoutBase layoutLook manyBits)

/-! ## What the layout functions have tested -/

/-- Three tests that "Layer.layout" has made where it returns: there is a layer, the layers are
whole groups, and there is a head of keys and values. -/
theorem tests_of_layout {h : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hl : layout h pc = .ok y) : h.L ≠ 0 ∧ h.L % 2 ^ h.ll = 0 ∧ h.Gk ≠ 0 := by
  unfold layout at hl
  obtain ⟨y0, hy, -⟩ := ok_of_bind hl
  clear hl
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e3, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e9, -⟩ := ok_of_refuse hy
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at e3 e9
  exact ⟨e3.1, e3.2, e9.1.1.1.1.1.2⟩

/-- Where "Layer.layout" returns y, "Forest.planeCols" has returned y.kbm at y's lookup and line
lmb. -/
theorem planeCols_of_layout {h : Model.Layer.Shape} {pc : List (List String)}
    {y : Model.Layer.Lay} (hl : layout h pc = .ok y) :
    Model.Forest.planeCols y.fo y.h.lmb = .ok y.kbm := by
  unfold layout at hl
  obtain ⟨y0, -, e⟩ := ok_of_bind hl
  unfold layoutLook at e
  dsimp only at e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨fo, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨kbm, hk, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨pub, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  obtain ⟨_, _, e⟩ := ok_of_bind e
  cases e
  exact hk

/-- Where "Head.layout" returns L at the shape hH, "Forest.planeCols" returns L.kb at L's lookup and
hH's line lmbH. -/
theorem planeCols_of_headLayout {hH : Model.Head.Shape} {tau : Array UInt64} {L : Model.Head.HL}
    (hy : Model.Head.layout hH tau = .ok L) :
    Model.Forest.planeCols L.fs hH.lmbH = .ok L.kb := by
  unfold Model.Head.layout at hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨L0, -, hy⟩ := ok_of_bind hy
  obtain ⟨calls, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨fs, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨kb, h9, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨pub, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  cases hy
  exact h9

/-- Four tests that "Attention.config" has made where it returns: the number of heads of keys and
values has at most one binary digit 1; lt ≤ lmh; lt ≤ lmo; as has a part. -/
theorem tests_of_config {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {C : Attention.Config} (hC : Attention.config P y sc midQ = .ok C) :
    manyBits P.h.Gk = false ∧ P.h.lt ≤ P.h.lmh ∧ P.h.lt ≤ P.h.lmo ∧ P.h.NAs ≠ 0 := by
  unfold Attention.config at hC
  obtain ⟨lines, -, hC⟩ := ok_of_bind hC
  obtain ⟨e1, hC⟩ := ok_of_refuse hC
  obtain ⟨e2, -⟩ := ok_of_refuse hC
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, decide_eq_false_iff_not, not_lt] at e2
  exact ⟨e1, e2.1.1.1.1.1.1.1, e2.1.1.1.1.1.2, e2.1.2⟩

/-! ## "Fit" and "OK" at the numbers of a parameter file -/

section
variable {P : Model.PolScan} {pc : List (List String)} {y : Model.Layer.Lay}
  {sc : Model.Layer.Scales} {midQ : ℕ → ℕ} {C : Attention.Config} {lines : List Attention.Line}
  {g : ℕ} {X : Attention.Plan} {tau : Array UInt64} {L : Model.Head.HL}

/-- **"Sz.Fit" at a parameter file's lines.** If "Layer.layout" returns y at the shape made of the
file, "Attention.config" returns at y, and "Attention.group" returns for some group: the numbers at
the file's lines meet "Sz.Fit", whatever u0, kT and NC are. -/
theorem fit_ofHdr (hy : layout (Model.Verify.layerShape P) pc = .ok y)
    (hC : Attention.config P y sc midQ = .ok C)
    (hG : Attention.group P y sc midQ lines g = .ok X) (u0 : ℕ) (kT NC : Seg → ℕ) :
    (Sz.ofHdr P.h u0 kT NC).Fit := by
  obtain ⟨-, -, hGk⟩ := tests_of_layout hy
  obtain ⟨m1, -, -, -⟩ := tests_of_config hC
  have e := layout_shape hy
  have eGk : P.h.Gk = 2 ^ ceilLog2 P.h.Gk := pow_of_manyBits m1 hGk
  refine ⟨eGk, ?_, ?_⟩
  · have h1 := (headsLaid_of_layout hy).pow
    rw [e, ldh_of_layout hy] at h1
    exact h1
  · obtain ⟨cf, hf, hp, -⟩ := L5.group_plan hG
    obtain ⟨A, hA⟩ := L5.shape_of_hid (L5.plan_shape hp).1
    have t := (L5.tested_of_shape hA).2
    have Cf := fitsCf_of_fill hf (laid2_of_layout hy) e (ldh_of_layout hy) u0 kT NC
    rw [Cf.H, Cf.lgk] at t
    show P.h.Gk ∣ P.h.H
    rw [eGk]
    exact Nat.dvd_of_mod_eq_zero t

/-- **"Sz.OK" at a parameter file's lines.** If "Layer.layout" returns y at the shape made of the
file, "Attention.config" returns at y, "Attention.group" returns for some group, "Head.layout"
returns at the head's shape made of the file and y, and for every segment of the proof
"Forest.planeCols" returns at some lookup with kT σ and the segment's line lm: the numbers at the
file's lines meet "Sz.OK". -/
theorem ok_ofHdr (hy : layout (Model.Verify.layerShape P) pc = .ok y)
    (hC : Attention.config P y sc midQ = .ok C)
    (hG : Attention.group P y sc midQ lines g = .ok X)
    (hH : Model.Head.layout (Model.Verify.headShape P y) tau = .ok L) (u0 : ℕ) (kT NC : Seg → ℕ)
    (hp : ∀ σ : Seg, σ.Below (P.h.L / 2 ^ P.h.ll) → ∃ (fs : Forest.Shape) (k : ℕ),
      fs.kT = kT σ ∧ Model.Forest.planeCols fs ((Sz.ofHdr P.h u0 kT NC).lmP σ) = .ok k) :
    (Sz.ofHdr P.h u0 kT NC).OK := by
  obtain ⟨hL0, hLm, -⟩ := tests_of_layout hy
  obtain ⟨-, c1, c2, c3⟩ := tests_of_config hC
  have e := layout_shape hy
  have L2 := laid2_of_layout hy
  have pos : ∀ a, P.h.lt ≤ a → 0 < 2 ^ a / 2 ^ P.h.lt := fun a ha =>
    Nat.div_pos (Nat.pow_le_pow_right (by norm_num) ha) (Nat.pow_pos (by norm_num))
  have a1 : P.h.lt ≤ P.h.lmaf := by have h1 := L2.lt_af; rw [e] at h1; exact h1
  have a2 : P.h.lt ≤ P.h.lmad := by have h1 := L2.lt_ad; rw [e] at h1; exact h1
  have a3 : P.h.lt ≤ P.h.lmar := by have h1 := L2.lt_ar; rw [e] at h1; exact h1
  have a4 : P.h.lt ≤ P.h.lmq := by have h1 := L2.lt_q; rw [e] at h1; exact h1
  have a5 : P.h.lt ≤ P.h.lmx := by
    have h1 := L2.lt_la
    have h2 := L2.la_x
    rw [e] at h1 h2
    exact Nat.le_trans (Nat.le_of_lt h1) h2
  have n1 : P.h.NAf ≠ 0 := by have h1 := L2.NAf0; rw [e] at h1; exact h1
  have n2 : P.h.NAd ≠ 0 := by have h1 := L2.NAd0; rw [e] at h1; exact h1
  obtain ⟨w1, w2, w3, w0⟩ := wc_H_pos hH (fitsH_ofHdr P y u0 kT NC)
  obtain ⟨cf, hf, hp', -⟩ := L5.group_plan hG
  obtain ⟨A, hA⟩ := L5.shape_of_hid (L5.plan_shape hp').1
  have t := (L5.tested_of_shape hA).1
  have Cf := fitsCf_of_fill hf L2 e (ldh_of_layout hy) u0 kT NC
  rw [Cf.lB, Cf.lt] at t
  exact {
    nGr := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hL0) (Nat.dvd_of_mod_eq_zero hLm))
      (Nat.pow_pos (by norm_num))
    wcaf := pos _ a1, wcad := pos _ a2, wcar := pos _ a3, wcq := pos _ a4, wcx := pos _ a5
    wch := pos _ c1, wco := pos _ c2, wchf := w1, wchd := w2, wchr := w3
    NAf := Nat.pos_of_ne_zero n1, NAd := Nat.pos_of_ne_zero n2, NAs := Nat.pos_of_ne_zero c3
    NHf := w0
    planes := fun σ hσ => by
      obtain ⟨fs, k, h1, h2⟩ := hp σ hσ
      obtain ⟨b1, b2, -⟩ := planeCols_ok h2
      rw [h1] at b2
      exact ⟨b1, b2⟩
    lB := by omega }

/-- The configuration that "Attention.fill" returns has the file's line lmbA. -/
theorem lmb_of_fill {cf : Attention.Cfg} (hf : Attention.fill P y sc lines g = .ok cf) :
    cf.lmb = P.h.lmbA := by
  unfold Attention.fill at hf
  obtain ⟨-, hf⟩ := L5.refuse_ok hf
  obtain ⟨-, hf⟩ := L5.refuse_ok hf
  obtain rfl := Except.ok.inj hf
  rfl

/-- A number of the lookup of each segment: of the layers' layout, of group g's attention plan, of
the head's layout. -/
def lookNo (f : Forest.Shape → ℕ) (y : Model.Layer.Lay) (fsA : ℕ → Forest.Shape)
    (L : Model.Head.HL) : Seg → ℕ
  | .ff _ => f y.fo
  | .att g => f (fsA g)
  | .head => f L.fs

/-- The last premise of "ok_ofHdr" is met at the returned lookups' kT: if "Layer.layout" and
"Head.layout" return as there, and for every group below L / 2^ll "Attention.group" returns a plan
whose lookup is fsA g. -/
theorem planes_ofHdr (hy : layout (Model.Verify.layerShape P) pc = .ok y)
    (hH : Model.Head.layout (Model.Verify.headShape P y) tau = .ok L) (fsA : ℕ → Forest.Shape)
    (hA : ∀ g < P.h.L / 2 ^ P.h.ll, ∃ (ls : List Attention.Line) (Z : Attention.Plan),
      Attention.group P y sc midQ ls g = .ok Z ∧ Z.fs = fsA g) (u0 : ℕ) (NC : Seg → ℕ) (σ : Seg)
    (hσ : σ.Below (P.h.L / 2 ^ P.h.ll)) :
    ∃ (fs : Forest.Shape) (k : ℕ), fs.kT = lookNo (·.kT) y fsA L σ ∧
      Model.Forest.planeCols fs ((Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).lmP σ) = .ok k := by
  cases σ with
  | ff g =>
    refine ⟨y.fo, y.kbm, rfl, ?_⟩
    have h1 := planeCols_of_layout hy
    rw [layout_shape hy] at h1
    exact h1
  | att g =>
    obtain ⟨ls, Z, hZ, hfs⟩ := hA g hσ
    obtain ⟨cf, hf, hp, -⟩ := L5.group_plan hZ
    have h1 := K5Law.kb_of_hid (L5.plan_shape hp).1
    rw [lmb_of_fill hf, hfs] at h1
    exact ⟨fsA g, Z.S.kbA, rfl, h1⟩
  | head => exact ⟨L.fs, L.kb, rfl, planeCols_of_headLayout hH⟩

/-- **Attention, with no premise on the numbers.** If "Layer.layout", "Attention.config" and
"Head.layout" return for a parameter file, "Attention.group" returns for every group below L / 2^ll
a plan whose lookup is fsA g, and for the group g below L / 2^ll the plan X: at the numbers of the
file's lines with the returned lookups' kT, for a valid name of attention, own or borrowed, the
number in the attention segment's list, the row and the column of its place are "L5.addrA" at X's
shape. -/
theorem place_eq_addrA_of_returns (hy : layout (Model.Verify.layerShape P) pc = .ok y)
    (hC : Attention.config P y sc midQ = .ok C)
    (hH : Model.Head.layout (Model.Verify.headShape P y) tau = .ok L) (fsA : ℕ → Forest.Shape)
    (hA : ∀ g < P.h.L / 2 ^ P.h.ll, ∃ (ls : List Attention.Line) (Z : Attention.Plan),
      Attention.group P y sc midQ ls g = .ok Z ∧ Z.fs = fsA g)
    (hG : Attention.group P y sc midQ lines g = .ok X) (hg : g < P.h.L / 2 ^ P.h.ll) (u0 : ℕ)
    (NC : Seg → ℕ) (c : AttSeg.Raw)
    (hv : c.Valid (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).DA) :
    (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).mu (.att g)
        ((Name.att g c).place (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC)).2.1 =
        some (L5.addrA X.S c).1 ∧
      ((Name.att g c).place (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC)).2.2.1 =
        (L5.addrA X.S c).2.1 ∧
      ((Name.att g c).place (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC)).2.2.2 =
        (L5.addrA X.S c).2.2 :=
  place_eq_addrA_of_group hy hG
    (ok_ofHdr hy hC hG hH u0 _ NC (planes_ofHdr hy hH fsA hA u0 NC))
    (fit_ofHdr hy hC hG u0 _ NC) hg c hv

/-- **The layers, with no premise on the numbers.** If "Layer.layout", "Attention.config" and
"Head.layout" return for a parameter file, "Attention.group" returns for every group below L / 2^ll
a plan whose lookup is fsA g, and the layers' shape has the digit forms and switches of "Switches"
and profile 4: at the numbers of the file's lines with the returned lookups' kT, in a group below L
/ 2^ll, the number in the list, the row and the column of a valid feed-forward name's place are
"placeOf" at y. -/
theorem place_eq_placeOf_of_returns (hy : layout (Model.Verify.layerShape P) pc = .ok y)
    (hC : Attention.config P y sc midQ = .ok C)
    (hH : Model.Head.layout (Model.Verify.headShape P y) tau = .ok L) (fsA : ℕ → Forest.Shape)
    (hA : ∀ g < P.h.L / 2 ^ P.h.ll, ∃ (ls : List Attention.Line) (Z : Attention.Plan),
      Attention.group P y sc midQ ls g = .ok Z ∧ Z.fs = fsA g)
    (Sw : Switches (Model.Verify.layerShape P)) (hp4 : (Model.Verify.layerShape P).p4 = true)
    (hg : g < P.h.L / 2 ^ P.h.ll) (u0 : ℕ) (NC : Seg → ℕ) (q : FFSeg.Cell)
    (hv : q.Valid (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).DF) :
    (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).mu (.ff g)
        ((Name.ff g q).place (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC)).2.1 =
        some (placeOf y (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).DF q).1 ∧
      ((Name.ff g q).place (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC)).2.2.1 =
        (placeOf y (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).DF q).2.1 ∧
      ((Name.ff g q).place (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC)).2.2.2 =
        (placeOf y (Sz.ofHdr P.h u0 (lookNo (·.kT) y fsA L) NC).DF q).2.2 := by
  obtain ⟨ls, Z, hZ, -⟩ := hA g hg
  exact place_eq_placeOf_of_layout hy Sw hp4
    (ok_ofHdr hy hC hZ hH u0 _ NC (planes_ofHdr hy hH fsA hA u0 NC)) hg q hv

end

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.tests_of_layout
#print axioms OnBytes.HonestTrace.planeCols_of_layout
#print axioms OnBytes.HonestTrace.planeCols_of_headLayout
#print axioms OnBytes.HonestTrace.tests_of_config
#print axioms OnBytes.HonestTrace.fit_ofHdr
#print axioms OnBytes.HonestTrace.ok_ofHdr
#print axioms OnBytes.HonestTrace.lmb_of_fill
#print axioms OnBytes.HonestTrace.planes_ofHdr
#print axioms OnBytes.HonestTrace.place_eq_addrA_of_returns
#print axioms OnBytes.HonestTrace.place_eq_placeOf_of_returns
