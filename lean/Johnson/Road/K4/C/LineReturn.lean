-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LineReturn.lean: CONDITIONAL.

What is here. The layers' own rounds (sub-protocol K4), the lookup's join: the form of the keys of
a segment at a layer (Env.line, OnBytes/Model/LayerForms.lean) RETURNS at each of the library's
thirty-four families, where the tensors that its text names are found and their blocks or entries
are there. The text of each family's arm is the library's line_‹family›_eq
(Johnson/Road/FormsKeysA.lean to FormsKeysD.lean). Three definitions of hypotheses or numbers;
statements and proofs. General in the sizes.

  `bind_there`, `bind_at`   a step of a text in Option.
  `LineRd v lam`    what the families of all layers read at layer lam.
  `LineRdM v lamM`  what the families of the layers with routed experts read.
  `famWidth v s`     the number of family s's entries, in the verifier's numbers.
  `gateQ_some`      the gate's quotient.
  **`line_some`**     the form is there.

Not shown here. That the hypotheses LineRd and LineRdM hold at any plan: no example is shown here.
WITH THE TWO CLAMPS ON (gcl, rcl), as under the library's eleven switches. Public data alone:
whether a form IS THERE, nothing on what it is worth.
No property is claimed.
-/
import Johnson.Road.K4.C.StreamReturn
import Johnson.Road.FormsKeysB
import Johnson.Road.FormsKeysC
import Johnson.Road.FormsKeysD

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env sumForms)
open Inst.Model.FFSeg (Fam isExp)

variable {v : Env}

/-- A step of a text in Option: what is bound is there, and what follows is there at every value. -/
theorem bind_there {α β : Type} {x : Option α} {f : α → Option β} (hx : x.isSome = true)
    (hf : ∀ a, (f a).isSome = true) : (x >>= f).isSome = true := by
  obtain ⟨a, rfl⟩ := some_of hx
  exact hf a

/-- The same at a known value. -/
theorem bind_at {α β : Type} {x : Option α} {f : α → Option β} {a : α} (e : x = some a)
    (h : (f a).isSome = true) : (x >>= f).isSome = true := by
  subst e
  exact h

/-- **What the families of all layers read at layer lam.** This defines a hypothesis; the definition
claims nothing. -/
structure LineRd (v : Env) (lam : ℕ) : Prop where
  u : Long v "u" lam (v.y.h.f / v.y.S2)
  g0 : Long v "g0" lam (v.y.h.f / v.y.S2)
  gh : Long v "gh" lam (v.y.h.f / v.y.S2)
  gc : Long v "gc" lam (v.y.h.f / v.y.S2)
  s : Long v "s" lam (v.y.h.f / v.y.S2)
  ru : Long v "ru" lam (v.y.h.f / v.y.S2)
  rg : Long v "rg" lam (v.y.h.f / v.y.S2)
  aw : Long v "aw" lam (v.y.h.d / v.y.S2)
  mw : Long v "mw" lam (v.y.h.d / v.y.S2)
  ra : Long v "ra" lam (v.y.h.d / v.y.S2)
  rm : Long v "rm" lam (v.y.h.d / v.y.S2)
  ro : Long v "ro" lam (v.y.h.d / v.y.S2)
  rd : Long v "rd" lam (v.y.h.d / v.y.S2)
  qkw : Long v "qkw" lam (v.y.nqk / v.y.S2)
  rqk : Long v "rqk" lam (v.y.nqk / v.y.S2)
  q : Long v "q" lam (v.y.dq / v.y.S2)
  kx : Long v "kx" lam (v.y.nqk / v.y.S2 - v.y.dq / v.y.S2)
  vw : Long v "vw" lam (v.y.dkv / v.y.S2)
  rv : Long v "rv" lam (v.y.dkv / v.y.S2)
  vv : Long v "v" lam (v.y.dkv / v.y.S2)
  s0 : Strm v (2 * lam)
  s1 : Strm v (2 * lam + 1)
  s2 : Strm v (2 * lam + 2)
  a : Short v "a" "zt" lam v.y.h.d
  m : Short v "m" "zt" lam v.y.h.d
  row : ∃ b trow, v.tabAt "ar@zt" = some b ∧ v.y.T_ "row" = some trow ∧
    ∀ x, x < v.y.NN * ledNR v.y.h.xl →
      (v.U3at b (trow.OFF + (v.y.NN * lam + x / ledNR v.y.h.xl) * ledNR v.y.h.xl +
        x % ledNR v.y.h.xl)).isSome = true
  fe : v.y.h.fe ≤ v.y.h.f
  dq : v.y.dq ≤ v.y.nqk

/-- **What the families of the layers with routed experts read**, at such a layer's number lamM
among these. This defines a hypothesis; the definition claims nothing. -/
structure LineRdM (v : Env) (lamM : ℕ) : Prop where
  xr : Short v "xr" "zt" lamM v.y.h.d
  lr : Short v "lr" "zt" lamM v.y.h.NE
  rl : Short v "rl" "zt" lamM v.y.h.NE
  sel : Short v "sel" "zt" lamM v.y.h.NE
  ly : Short v "ly" "zt" lamM v.y.h.NE
  l3 : Short v "l3" "zt" lamM v.y.h.NE
  sc : Short v "sc" "zt" lamM 1

/-- The number of a family's entries, in the verifier's numbers. -/
def famWidth (v : Env) : Fam → ℕ
  | .G | .U | .UT | .GH | .UH | .G0 | .F | .CG => v.y.h.f
  | .QK | .QKH | .CQK => v.y.nqk
  | .N1 | .N2 | .O | .D | .XR | .OH | .DH | .N1H | .N2H | .CN1 | .CN2 => v.y.h.d
  | .V | .VH | .CV => v.y.dkv
  | .LR | .LT | .DD | .LH | .SEL | .L3 | .CLR => v.y.h.NE
  | .ROW => v.y.NN * ledNR v.y.h.xl
  | .MR => 1

/-- The gate's quotient is there. -/
theorem gateQ_some {lam a b : ℕ} (R : LineRd v lam) (hg : v.y.h.gcl = true) (wh : Array E)
    (hb : b ≤ v.y.h.f) : (gateQ v lam wh a b).isSome = true := by
  have hn : b / v.y.S2 - 0 / v.y.S2 ≤ v.y.h.f / v.y.S2 := by
    rw [Nat.zero_div, Nat.sub_zero]
    exact Nat.div_le_div_right hb
  have h0 : 0 / v.y.S2 ≤ a / v.y.S2 := by
    rw [Nat.zero_div]
    exact Nat.zero_le _
  unfold gateQ
  rw [hg]
  exact bind_there (SBA_some R.g0 h0 hn) fun _ => bind_there (SBA_some R.gh h0 hn) fun _ => rfl

/-- **THE FORM OF A FAMILY's KEYS AT A LAYER IS THERE.** CONDITIONAL: on what the family reads (R
for a family of all layers, M for one of the layers with routed experts), on the two clamps, and on
the numbers of the weights: at most one for each block (hw), and, for the rows of digits, at most
one for each digit (he). -/
theorem line_some (s : Fam) {lam : ℕ} {ew wh : Array E} (hg : v.y.h.gcl = true)
    (hr : v.y.h.rcl = true) (R : isExp s = false → LineRd v lam)
    (M : isExp s = true → LineRdM v (lam / 2)) (hw : wh.size ≤ famWidth v s / v.y.S2)
    (he : s = .ROW → ew.size ≤ v.y.NN * ledNR v.y.h.xl) :
    (v.line (segName s) lam ew wh).isSome = true := by
  have z0 : ∀ a : ℕ, 0 / v.y.S2 ≤ a / v.y.S2 := fun a => by
    rw [Nat.zero_div]
    exact Nat.zero_le _
  have zn : ∀ {b n : ℕ}, b ≤ n → b / v.y.S2 - 0 / v.y.S2 ≤ n / v.y.S2 := fun {b n} h => by
    rw [Nat.zero_div, Nat.sub_zero]
    exact Nat.div_le_div_right h
  cases s with
  | G =>
    have R := R rfl
    show (v.line "G" lam ew wh).isSome = true
    rw [line_G_eq]
    split_ifs
    · exact bind_there (gateQ_some R hg wh (Nat.le_refl _)) fun _ =>
        site_some _ _ _ _ (SA_some R.rg hw)
    · exact bind_there (gateQ_some R hg wh R.fe) fun _ =>
        bind_there (site_some _ _ _ _ (SBA_some R.rg (z0 _) (zn R.fe))) fun _ =>
        bind_there (gateQ_some R hg wh (Nat.le_refl _)) fun _ =>
        bind_there (site_some _ _ _ _ (SBA_some R.rg (z0 _) (zn (Nat.le_refl _)))) fun _ => rfl
  | U =>
    have R := R rfl
    show (v.line "U" lam ew wh).isSome = true
    rw [line_U_eq]
    split_ifs
    · exact bind_there (SBA_some R.u (z0 _) (zn (Nat.le_refl _))) fun _ =>
        site_some _ _ _ _ (SA_some R.ru hw)
    · exact bind_there (SBA_some R.u (z0 _) (zn R.fe)) fun _ =>
        bind_there (site_some _ _ _ _ (SBA_some R.ru (z0 _) (zn R.fe))) fun _ =>
        bind_there (SBA_some R.u (z0 _) (zn (Nat.le_refl _))) fun _ =>
        bind_there (site_some _ _ _ _ (SBA_some R.ru (z0 _) (zn (Nat.le_refl _)))) fun _ => rfl
  | UT =>
    show (v.line "UT" lam ew wh).isSome = true
    rw [line_UT_eq]
    exact bind_there (SA_some (R rfl).u hw) fun _ => rfl
  | QK =>
    have R := R rfl
    show (v.line "QK" lam ew wh).isSome = true
    rw [line_QK_eq]
    exact bind_there (bind_there (SBA_some R.qkw (z0 _) (zn R.dq)) fun _ =>
        site_some _ _ _ _ (SBA_some R.rqk (z0 _) (zn R.dq))) fun _ =>
      bind_there (bind_there (SBA_some R.qkw (z0 _) (zn (Nat.le_refl _))) fun _ =>
        site_some _ _ _ _ (SBA_some R.rqk (z0 _) (zn (Nat.le_refl _)))) fun _ => rfl
  | N1 =>
    show (v.line "N1" lam ew wh).isSome = true
    rw [line_N1_eq]
    exact bind_there (SA_some (R rfl).aw hw) fun _ => site_some _ _ _ _ (SA_some (R rfl).ra hw)
  | N2 =>
    show (v.line "N2" lam ew wh).isSome = true
    rw [line_N2_eq]
    exact bind_there (SA_some (R rfl).mw hw) fun _ => site_some _ _ _ _ (SA_some (R rfl).rm hw)
  | O =>
    show (v.line "O" lam ew wh).isSome = true
    rw [line_O_eq]
    exact bind_there (SxsA_some (R rfl).s1 wh) fun _ =>
      bind_there (SxsA_some (R rfl).s0 wh) fun _ => site_some _ _ _ _ (SA_some (R rfl).ro hw)
  | D =>
    show (v.line "D" lam ew wh).isSome = true
    rw [line_D_eq]
    exact bind_there (SxsA_some (R rfl).s2 wh) fun _ =>
      bind_there (SxsA_some (R rfl).s1 wh) fun _ => site_some _ _ _ _ (SA_some (R rfl).rd hw)
  | V =>
    show (v.line "V" lam ew wh).isSome = true
    rw [line_V_eq]
    exact bind_there (SA_some (R rfl).vw hw) fun _ => site_some _ _ _ _ (SA_some (R rfl).rv hw)
  | LR =>
    have M := M rfl
    show (v.line "LR" lam ew wh).isSome = true
    rw [line_LR_eq]
    dsimp only
    rw [if_pos hr]
    exact bind_there (sumForms_some fun x hx => bind_there (shA_some M.ly hx) fun _ =>
      bind_there (shA_some M.l3 hx) fun _ => rfl) fun _ =>
      site_some _ _ _ _ (shSum_some M.rl (Nat.le_refl _))
  | XR =>
    show (v.line "XR" lam ew wh).isSome = true
    rw [line_XR_eq]
    exact bind_there (shSum_some (M rfl).xr (Nat.le_refl _)) fun _ => rfl
  | LT =>
    show (v.line "LT" lam ew wh).isSome = true
    rw [line_LT_eq]
    exact sumForms_some fun x hx => bind_there (shA_some (M rfl).lr hx) fun _ => rfl
  | DD =>
    show (v.line "DD" lam ew wh).isSome = true
    rw [line_DD_eq]
    exact bind_there (foldDD_some ew (M rfl).lr (M rfl).sel _
      (fun x hx => List.mem_range.mp (List.mem_reverse.mp hx)) _) fun _ => rfl
  | GH =>
    have R := R rfl
    show (v.line "GH" lam ew wh).isSome = true
    rw [line_GH_eq]
    split_ifs
    · exact bind_there (SA_some R.rg hw) fun _ => rfl
    · exact bind_there (SBA_some R.rg (z0 _) (zn R.fe)) fun _ =>
        bind_there (SBA_some R.rg (z0 _) (zn (Nat.le_refl _))) fun _ => rfl
  | UH =>
    have R := R rfl
    show (v.line "UH" lam ew wh).isSome = true
    rw [line_UH_eq]
    split_ifs
    · exact bind_there (SA_some R.ru hw) fun _ => rfl
    · exact bind_there (SBA_some R.ru (z0 _) (zn R.fe)) fun _ =>
        bind_there (SBA_some R.ru (z0 _) (zn (Nat.le_refl _))) fun _ => rfl
  | OH =>
    show (v.line "OH" lam ew wh).isSome = true
    rw [line_OH_eq]
    exact bind_there (SA_some (R rfl).ro hw) fun _ => rfl
  | DH =>
    show (v.line "DH" lam ew wh).isSome = true
    rw [line_DH_eq]
    exact bind_there (SA_some (R rfl).rd hw) fun _ => rfl
  | VH =>
    show (v.line "VH" lam ew wh).isSome = true
    rw [line_VH_eq]
    exact bind_there (SA_some (R rfl).rv hw) fun _ => rfl
  | LH =>
    show (v.line "LH" lam ew wh).isSome = true
    rw [line_LH_eq]
    exact bind_there (shSum_some (M rfl).rl (Nat.le_refl _)) fun _ => rfl
  | QKH =>
    have R := R rfl
    show (v.line "QKH" lam ew wh).isSome = true
    rw [line_QKH_eq]
    exact bind_there (bind_there (SBA_some R.rqk (z0 _) (zn R.dq)) fun _ => rfl) fun _ =>
      bind_there (bind_there (SBA_some R.rqk (z0 _) (zn (Nat.le_refl _))) fun _ => rfl) fun _ => rfl
  | N1H =>
    show (v.line "N1H" lam ew wh).isSome = true
    rw [line_N1H_eq]
    exact bind_there (SA_some (R rfl).ra hw) fun _ => rfl
  | N2H =>
    show (v.line "N2H" lam ew wh).isSome = true
    rw [line_N2H_eq]
    exact bind_there (SA_some (R rfl).rm hw) fun _ => rfl
  | ROW =>
    obtain ⟨b, trow, e1, e2, H⟩ := (R rfl).row
    show (v.line "ROW" lam ew wh).isSome = true
    rw [line_ROW_eq]
    refine bind_at e1 (bind_at e2 (sumForms_some fun x hx => ?_))
    rw [Option.isSome_map]
    exact H x (Nat.lt_of_lt_of_le hx (he rfl))
  | SEL =>
    show (v.line "SEL" lam ew wh).isSome = true
    rw [line_SEL_eq]
    exact sumForms_some fun x hx => bind_there (shA_some (M rfl).sel hx) fun _ => rfl
  | L3 =>
    show (v.line "L3" lam ew wh).isSome = true
    rw [line_L3_eq]
    exact sumForms_some fun x hx => bind_there (shA_some (M rfl).l3 hx) fun _ => rfl
  | G0 =>
    show (v.line "G0" lam ew wh).isSome = true
    rw [line_G0_eq]
    exact bind_there (SA_some (R rfl).g0 hw) fun _ => rfl
  | CN1 =>
    show (v.line "CN1" lam ew wh).isSome = true
    rw [line_CN1_eq]
    exact bind_there (SA_some (R rfl).aw hw) fun _ =>
      bind_there (shSum_some (R rfl).a (Nat.le_refl _)) fun _ => rfl
  | CN2 =>
    show (v.line "CN2" lam ew wh).isSome = true
    rw [line_CN2_eq]
    exact bind_there (SA_some (R rfl).mw hw) fun _ =>
      bind_there (shSum_some (R rfl).m (Nat.le_refl _)) fun _ => rfl
  | CQK =>
    have R := R rfl
    show (v.line "CQK" lam ew wh).isSome = true
    rw [line_CQK_eq]
    exact bind_there (SA_some R.qkw hw) fun _ =>
      bind_there (SBA_some R.q (z0 _) (zn (Nat.le_refl _))) fun _ =>
      bind_there (SBA_some R.kx (Nat.le_refl _) (Nat.le_refl _)) fun _ => rfl
  | CV =>
    show (v.line "CV" lam ew wh).isSome = true
    rw [line_CV_eq]
    exact bind_there (SA_some (R rfl).vw hw) fun _ =>
      bind_there (SA_some (R rfl).vv hw) fun _ => rfl
  | CLR =>
    have M := M rfl
    show (v.line "CLR" lam ew wh).isSome = true
    rw [line_CLR_eq]
    exact bind_there (sumForms_some fun x hx => bind_there (shA_some M.ly hx) fun _ =>
      bind_there (shA_some M.lr hx) fun _ =>
      bind_there (shA_some M.l3 hx) fun _ => rfl) fun _ => rfl
  | F =>
    have R := R rfl
    show (v.line "F" lam ew wh).isSome = true
    rw [line_F_eq]
    dsimp only
    rw [if_pos hg]
    exact bind_there (SA_some R.g0 hw) fun _ => bind_there (SA_some R.gc hw) fun _ =>
      bind_there rfl fun _ => bind_there (SA_some R.s hw) fun _ => rfl
  | MR =>
    show (v.line "MR" lam ew wh).isSome = true
    rw [line_MR_eq]
    exact bind_there (shA_some (M rfl).sc (Nat.zero_lt_one)) fun _ => rfl
  | CG =>
    show (v.line "CG" lam ew wh).isSome = true
    rw [line_CG_eq]
    exact bind_there (SA_some (R rfl).gh hw) fun _ =>
      bind_there (SA_some (R rfl).gc hw) fun _ => rfl

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.bind_there
#print axioms OnBytes.Road.K4.C.bind_at
#print axioms OnBytes.Road.K4.C.gateQ_some
#print axioms OnBytes.Road.K4.C.line_some
