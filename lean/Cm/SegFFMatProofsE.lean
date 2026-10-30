-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFMatProofsE.lean: lemmas on the places that the key families read (`inFF_cSs`, `inFF_mXS`,
`inFF_cLow`) and on runs that do not meet. The statements on the families themselves:
Cm/TargetSegFFMatProofsE.lean.
-/
import Cm.SegFFMatProofs
import Cm.SegFFMatProofsB
import Cm.SegFFMatProofsD

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.All Inst.Model.Layout Finset
open Ex

/-! ## Runs that do not meet -/

theorem ok_runs2 {a m b n v : ℕ} (h : a + m ≤ b ∨ b + n ≤ a) (ha : a + m ≤ v) (hb : b + n ≤ v) :
    Src.OK (Src.run a m ++ Src.run b n) v :=
  ok_append (ok_run ha) (ok_run hb) fun u hu u' hu' => by
    have := mem_vars_run.1 hu
    have := mem_vars_run.1 hu'
    omega

theorem ok_runs3 {a m b n c r v : ℕ} (h : a + m ≤ b ∨ b + n ≤ a) (h' : a + m ≤ c ∨ c + r ≤ a)
    (h'' : b + n ≤ c ∨ c + r ≤ b) (ha : a + m ≤ v) (hb : b + n ≤ v) (hc : c + r ≤ v) :
    Src.OK (Src.run a m ++ Src.run b n ++ Src.run c r) v :=
  ok_append (ok_runs2 h ha hb) (ok_run hc) fun u hu u' hu' => by
    rw [vars_append, List.mem_append] at hu
    have := mem_vars_run.1 hu'
    rcases hu with hu | hu <;> have := mem_vars_run.1 hu <;> omega

variable [scl : Scl]

/-! ## The places that the key families read -/

section Places
variable {E : Type} [Field E] (g : ℕ)

theorem inFF_cSs {q rh : CForm E} (hq : InFF g q) (hr : InFF g rh) (k : ℕ) : InFF g (cSs q rh k) :=
  AllPl.sub (AllPl.smul _ (AllPl.sub (AllPl.cK _) (AllPl.smul _ hq))) (AllPl.smul _ hr)

omit scl in
theorem inFF_mXS {s j i : ℕ} (hs : s ≤ 2 * DF.nl) (hj : j < DF.d) (hi : i < DF.T) :
    InFF g (mXS g s j i : CForm E) := by
  unfold mXS FFSeg.streamAt
  split_ifs with h0 h8
  · exact inFF_cVal g Nat.one_pos hj hi
  · exact inFF_cVal g Nat.one_pos hj hi
  · refine inFF_cVal g ?_ hj hi
    show s - 1 < 2 * DF.nl - 1
    omega

theorem inFF_cLow (s : FFSeg.Fam) {l x i : ℕ} (hl : l < DF.nl) (hp : FFSeg.present s l = true)
    (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    InFF g (cLow g s l x i : CForm E) := by
  have V : ∀ {Y : FFSeg.Arr} {a j : ℕ},
      a < Y.cnt DF → j < Y.width DF → InFF g (cVal g Y a j i : CForm E) :=
    fun ha hj => inFF_cVal g ha hj hi
  cases s
  case G => exact inFF_cSs g (AllPl.add (V hl hx) (AllPl.smul _ (V hl hx))) (V hl hx) _
  case U => exact inFF_cSs g (V hl hx) (V hl hx) _
  case QK => exact inFF_cSs g (V hl hx) (V hl hx) _
  case O =>
    exact inFF_cSs g
      (AllPl.sub (inFF_mXS g (by omega) hx hi) (inFF_mXS g (by omega) hx hi)) (V hl hx) _
  case D =>
    exact inFF_cSs g
      (AllPl.sub (inFF_mXS g (by omega) hx hi) (inFF_mXS g (by omega) hx hi)) (V hl hx) _
  case V => exact inFF_cSs g (V hl hx) (V hl hx) _
  case LR =>
    have half : l / 2 < DF.ne :=
      FFSeg.CastValid.half_lt hl (by simpa [FFSeg.present, FFSeg.isExp] using hp)
    exact inFF_cSs g (AllPl.add (AllPl.smul _ (V half hx)) (V half hx)) (V half hx) _
  all_goals exact AllPl.cK _

end Places

end Cm.Seg
