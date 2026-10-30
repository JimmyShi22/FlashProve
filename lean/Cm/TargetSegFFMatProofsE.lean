-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegFFMatProofsE.lean: proofs of four of the five statements of Cm/TargetSegFFMat.lean,
over p = 2^64 - 2^32 + 1: `matKey_live` (V: the family's value at a live vertex), `matKey_wf` (W:
well formed), `matKey_places` (P: the places read), `matKey_ok`. The fifth, `matKey_dead`, is
proved in Cm/TargetSegFFMatProofs.lean and used here.

Book-keeping of the model's arithmetisation: the seven families of lookup keys of the feed-forward
segment with `isMat s = true` (Cm/SegFFMat.lean; `matKeyFam`, Cm/TargetSegFFMat.lean) are well
formed and read only places of valid cells that the segment reads (`IsFF`, Cm/SegPilotKit.lean).

`ok_runs2`, `ok_runs3`,
`inFF_cSs`, `inFF_mXS`, `inFF_cLow` are Cm/SegFFMatProofsE.lean's. The fields are `Cb.Gl.F`,
`Cb.Gl.E` (Cb/Gl/GlField.lean); the format is
`Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean).





The
statements and their limits: Cm/TargetSegFFMat.lean, the head, Limits.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFMatProofsE
import Cm.TargetSegAll
import Cm.TargetSegFFMatProofsA
import Cm.TargetSegFFMatProofs
import Cm.TargetSegFFMat
import Cm.TargetSegIdxModelProofs
import Cm.TargetSegIdxModel
import Cm.TargetSegFF
import Cm.TargetSegFFAffPass
import Cm.TargetSegFFMatProofsC
import Cm.TargetSegFFMatProofsB
import Cm.TargetSegFFMatProofsD


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.All Inst.Model.Layout Finset
open Ex

/-! ## Nine index atoms meet `IdxAtom.OK`, under the hypotheses below -/

section OK
variable (v L : ℕ) (σj σe σx : List Src)

theorem aV_ok (hj : 5120 ≤ 2 ^ σj.length) (hx : 1024 ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σx) v) :
    (aV L σj σx).OK fmtRef v :=
  ok2 v (first ppref L + 1) ppref.d (ppref.nkv * ppref.ch) 2 .low .high σj σx (by decide)
    (by decide) (by decide) (by decide) hj hx h
theorem aO_ok (hj : 5120 ≤ 2 ^ σj.length) (hx : 5120 ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σx) v) :
    (aO L σj σx).OK fmtRef v :=
  ok2 v (first ppref L + 2) (ppref.nq * ppref.ch) ppref.d 2 .low .high σj σx (by decide) (by decide)
    (by decide) (by decide) hj hx h
theorem aG_ok (hj : 5120 ≤ 2 ^ σj.length) (hx : fOf L ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σx) v) :
    (aG L σj σx).OK fmtRef v :=
  ok2 v (first ppref L + 3) ppref.d (fOf L) 2 .low .high σj σx (by decide) (by decide)
    (by decide) (fOf_pos L) hj hx h
theorem aU_ok (hj : 5120 ≤ 2 ^ σj.length) (hx : fOf L ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σx) v) :
    (aU L σj σx).OK fmtRef v :=
  ok2 v (first ppref L + 4) ppref.d (fOf L) 2 .low .high σj σx (by decide) (by decide)
    (by decide) (fOf_pos L) hj hx h
theorem aD_ok (hj : fOf L ≤ 2 ^ σj.length) (hx : 5120 ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σx) v) :
    (aD L σj σx).OK fmtRef v :=
  ok2 v (first ppref L + (if hasExperts L then 7 else 5)) (fOf L) ppref.d 2 .low .high σj σx
    (by decide) (by decide) (fOf_pos L) (by decide) hj hx h
theorem aR_ok (hj : 5120 ≤ 2 ^ σj.length) (he : 128 ≤ 2 ^ σe.length) (h : Src.OK (σj ++ σe) v) :
    (aR L σj σe).OK fmtRef v :=
  ok2 v (first ppref L + 9) ppref.d ppref.nexp 2 .low .high σj σe (by decide) (by decide)
    (by decide) (by decide) hj he h
theorem aEg_ok (hj : 5120 ≤ 2 ^ σj.length) (he : 128 ≤ 2 ^ σe.length)
    (hx : 8192 ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σe ++ σx) v) : (aEg L σj σe σx).OK fmtRef v :=
  ok3 v (first ppref L + 5) ppref.d ppref.nexp ppref.fe 2 .low .low .high σj σe σx (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hj he hx h
theorem aEu_ok (hj : 5120 ≤ 2 ^ σj.length) (he : 128 ≤ 2 ^ σe.length)
    (hx : 8192 ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σe ++ σx) v) : (aEu L σj σe σx).OK fmtRef v :=
  ok3 v (first ppref L + 6) ppref.d ppref.nexp ppref.fe 2 .low .low .high σj σe σx (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hj he hx h
theorem aEd_ok (hj : 8192 ≤ 2 ^ σj.length) (he : 128 ≤ 2 ^ σe.length)
    (hx : 5120 ≤ 2 ^ σx.length) (h : Src.OK (σj ++ σe ++ σx) v) : (aEd L σj σe σx).OK fmtRef v :=
  ok3 v (first ppref L + 8) ppref.fe ppref.nexp ppref.d 2 .low .low .high σj σe σx (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hj he hx h

end OK

variable [scl : Scl]

/-! ## (W) -/

omit scl in
theorem matKey_wf : Spec.matKey_wf := by
  intro _ X g tb s
  refine fam_wf fmtRef (All.add (WF1.aff fmtRef _ _) ?_)
  cases s
  case V =>
    refine wf_blk fmtRef _ _ fun k _ => ?_
    rw [vx_V]
    exact aV_ok _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
      (ok_runs2 (by omega) (by omega) (by omega))
  case O =>
    refine wf_blk fmtRef _ _ fun k _ => ?_
    rw [vx_O]
    exact aO_ok _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
      (ok_runs2 (by omega) (by omega) (by omega))
  case LR =>
    refine wf_blk fmtRef _ _ fun k _ => ?_
    rw [vx_LR]
    exact aR_ok _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
      (ok_runs2 (by omega) (by omega) (by omega))
  case G =>
    refine All.add (wf_blk fmtRef _ _ fun k _ => ?_) (wf_blk fmtRef _ _ fun k _ => ?_) <;> rw [vx_G]
    · exact aG_ok _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; exact fOf_le _)
        (ok_runs2 (by omega) (by omega) (by omega))
    · exact aEg_ok _ _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
        (by rw [run_length]; norm_num)
        (ok_runs3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  case U =>
    refine All.add (wf_blk fmtRef _ _ fun k _ => ?_) (wf_blk fmtRef _ _ fun k _ => ?_) <;> rw [vx_U]
    · exact aU_ok _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; exact fOf_le _)
        (ok_runs2 (by omega) (by omega) (by omega))
    · exact aEu_ok _ _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
        (by rw [run_length]; norm_num)
        (ok_runs3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  case D =>
    refine All.add (wf_blk fmtRef _ _ fun k _ => ?_) (wf_blk fmtRef _ _ fun k _ => ?_) <;> rw [vx_D]
    · exact aD_ok _ _ _ _ (by rw [run_length]; exact fOf_le _) (by rw [run_length]; norm_num)
        (ok_runs2 (by omega) (by omega) (by omega))
    · exact aEd_ok _ _ _ _ _ (by rw [run_length]; norm_num) (by rw [run_length]; norm_num)
        (by rw [run_length]; norm_num)
        (ok_runs3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  case QK =>
    refine wf_blk fmtRef _ _ fun k _ => ?_
    rw [vx_QK]
    refine qk_ok _ _ _ _ (by simp [run_length]) (by rw [run_length]; norm_num)
      (ok_append
        (ok_append (ok_run (by omega)) (ok_bit _ _) fun _ _ u' hu' => absurd hu' List.not_mem_nil)
        (ok_run (by omega)) fun u hu u' hu' => ?_)
    rw [vars_append, List.mem_append] at hu
    have := mem_vars_run.1 hu'
    rcases hu with hu | hu
    · have := mem_vars_run.1 hu
      omega
    · exact absurd hu List.not_mem_nil
  all_goals exact All.zero

/-! ## (P) -/

section Places2
variable (g : ℕ)

omit scl in
/-- Under `hY`, `hl`, `hi`: every place of the form `gVal g Y l j i` is the place of a valid cell
(`InFF`). This and the next three lemmas are on forms in the blocks (`mblk`) of `wpart`. -/
theorem pl_g (Y : FFSeg.Arr) (hY : Y.cnt DF = DF.nl) {l j i : ℕ}
    (hl : l < 2 ^ 2) (hi : i < 2 ^ 10) :
    InFF g (gVal g Y l j i : CForm Cb.Gl.E) :=
  inFF_gVal g (hY ▸ hl) hi
omit scl in
theorem pl_sel {l j i : ℕ} (hl : l < 2 ^ 2) (hi : i < 2 ^ 10) (hj : j < 2 ^ 20) :
    InFF g (cVal g .sel (l / 2) (j / 2 ^ 13) i : CForm Cb.Gl.E) := by
  refine inFF_cVal g ?_ ?_ hi
  · show l / 2 < 2
    omega
  · show j / 2 ^ 13 < 128
    omega
omit scl in
theorem pl_xr {l j i : ℕ} (hl : l < 2 ^ 2) (hi : i < 2 ^ 10) :
    InFF g (gVal g .xr (l / 2) j i : CForm Cb.Gl.E) := by
  refine inFF_gVal g ?_ hi
  show l / 2 < 2
  omega
omit scl in
theorem pl_hi (Y : FFSeg.Arr) (hY : Y.cnt DF = DF.nl) (hW : Y.width DF = 16384) {l j i : ℕ}
    (hl : l < 2 ^ 2) (hi : i < 2 ^ 10) :
    InFF g (cVal g Y l (DF.fe + j % 2 ^ 13) i : CForm Cb.Gl.E) := by
  refine inFF_cVal g (hY ▸ hl) ?_ hi
  rw [hW]
  show 8192 + j % 2 ^ 13 < 16384
  omega

end Places2

omit scl in
theorem matKey_places : Spec.matKey_places := by
  intro _ X g tb s
  refine fam_places (All.add (Pl1.aff fun b hb => ?_) ?_)
  · unfold lowForm
    exact AllPl.ite (fun hL => inFF_cLow g s (dec3_lt hb).1 hL.2 hL.1 (dec3_lt hb).2.2)
      fun _ => AllPl.cK _
  · cases s
    case V | O | QK =>
      refine places_blk _ _ fun f hf l hl x _ i hi j _ => ?_
      rw [List.mem_singleton] at hf
      subst hf
      exact pl_g g _ rfl hl hi
    case LR =>
      refine places_blk _ _ fun f hf l hl x _ i hi j _ => ?_
      rw [List.mem_singleton] at hf
      subst hf
      exact pl_g g _ rfl hl hi
    case G | U =>
      refine All.add (places_blk _ _ fun f hf l hl x _ i hi j _ => ?_)
        (places_blk _ _ fun f hf l hl x _ i hi j hj => ?_)
      · rw [List.mem_singleton] at hf
        subst hf
        exact pl_g g _ rfl hl hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact pl_sel g hl hi hj
        · exact pl_xr g hl hi
    case D =>
      refine All.add (places_blk _ _ fun f hf l hl x _ i hi j hj => ?_)
        (places_blk _ _ fun f hf l hl x _ i hi j hj => ?_)
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl
        · exact inFF_cVal g hl hj hi
        · exact inFF_cVal g hl hj hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
        rcases hf with rfl | rfl | rfl
        · exact pl_sel g hl hi hj
        · exact pl_hi g _ rfl rfl hl hi
        · exact pl_hi g _ rfl rfl hl hi
    all_goals exact All.zero

/-! ## (V), and what is required of a family of keys (`KeyOK`) -/

omit scl in
theorem matKey_live : Spec.matKey_live := by
  intro _ X g tb s hg hs x₀ W A l x i hl hp hx hi
  cases s
  case G => exact live_G g tb x₀ W A hg hl hx hi
  case U => exact live_U g tb x₀ W A hg hl hx hi
  case QK => exact live_QK g tb x₀ W A hg hl hx hi
  case O => exact live_O g tb x₀ W A hg hl hx hi
  case D => exact live_D g tb x₀ W A hg hl hx hi
  case V => exact live_V g tb x₀ W A hg hl hx hi
  case LR => exact live_LR g tb x₀ W A hg hl hp hx hi
  all_goals exact absurd hs (by decide)

omit scl in
theorem matKey_ok : Spec.matKey_ok := by
  intro _ X g tb s hg hs
  refine ⟨fun x₀ W A S hpad => ⟨fun h l hl hp x hx i hi => ?_, fun h b hb => ?_⟩,
    matKey_wf X g tb s,
    matKey_places X g tb s⟩
  · rw [← matKey_live X g tb s hg hs x₀ W A l x i hl hp hx hi]
    exact h _ (enc3_lt hl (lt_of_lt_of_le hx (len_le s)) hi)
  · by_cases hL : Live s b
    · obtain ⟨l, x, i, hl, hp, hx, hi, hd⟩ := live_cases s hb hL
      have he : b = enc3 (vxOf s) l x i := by
        have h1 : l = b / 2 ^ 10 / 2 ^ vxOf s := (congrArg Prod.fst hd).symm
        have h2 : x = b / 2 ^ 10 % 2 ^ vxOf s := (congrArg (fun q => q.2.1) hd).symm
        have h3 : i = b % 2 ^ 10 := (congrArg (fun q => q.2.2) hd).symm
        unfold enc3
        rw [h1, h2, h3, Nat.div_add_mod', Nat.div_add_mod']
      rw [he, matKey_live X g tb s hg hs x₀ W A l x i hl hp hx hi]
      exact h l hl hp x hx i hi
    · rw [matKey_dead X g tb s x₀ W A b hL]
      exact hpad

end Cm.Seg.TS
