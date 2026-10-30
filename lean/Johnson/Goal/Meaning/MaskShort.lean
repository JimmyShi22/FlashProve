--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/MaskShort.lean: under reqOk the request's mask code is not longer than its main
code; so the old mask code in the frame of a code switch out of a link's group is not.

reqOk codes s (OnBytes/Iop/Req.lean), the test that ReqFrame.start puts, asks ioppOk of the last
test's stages; reqShapeOk asks that the first of these stages has the request's two codes; and
ioppStageOk (OnBytes/Iop/Prox.lean) asks maskFits c zk: zk.logN ≤ c.logN. No maker of codes is
spoken of: these are tests on the codes that the record holds.
  mask_le_main: reqOk codes s = true, codes.base[s.code]? = some c, codes.mask[s.maskCode]? =
    some zk give zk.logN ≤ c.logN.
  frame_mask_le: where switchFrame S old T g anew = some W, with reqOk S.codes s and the carried
    rows under the request's two codes: W.zk.logN ≤ W.code.logN.
Not claimed: a bound on the main code's length (the switch's own test on the plan asks logN ≤ 32 of
it); that a record's carried rows are under the request's codes.
-/
import OnBytes.Iop.Req
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes
open OnBytes.Params (ReqShape IoppStage)

theorem mask_le_main {codes : Codes} {s : ReqShape} (h : reqOk codes s = true) {c zk : Code}
    (hc : codes.base[s.code]? = some c) (hz : codes.mask[s.maskCode]? = some zk) :
    zk.logN ≤ c.logN := by
  unfold reqOk at h
  simp only [hc, hz, Bool.and_eq_true] at h
  obtain ⟨hs, -, hi⟩ := h
  unfold reqShapeOk at hs
  simp only [Bool.and_eq_true] at hs
  have hh := hs.2
  cases hl : s.last with
  | nil =>
    rw [hl] at hh
    simp at hh
  | cons t rest =>
    rw [hl] at hh hi
    simp only [List.head?_cons, Option.any_some, Bool.and_eq_true, beq_iff_eq] at hh
    unfold ioppOk at hi
    simp only [Bool.and_eq_true] at hi
    have h1 := hi.2
    unfold ioppStagesOk at h1
    simp only [Bool.and_eq_true] at h1
    have h2 := h1.1
    unfold ioppStageOk at h2
    rw [hh.1.1.1, hh.1.1.2, hc, hz] at h2
    simp only [Bool.and_eq_true] at h2
    have h3 : maskFits c zk = true := h2.1.1.1.2
    unfold maskFits at h3
    exact of_decide_eq_true h3

/-- **The old mask code in the frame of a switch is not longer than the old main code.** -/
theorem frame_mask_le {S : Statement} {s : ReqShape} (h : reqOk S.codes s = true)
    {old : SingleRows} (h1 : old.code = s.code) (h2 : old.maskCode = s.maskCode)
    {T : SwitchTarget} {g : Nat} {anew : Array Nat} {W : SwitchFrame}
    (hW : switchFrame S old T g anew = some W) : W.zk.logN ≤ W.code.logN := by
  unfold switchFrame at hW
  cases e1 : S.codes.base[old.code]? with
  | none => simp [e1] at hW
  | some code =>
    cases e2 : S.codes.mask[old.maskCode]? with
    | none => simp [e1, e2] at hW
    | some zk =>
      cases e3 : S.codes.base[T.shape.code]? with
      | none => simp [e1, e2, e3] at hW
      | some nc =>
        simp only [e1, e2, e3, Option.bind_eq_bind, Option.bind_some] at hW
        by_cases hg : (anew.size == (switchKept old).size) = true
        · simp only [hg, guard, Option.bind_some, Option.pure_def, Option.some.injEq,
            ↓reduceIte] at hW
          subst hW
          rw [h1] at e1
          rw [h2] at e2
          exact mask_le_main h e1 e2
        · simp only [guard, if_neg hg] at hW
          cases hW

#print axioms mask_le_main
#print axioms frame_mask_le

end Meaning.K2
