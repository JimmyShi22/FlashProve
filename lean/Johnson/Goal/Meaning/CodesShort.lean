-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/CodesShort.lean: every code in the lists of a proof's chains, MASK CODES TOO,
has a length of at most 2^32 (logN ≤ 32); so the old mask code in the frame of a code switch has.

The library has the like for the messages' lengths (CodesCap: logEll ≤ 64,
OnBytes/Params/Fit/CodesCap.lean:35; proofSized_codes, OnBytes/Params/Fit/CodesSized.lean:109). Its
ground, GroupFit (OnBytes/Params/Fit/SolveCap.lean), holds logN ≤ 32 of both codes of every solved
group; the walk here is that of the two files, with logN kept in the place of logEll.
  CodesN codes: every code of both lists has logN ≤ 32.
  placeCode_n, ioppStages_n, linSized_n: one code more; a list of stages; the test on the table.
  proofSized_n: CodesN z.codes, from LinesCap l and proofSized's return.
  proofSized_read: the same from the return of the reader of the parameter file's security lines
    (linesCap_of_read, OnBytes/Params/Fit/LinesCap.lean:266).
  frame_n: where switchFrame (OnBytes/Iop/Cs.lean) returns W at a statement with CodesN codes:
    W.zk.logN ≤ 32 and W.code.logN ≤ 32.
Not claimed: that a record's codes are a plan's; which number a code has in its list.
-/
import OnBytes.Params.Fit.CodesSized
import OnBytes.Params.Fit.LinesCap
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Params

/-- Every code of both lists has a length of at most 2 ^ 32. -/
def CodesN (codes : Codes) : Prop :=
  (∀ c ∈ codes.base.toList, c.logN ≤ 32) ∧ ∀ c ∈ codes.mask.toList, c.logN ≤ 32

theorem codesN_empty : CodesN {} :=
  ⟨fun _ hc => (List.not_mem_nil hc).elim, fun _ hc => (List.not_mem_nil hc).elim⟩

/-- One code more. -/
theorem placeCode_n {list : Array Code} {c : CodeSize} (hl : ∀ x ∈ list.toList, x.logN ≤ 32)
    (hc : CodeFit c) : ∀ x ∈ (placeCode list c).1.toList, x.logN ≤ 32 := by
  unfold placeCode
  dsimp only
  split
  · exact hl
  · intro x hx
    rw [Array.toList_push] at hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hl x hx
    · obtain rfl := List.mem_singleton.1 hx
      exact hc.1

/-- The codes of a list of stages. -/
theorem ioppStages_n : ∀ (st : List StageSize) (codes : Codes), CodesN codes →
    (∀ y ∈ st, GroupFit y.g) → CodesN (ioppStages st codes).2 := by
  intro st
  induction st with
  | nil =>
    intro codes H _
    exact H
  | cons y rest ih =>
    intro codes H hf
    unfold ioppStages
    dsimp only
    have hy := hf y List.mem_cons_self
    exact ih _ ⟨placeCode_n H.1 hy.1, placeCode_n H.2 hy.2⟩
      fun y' hy' => hf y' (List.mem_cons_of_mem _ hy')

/-- The codes that the test on the table adds. -/
theorem linSized_n {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) (HF : GroupCap L.folded)
    (HO : GroupCap L.omega) (HW : GroupCap L.own) (H : CodesN codes) : CodesN c := by
  obtain ⟨G, X, Y, Z, a, b, stU, stO, stW, eF, eO, eW, hT, hU, hO, hW, _, _, _, _, _, _, _, _, _,
    _, _, ec⟩ := linSized_parts h
  obtain ⟨sX, sY, sZ⟩ := linTurns_solves 33 _ _ _ _ hT
  have fX : GroupFit X.group := fit_of_solves sX (by rw [eF]; exact HF.logN)
    (by rw [eF]; exact Nat.le_trans HF.mask HF.logN)
  have fZ : GroupFit Z.group := fit_of_solves sZ (by rw [eW]; exact HW.logN)
    (by rw [eW]; exact Nat.le_trans HW.mask HW.logN)
  have gU := stages_fit HF.stages fX hU
  have gW := stages_fit HW.stages fZ hW
  have gO : ∀ y ∈ stO, GroupFit y.g := by
    rcases hO with ⟨hs, hO⟩ | rfl
    · exact stages_fit HO.stages (fit_of_solves (sY hs) (by rw [eO]; exact HO.logN)
        (by rw [eO]; exact Nat.le_trans HO.mask HO.logN)) hO
    · intro y hy
      exact (List.not_mem_nil hy).elim
  rw [ec]
  exact ioppStages_n _ _ (ioppStages_n _ _ (ioppStages_n _ _ H gU) gO) gW

/-- **The codes of a proof's chains.** -/
theorem proofSized_n {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) (H : LinesCap l) : CodesN z.codes := by
  unfold proofSized at h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨link, hl, h⟩ := opt_bind h
  obtain ⟨stages, hs, h⟩ := opt_bind h
  obtain ⟨T, _, h⟩ := opt_bind h
  split at h
  rename_i last codes1 hio
  replace h := opt_guard h
  obtain ⟨⟨batch, c2⟩, hb, h⟩ := opt_bind h
  cases h
  have fL : GroupFit link.group := fit_of_solves (solveGroup_solves hl) H.link.logN
    (Nat.le_trans H.link.mask H.link.logN)
  have g1 : ∀ y ∈ stages, GroupFit y.g := by
    refine stages_fit H.link.stages ?_ hs
    exact ⟨fL.1, fL.2⟩
  have c1 : CodesN codes1 := by
    have k := ioppStages_n stages {} codesN_empty g1
    rw [hio] at k
    exact k
  exact linSized_n hb H.folded H.omega H.own c1

/-- From the return of the reader of the security lines. -/
theorem proofSized_read {pol rest : ByteArray} {l : Lines} (hr : readLines pol = .ok (l, rest))
    {sub : Subproofs} {z : ProofSized} (h : proofSized l sub = some z) : CodesN z.codes :=
  proofSized_n h (linesCap_of_read hr)

/-- **The two old codes in the frame of a switch.** -/
theorem frame_n {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {W : SwitchFrame} (h : switchFrame S old T g anew = some W)
    (H : CodesN S.codes) : W.zk.logN ≤ 32 ∧ W.code.logN ≤ 32 := by
  unfold switchFrame at h
  cases h1 : S.codes.base[old.code]? with
  | none => simp [h1] at h
  | some code =>
    cases h2 : S.codes.mask[old.maskCode]? with
    | none => simp [h1, h2] at h
    | some zk =>
      cases h3 : S.codes.base[T.shape.code]? with
      | none => simp [h1, h2, h3] at h
      | some nc =>
        simp only [h1, h2, h3, Option.bind_eq_bind, Option.bind_some] at h
        by_cases hg : (anew.size == (switchKept old).size) = true
        · simp only [hg, guard, Option.bind_some, Option.pure_def, Option.some.injEq,
            ↓reduceIte] at h
          subst h
          exact ⟨H.2 zk (Array.mem_toList_iff.2 (Array.mem_of_getElem? h2)),
            H.1 code (Array.mem_toList_iff.2 (Array.mem_of_getElem? h1))⟩
        · simp [hg, guard] at h

#print axioms proofSized_n
#print axioms proofSized_read
#print axioms frame_n

end Meaning.K2
