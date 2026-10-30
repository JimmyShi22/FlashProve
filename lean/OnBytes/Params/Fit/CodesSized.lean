-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/CodesSized.lean: the lists of codes of a proof's chains and of a key's chains, as
the derivation makes them from the parameter file's lines, hold only codes with short messages.

"proofSized" (OnBytes/Params/DeriveReq.lean) and "Plan.keySized" (OnBytes/Plan/KeyOneTime.lean) fill
their lists of codes by "ioppStages" alone: from the stages of the last test, of the three tests on
the table ("linSized") and of the test of the proof of the ranges ("Plan.rangesSized"). Each list of
stages comes from "solveStages" at a group that was solved at a line's two lengths; of a proof's
last test: at that group with its row variables, its slots and the field of its main rows set anew,
which leaves lengths and messages as they are. So OnBytes/Params/Fit/CodesCap.lean applies to each.

Main theorems.
 - linSized_codes: linSized adds only such codes, under the ranges of its three lines.
 - rangesSized_test: the test of what rangesSized returns is what solveTest returns at the line's
   group with some row variables, at some load, and the codes are ioppStages' of that test's stages.
   ("rangesSized_parts", OnBytes/Params/Fit/SizedParts.lean, says which variables and more.)
   rangesSized_codes: so it adds only such codes.
 - rangesLines_group: the group of what rangesLines returns is the line that went in.
 - **proofSized_codes**, **keySized_codes**: CodesCap z.codes, from LinesCap l
   (OnBytes/Params/Fit/LinesCap.lean) and the routine's yes.

Limits. Nothing on the link between two tables (linkSized), whose codes are a list of their own.
Nothing on which number a code has in its list. The program does not import this file.


-/
import OnBytes.Params.Fit.CodesCap
import OnBytes.Params.Fit.LinParts
import OnBytes.Plan.KeyOneTime

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- **The codes that the test on the table adds.** -/
theorem linSized_codes {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x : LinSized} (h : linSized s L T codes = some (x, c)) (HF : GroupCap L.folded)
    (HO : GroupCap L.omega) (HW : GroupCap L.own) (H : CodesCap codes) : CodesCap c := by
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
  exact ioppStages_cap _ _ (ioppStages_cap _ _ (ioppStages_cap _ _ H gU) gO) gW

/-- What rangesSized returns: its test and its codes. -/
theorem rangesSized_test {s : Setting} {L : Plan.RangesLines} {codes c : Codes}
    {z : Plan.RangesSized} (h : Plan.rangesSized s L codes = some (z, c)) :
    ∃ (load : GroupLoad) (kh : Nat × Nat),
      solveTest s .once L.group load id { shapeOf L.group kh.1 false with h := kh.2 } =
        some z.test ∧
      c = (ioppStages z.test.stages codes).2 := by
  unfold Plan.rangesSized at h
  extract_lets at h
  replace h := opt_guard h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨last, _, h⟩ := opt_bind h
  replace h := opt_guard h
  replace h := opt_guard h
  obtain ⟨test, ht, h⟩ := opt_bind h
  split at h
  rename_i stages codes' hio
  obtain ⟨first, _, h⟩ := opt_bind h
  replace h := opt_guard h
  cases h
  exact ⟨_, _, ht, by rw [hio]⟩

/-- The codes that the proof of the ranges adds. -/
theorem rangesSized_codes {s : Setting} {L : Plan.RangesLines} {codes c : Codes}
    {z : Plan.RangesSized} (h : Plan.rangesSized s L codes = some (z, c)) (HG : GroupCap L.group)
    (H : CodesCap codes) : CodesCap c := by
  obtain ⟨load, kh, ht, ec⟩ := rangesSized_test h
  rw [ec]
  exact ioppStages_cap _ _ H
    (solveTest_fit HG HG.logN (Nat.le_trans HG.mask HG.logN) ht).2

/-- The group of the lines of the proof of the ranges is the line that went in. -/
theorem rangesLines_group {shape : Plan.Shape} {group : GroupLine} {partLog : Nat}
    {L : Plan.RangesLines} (h : Plan.rangesLines shape group partLog = some L) :
    L.group = group := by
  unfold Plan.rangesLines at h
  rcases ite_cases h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  · cases ha : Plan.allSome (shape.lookups.map (Plan.lookupOfShape shape.kCol partLog)) with
    | none =>
      rw [ha] at h
      cases h
    | some v =>
      rw [ha] at h
      obtain rfl := Option.some.inj h
      rfl

/-- **The codes of a proof's chains.** -/
theorem proofSized_codes {l : Lines} {sub : Subproofs} {z : ProofSized}
    (h : proofSized l sub = some z) (H : LinesCap l) : CodesCap z.codes := by
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
  have c1 : CodesCap codes1 := by
    have k := ioppStages_cap stages {} codesCap_empty g1
    rw [hio] at k
    exact k
  exact linSized_codes hb H.folded H.omega H.own c1

/-- **The codes of a key's chains.** -/
theorem keySized_codes {l : Lines} {shape : Plan.Shape} {z : Plan.KeySized}
    (h : Plan.keySized l shape = some z) (H : LinesCap l) : CodesCap z.codes := by
  unfold Plan.keySized at h
  extract_lets at h
  obtain ⟨T, _, h⟩ := opt_bind h
  obtain ⟨L, hL, h⟩ := opt_bind h
  extract_lets at h
  replace h := opt_guard h
  obtain ⟨⟨once, c1⟩, ho, h⟩ := opt_bind h
  obtain ⟨⟨ranges, c2⟩, hr, h⟩ := opt_bind h
  cases h
  have k1 : CodesCap c1 := linSized_codes ho H.onceFolded H.onceOmega H.onceOwn codesCap_empty
  exact rangesSized_codes hr (by rw [rangesLines_group hL]; exact H.onceRanges) k1

end OnBytes.Params

#print axioms OnBytes.Params.linSized_codes
#print axioms OnBytes.Params.rangesSized_test
#print axioms OnBytes.Params.rangesSized_codes
#print axioms OnBytes.Params.proofSized_codes
#print axioms OnBytes.Params.keySized_codes
