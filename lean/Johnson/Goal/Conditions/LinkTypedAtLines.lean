-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/LinkTypedAtLines.lean: THE FIRST HALF OF Johnson/Goal/Conditions/LinkInScope.lean ((526)), CUT OUT TO THE LETTER, so that it stands over the link's TEXTS and the typed parameters alone (no law on the link beneath it):
configure_sized · scope_reads · record_is_frP · p15Of_of_lines · inScope_typed: at every three public files in scope the parameters that the planner makes for the entry file's link are the typed ones of the full size.
LinkInScope.lean itself is not in this library. No statement and no proof line turns. Nothing on soundness.
-/
import Johnson.Goal.Scope.ScopeLines
import OnBytes.K.KeySalt
import Johnson.Desc.K15.TypedP

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-- What configure returns holds what sized returns on the same lines and shapes. -/
theorem configure_sized {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat} {made : Configured}
    (h : configure l x cfg bits = .ok made) : sized l x = .ok made.sized := by
  unfold configure at h
  obtain ⟨z, hz, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, _, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    exact hz
  · cases h

end OnBytes.Params

namespace Desc.K15
open OnBytes OnBytes.Params VerifiableInference.Desc

/-- In scope, the parameter file's first 32 lines read as the library's typed lines: another file's
theorem (Johnson/Goal/Scope/ScopeLines.lean), at the name that the laws on the sizes use
(recordGround.lines is Params.recordLines by rfl). -/
theorem scope_reads {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) : ∃ b, Params.readLines Z.pol =
    .ok (Params.recordLines, b) :=
  Johnson.G.ScopeLines.inScope_reads hZ

set_option maxRecDepth 100000 in
/-- The typed record's four values are frP's fields: by the kernel. -/
theorem record_is_frP :
    sameP
        { set := settingOf recordLines, codes := recordCodes, S := recordLink, stages :=
          recordStages } frP = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem p15Of_of_lines {pol KL lay b : ByteArray} {p : Model.Verify.Planned}
    (h : Model.Verify.planned pol KL (some lay) = .ok p)
        (hr : Params.readLines pol = .ok (Params.recordLines, b)) :
    p15Of p.chains = frP := by
  obtain ⟨l, rest, shapes, hl, hm⟩ := Model.Verify.planned_madeKey h
  rw [hr] at hl
  injection hl with hl
  injection hl with h1 _
  subst h1
  obtain ⟨hs, T, hT, hL⟩ := sized_link (configure_sized hm)
  obtain rfl : T = recordTable := Option.some.inj (hT.symm.trans record_table)
  have hq := Option.some.inj (hL.symm.trans record_link)
  have q1 : p.chains.made.sized.link = ⟨recordLink, recordTable, ⟨recordG1, 97, recordStages⟩⟩ :=
      congrArg Prod.fst hq
  have q2 : p.chains.made.sized.entryCodes = recordCodes := congrArg Prod.snd hq
  refine Eq.trans ?_ (sameP_eq record_is_frP)
  show P15.mk p.chains.made.sized.set p.chains.made.sized.entryCodes p.chains.made.sized.link.shape
    p.chains.made.sized.link.linked.stages = _
  rw [hs, q1, q2]

/-- **THE LAW.** -/
theorem inScope_typed {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Model.Verify.Planned}
    (h : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) : sameP (p15Of p.chains) frP =
        true := by
  obtain ⟨b, hb⟩ := scope_reads hZ
  rw [p15Of_of_lines h hb]
  simp [sameP]

end Desc.K15

#print axioms Desc.K15.inScope_typed
