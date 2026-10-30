-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoHead.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoHead.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  owed3_at, head_cut
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  drawsA, drawsEv, owed3
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoHead
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoDraws
import Johnson.Top.H.FlPort.FoPadCut

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun

/-- The three numbers in the record. -/
theorem owed3_at (M : PadMid) (pub : Array Nat) (F : Fork) :
    (M.heard pub F).owedObjects = F.owed.size ∧ (M.heard pub F).owedPlanes = F.owed.size + 1 ∧
      (M.heard pub F).owedJoin = F.owed.size + 2 := by
  refine ⟨rfl, ?_, ?_⟩
  · show (F.owed.push _).size = _
    rw [Array.size_push]
  · show ((F.owed.push _).push _).size = _
    rw [Array.size_push, Array.size_push]

/-- The draws in a run of lkPad. -/
theorem head_cut {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (hc : PadCut calls pub lid F c g F' c' M) :
    M.F4 = owed3 F ∧ Evs (drawsEv (M.h pub) M.theta M.alpha) c M.c4 ∧
      (¬ (M.h pub).NC > 1 → M.theta = zeroE) ∧ M.a = drawsA (M.h pub) M.theta M.alpha := by
  obtain ⟨d1, d2, d3, d4⟩ := draws_ok _ _ _ _ _ _ _ _ hc.draws
  exact ⟨d2, d1, d3, d4⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K)

end

end Fo.Tp
