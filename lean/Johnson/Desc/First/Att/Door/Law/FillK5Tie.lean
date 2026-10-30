-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/FillK5Tie.lean: ONE OF K5Fill's SEVENTEEN PREMISES ON THE FILLING: callerIn: AT «fillK5 d Mg» FOR EVERY Mg: BY LEAN; the other sixteen hang on what lies beneath (other owners' items; keepings). AND WHAT A YES OF look m's Bool GIVES. Mathlib beneath (it names our laws' files).
import Johnson.Desc.First.Att.Door.FillK5
import Johnson.Desc.First.Att.K05T2
import OnBytes.Tie.Pv.Lookup.Forest.FoEv

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First

/-- **K5Fill.callerIn (Johnson/Desc/First/Att/K05T2.lean) at our layer, whatever lies beneath.** -/
theorem fillK5_is_callerIn {Pp W : Type} (d : K5Data) (Mg : Meaning Pp W) (π : Pp) {m first : Nat}
    (h : d.isAtt m = true) (hf : d.first? m = some first) (s : S) :
    (fillK5 d Mg).pub (.callerIn m) (π, s) = Att.P.k5CallerIn3 first s := by
  rw [fillK5_callerIn d Mg h, hf]
  rfl

/-- **What a yes of look m's Bool gives**: the two facts on the lookup's last claim that our runs' returns ask
(RunsReturn, Johnson/Desc/First/Att/K05MadeAt.lean), and that both homes are laid. -/
theorem lookAtt_gives {s : S} (h : lookAttB s = true) :
    ∃ a g gL, s.here = .att a ∧ a.g = some g ∧ a.lookHeard = some gL ∧ sameHeardB g gL = true ∧
      gL.cEnd.ents = #[] ∧ _root_.Fo.FilledA a.F gL.cEnd := by
  unfold lookAttB lookAttUpTo at h
  split at h
  · rename_i a e
    split at h
    · rename_i g gL e1 e2
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      refine ⟨a, g, gL, e, e1, e2, h1, ?_, fun x hx => h3 x hx⟩
      exact Array.isEmpty_iff.1 h2
    · cases h
  · cases h

#print axioms fillK5_is_callerIn
#print axioms lookAtt_gives

end H2K5.Door
