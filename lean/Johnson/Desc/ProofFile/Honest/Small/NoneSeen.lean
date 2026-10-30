-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/NoneSeen.lean: THAT A PART's MOVES READ NOTHING OF WHAT HAS BEEN
SEEN, as a proposition that can fail, in place of a reading of a text. One definition and three
theorems, two of them CONDITIONAL. By type every move is handed the rounds shown so far and, where
columns are handed, the opened columns (`Seen`, Honest/Frame.lean); whether it reads them is its
body's.

  `Part.readsNoneSeen`   every move says the same at any two values of `Seen` (rounds shown and
                         opened columns), all else the same: a definition
  `quietPart_noneSeen`   the frame's quiet part is such a part
  `scalarsPart_noneSeen`   CONDITIONAL: so is `scalarsPart name n vals`, where vals yields the same
                           at any two fronts that agree in what was heard and handed on
  `lift_noneSeen`   CONDITIONAL: so is a part seated by `Part.lift`, at every lens, where the part
                    is

Why. The field `exact` of `Good` (Honest/Side.lean) draws a part's spent run apart from where the
run stands; should a value of the part hang, through what was seen, on a coin of that run, the
equation says nothing on that run (Honest/Small/Scalars.lean, Limits; Honest/Small/ToyScalars.lean
has a line at which that bites). What is handed on is made of the input and the challenges alone, by
`Move.hand`'s type: so, in the IOP as written in Lean, what was seen is the road by which a coin
that lies under an item sent in front, or in an opened column of a table sent in front, can reach a
value. A part that reads none of it does not walk that road.

Written by the authors of the honest side of the output head's own rounds (K6), in the frame's
folder, not by the frame's authors. All names stand in the namespace ProofFile.Honest.Small, which a
caller opens, BUT FOR ONE: the definition `Part.readsNoneSeen` stands in the type's own namespace
(ProofFile.Honest.Part.readsNoneSeen), so that q.readsNoneSeen can be written.

Limits. No law on a distribution, and no sentence on what a real run's challenges hang on. IT SHUTS
ONE ROAD, IN THE IOP AS WRITTEN IN LEAN: nothing on the challenges heard, which in the compiled
protocol hang on all that was sent, and which by type hold a sealed digest too; nothing on the
input; nothing on the runs that a part is handed. Nothing on the masked sumcheck's part. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small

variable {V W X V' W' Y : Type}

/-- **The part's moves read nothing of what has been seen**: each says the same at any two values of
`Seen` (the rounds shown, and the opened columns or none), at the same coins and the same state. -/
def _root_.ProofFile.Honest.Part.readsNoneSeen (q : Part V W X) : Prop :=
  ∀ mv ∈ q.moves, ∀ c s s' t, mv.say c s t = mv.say c s' t

/-- The frame's quiet part reads nothing of what has been seen. -/
theorem quietPart_noneSeen (n : Nat) : (quietPart n : Part V W X).readsNoneSeen := by
  intro mv hmv c s s' t
  have h := List.eq_of_mem_replicate hmv
  subst h
  rfl

/-- CONDITIONAL. So does the scalars' part, where its values do. -/
theorem scalarsPart_noneSeen (name : String) (n : Nat) (vals : W → Front X → List OnBytes.E)
    (hv : ∀ w (fr fr' : Front X), fr.heard = fr'.heard → fr.own = fr'.own →
      vals w fr = vals w fr') :
    (scalarsPart name n vals : Part V W X).readsNoneSeen := by
  intro mv hmv c s s' t
  have h := List.mem_singleton.1 hmv
  subst h
  show Except.ok (sayE (addL (padTo n (vals t.input ⟨t.heard, t.own, s⟩)) _)) =
    Except.ok (sayE (addL (padTo n (vals t.input ⟨t.heard, t.own, s'⟩)) _))
  rw [hv t.input ⟨t.heard, t.own, s⟩ ⟨t.heard, t.own, s'⟩ rfl rfl]

/-- CONDITIONAL. So does a part seated at whatever lens, where the part does. -/
theorem lift_noneSeen (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (q : Part V' W' Y) (hq : q.readsNoneSeen) : (q.lift see wit get set).readsNoneSeen := by
  intro mv hmv c s s' t
  obtain ⟨mv₀, h₀, rfl⟩ := List.mem_map.1 hmv
  exact hq mv₀ h₀ c s s' (t.narrow wit get)

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.quietPart_noneSeen
#print axioms ProofFile.Honest.Small.scalarsPart_noneSeen
#print axioms ProofFile.Honest.Small.lift_noneSeen
