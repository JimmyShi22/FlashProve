-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/NoneSeenSum.lean: NOT a law on a distribution: CONDITIONAL: THAT
THE MASKED SUMCHECK's PART (`sumPart`, Honest/Sum.lean) READS NOTHING OF WHAT HAS BEEN SEEN
(`Part.readsNoneSeen`, Honest/Small/NoneSeen.lean: neither the rounds shown nor the opened columns),
WHERE ITS JOB DOES NOT.

  `SumJob.readsNoneSeen`   all five functions of the job (points, lead, round, inY, ends) yield the
                           same at any two fronts that agree in what was heard and handed on: a
                           definition
  `askG_noneSeen`, `said_noneSeen`   CONDITIONAL on the same: the steps
  `sumPart_noneSeen`   CONDITIONAL on the same: the part's moves read nothing of what has been seen

A thin file apart: it imports Honest/SumLaw/Said.lean (a file of the folder of the masked sumcheck's
law, by other authors; it states no law on a distribution) for `askG`, the four forms `saidFirst`,
`saidVar`, `saidY`, `saidEnds`, and `sumPart_moves`, which has the part's moves in those words.

Written by the authors of the honest side of the output head's own rounds (K6), in the frame's
folder, not by the frame's authors. All names stand in the namespace ProofFile.Honest.Small, which a
caller opens, BUT FOR ONE: the definition `SumJob.readsNoneSeen` stands in the type's own namespace
(ProofFile.Honest.SumJob.readsNoneSeen), so that J.readsNoneSeen can be written of a job J.

Limits. Those of Honest/Small/NoneSeen.lean, but for its word on the masked sumcheck's part. A front
(`Front`) holds a `Seen`: so "at any two fronts that agree in what was heard and handed on" binds
every value of the rounds shown and of the opened columns. `inY` is handed the "ends" run's own
coins, by `sumPart`'s text (Honest/Sum.lean), which hands it `endCoins`: that is no reading of what
was seen. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Said
import Johnson.Desc.ProofFile.Honest.Small.NoneSeen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open OnBytes (E)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open ProofFile.Honest.SumLaw

variable {V W X : Type}

/-- **The job reads nothing of what has been seen**: its five functions yield the same at any two
fronts that agree in what was heard and what was handed on. -/
def _root_.ProofFile.Honest.SumJob.readsNoneSeen (J : SumJob W X) : Prop :=
  ∀ w (fr fr' : Front X), fr.heard = fr'.heard → fr.own = fr'.own →
    J.points w fr = J.points w fr' ∧ J.lead w fr = J.lead w fr' ∧ J.round w fr = J.round w fr' ∧
      J.inY w fr = J.inY w fr' ∧ J.ends w fr = J.ends w fr'

/-- CONDITIONAL. What a move says, in the part's own words, is the same at any two values of `Seen`,
where the job and the move's form read nothing of what has been seen. -/
theorem askG_noneSeen (name endName : String) (J : SumJob W X) (hJ : J.readsNoneSeen)
    (f : List Var → Front X → List E → List E → List E → W → List E)
    (hf : ∀ w (fr fr' : Front X), fr.heard = fr'.heard → fr.own = fr'.own →
      ∀ all u m ds, f all fr u m ds w = f all fr' u m ds w)
    (n : Nat) (c : SumCoins name endName J) (s s' : Seen) (t : State W X) :
    askG name endName J f n c s t = askG name endName J f n c s' t := by
  have hp := (hJ t.input
    ⟨t.heard.take (t.heard.length - n), t.own, s.front n⟩
    ⟨t.heard.take (t.heard.length - n), t.own, s'.front n⟩ rfl rfl).1
  have h1 : J.callAt t.input ⟨t.heard.take (t.heard.length - n), t.own, s.front n⟩ =
      J.callAt t.input ⟨t.heard.take (t.heard.length - n), t.own, s'.front n⟩ := by
    simp only [SumJob.callAt, hp]
  show f (J.callAt t.input
      ⟨t.heard.take (t.heard.length - n), t.own, s.front n⟩).all _ _ _ _ _ =
    f (J.callAt t.input
      ⟨t.heard.take (t.heard.length - n), t.own, s'.front n⟩).all _ _ _ _ _
  rw [h1]
  exact hf t.input ⟨t.heard.take (t.heard.length - n), t.own, s.front n⟩
    ⟨t.heard.take (t.heard.length - n), t.own, s'.front n⟩ rfl rfl _ _ _ _

/-- CONDITIONAL on hJ. Each of the four forms of a move yields the same at any two fronts that agree
in what was heard and handed on. -/
theorem said_noneSeen (J : SumJob W X) (hJ : J.readsNoneSeen) (w : W) (fr fr' : Front X)
    (hh : fr.heard = fr'.heard) (ho : fr.own = fr'.own) (all : List Var) (u m ds : List E) :
    saidFirst J all fr u m ds w = saidFirst J all fr' u m ds w ∧
    (∀ i, saidVar J i all fr u m ds w = saidVar J i all fr' u m ds w) ∧
    (∀ e, saidY J e all fr u m ds w = saidY J e all fr' u m ds w) ∧
    ∀ e, saidEnds J e all fr u m ds w = saidEnds J e all fr' u m ds w := by
  obtain ⟨-, h2, h3, h4, h5⟩ := hJ w fr fr' hh ho
  exact ⟨by simp only [saidFirst, h2], fun _ => by simp only [saidVar, h3],
    fun _ => by simp only [saidY, h4], fun _ => by simp only [saidEnds, h5]⟩

/-- CONDITIONAL. **The masked sumcheck's part reads nothing of what has been seen, where its job
does not.** -/
theorem sumPart_noneSeen (name endName : String) (J : SumJob W X) (hJ : J.readsNoneSeen) :
    (sumPart name endName J : Part V W X).readsNoneSeen := by
  intro mv hmv c s s' t
  rw [sumPart_moves] at hmv
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hmv
  show Except.ok (sayE (g c s t)) = Except.ok (sayE (g c s' t))
  suffices h : g c s t = g c s' t by rw [h]
  unfold sumGs at hg
  simp only [List.mem_append, List.mem_singleton, List.mem_map, List.mem_range] at hg
  rcases hg with (rfl | ⟨i, -, rfl⟩) | hg
  · exact askG_noneSeen name endName J hJ _
      (fun w fr fr' hh ho all u m ds => (said_noneSeen J hJ w fr fr' hh ho all u m ds).1) _ c _ _ t
  · exact askG_noneSeen name endName J hJ _
      (fun w fr fr' hh ho all u m ds => (said_noneSeen J hJ w fr fr' hh ho all u m ds).2.1 i) _ c
      _ _ t
  · cases he : J.shape.ends with
    | none =>
      rw [he] at hg
      cases hg
    | some e =>
      rw [he] at hg
      rcases List.mem_pair.1 hg with rfl | rfl
      · exact askG_noneSeen name endName J hJ _
          (fun w fr fr' hh ho all u m ds => (said_noneSeen J hJ w fr fr' hh ho all u m ds).2.2.1 e)
          _ c _ _ t
      · exact askG_noneSeen name endName J hJ _
          (fun w fr fr' hh ho all u m ds => (said_noneSeen J hJ w fr fr' hh ho all u m ds).2.2.2 e)
          _ c _ _ t

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.askG_noneSeen
#print axioms ProofFile.Honest.Small.said_noneSeen
#print axioms ProofFile.Honest.Small.sumPart_noneSeen
#print axioms ProofFile.Honest.SumJob.readsNoneSeen
