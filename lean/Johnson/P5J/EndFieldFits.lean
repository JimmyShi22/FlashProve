-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/EndFieldFits.lean: LEAN's OWN WORD THAT end_first_full (Johnson/Desc/Sound/EndFirstAt.lean)
HAS THE TYPE OF THE FIELD END OF TablesFitR (Johnson/P5J/TopTablesR.lean) AT THE TWO LETTERS AT WHICH THE
TOWER ASKS IT: links := fullLinks, ps := At.ps (Johnson/P5J/LettersAt.lean), whatever the other letters.
That theorem is stated at flatPlacesOf fullLinks true, which is At.ps unfolded.
  end_at_ps   the field's text at fullLinks | At.ps: a statement of its own.
  an example (no declaration: it is to be counted by nobody): a TablesFitR at these two letters with the
              field END laid anew by name: it says nothing; that it elaborates is the fit.
What is not claimed. Anything beyond that fit. Nothing on soundness.

-/
import Johnson.Desc.Sound.EndFirstAt
import Johnson.P5J.LettersAt
import Johnson.P5J.TopTablesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J

open OnBytes OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound
open _root_.Run _root_.Run.PQ

/-- **END in the field's own letters, at fullLinks and At.ps.** -/
theorem end_at_ps : ∀ i, openAfter (insQ fullLinks At.ps) (outsQ fullLinks At.ps)
    (· ∈ start fullLinks) At.ps.length i → i ∈ endFirst := end_first_full

variable {C : CK} {D : WholeD} {all : List LeftT} {Y P P₀ S₁' S₂' S₃' X₁ X₂ Cl W : Type}
  (start₂ : P → S₂') (start₃ : P → S₁' → S₂' → Option S₃')
  (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl W)
  (Q : Places D all (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') W)
  (get : P × S₁' → P₀ × VerifiableInference.Desc.First.S) (N₁ : Numbers)
  (Mg₁ : VerifiableInference.Desc.First.Meaning P₀ W)
  (R₀ : (P × S₁') × (EAll D all).Str → W → Prop) (Ns : NumbersS)
  (Mg : MeaningS S₂' (P × S₁') W) (Pm : PromMeaning S₂')
  (PLm : PromMeaningL S₂' S₃' (P × S₁')) (split : Bool)
  (Q₂ : ℕ → ((P × S₁') × S₂') × (EAll D all).Str → ((P × S₁') × S₂') × (EAll D all).Str → Prop)
  (Rc : P × S₁' → Prop)

/-- The field END, laid by its name, at fullLinks and At.ps. -/
example
    (fit : TablesFitR start₂ start₃ T Q get N₁ Mg₁ fullLinks At.ps R₀ Ns Mg Pm PLm split Q₂ Rc) :
    TablesFitR start₂ start₃ T Q get N₁ Mg₁ fullLinks At.ps R₀ Ns Mg Pm PLm split Q₂ Rc :=
  { fit with END := end_at_ps }

end P5J

#print axioms P5J.end_at_ps
