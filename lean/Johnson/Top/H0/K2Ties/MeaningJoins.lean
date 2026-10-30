-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/MeaningJoins.lean: SIX FIELDS OF WHAT IS OWED AT A PLACE OF THE CODE SWITCH
    (`K2AllOwes`, Assembly.lean) ARE THE COMPOSED MEANING's OWN FIELDS, BY UNFOLDING. Six theorems.
    A law file: no sub-protocol imports it.

Why. The ties speak of a pin, of "every leaf is shown", of "no collision", of "the sample is held"
    and of the rows at the place's own parameters (the typed structure's codes c, a description, a
    numbering of arrays, a reader of OOD samples, a list of members). The composed meaning `mgAll D
    Mg₀` (Johnson/Desc/Sound/MgAll.lean) has these sentences as its fields at D's parameters. Where
    the place's parameters ARE D's, the fields hold outright.

What is said, at the description D.G, the numbering D.arr, the members D.ms; c: the place's codes.
  `hheld_paid`, `hrowM_paid`: NO CONDITION: by definition.
  `hshown_of_cs`: from c = D.cs.
  `hpin_of_cs`, `hpin3_of_cs`, `hnc_of_cs`: from c = D.cs and "D's reader of OOD samples is the
      named one at D's own codes and a list of tenants" (`smpNamed`,
      Johnson/Desc/Sound/SmpNamed.lean), at the place's reader := the named one at c and that list.
  c is a variable: so the one equation is spent by substitution, and the typed structure's `r.cs`
      goes in for c.

Limits. THE EQUATION c = D.cs AT THE WRITTEN TYPED STRUCTURES AND THE CLOSED CONSTANT IS NOT SHOWN
    HERE. The field on the carried claim (hcar) is not here: it hangs on the constant's own term. No
    soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.SmpNamed
import Johnson.Top.H0.K2Ties.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (smpHeld)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning rowSays wordsAtFirst)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} (D : MgData Xi P Tok
    rows cols nR X) (Mg₀ : Meaning P (Wq rows cols Tok))

theorem hheld_paid : ∀ j t (a : P × First.S), (mgAll D Mg₀).held j t a = smpHeld a.2.st a.2.book j t
    := fun _ _ _ => rfl

theorem hrowM_paid (m : ℕ) : ∀ c a y w, (mgAll D Mg₀).row m c a y w → rowSays D.N (wordsAtFirst (P
    := P) D.arr) m c a y w := fun _ _ _ _ h => h

theorem hshown_of_cs {c : OnBytes.Codes} (e : c = D.cs) : ∀ j t y, (mgAll D Mg₀).shown j t y ↔
    shownJT c D.G D.ms j t y := by
  subst e
  exact fun _ _ _ => Iff.rfl

theorem hpin_of_cs {c : OnBytes.Codes} (e : c = D.cs) (seats : List (ℕ × ℕ)) (hD : D.smp = smpNamed
    D.cs seats) : ∀ (q : ℕ × ℕ) a y w, pinJT c D.G D.arr (smpNamed c seats) D.ms q.1 q.2 a y w →
    (mgAll D Mg₀).pin q.1 q.2 a y w := by
  subst e
  intro q a y w h
  rw [mgAll_pin, hD]
  exact h

theorem hpin3_of_cs {c : OnBytes.Codes} (e : c = D.cs) (seats : List (ℕ × ℕ)) (hD : D.smp = smpNamed
    D.cs seats) : ∀ (q : ℕ × ℕ) a y w, (mgAll D Mg₀).pin q.1 q.2 a y w → pinJT c D.G D.arr (smpNamed
    c seats) D.ms q.1 q.2 a y w := by
  subst e
  intro q a y w h
  rw [mgAll_pin, hD] at h
  exact h

theorem hnc_of_cs {c : OnBytes.Codes} (e : c = D.cs) (seats : List (ℕ × ℕ)) (hD : D.smp = smpNamed
    D.cs seats) : ∀ j t a y, (mgAll D Mg₀).noColl j t a y ↔ noCollJT c D.G (smpNamed c seats) D.ms j
    t a y := by
  subst e
  intro j t a y
  rw [mgAll_noColl, hD]

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.hheld_paid
#print axioms VerifiableInference.Desc.First.K2Ties.hrowM_paid
#print axioms VerifiableInference.Desc.First.K2Ties.hshown_of_cs
#print axioms VerifiableInference.Desc.First.K2Ties.hpin_of_cs
#print axioms VerifiableInference.Desc.First.K2Ties.hpin3_of_cs
#print axioms VerifiableInference.Desc.First.K2Ties.hnc_of_cs
