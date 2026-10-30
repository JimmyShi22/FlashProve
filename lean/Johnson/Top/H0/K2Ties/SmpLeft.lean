-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/SmpLeft.lean: THE NAMED READER OF OOD SAMPLES (`smpNamed`,
    Johnson/Desc/Sound/SmpNamed.lean) GIVES BEHIND A CODE SWITCH WHAT IT GIVES IN FRONT, at a member
    whose message was sampled in front. Two theorems. A law file: no sub-protocol imports it.

Why. The code switch's fifth tie owes (the field smp of `K2Owes`, T5.lean): the reader of OOD
    samples gives behind what it gives in front at the members that sit at the index masks' tenant.
    At the closed constant that reader is `smpNamed`: it finds a member's message by a fixed number.

What is said.
  `smpNamed_left`: under `Left s s'` (Left.lean), where the statement in front holds a sampled
      oracle message at the member's fixed number: the reader's two values are one. By
      `K1.smpAt_stay` over the field smp of `Left`.
  `smp_of_named`: so the field smp, at any structure of parameters whose reader is `smpNamed` at its
      own codes: from "inside the fence a sampled message stands at the fixed number of each member
      at the index masks' tenant".

Limits. That last sentence is a premise: it should follow from the promise's clause "the sample is
    held" with "the book's places are the listed ones": NOT TYPED. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.SmpNamed
import Johnson.Desc.K1.Law.SmpHeldAt
import Johnson.Top.H0.K2Ties.T5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open OnBytes.Maker
open VerifiableInference.Desc (Place Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning)

/-- **Under `Left` the named reader's value stays**, at a member whose message was sampled in front.
    -/
theorem smpNamed_left {P : Type} (cs : OnBytes.Codes) (seats : List (ℕ × ℕ)) (z : P) {s s' : S} (hL
    : Left s s') (x : Mem) (X : OnBytes.Oracle) (hx : s.st.oracles[Sound.numAt seats x]? = some X)
        (hs :
    X.sampled = true) :
    smpNamed cs seats (z, s') x.1 x.2 = smpNamed cs seats (z, s) x.1 x.2 := by
  by_cases hq : x.1.seat x.2 ∈ seats
  · rw [smpNamed_at cs seats _ _ _ hq, smpNamed_at cs seats _ _ _ hq]
    exact Desc.K1.smpAt_stay cs _ _ hL.smp _ X hx hs
  · rw [smpNamed_none cs seats _ _ _ hq, smpNamed_none cs seats _ _ _ hq]

/-- **The field smp of `K2Owes`**, at a structure of parameters whose reader is the named one. -/
theorem smp_of_named {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr :
    Frame} (D : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wq rows cols Tok)) (links : List
    ModelPart) (ps : List Place) (k : ℕ) (z : P) (Rch : First.S × Fr.E.Str → Prop) (seats : List (ℕ × ℕ))
    (hD : D.smp = smpNamed D.cs seats) (hS : ∀ a : First.S × Fr.E.Str, fenceAt D Mg₀ links ps k z
    Rch a → ∀ x ∈ D.ms, SitsAt x D.N.index.1 D.N.index.2 → ∃ Y, a.1.st.oracles[Sound.numAt seats x]?
        =
    some Y ∧ Y.sampled = true) :
    ∀ (a : First.S × Fr.E.Str) (s' : First.S), fenceAt D Mg₀ links ps k z Rch a → Left a.1 s' → ∀ x
        ∈ D.ms, SitsAt x D.N.index.1 D.N.index.2 → D.smp (z, s') x.1 x.2 = D.smp (z, a.1) x.1 x.2 :=
        by
  intro a s' ha hL x hx hs
  obtain ⟨Y, h1, h2⟩ := hS a ha x hx hs
  rw [hD]
  exact smpNamed_left D.cs seats z hL x Y h1 h2

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.smpNamed_left
#print axioms VerifiableInference.Desc.First.K2Ties.smp_of_named
