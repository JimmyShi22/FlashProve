-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/SeatedJoined.lean: WHAT ONE SENDING LAYS INTO THE RECORD's BOOK, WHOLE
(`K1.SeatedBy`, Johnson/Desc/K1/Law/SeatedAtRecord.lean), AT THE TWO SENDINGS THAT THE FIRST CHAIN
HOLDS JOINED WITH A BLOCK BEHIND THEM. Statements with their proofs. No statement here names the
table of joints.
Main names:
  `atM4_seated`: W's commitment with kind K13's block behind it: in a file of its own
    (Johnson/Desc/K13/Law/SeatedM4.lean), which this one imports.
  `openingZero_seated`: the first segment's opening with "link 0: opened" behind it
    (Johnson/Desc/K1/Law/OpeningZero.lean): the like.

What is not claimed. Nothing beyond `K1.SeatedBy`'s own words. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.SeatedM4
import Johnson.Desc.K1.Law.OpeningZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk (LayPar)
open Johnson.Desc.First.Walk.Tied (openedZeroGives)

variable {Cl : Type}

/-- **The first segment's opening with "link 0: opened" behind it.** -/
theorem openingZero_seated {q : Params.First} {gp : Desc.Plain.GPar} {nm : String} {X : LayPar}
    {fvs : List Bool} {kCol : ℕ} {s t : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t) :
    K1.SeatedBy (K1.firstPar q gp) s.book s.st.oracles.size s.roots t.book t.st.oracles.size
      t.roots := by
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid h
  obtain ⟨_, _, ⟨_, _, e3, e4, e5, _⟩, _⟩ := openedZeroGives X fvs kCol s₁ t h2
  rw [e3, e4, e5]
  exact K1.firstAtS_seated q gp s s₁ r₁ r₂ g₁ h1

end VerifiableInference.Desc.K13.Law
