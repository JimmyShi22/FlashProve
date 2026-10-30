-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/PublicSAt.lean: THE PRINTER's PUBLIC PREMISE AT WHAT verify()'s DESCRIPTION
LAYS: PublicS (Johnson/Prover/Print/FormBack.lean) at dataAtFiles flashProveData Z, and the leaf salt's length:
from protocolDataWellFormed and the one test wordsFitAt (Johnson/Goal/Meaning/PublicSizesAt.lean).

One theorem: publicS_built. Each field is a call: roots, depths: madeFit_DK | madeFit_DP; rounds:
rounds_built; the stored table's depth: depth_lt (Johnson/Goal/Meaning/PublicFitAt.lean); trees:
trees_DK | trees_DP; no list empty: lists_full; items, bindings, the leaf salt: wordsFitAt_says
(PublicSizesAt.lean).

Limits. protocolDataWellFormed and wordsFitAt at given public files ARE PREMISES HERE. In scope the second follows
from the first (wordsFitAt_the, Johnson/Goal/Meaning/WordsFitAtThe.lean); that the first accepts is
proved in Lean, in the side library (outside the main library and with that library's own limits),
at the written copy of the full-size example's files under every acceptance policy in scope
(theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean; owner: Johnson/Goal/Conditions/HomeLast.lean,
limit 4). The scope is wider than these files; elsewhere in it that protocolDataWellFormed accepts stays a premise.
The copy's file's public premise is not spoken of.
This file states no goal.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.PublicSizesAt
import Johnson.Prover.Print.FormBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning
open OnBytes.Maker OnBytes.Slice OnBytes.Prover
open FlashProve FlashProve
open LPFD.Full (saltG)

/-- **PublicS at what verify()'s description lays at Z, and the leaf salt's length.** -/
theorem publicS_built (Z : VerifierAndGoals.PublicFiles) (hl : protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hs : wordsFitAt (VerifierAndGoals.asDescriptionFiles Z) = true) :
    Johnson.Prover.Print.PublicS (dataAtFiles flashProveData Z) ∧ saltG (dataAtFiles flashProveData Z).G ≤ 64 := by
  have hy := wordsFitAt_says hl hs
  have r := rounds_built Z
  have l := lists_full Z hl
  refine ⟨⟨((madeFit_DK Z).at _).roots, ((madeFit_DP Z).at _).roots,
    ⟨⟨?_, ?_, ?_⟩, hy.itemsK, trees_DK Z _, ((madeFit_DK Z).at _).depths, depth_lt, hy.bindK⟩,
    ⟨⟨?_, ?_, ?_⟩, hy.itemsP, trees_DP Z _, ((madeFit_DP Z).at _).depths, depth_lt, hy.bindP⟩,
    ⟨l.1.2.1, l.1.2.2⟩, ⟨l.2.2.1, l.2.2.2⟩⟩, hy.salt⟩
  · show (dataAtFiles flashProveData Z).DK.ds₁.length + 1 < 2 ^ 64
    have := r.1.1
    omega
  · show (dataAtFiles flashProveData Z).DK.ds₂.length < 2 ^ 64
    have := r.1.2.1
    omega
  · show (dataAtFiles flashProveData Z).DK.ds₃.length < 2 ^ 64
    have := r.1.2.2
    omega
  · show (dataAtFiles flashProveData Z).DP.ds₁.length + 1 < 2 ^ 64
    have := r.2.1
    omega
  · show (dataAtFiles flashProveData Z).DP.ds₂.length < 2 ^ 64
    have := r.2.2.1
    omega
  · show (dataAtFiles flashProveData Z).DP.ds₃.length < 2 ^ 64
    have := r.2.2.2
    omega

end Meaning

#print axioms Meaning.publicS_built
