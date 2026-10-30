-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PlanNames.lean: THE JOIN OF Johnson/Road/K4/K4PlanLab.lean WITH
`names_tie` (Johnson/Road/K4/NamesTie.lean). `NamesTied Z`, the premise under which the twelve tests
at the groups read no built link, is that theorem's end at the twelve feed-forward links: here the
call. Two theorems: calls.

  `namesTied_of_scope`: in the goals' scope, at an opening of the maker at the second hash
    function's own function: `NamesTied Z`.
  `parts_of_allLab_scope`: so there one yes of `allLabB Z` gives each of the 24 closed tests.

Limits. K04_law IS NOT PROVED BY THIS. THAT THERE IS AN OPENING IS SHOWN BY NO THEOREM HERE. At
`OnBytes.secondHashFunction` alone.
-/
import Johnson.Road.K4.K4PlanLab
import Johnson.Road.K4.NamesTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The names' tie at the twelve feed-forward links, in scope, at an opening.** -/
theorem namesTied_of_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) : NamesTied Z :=
  fun _ hg _ hμ => names_tie hS hR O hg hμ

/-- **There one yes of the test without the built links gives each of the 24.** -/
theorem parts_of_allLab_scope (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hB : allLabB Z = true) :
    commonFastB Z = true ∧ (∀ g, g < 12 → firstFastB Z g = true) ∧
      ∀ g, 0 < g → g < 12 → seamFastB Z g = true :=
  parts_of_allLab Z (namesTied_of_scope hS hR O) hB

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.namesTied_of_scope
#print axioms OnBytes.Road.K4.parts_of_allLab_scope
