-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/AtCLaws.lean: small laws of Johnson/Desc/First/K4/AtC.lean. Statements and
proofs.

  `addClaim_claimOf`: adding the claim `claimOf a` to the one equation (`addClaim`,
    Johnson/Desc/Claim.lean) is adding the form a as `verify-on-bytes` does (`Fork.lin`): at every
    ledger, refusals too.
  `addAll_claimOf`: so adding a list of such claims, in order, is K4's own `addForms` of the forms.
  `blockAtC_names`: the block states the runs of claims "front", "back", in this order, and the run
    "free-slot" behind the batching, and no other.
  `atClaims_run`: a run of `atClaims b` is the run of b under the same name, its forms carried over.
  `blockAtC_decide`: it decides as `blockAtS p` does.

Limits. Equations on what texts return. Nothing on soundness.
-/
import Johnson.Desc.First.K4.AtC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim addClaim addAll)
open VerifiableInference.Desc.First (S)

/-- Adding no run of entries leaves the ledger as it is. -/
theorem pushRuns_none (F : Fork) (k : E) : F.pushRuns k #[] = some F := by
  cases F
  rfl

/-- **Adding `claimOf a` is adding the form a.** -/
theorem addClaim_claimOf (F : Fork) (a : Aff) : addClaim F (claimOf a) = F.lin a := by
  unfold addClaim Fork.lin claimOf
  congr 1
  funext x
  simp [pushRuns_none]

/-- **Adding a list of such claims is adding the forms.** -/
theorem addAll_claimOf (F : Fork) (fs : Array Aff) :
    addAll F (fs.toList.map claimOf) = addForms fs F := by
  unfold addAll addForms
  rw [← Array.foldlM_toList, List.foldlM_map]
  congr 1
  funext G a
  exact addClaim_claimOf G a

/-- **Which runs the block states.** -/
theorem blockAtC_names (p : Par) :
    (blockAtC p).claims.map (·.1) = ["front", "back"] ∧
      (blockAtC p).after.map (·.1) = ["free-slot"] :=
  ⟨rfl, rfl⟩

/-- A run of `atClaims b` is b's run of that name, its forms carried over. -/
theorem atClaims_run {T : Type} (b : Block T Aff) (name : String) :
    (atClaims b).claims.lookup name =
      (b.claims.lookup name).map fun run n s => (run n s).map fun y => (y.1.map claimOf, y.2) := by
  show (b.claims.map fun x =>
    (x.1, fun n s => (x.2 n s).map fun y => (y.1.map claimOf, y.2))).lookup name = _
  induction b.claims with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.lookup_cons, List.lookup_cons]
    cases name == x.1 with
    | true => rfl
    | false => exact ih

/-- It decides as K4's block at the carried record does. -/
theorem blockAtC_decide (p : Par) : (blockAtC p).decide = (blockAtS p).decide := rfl

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.addClaim_claimOf
#print axioms OnBytes.Desc.First.K4.addAll_claimOf
#print axioms OnBytes.Desc.First.K4.blockAtC_names
#print axioms OnBytes.Desc.First.K4.atClaims_run
