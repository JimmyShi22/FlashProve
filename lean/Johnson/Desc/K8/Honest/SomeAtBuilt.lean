-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/SomeAtBuilt.lean: THE SMALLNESS TEST: AT EACH BUILT SEGMENT THE DESCRIPTION's
OWN PARAMETERS OF THE DRAW NAME A MATRIX: the field some of the records `K8Items` and `K8ItemsAt`
(Johnson/Desc/ProofFile/Honest/K8/Seated.lean, SeatedItemsAt.lean). One theorem; no definition; none
of the library's goals.

  `ks_ne_at_built`   in the goals' scope, where the description passes its test on its plan:
                   l < 25 · the built segment Xl ⊢ (ProofFile.k8Par Z Bs.G₀ Xl l).ks ≠ []
HOW. `matrix_at_built`, `made_count` (Johnson/Desc/K8/Honest/HeldOutright.lean) · the library's
`made_at_built` (Johnson/P1K8R/SecondLaidAtBatch.lean).
NO OPTION IS RAISED, NO INSTANCE TAKEN AWAY. TACTICS THAT SEARCH: `omega` on one line, on two
counts.
Limits. Public data alone. IN SCOPE ALONE. Which of the files that this head names are rows of the
library is for the library's own list to say: it is not said here.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.HeldOutright

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block FileDescription Chain Claim)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The draw's own parameters name a matrix.** -/
theorem ks_ne_at_built (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {Xl : LinkH} (e3 : Bs.G₀.built[l]? = some Xl) :
    (ProofFile.k8Par Z Bs.G₀ Xl l).ks ≠ [] := by
  have hN := matrix_at_built hS hR O hOk hl e3
  have hc := made_count (_root_.P1K8.made_at_built hS hR O hl e3)
  intro e
  have e' : (Xl.tl.mats.toList.map (·.k)).length = 0 := by
    have e2 : Xl.tl.mats.toList.map (·.k) = [] := e
    rw [e2]
    rfl
  rw [List.length_map, Array.length_toList] at e'
  omega

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.ks_ne_at_built
