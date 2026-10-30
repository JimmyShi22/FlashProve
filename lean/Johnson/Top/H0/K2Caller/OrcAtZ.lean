-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/OrcAtZ.lean: the code switch: THE ORACLES' READING INSIDE THE CLOSED
«carry» (CarryClosed.lean's carryAtZ: K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z)) READS AT THE KEY j THE
TREE NUMBER j ITSELF, for every tree of the first chain.
  whole_is_data  where ProofFile.wholeAt Z (Johnson/Desc/ProofFile/CarryAt.lean) has
               data D: D is the data of an IOP as written, at the file's name "proof file"
  orcY_atZ     THE STATEMENT: K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) Y j x = Y.col j x for j < D.t₁. By
               orcY_of_data (K2Hears/OrcAtFrame.lean)
WHAT IT IS FOR. It is TableSide.lean's premise horc at orc := the closed carry's own reading and
trees := D.t₁. It also pays a caution in a text of this project that is not in this repository:
«that the first tree of the list with the key is the first chain's own is owed».
LIMITS. Where ProofFile.wholeAt Z has no data the two lists are empty and nothing is said. That D.t₁ is 83
in the goals' scope is K2Hears/FrameInScope.lean's t₁_in_scope, at ITS laid data: that these are
ProofFile.wholeAt's is not said here. No soundness is claimed.
-/
import Johnson.Top.H0.K2Caller.CarryClosed
import Johnson.Top.H0.K2Hears.OrcAtFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes.Maker OnBytes.Flat OnBytes.Slice
open VerifiableInference.Desc (Strs)

theorem whole_is_data (Z : ProofFile.Pub) (D : WholeD) (h : ProofFile.wholeAt Z = some D) :
    ∃ N c, (ProofFile.seatedAt ProofFile.emptySecondHashFunction Z N c).data "proof file" = .ok D := by
  unfold ProofFile.wholeAt at h
  obtain ⟨N, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨c, -, h⟩ := Option.bind_eq_some_iff.1 h
  refine ⟨N, c, ?_⟩
  cases hd : (ProofFile.seatedAt ProofFile.emptySecondHashFunction Z N c).data "proof file" with
  | error e =>
    rw [hd] at h
    cases h
  | ok D' =>
    rw [hd] at h
    rw [Option.some.inj h]

theorem orcY_atZ (Z : ProofFile.Pub) (D : WholeD) (h : ProofFile.wholeAt Z = some D) (Y : Strs) (j x : ℕ)
    (hj : j < D.t₁) : K2.orcY (ProofFile.allAt Z) (ProofFile.keyAt Z) Y j x = Y.col j x := by
  obtain ⟨N, c, hD⟩ := whole_is_data Z D h
  unfold ProofFile.allAt ProofFile.keyAt
  rw [h]
  exact K2.orcY_of_data hD _ Y j x hj

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.orcY_atZ
