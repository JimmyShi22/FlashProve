-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/ParFacts.lean: THE SMALLNESS TEST: THE NUMBERS OF A PLACE OF THE KIND's OWN
LOT (`ProofFile.k8Par`, Johnson/Desc/ProofFile/Lot/K8.lean) AGAINST THE DATA OF THE TEST IN THE PLANNED
LINK X OF WHICH THEY ARE MADE: the facts on public numbers that the law of the draw asks of these
data. Lemmas on the library's own definitions, each by unfolding; none of its goals.

  `k8Par_ks`, `k8Par_ms`, `k8Par_tau`   the matrices' columns, their rows and the number of
                   combinations of X.tl ARE the place's: by the place's own text
  `k8Par_nm`   the number of matrices is the length of the place's list of columns, IF X.tl.NM is
                   the size of X.tl.mats
  `k8Par_asks_head`   at a link of the head's kind the place's families of tables are `Asks.head
                   G.W.hS`
  `k8Par_upd`   the four facts read neither the mark "closed" nor the count of draws: so they hold
                   as well of X.tl with these two fields laid anew
Limits. LEFT, ON THE PLAN's DATA ALONE: that X.tl.NM is the size of X.tl.mats; that no matrix is
drawn in them (cfF is empty); that no draw is counted in them (foldDrawn is 0). That a chain's link
is X, and that X.tl is a plan's own data, is the library's `IM.ground_tails`
(Johnson/IMR/K8Seat.lean), in its scope.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Lot.K8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model

theorem k8Par_ks (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat) :
    X.tl.mats.toList.map (·.k) = (ProofFile.k8Par Z G X l).ks := rfl

theorem k8Par_ms (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat) :
    X.tl.mats.toList.map (·.m) = (ProofFile.k8Par Z G X l).ms := rfl

theorem k8Par_tau (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat) :
    X.tl.tau = (ProofFile.k8Par Z G X l).tau := rfl

theorem k8Par_nm (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat)
    (h : X.tl.NM = X.tl.mats.size) : X.tl.NM = (ProofFile.k8Par Z G X l).ks.length := by
  rw [← k8Par_ks, List.length_map, Array.length_toList]
  exact h

theorem k8Par_asks_head (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat)
    (h : X.kind = 2) : (ProofFile.k8Par Z G X l).asks = Asks.head G.W.hS := by
  show ProofFile.k8Asks G X = _
  unfold ProofFile.k8Asks
  rw [h]
  rfl

/-- The four facts, of the link's data with the mark "closed" and the count of draws laid anew. -/
theorem k8Par_upd (Z : ProofFile.Pub) (G : ProofFile.Ground) (X : Stages.LinkH) (l : Nat) (c : Bool) (n : Nat)
    (h : X.tl.NM = X.tl.mats.size) :
    ({ X.tl with funClosed := c, foldDrawn := n } : HTailF2).NM = (ProofFile.k8Par Z G X l).ks.length ∧
      ({ X.tl with funClosed := c, foldDrawn := n } : HTailF2).mats.toList.map (·.k) =
        (ProofFile.k8Par Z G X l).ks ∧
      ({ X.tl with funClosed := c, foldDrawn := n } : HTailF2).mats.toList.map (·.m) =
        (ProofFile.k8Par Z G X l).ms ∧
      ({ X.tl with funClosed := c, foldDrawn := n } : HTailF2).tau = (ProofFile.k8Par Z G X l).tau :=
  ⟨k8Par_nm Z G X l h, rfl, rfl, rfl⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.k8Par_ks
#print axioms VerifiableInference.Desc.First.K8.Honest.k8Par_ms
#print axioms VerifiableInference.Desc.First.K8.Honest.k8Par_tau
#print axioms VerifiableInference.Desc.First.K8.Honest.k8Par_nm
#print axioms VerifiableInference.Desc.First.K8.Honest.k8Par_asks_head
#print axioms VerifiableInference.Desc.First.K8.Honest.k8Par_upd
