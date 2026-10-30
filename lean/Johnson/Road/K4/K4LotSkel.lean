-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4LotSkel.lean: the skeleton of K4's sub-protocol, off the lot's member.

Words. The code's `Block` is a sub-protocol at one place. Its skeleton (`ProofFile.Sk.skel`,
Johnson/Desc/ProofFile/Law/Skel/Skel.lean) is the `Block` less its functions: name · place · number
of rounds · length of the list `oracles` · the rounds that tell a tree · `before` · its test on the
plan · the names of its lists of claims · the names of its runs behind the batching.

What it says.
  `k4Lot_blocks`   K4's lot's `Block`s are `k4Block` of what `k4From` lays. By unfolding.
  `skel_k4Block`   the skeleton of `k4Block x` is `skOfView` at K4's number of rounds, at
                   `covers x.2.P && x.1` and at the pair's plain fields (`k4ViewOf x`). No premise.

Limits. Equations on plain data; nothing is evaluated. Nothing on soundness.
-/
import Johnson.Road.K4.K4CutRows
import Johnson.Road.K4.K4FromSk
import Johnson.Desc.ProofFile.Law.Skel.Skel

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par rounds covers)
open ProofFile.Sk (Skel skel toldFrom)

/-- Of a list of empty lists none tells a tree. -/
theorem toldFrom_nil {α : Type} : ∀ (es : List α) (k : ℕ),
    toldFrom k (es.map fun _ => ([] : List VerifiableInference.Desc.Oracle)) = []
  | [], _ => rfl
  | _ :: es, k => by
    simpa [toldFrom] using toldFrom_nil es (k + 1)

theorem k4Block_place (x : Bool × Par) :
    (ProofFile.k4Block x).place = ⟨1, some x.2.link, x.2.piece, .K4⟩ := rfl

/-- K4's lot's `Block`s. -/
theorem k4Lot_blocks (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (ProofFile.k4Lot Z).blocks G = (ProofFile.k4From Z G G.built.toList 0 none).map ProofFile.k4Block := rfl

/-- K4's skeleton, from the number of rounds, the test on the plan and a pair's plain fields. -/
def skOfView (n : ℕ) (ok : Bool) (v : Bool × String × ℕ × ℕ × List (ℕ × ℕ) × ℕ) : Skel :=
  { name := v.2.1, place := ⟨1, some v.2.2.1, v.2.2.2.1, .K4⟩, nRounds := n, nOracles := n,
    told := [], before := v.2.2.2.2.1, planOk := ok, claims := ["front", "back"],
    after := ["free-slot"] }

/-- **The skeleton of K4's sub-protocol.** -/
theorem skel_k4Block (x : Bool × Par) :
    skel (ProofFile.k4Block x) =
      skOfView (rounds x.2.P x.2.hp x.2.g).length (covers x.2.P && x.1) (k4ViewOf x) := by
  simp only [skel, skOfView, k4ViewOf, k4Block_name, k4Block_place, k4Block_rounds,
    k4Block_oracles, k4Block_before, k4Block_planOk, k4Block_claims, k4Block_after,
    List.length_map, entries_len, toldFrom_nil]

#print axioms OnBytes.Road.K4.toldFrom_nil
#print axioms OnBytes.Road.K4.k4Block_place
#print axioms OnBytes.Road.K4.k4Lot_blocks
#print axioms OnBytes.Road.K4.skel_k4Block

end OnBytes.Road.K4
