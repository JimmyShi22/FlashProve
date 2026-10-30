--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/AtSeats/HandsAtSeal.lean: WHAT ONE BLOCK OWES TOWARD "the
promise's half that reads the verifier's state alone is handed on" (`IM.Hands`)
, AT A CHAIN's LAST BLOCK (`ChainEnd.chainEnd`, Johnson/Desc/ChainEnd.lean), at
any type of claims that it is carried to. Statements with their proofs. `chainEnd_same`: a yes of
  the block's step hands the state back: its decision tests and lays nothing. `hands_seal`:
  **`IM.Hands N links ps E ft k`** at the block: by the other house's `hands_same`. WHAT
    STAYS A PREMISE: what the table says of the block's two borders: at a state without a mark, the
    promise's half in front gives the promise's half behind, AT THE SAME STATE.
What is not claimed. That premise. Nothing on soundness.

-/
import Johnson.IMR.HandsDef
import Johnson.Desc.ChainEnd
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First (S ModelPart Numbers)
open VerifiableInference.Desc
open ProofFile (Cl)

/-- A yes of the last block's step hands the state back. -/
theorem chainEnd_same (chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → ChainEnd.Clauses) (ft : ℕ) (s s' : S)
    (h : IM.Yes ft ((ChainEnd.chainEnd chain piece sealed inFront asks : Block S Unit).retype :
      Block S Cl) s s') : s' = s := by
  obtain ⟨rs, cols, n, e⟩ := h
  obtain ⟨_, gs, hd⟩ := K1.step_ok ft _ _ _ rs cols n e
  have hd' : ((ChainEnd.refuse (asks s)).map fun _ => s) = .ok s' := hd
  cases hr : ChainEnd.refuse (asks s) with
  | error m =>
    rw [hr] at hd'
    cases hd'
  | ok u =>
    rw [hr] at hd'
    exact (Except.ok.inj hd').symm

/-- **A chain's last block.** -/
theorem hands_seal (N : Numbers) (links : List ModelPart) (ps : List Place) (E : ℕ → S → Bool)
    (ft k chain piece : ℕ) (sealed : Bool) (inFront : List Fmt.DeclaredRound)
    (asks : S → ChainEnd.Clauses)
    (hT : ∀ s, s.failed = none → IM.XK N links ps E k s = true →
      IM.XK N links ps E (k + 1) s = true) :
    IM.Hands N links ps E ft k
      ((ChainEnd.chainEnd chain piece sealed inFront asks : Block S Unit).retype : Block S Cl) :=
  IM.hands_same (chainEnd_same chain piece sealed inFront asks ft) hT

end HashBuild
