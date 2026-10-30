-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/OrcAtFrame.lean: the code switch: the reading of the oracles by key and
position (`orcY`, OrcStrs.lean), at the frame that the rule of composition has for a file's first
chain, reads AT THE KEY j THE TREE NUMBER j ITSELF, for every tree j of the first chain. Statements
and proofs; no definition.

Why. `orcY all key Y k x` is the column of the first tree of the list whose key is k. At that frame
the list holds the trees of all three chains, and the second chain's trees bear the keys 0, 1, …
again (KeyOfFits.lean). The first chain's trees stand first in the list, each under its own number:
so the reading finds them.

  `orcY_first`     where the tree j is the first of the list with its key: orcY … (key j) x = Y.col
    j x
  `orcY_of_data`   at the data D of an IOP as written: orcY (allOf (D.at a)) (D.at a).key₁ Y j x =
                   Y.col j x for j < D.t₁
  `orcY_in_scope`  in the goals' scope, at the laid data: the same for j < 83
Limits. That the number of a kept message's tree is below 83, and that it is the seat's tree, is not
said here. The first chain alone. Nothing on soundness.

-/
import Johnson.Top.H0.K2Hears.OrcStrs
import Johnson.Top.H0.K2Hears.FrameInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Strs FileDescription)
open VerifiableInference.Desc.Sound (allOf nAll)
open LPFD.Full (proofDataAndDecisionOfPublicFiles laidPOf_ok RunPF)

/-- Where the tree j is the first of the list with its key, the reading there is its column. -/
theorem orcY_first (all : List LeftT) (key : Nat → Nat) (Y : Strs) (j x : Nat)
    (hF : (all.find? fun L => key L.no == key j).map (·.no) = some j) :
    orcY all key Y (key j) x = Y.col j x := by
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1 hF
  unfold orcY
  rw [hT]

/-- **At the data of an IOP as written: at the key j the reading has the tree j's column.** -/
theorem orcY_of_data {Xi : Type} {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) (a : Nat) (Y : Strs) (j x : Nat) (hj : j < D.t₁) :
    orcY (allOf (D.at a)) (D.at a).key₁ Y j x = Y.col j x := by
  have hk : (D.at a).key₁ j = j := key_of_data h j hj
  have hF := first_of_id (D.at a) D.t₁ (t₁_le_all (D.at a)) (key_of_data h) j hj
  have e := orcY_first (allOf (D.at a)) (D.at a).key₁ Y j x hF
  rwa [hk] at e

/-- **In the goals' scope, at the laid data.** -/
theorem orcY_in_scope {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : RunPF}
    (hZ : VerifierAndGoals.InScope Z = true) (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)) (a : Nat)
    (Y : Strs) (j x : Nat) (hj : j < 83) :
    orcY (allOf (D.at a)) (D.at a).key₁ Y j x = Y.col j x := by
  obtain ⟨F, -, -, hD, -, -⟩ := laidPOf_ok h
  exact orcY_of_data hD a Y j x (by rw [t₁_in_scope hZ h]; exact hj)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.orcY_first
#print axioms VerifiableInference.Desc.First.K2.orcY_of_data
#print axioms VerifiableInference.Desc.First.K2.orcY_in_scope
