-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LinkJoinB.lean: THE JOIN, SECOND PART: small laws, general in P, that tie
linkAll's own terms (Johnson/Prover/Link/LinkAll.lean) to what the chain's walk hands and leaves.
Statements and proofs.
The join: the proof of link_yes (LinkJoinF.lean), in six files: LinkJoinA to LinkJoinF.

  lT_eq          where the six front blocks, the test's front and the batching say yes on linkAll's
                 first six rounds and stored columns, lT is the record that the batching leaves
  colsFor_map    a look-up that finds f w at each wanted triple w lays the columns (key, position,
                 f w)
  k12_letters    a test's block that passes its test on the plan has stages, declared rounds and
                 oracle messages

Not shown here. That any part says yes. Nothing on soundness; nothing on what any value that is sent
discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkLook
import Johnson.Prover.Link.LinkYesStm
import Johnson.Prover.Link.FormGave
import Johnson.Desc.K15.HsemOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Plain.One (colsFor)
open _root_.Desc.K15 (P15 St p12Of t12Of frontBlock blocksOrV readsAtLink)
open H2K.JointK (laidOf)
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run.PQ (SgX storedKey)
open _root_.Iop (twoExternalStrings)

theorem lT_eq (P : P15) (S : Sz) (t : ℕ) (X : LIn S) (C : LCoins) (D : ℕ → Fmt.Drawn) (d' : St)
    (t' : T12)
    (h6 : foldBlocks 0 (frontBlock P :: blocksOrV P) (_root_.Desc.K15.first P.codes X.keys)
      (lFront S t X C D) (lStoredCols P S X D) = .ok (d', [], []))
    (hf : (guardedProximityTestParts.front (p12Of P)).decide (t12Of d') [] [] = .ok (t12Of d'))
    (hb : (guardedProximityTestParts.bat (p12Of P) (((laidOf (p12Of P)).take 1).map (·.1))).decide (t12Of d')
      [noDigest ⟨[], D 5⟩] [] = .ok t') : lT P S t X C D = t' := by
  unfold lT
  simp only [h6]
  show ((guardedProximityTestParts.bat (p12Of P) (((laidOf (p12Of P)).take 1).map (·.1))).decide
    (((guardedProximityTestParts.front (p12Of P)).decide (t12Of d') [] []).toOption.getD (t12Of d'))
    [noDigest ⟨[], D 5⟩] []).toOption.getD _ = t'
  rw [hf]
  show ((guardedProximityTestParts.bat (p12Of P) (((laidOf (p12Of P)).take 1).map (·.1))).decide (t12Of d')
    [noDigest ⟨[], D 5⟩] []).toOption.getD _ = t'
  rw [hb]
  rfl

theorem colsFor_map (L : ℕ → ℕ → Option (List UInt64)) (f : ℕ × ℕ × ℕ → List UInt64) :
    ∀ ws : List (ℕ × ℕ × ℕ), (∀ w ∈ ws, L w.1 w.2.1 = some (f w)) →
      colsFor L ws = some (ws.map fun w => (w.1, w.2.1, f w))
  | [], _ => rfl
  | w :: ws, h => by
    show (match L w.1 w.2.1, colsFor L ws with
      | some c, some cs => some ((w.1, w.2.1, c) :: cs)
      | _, _ => none) = _
    rw [h w List.mem_cons_self, colsFor_map L f ws fun w' hw' => h w' (List.mem_cons_of_mem _ hw')]
    rfl

theorem k12_letters (p : P12) (h : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    ∃ first rest ds os, p.nums.stages = first :: rest ∧ H2U.roundsOfNums p.nums = some ds ∧
      H2U.testOracles p.nums = some os := by
  unfold proximityTestKind at h
  split at h
  · rename_i first rest ds os e1 e2 e3
    exact ⟨first, rest, ds, os, e1, e2, e3⟩
  · cases h

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.lT_eq
#print axioms Johnson.Prover.Link.colsFor_map
#print axioms Johnson.Prover.Link.k12_letters
