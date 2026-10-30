-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotHeardClosed.lean: for HeardOfFold: the closed lines at the written sizes of a key (keyFull): each by
an evaluation in Lean's kernel.

  looksF, faceF   the two lookups' public records and faces at the written sizes
  looks_two, face_plain   two lookups; no shift; as many parts as the plan's lookup has
  pos_full        AT EACH OF THE 2 × 12 PARTS: the number of the first round of the part's last key level, and of the
                  "LINE" behind it, in the honest side's row of stages (firstRound, Honest/K3/Stages.lean) IS the number
                  of rounds that the verifier's text has taken in front of it (oKeys, offK, Kr, E2E/LotHeardText.lean)
  pos_full_no     a control: with the parts' steps left out of the verifier's count the two numbers differ
  rifR, rif_rows, base_full   roundsInFront reads the rows (place, number of rounds) alone; at the first chain's
                  written rows: 4 rounds stand in front of the first lookup, 9,585 in front of the second; the first
                  lookup has 9,581
  Kr_snoc         a run's rounds, the last level split off

Limits. At the written sizes. Public numbers alone. Nothing on any property.
-/
import E2E.LotHeardText
import E2E.KeyPlaces
import Johnson.Desc.First.Look.K3Key
import Johnson.Goal.PlanValues.KeySizedReturns
import Johnson.Desc.ProofFile.Honest.ForKinds
import OnBytes.Iop.Wf

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.FirstH.Lots
open OnBytes
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K3 (faceOfLkp)
open ProofFile.Honest (roundsInFront)
open ProofFile.Honest.K3 (LFace firstRound Stage)
open Johnson.RunOne.Sound (rowsOf)
open AtPublicFiles.KeyBook (fullFirst)
open Lk6.AtPlan (keyFull)

/-- The lookups' public records at the written sizes. -/
def looksF : List Lkp.Public := Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)

/-- Lookup i's face at the written sizes. -/
def faceF (i : Nat) : LFace := faceOfLkp (looksF.getD i default)

theorem looks_two : looksF.length = 2 := by decide +kernel

theorem face_plain : ∀ i, i < 2 → (faceF i).shifted = false ∧
    (keyFull.ranges.x.lookups.getD i default).parts.length = (faceF i).parts.length := by
  decide +kernel

/-- **The two counts of rounds agree, at each part of each lookup.** -/
theorem pos_full : ∀ i, i < 2 → ∀ p, p < (faceF i).parts.length →
    1 ≤ (faceF i).parts.getD p 0 ∧
    firstRound (faceF i) (.key p ((faceF i).parts.getD p 0 - 1)) =
      oKeys (faceF i) + offK (faceF i).parts p + Kr 0 0 ((faceF i).parts.getD p 0 - 1) ∧
    firstRound (faceF i) (.keyLine p ((faceF i).parts.getD p 0 - 1)) =
      oKeys (faceF i) + offK (faceF i).parts p + Kr 0 0 ((faceF i).parts.getD p 0 - 1) +
        ((faceF i).parts.getD p 0 - 1) + 3 := by
  decide +kernel

/-- A control: the comparison can say no: with the parts' steps left out of the verifier's count the two differ. -/
theorem pos_full_no : firstRound (faceF 0) (.key 0 ((faceF 0).parts.getD 0 0 - 1)) ≠
    1 + 3 * ((faceF 0).planes - 1) + 1 + Kr 0 0 ((faceF 0).parts.getD 0 0 - 1) := by
  decide +kernel

/-- roundsInFront's text, off the rows. -/
def rifR : List (Place × Nat) → Place → Option Nat
  | [], _ => none
  | b :: bs, a => if b.1 == a then some 0 else (rifR bs a).map (· + b.2)

theorem rif_rows {S Cl : Type} : ∀ (bs : List (Block S Cl)) (a : Place),
    roundsInFront bs a = rifR (rowsOf bs) a
  | [], _ => rfl
  | b :: bs, a => by
    show (if b.place == a then some 0 else (roundsInFront bs a).map (· + b.rounds.length)) =
      if b.place == a then some 0 else (rifR (rowsOf bs) a).map (· + b.rounds.length)
    rw [rif_rows bs a]

theorem base_full : rifR fullFirst ⟨1, some 0, 2, .K3⟩ = some 4 ∧
    rifR fullFirst ⟨1, some 1, 2, .K3⟩ = some 9585 ∧ (fullFirst[4]?).map (·.2) = some 9581 := by
  decide +kernel

theorem Kr_snoc (more : Nat) : ∀ (n l : Nat), Kr more l (n + 1) = Kr more l n + (more + l + n + 4)
  | 0, l => by
    rw [Kr_succ]
    simp [Kr]
  | n + 1, l => by
    rw [Kr_succ, Kr_snoc more n (l + 1), Kr_succ more l n]
    omega

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.looks_two
#print axioms AtPublicFiles.FirstH.Lots.face_plain
#print axioms AtPublicFiles.FirstH.Lots.pos_full
#print axioms AtPublicFiles.FirstH.Lots.pos_full_no
#print axioms AtPublicFiles.FirstH.Lots.rif_rows
#print axioms AtPublicFiles.FirstH.Lots.base_full
#print axioms AtPublicFiles.FirstH.Lots.Kr_snoc
