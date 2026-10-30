-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.BeforeK12
import Johnson.Desc.K12.Law.PlacesSmall
import Johnson.Desc.K12.JoinGuarded
/-
Johnson/Desc/K12/Law/BeforeO.lean: opened_sent (BeforeK12.lean) IS NOT EMPTY AT A REAL PLACE: its premises are met together at piO (the proximity test O of the smaller stored example) OVER A CHAIN IN FRONT THAT IS MADE UP: one round that sends five roots. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  THE PLACE IS THE REAL ONE; THE ROUNDS IN FRONT OF THE BLOCK ARE NOT THE FILE's: no closed description of a file lies. So: a member of the premises, not of a file's plan.
  before_O: beforeAt's yes, by the kernel. before_O_late: beforeAt says no at a chain in which the block stands first: there the messages 1 | 2 that the place names fall on the block's OWN later trees, sent too late (the five roots behind are never looked at). Better controls: SeatWord.lean. word_O: the theorem's conclusion there.

-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace H2K.Member
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Made (opened_sent SentBy)

/-- A made-up round: five roots, no draw. -/
def r5 : Fmt.DeclaredRound := ⟨{ Fmt.M1.rBat.entry with roots := 5, drawE := 0 }, [], []⟩
/-- A made-up block with that one round. -/
def b5 : Block T12 Unit := { (asks "five roots" piO.place fun _ => true) with rounds := [r5] }
def bO : Block T12 Unit := proximityTestKind guardedProximityTestParts piO
def dO3 : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound := ([], r5 :: bO.rounds, [])

theorem fixed_O : H2K.FixedBefore.fixedOk piO = true := by decide +kernel
theorem rounds_O : H2U.roundsOfNums piO.nums = some bO.rounds := by decide +kernel
theorem bef_O : bO.before = piO.before := by decide +kernel
theorem before_O : beforeAt dO3 ([], [], []) 1 0 [b5, bO] = true := by decide +kernel
theorem before_O_late :
    beforeAt (([], bO.rounds ++ [r5], []) : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
      ([], [], []) 1 0 [bO, b5] = false := by decide +kernel

theorem word_O :
    (∀ (j : ℕ) (s : Fmt.M1.Stage), j + 1 < piO.nums.stages.length → piO.nums.stages[j]? = some s →
      ∀ r ∈ (bO.rounds.drop (H2K.FixedBefore.foldStart 1 piO.nums.stages j + 1 + s.k)).take 2,
      ∀ o ∈ r.opens, SentBy dO3 1 (0 + roundsIn [b5])
        (0 + roundsIn [b5] + (H2K.FixedBefore.foldStart 1 piO.nums.stages j + 1)) o) ∧
    (∀ r ∈ (bO.rounds.drop
        (H2K.FixedBefore.foldStart 1 piO.nums.stages (piO.nums.stages.length - 1))).take 2,
      ∀ o ∈ r.opens, SentBy dO3 1 (0 + roundsIn [b5])
        (0 + roundsIn [b5] +
          H2K.FixedBefore.foldStart 1 piO.nums.stages (piO.nums.stages.length - 1)) o) :=
  opened_sent piO fixed_O bO.rounds rounds_O dO3 ([], [], []) 1 0 [b5] bO [] bef_O rfl rfl
    before_O [r5] [] (by simp [chainOf, dO3]) rfl rfl

end H2K.Member

#print axioms H2K.Member.before_O
#print axioms H2K.Member.before_O_late
#print axioms H2K.Member.word_O
