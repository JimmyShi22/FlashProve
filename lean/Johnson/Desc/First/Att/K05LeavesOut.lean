-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05LeavesOut.lean: kind K5: THE KIND's SUB-PROTOCOL LEAVES THE STATEMENT AND ALL THAT WAS PUT OUT: an instance of the law that is general in the relation
(Johnson/Desc/First/Att/K05Leaves.lean: k5AtN_whole · lotN_whole) at the relation "the statement and what was put out are as they were".

Why. The keeping beneath a law in other files on the index-mask message's ledger asks of every sub-protocol of the kind that an accepting decision leaves that ledger, the
statement's groups and the message's number (S.out.indexMasks). The relation Quiet, of which the like is shown (Johnson/Goal/Meaning/RecSeated.lean: k5AtN_quiet), does not speak of
"out".

Main names:
  `SameStOut s t`: t.st = s.st ∧ t.out = s.out. `sameStOut_refl`, `sameStOut_putFork`, `sameStOut_lay`: it is reflexive; a write of the ledger keeps it; the seat's lay keeps it.
  `k5AtN_stOut`, `lotN_stOut`: the block k5AtN's, and every block's of the kind's lot: the decision, each run of claims and each run behind the batching keep it.
  `lotN_decide_stOut`: the decision alone, as two equations.
Limits: those of K05Leaves.lean: it speaks of the LOT's block, not of the seated entry.
Is it empty here? Where a decision or a run rejects nothing is said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Leaves

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Claim)
open VerifiableInference.Desc.Keeps (Whole)

/-- The statement and all that was put out. -/
def SameStOut (s t : First.S) : Prop := t.st = s.st ∧ t.out = s.out

theorem sameStOut_refl (s : First.S) : SameStOut s s := ⟨rfl, rfl⟩

theorem sameStOut_putFork (s : First.S) (G : Fork) : SameStOut s (s.putFork G) := by
  unfold First.S.putFork
  cases hh : s.here with
  | head a => by_cases ho : a.opened = true <;> simp [ho, SameStOut]
  | _ => exact ⟨rfl, rfl⟩

theorem sameStOut_lay (s : First.S) (h : Heard) (G : Fork) (s' : First.S) (hl : seatSO.lay s h G = some s') : SameStOut s s' := by
  obtain ⟨a, _, rfl⟩ := seatSO_lay hl
  exact ⟨rfl, rfl⟩

/-- **The kind's sub-protocol leaves the statement and all that was put out.** -/
theorem k5AtN_stOut {W : Verify.Public} {l g : ℕ} {before : List (ℕ × ℕ)} {b' : Block First.S Claim}
    (hb : k5AtN W l g before = some b') : Whole SameStOut b' :=
  k5AtN_whole SameStOut sameStOut_refl sameStOut_putFork sameStOut_lay hb

theorem lotN_stOut {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block First.S ProofFile.Cl} (h : b₁ ∈ (H2K5.lotN Z).blocks G) :
    Whole SameStOut b₁ :=
  lotN_whole SameStOut sameStOut_refl sameStOut_putFork sameStOut_lay h

/-- The decision alone. -/
theorem lotN_decide_stOut {Z : ProofFile.Pub} {G : ProofFile.Ground} {b₁ : Block First.S ProofFile.Cl} (h : b₁ ∈ (H2K5.lotN Z).blocks G)
    {s s' : First.S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (e : b₁.decide s rs gs = .ok s') :
    s'.st = s.st ∧ s'.out = s.out :=
  (lotN_stOut h).1 s rs gs s' e

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.k5AtN_stOut
#print axioms VerifiableInference.Desc.First.Att.P.lotN_stOut
#print axioms VerifiableInference.Desc.First.Att.P.lotN_decide_stOut
