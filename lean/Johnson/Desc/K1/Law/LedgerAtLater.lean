-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LedgerAtLater.lean: at a segment's later places no mask entry is taken.

  k1Quiet_st      the quiet block behind the reads' sending leaves the statement.
  later_ledStay   behind a yes of either block (Later, Johnson/Desc/K1/Law/InOrderAtLater.lean), on
                  any rounds: LedStay (Johnson/Desc/K13/Law/LedgersStay.lean).
  later_ledgerAt  so the ledger of every message is that of the same number of takes.

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.K13.Law.LedgersStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Keeps (Decides)
open VerifiableInference.Desc.K13.Law (LedStay LedgerAt commitAtS_ledStay)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

theorem k1Quiet_st (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides (fun s s' : S => s'.st = s.st) (k1Quiet G l X) := by
  refine k1Quiet_decides _ (fun P s rs gs s' h => ?_) (fun P s rs gs s' h => ?_)
    (fun A s s' h => ?_) G l X
  · exact (K8.ReadsQuiet.layers_frame h).2.2.1
  · exact (K8.ReadsQuiet.head_frame h).2.2.1
  · obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
    rfl

/-- **At both blocks of a segment's later places nothing is taken.** -/
theorem later_ledStay {B own : Block S Unit} (hB : Later B own) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide s rs gs = .ok s') :
    LedStay s.st s'.st := by
  cases hB with
  | digits q gp l piece digits => exact commitAtS_ledStay _ l 2 digits s rs gs s' h
  | reads Z G l X pr reads =>
    have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
        (rs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
        (k1Quiet G l X).decide s₁
          (rs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
          (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
    obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
    rw [k1Quiet_st G l X _ _ _ _ h2]
    exact commitAtS_ledStay _ l 1 reads s _ _ s₁ h1

theorem later_ledgerAt {B own : Block S Unit} (hB : Later B own) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : B.decide s rs gs = .ok s') {o k : ℕ}
    (hk : LedgerAt s.st o k) : LedgerAt s'.st o k :=
  (later_ledStay hB s s' rs gs h).at hk

end VerifiableInference.Desc.K1
