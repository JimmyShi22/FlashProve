-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/BlocksAtLater.lean: THE FOUR FACTS THAT block_tied ASKS OF A BLOCK's TEXT, AT K1's TWO SORTS OF LATER BLOCK: the digits' commitment (laterAt … 2 digits = commitAtS (parLater …)) and
the reads' place's joined block (k1Reads, Johnson/IMR/K1Seat.lean: K1's sending of the reads with the quiet step behind it): two declared rounds · IsSend · a yes leaves the mark · a yes is a step StepL at
the state's frame's group.
  commit_mark · reads_mark · rounds_k1Quiet · rounds_k1Reads · isSend_k1Reads (the step: stepL_commitAtS · stepL_k1Reads)
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.ReadsStep
import Johnson.Desc.K1.Law.SitsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

/-- A yes of commitAtS leaves the mark. -/
theorem commit_mark (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Unit).decide s [r₁, r₂] gs = .ok s') :
    s'.failed = s.failed := by
  obtain ⟨L, hL, _⟩ := commitAtS_group P link moment arrays s s' r₁ r₂ gs h
  exact (stepL_commitAtS P link moment arrays s s' r₁ r₂ gs h L.check.frame.group
    (fun L' hL' => by rw [Option.some.inj (hL.symm.trans hL')]) ()).mark

theorem rounds_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : q.rounds = [] := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  · split at h
    · obtain rfl := Option.some.inj h
      rfl
    · cases h

theorem rounds_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (h : ProofFile.readsQuietAt G l X piece = some q) : q.rounds = [] := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      unfold First.Att.readsAtO at h
      obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact rounds_blockAt h
    · rw [if_neg h2] at h
      cases h

theorem rounds_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) : (k1Quiet G l X).rounds = [] := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => rfl
  | some q => exact rounds_readsQuietAt l X _ q hq

theorem rounds_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) : (k1Reads Z G l X pr reads).rounds.length = 2 := by
  show ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds ++
    (k1Quiet G l X).rounds).length = 2
  rw [rounds_k1Quiet, List.append_nil]
  rfl

theorem isSend_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) :
    IsSend (parLater G.first (gpOf Z) l pr 1) (fun s : S => s.st) (k1Reads Z G l X pr reads) :=
  isSend_andThen _ _ _ _ _ (isSend_laterAt _ _ _ _ _ _) rfl (leaves_k1Quiet (leavesAtt _) l X)

/-- A yes of the reads' place's block leaves the mark. -/
theorem reads_mark (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s') : s'.failed = s.failed := by
  cases hL : s.link? with
  | none => exact (stepL_k1Reads Z G l X pr reads s s' r₁ r₂ gs h 0
      (fun L hL' => by rw [hL] at hL'; cases hL') ()).mark
  | some L => exact (stepL_k1Reads Z G l X pr reads s s' r₁ r₂ gs h L.check.frame.group
      (fun L' hL' => by rw [Option.some.inj (hL.symm.trans hL')]) ()).mark

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.commit_mark
#print axioms VerifiableInference.Desc.K1.rounds_k1Reads
#print axioms VerifiableInference.Desc.K1.isSend_k1Reads
#print axioms VerifiableInference.Desc.K1.reads_mark
