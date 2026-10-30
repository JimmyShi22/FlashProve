-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ReadsStep.lean: A LINK's READS' PLACE: THE LOT's JOINED BLOCK (k1Reads, Johnson/IMR/K1Seat.lean: K1's sending of the reads with the quiet step joined behind it): A YES OF IT IS A STEP StepL
(Johnson/Desc/K1/Law/KeepAtLater.lean), as a yes of the sending alone is: the quiet step leaves all that the promise's book-keeping reads.
  QuietL q          a yes of q leaves the statement, the book, the mark, the count of rows that waits, where the chain stands, and the open link's part of the state
  quietL_layers | _head | _att · quietL_blockAt · quietL_readsQuietAt · quietL_k1Quiet (where no block could be made the refuser never says yes)
  StepL.then        a step, then such a yes, is a step
  stepL_k1Reads     **a yes of the reads' place's block is a step**, where the state's frame's group is g
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.IMR.K1Seat
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Goal.Meaning.RecReadsAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open OnBytes.Model.Stages (LinkH)
open IM (k1Reads k1Quiet)

variable {Pp : Type}

/-- What the promise's book-keeping reads is left. -/
def QuietL (q : Block S Unit) : Prop :=
  ∀ s s' rs gs, q.decide s rs gs = .ok s' →
    s'.st = s.st ∧ s'.book = s.book ∧ s'.failed = s.failed ∧ s'.rowsOwed = s.rowsOwed ∧
      First.standOf s' = First.standOf s ∧ s'.link? = s.link?

theorem quietL_layers (P : K8.ReadsQuiet.PG) : QuietL (K8.ReadsQuiet.layers P) := by
  intro s s' rs gs h
  obtain ⟨a, own, tl', ha, _, _, rfl⟩ := K8.ReadsQuiet.layers_ok h
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> simp [First.standOf, S.link?, ha]

theorem quietL_head (P : K8.ReadsQuiet.PH) : QuietL (K8.ReadsQuiet.head P) := by
  intro s s' rs gs h
  obtain ⟨a, cov, x, t, tl', ha, ho, _, _, _, _, rfl⟩ := K8.ReadsQuiet.head_ok h
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> simp [First.standOf, S.inLink, S.fork?, S.link?, ha, ho]

theorem quietL_att {W : Verify.Public} {l g : Nat} {q : Block S Unit}
    (hq : First.Att.readsAtO W l g = some q) : QuietL q := by
  unfold First.Att.readsAtO at hq
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 hq
  intro s s' rs gs h
  obtain ⟨a, t, tl, ha, rfl⟩ := Meaning.K2.readsAtSO_eq h
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩ <;> simp [First.standOf, S.link?, ha]

theorem quietL_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {H : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {q : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy H kinds l = some q) : QuietL q := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact quietL_layers _
  · split at h
    · obtain rfl := Option.some.inj h
      exact quietL_head _
    · cases h

theorem quietL_readsQuietAt {G : ProofFile.Ground} (l : Nat) (X : LinkH) (piece : Nat) (q : Block S Unit)
    (h : ProofFile.readsQuietAt G l X piece = some q) : QuietL q := by
  unfold ProofFile.readsQuietAt at h
  by_cases h1 : (X.kind == 1) = true
  · rw [if_pos h1] at h
    by_cases h2 : (piece == 4) = true
    · rw [if_pos h2] at h
      exact quietL_att h
    · rw [if_neg h2] at h
      cases h
  · rw [if_neg h1] at h
    by_cases h2 : (piece == (if X.kind == 0 then 4 else 5)) = true
    · rw [if_pos h2] at h
      exact quietL_blockAt h
    · rw [if_neg h2] at h
      cases h

theorem quietL_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) : QuietL (k1Quiet G l X) := by
  unfold k1Quiet
  dsimp only
  cases hq : ProofFile.readsQuietAt G l X (if X.kind == 0 || X.kind == 1 then 4 else 5) with
  | none => exact fun s s' rs gs h => nomatch h
  | some q => exact quietL_readsQuietAt l X _ q hq

/-- A step, then a yes of a block that leaves the book-keeping's part, is a step. -/
theorem StepL.then {P : Par} {g : Nat} {z : Pp} {s s₁ s' : S} (h : StepL P g (z, s) (z, s₁))
    (e : s'.st = s₁.st ∧ s'.book = s₁.book ∧ s'.failed = s₁.failed ∧ s'.rowsOwed = s₁.rowsOwed ∧
      First.standOf s' = First.standOf s₁ ∧ s'.link? = s₁.link?) : StepL P g (z, s) (z, s') := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := e
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Joins s.st s'.st g _
    rw [e1]
    exact h.joins
  · show Booked P s.book s.st.oracles.size s'.book s'.st.oracles.size
    rw [e1, e2]
    exact h.booked
  · show s'.failed = s.failed
    rw [e3]
    exact h.mark
  · show First.standOf s' = First.standOf s
    rw [e5]
    exact h.stand
  · show s'.noneWaits = true
    have := h.waits
    unfold S.noneWaits at this ⊢
    rw [e4]
    exact this
  · intro L' hL'
    exact h.link L' (by show s₁.link? = some L'; rw [← e6]; exact hL')

/-- **A YES OF THE READS' PLACE's BLOCK IS A STEP.** -/
theorem stepL_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (X : LinkH) (pr : ℕ)
    (reads : Option (List ℕ)) (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (k1Reads Z G l X pr reads).decide s [r₁, r₂] gs = .ok s') (g : Nat)
    (hg : ∀ L, s.link? = some L → L.check.frame.group = g) (z : Pp) :
    StepL (parLater G.first (gpOf Z) l pr 1) g (z, s) (z, s') := by
  have h' : ((laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).decide s
      ([r₁, r₂].take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
      (gs.take (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)).bind (fun s₁ =>
      (k1Quiet G l X).decide s₁
        ([r₁, r₂].drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).rounds.length)
        (gs.drop (laterAt G.first (gpOf Z) l pr 1 reads : Block S Unit).openings)) = .ok s' := h
  obtain ⟨s₁, h1, h2⟩ := (bind_ok _ _ _).1 h'
  have h1' : (commitAtS (parLater G.first (gpOf Z) l pr 1) l 1 reads : Block S Unit).decide s
      [r₁, r₂] _ = .ok s₁ := h1
  exact (stepL_commitAtS _ l 1 reads s s₁ r₁ r₂ _ h1' g hg z).then (quietL_k1Quiet G l X _ _ _ _ h2)

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.quietL_k1Quiet
#print axioms VerifiableInference.Desc.K1.stepL_k1Reads
