-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineRunsThreads.lean: THE INVARIANTS OF FORM AS A MEMBER OF `ThreadsP`
(Johnson/Desc/ProofFile/Honest/Law/OwedParts.lean): the structure of hypotheses that the frame's laws on a run that has
returned take by type (`OnAtRun₁`, `OnAtRun₂`, `OnAtRun₃`, `owed_at_run`: Honest/Law/OwedAtRun.lean). General in the
description, the book and the prover.

  `form_pieces`       `PlaysOn` at every sub-protocol of the three lists along `formAt` (E2E/OfflineRunsForm.lean), and `formAt`
                      at the three starts: what `runs_of_blocks` (E2E/OfflineRunsLaw.lean) feeds to `runC_returns`
  `threadsOfBlocks`   the member, from the premises of `RunsOfBlocks` that read no challenge
  `threadsOfBlocks_first`, `_shared`, `_second`   its three families of invariants are `formAt`: by unfolding

WHAT SUCH A THREAD KNOWS. The form alone: `InsideOf` at these invariants says of the state in front of a part its
input, how many challenges of what form it has heard, that columns are handed, and that the tables at hand fit what was
declared. It says nothing on the witness, on a coin or on the verifier's state: an On that needs more has to get it
from the run's own equations (`midAtW`, `beforeAt`), which `OnAtRun` hands beside. Nothing on any property.
-/
import E2E.OfflineRunsLaw
import Johnson.Desc.ProofFile.Honest.Law.OwedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest
open VerifiableInference.Desc

variable {Xi W₀ Rc Ky Tr X₀ X : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **`PlaysOn` along the invariants of form, and these at the three starts.** -/
theorem form_pieces (hR : ready F Bk H w₀ rc x k = .ok R) (plan : F.planOk = true)
    (hroot : rootedAll F H = true) (hP : PlanServes H w₀ rc R)
    (hB : BlocksPlay F Bk H R.own R.common) :
    (∀ j b, F.first.blocksInOrder[j]? = some b → PlaysOn .own Bk 0 0 H.first b
      (formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder j)
      (formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder (j + 1))) ∧
    (∀ j b, F.shared.blocksInOrder[j]? = some b → PlaysOn .shared Bk 1 0 H.shared b
      (formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder j)
      (formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder (j + 1))) ∧
    (∀ j b, F.second.blocksInOrder[j]? = some b → PlaysOn .own Bk 2 F.lastChainFirstTreeNumber H.second b
      (formAt (H.storedWords w₀ rc) (takenThird F) (startThird F) R.own F.second.blocksInOrder j)
      (formAt (H.storedWords w₀ rc) (takenThird F) (startThird F) R.own F.second.blocksInOrder (j + 1))) ∧
    formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder 0 k (F.start₁ (F.pub x))
      { R.start₁ H with opened := some [] } (envOf (H.storedWords w₀ rc) (fun _ _ => none) []) ∧
    formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder 0 k (F.start₂ (F.pub x))
      { R.start₂ H with opened := some [] } (envOf (H.storedWords w₀ rc) (fun _ _ => none) []) ∧
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder F.first.blocksInOrder.length k e₁ m₁
        E₁ →
      formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder F.shared.blocksInOrder.length k
        e₂ m₂ E₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      formAt (H.storedWords w₀ rc) (takenThird F) (startThird F) R.own F.second.blocksInOrder 0 k s₃
        { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂) := by
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have P := (F.planOk_ok).1 plan
  simp only [rootedAll, Bool.and_eq_true] at hroot
  obtain ⟨⟨r1, r2⟩, r3⟩ := hroot
  have e1 : R.first.flatMap (·.oracles) = (rowsOfChain F.first.blocksInOrder).flatMap (·.2) :=
    oracles_of_pairs (steps_pairs s1)
  have e2 : R.shared.flatMap (·.oracles) = (rowsOfChain F.shared.blocksInOrder).flatMap (·.2) :=
    oracles_of_pairs (steps_pairs s2)
  refine ⟨fun j b hb => playsOn_of_blockPlays s1 P.blocks₁ r1 _ _ _ _ hP.first.inTime
      (fun taken _ u hu => ⟨hP.first.stored u hu, fun o ho ch i e => absurd e (hP.own₁ u hu o ho ch i)⟩)
      hb (hB.first j b hb),
    fun j b hb => playsOn_of_blockPlays s2 P.blocks₂ r2 _ _ _ _ hP.shared.inTime
      (fun taken _ u hu => ⟨hP.shared.stored u hu, fun o ho ch i e => absurd e (hP.own₂ u hu o ho ch i)⟩)
      hb (hB.shared j b hb),
    fun j b hb => playsOn_of_blockPlays s3 P.blocks₃ r3 _ _ _ _ hP.second.inTime
      (fun taken hT u hu => ⟨hP.second.stored u hu, fun o ho ch i e => ?_⟩) hb (hB.second j b hb),
    ?_, ?_, ?_⟩
  · -- what the second chain takes over is at hand
    obtain ⟨l₁, l₂, t1, t2, rfl⟩ := hT
    rcases hP.taken u hu o ho ch i e with ⟨rfl, orc, h1, h2⟩ | ⟨rfl, orc, h1, h2⟩
    · rw [e1] at h1
      obtain ⟨pt, g1, g2⟩ := t1.2 i orc h1
      exact ⟨pt, by simp [taken₃, g1], g2.trans h2⟩
    · rw [e2] at h1
      obtain ⟨pt, g1, g2⟩ := t2.2 i orc h1
      exact ⟨pt, by simp [taken₃, g1], g2.trans h2⟩
  · exact ⟨⟨rfl, ⟨[], [], [], ⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩,
      fun _ _ => none, [], rfl, rfl, tablesFit_nil⟩
  · exact ⟨⟨rfl, ⟨[], [], [], ⟨rfl, rfl⟩, rfl, rfl, rfl⟩, rfl, rfl⟩,
      fun _ _ => none, [], rfl, rfl, tablesFit_nil⟩
  · intro v₁ m₁ E₁ v₂ m₂ E₂ s₃ o₁ o₂ hI₁ hI₂ _ _ _
    obtain ⟨M₁, tk₁, l₁, rfl, rfl, t1⟩ := hI₁
    obtain ⟨M₂, tk₂, l₂, rfl, rfl, t2⟩ := hI₂
    obtain ⟨a₀, b₀, d₁, ⟨rfl, rfl⟩, f1, g1, g1'⟩ := M₁.heard
    obtain ⟨a₀', b₀', d₂, ⟨rfl, rfl⟩, f2, g2, -⟩ := M₂.heard
    have w1 : roundsIn F.first.blocksInOrder F.first.blocksInOrder.length = F.roundsDeclaredByBlocks.1 := by
      unfold roundsIn
      rw [List.take_length]
      rfl
    have w2 : roundsIn F.shared.blocksInOrder F.shared.blocksInOrder.length = F.roundsDeclaredByBlocks.2.1 := by
      unfold roundsIn
      rw [List.take_length]
      rfl
    have u1 : oraclesIn F.first.blocksInOrder F.first.blocksInOrder.length =
        (rowsOfChain F.first.blocksInOrder).flatMap (·.2) := by
      unfold oraclesIn
      rw [List.take_length]
    have u2 : oraclesIn F.shared.blocksInOrder F.shared.blocksInOrder.length =
        (rowsOfChain F.shared.blocksInOrder).flatMap (·.2) := by
      unfold oraclesIn
      rw [List.take_length]
    rw [w1] at f1
    rw [w2] at f2
    rw [u1] at t1
    rw [u2] at t2
    refine ⟨⟨rfl, ⟨m₁.st.heard ++ m₂.st.heard, m₁.loc, [], ⟨d₁, d₂, f1, f2, ?_, ?_⟩, rfl,
      (List.append_nil _).symm, (List.append_nil _).symm⟩, ?_, rfl⟩,
      taken₃ l₁ l₂, [], ⟨l₁, l₂, t1, t2, rfl⟩, envThird_eq _ _ _, tablesFit_nil⟩
    · rw [g1, g2]
      rfl
    · rw [g1']
      rfl
    · show (m₁.seen ++ m₂.seen).map (·.drawn) = m₁.st.heard ++ m₂.st.heard
      rw [List.map_append, M₁.seen, M₂.seen]

/-- **The invariants of form as a member of `ThreadsP`.** -/
def threadsOfBlocks (hR : ready F Bk H w₀ rc x k = .ok R) (plan : F.planOk = true)
    (hroot : rootedAll F H = true) (hP : PlanServes H w₀ rc R)
    (hB : BlocksPlay F Bk H R.own R.common) : ThreadsP F Bk H w₀ rc x k R where
  I₁ := formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder
  I₂ := formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder
  I₃ := formAt (H.storedWords w₀ rc) (takenThird F) (startThird F) R.own F.second.blocksInOrder
  h₁ := (form_pieces hR plan hroot hP hB).1
  h₂ := (form_pieces hR plan hroot hP hB).2.1
  h₃ := (form_pieces hR plan hroot hP hB).2.2.1
  a₁ := (form_pieces hR plan hroot hP hB).2.2.2.1
  a₂ := (form_pieces hR plan hroot hP hB).2.2.2.2.1
  a₃ := (form_pieces hR plan hroot hP hB).2.2.2.2.2

/-- Its first family of invariants. -/
theorem threadsOfBlocks_first (hR : ready F Bk H w₀ rc x k = .ok R) (plan : F.planOk = true)
    (hroot : rootedAll F H = true) (hP : PlanServes H w₀ rc R)
    (hB : BlocksPlay F Bk H R.own R.common) :
    (threadsOfBlocks hR plan hroot hP hB).I₁ =
      formAt (H.storedWords w₀ rc) takenNone startNone R.own F.first.blocksInOrder := rfl

/-- Its second. -/
theorem threadsOfBlocks_shared (hR : ready F Bk H w₀ rc x k = .ok R) (plan : F.planOk = true)
    (hroot : rootedAll F H = true) (hP : PlanServes H w₀ rc R)
    (hB : BlocksPlay F Bk H R.own R.common) :
    (threadsOfBlocks hR plan hroot hP hB).I₂ =
      formAt (H.storedWords w₀ rc) takenNone startNone R.common F.shared.blocksInOrder := rfl

/-- Its third. -/
theorem threadsOfBlocks_second (hR : ready F Bk H w₀ rc x k = .ok R) (plan : F.planOk = true)
    (hroot : rootedAll F H = true) (hP : PlanServes H w₀ rc R)
    (hB : BlocksPlay F Bk H R.own R.common) :
    (threadsOfBlocks hR plan hroot hP hB).I₃ =
      formAt (H.storedWords w₀ rc) (takenThird F) (startThird F) R.own F.second.blocksInOrder := rfl

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.form_pieces
#print axioms AtPublicFiles.OfflineRows.threadsOfBlocks
#print axioms AtPublicFiles.OfflineRows.threadsOfBlocks_first
#print axioms AtPublicFiles.OfflineRows.threadsOfBlocks_shared
#print axioms AtPublicFiles.OfflineRows.threadsOfBlocks_second
