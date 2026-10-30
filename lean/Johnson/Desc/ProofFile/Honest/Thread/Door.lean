-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/Door.lean: THE PREMISE AT THE SECOND CHAIN's START, BEHIND ITS
YES (`DoorBehind`: Honest/Thread/File.lean), CUT INTO WHAT BEARS CONTENT: as
Honest/Thread/Enters.lean cuts the two other starts. `DoorBehind` says: from the two earlier threads
at their last borders, wherever the second chain's start says yes, the whole third thread holds
there: seven clauses. Where the third thread's letters ahead and near are laid as the two earlier
chains' rounds, three of the seven hold by the frame's own text. What is left is what the third
thread's letters say AT THE START. Conditional lemmas on our own definitions; general in the
description, the prover and the three threads.

  1  `trees_taken_of`   THE TREES THAT ARE TAKEN OVER ARE AT HAND: where each source that the third
     thread takes over is an own tree of the first or of the shared chain that is at hand at that
     chain's last border, and the third thread's table there is that thread's
  2  `doorBehind_of`

WHAT HOLDS BY THE FRAME's OWN TEXT (`Ready.start₃`, Honest/Frame.lean; `envThird`,
Honest/Law/Thread.lean), under five equations on the letters (hah₁ hn₁ hah₂ hah hnear): (F) the
challenges heard are the two chains', in a row, and fit ahead · of (X): what was shown drew what was
heard; the stops read the first chain's challenges alone; no own tree is sent, none is at hand; no
column is read; the fold over no member returns the first state · of (H): the stored columns, under
hst; the trees, under htrees, which `trees_taken_of` pays.

WHAT IS LEFT AS NAMED PREMISES ON THE THIRD THREAD's LETTERS, each asked from the two threads' ends
and the start's yes: hbeg (the state that the start returns is the one that the thread begins with,
at all challenges heard) · hForm · hItems (THE ITEMS THAT ARE OPEN AT THE START) · hr; and hv,
which is asked outright.

ahead AND near ARE TYPED WITH THE LISTS' OWN LENGTHS: no number is written: so the lemma is free of
the description's size.

Limits. The first and the shared thread have no round in front of them (hah₁ hah₂), and the first
chain's stops read all its challenges (hn₁): as `enters₁_of` and `enters₂_of` take them. None is one
of the library's goals. This file proves nothing about soundness, completeness, hiding or any other
property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts}

section
variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {x : Xi} {k : Coins Bk}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}

/-- **THE TREES THAT ARE TAKEN OVER ARE AT HAND AT THE SECOND CHAIN's START.** n₁, n₂: the two
borders. -/
theorem trees_taken_of {n₁ n₂ : Nat} {e₁ : F.S₁} {m₁ : Mid (Local W₀ Rc Xi Tr) X} {E₁ : Env}
    {e₂ : F.S₂} {m₂ : Mid (Common W₀ Rc Ky) X₀} {E₂ : Env}
    (u₁ : Thr T₁ n₁ k e₁ m₁ E₁) (u₂ : Thr T₂ n₂ k e₂ m₂ E₂)
    (tk : ∀ σ ∈ T₃.taken,
      (∃ j, σ = .taken 0 j ∧ Fmt.TreeSource.own j ∈ T₁.hand n₁ ∧
        T₃.tableAt σ k (R.start₃ H m₁ m₂) = T₁.tableAt (.own j) k m₁) ∨
      ∃ j, σ = .taken 1 j ∧ Fmt.TreeSource.own j ∈ T₂.hand n₂ ∧
        T₃.tableAt σ k (R.start₃ H m₁ m₂) = T₂.tableAt (.own j) k m₂) :
    T₃.Trees T₃.taken k (R.start₃ H m₁ m₂) (envThird E₁ E₂) := by
  unfold Thr Thread.Hand at u₁ u₂
  intro σ hσ
  rcases tk σ hσ with ⟨j, rfl, hj, ht⟩ | ⟨j, rfl, hj, ht⟩
  · have h := u₁.1.2 (.own j) hj
    unfold Thread.handAt at h ⊢
    rw [ht]
    exact h
  · have h := u₂.1.2 (.own j) hj
    unfold Thread.handAt at h ⊢
    rw [ht]
    exact h

/-- **THE DOOR, BEHIND ITS YES.** -/
theorem doorBehind_of (hah₁ : T₁.ahead = []) (hn₁ : T₁.near = 0) (hah₂ : T₂.ahead = [])
    (hah : T₃.ahead =
      declsTo T₁.bs F.first.blocksInOrder.length ++ declsTo T₂.bs F.shared.blocksInOrder.length)
    (hnear : T₃.near = (declsTo T₁.bs F.first.blocksInOrder.length).length)
    (hst : ∀ v, T₁.valid v → ∀ i p, T₁.stored v i p = T₃.stored R.own i p)
    (htrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.Trees T₃.taken k (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (hbeg : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.begun k R.own (m₁.st.heard ++ m₂.st.heard) s₃)
    (hForm : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.Form 0 k s₃ (R.start₃ H m₁ m₂))
    (hItems : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.Items (T₃.opened 0) k s₃ (R.start₃ H m₁ m₂) (envThird E₁ E₂))
    (hr : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, Thr T₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      Thr T₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.rides 0 R.own s₃)
    (hv : T₃.valid R.own) : DoorBehind F H T₁ T₂ T₃ x k R := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs
  have u₁' := u₁
  have u₂' := u₂
  unfold Thr Thread.Hand Thread.Fit Thread.Made at u₁' u₂'
  obtain ⟨⟨hst₁, -⟩, hF₁, -, -, ⟨hseen₁, hloc₁, -, -, -⟩, -, hv₁⟩ := u₁'
  obtain ⟨-, hF₂, -, -, ⟨hseen₂, -, -, -, -⟩, -, -⟩ := u₂'
  rw [hah₁, List.nil_append] at hF₁
  rw [hah₂, List.nil_append] at hF₂
  have l₁ := drawsFit_length _ _ hF₁
  have l₂ := drawsFit_length _ _ hF₂
  have hloc : T₁.locOf m₁.st.heard = m₁.st.heard := by
    simp [Thread.locOf, Thread.front, hn₁, hah₁]
  have hfr : T₃.front = (m₁.st.heard ++ m₂.st.heard).length := by
    unfold Thread.front
    rw [hah, List.length_append, List.length_append, l₁, l₂]
  have hs12 : (m₁.seen ++ m₂.seen).map (·.drawn) = m₁.st.heard ++ m₂.st.heard := by
    rw [List.map_append, hseen₁, hseen₂]
  have hh : T₃.hand 0 = T₃.taken := List.append_nil _
  unfold Thr
  refine ⟨⟨fun i p => ?_, ?_⟩, ?_, hForm e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs,
    hItems e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs, ?_, hr e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs, hv⟩
  · show E₁.stored i p = T₃.stored R.own i p
    rw [hst₁ i p]
    exact hst _ hv₁ i p
  · rw [hh]
    exact htrees e₁ m₁ E₁ e₂ m₂ E₂ u₁ u₂
  · unfold Thread.Fit
    show drawsFit (T₃.ahead ++ []) (m₁.st.heard ++ m₂.st.heard) = true
    rw [List.append_nil, hah, drawsFit_append, List.take_left' l₁, List.drop_left' l₁, hF₁, hF₂]
    rfl
  · unfold Thread.Made
    refine ⟨hs12, ?_, rfl, fun _ _ => rfl, s₃, [], ?_, rfl, ?_⟩
    · show m₁.loc = T₃.locOf (m₁.st.heard ++ m₂.st.heard)
      unfold Thread.locOf
      rw [hfr, List.drop_length, List.append_nil, hnear, List.take_left' l₁]
      exact hloc₁.trans hloc
    · show T₃.begun k R.own ((m₁.st.heard ++ m₂.st.heard).take T₃.front) s₃
      rw [hfr, List.take_length]
      exact hbeg e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs
    · show foldBlocks T₃.ft (T₃.bs.take 0) s₃ ((m₁.seen ++ m₂.seen).drop T₃.front) [] =
        .ok (s₃, [], [])
      have e1 : (m₁.seen ++ m₂.seen).length = T₃.front := by
        rw [hfr, ← hs12, List.length_map]
      rw [← e1, List.drop_length]
      rfl

end

end ProofFile.Honest

#print axioms ProofFile.Honest.trees_taken_of
#print axioms ProofFile.Honest.doorBehind_of
