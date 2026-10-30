-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyDoorS.lean: the library's `DoorBehindS` (Johnson/Desc/ProofFile/Honest/Thread/FileD.lean) from
its clauses, each asked from the pairs `ThrS`: a twin of `doorBehind_of`
(Johnson/Desc/ProofFile/Honest/Thread/Door.lean).

Why. The bare door asks its clauses from bare `Thr`. There the road for `hbeg` and `hForm` has no payer:
one state for each run wants a `Said`. The library's `doorBehindS_of` takes the whole bare door, so it
keeps that debt. This statement asks each clause from the pairs instead.

Main names.
  `doorPairs_of`: `DoorBehindS` from the clauses: the proof of `doorBehind_of`, at the first half of each
    pair, at the state with the two ends' fields `opened` joined, which is where `DoorBehindS` ends.

What stays open. It stands on the text of `DoorBehindS`, with its hypotheses on the field
`opened`. Nothing here says that a thread stands.
General in the threads; no coin of a committer is named but as a letter.

NOT IN FRONT OF A LAW OVER COINS: `doorPairs_of` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: it stands behind `ThrS` at a run's coins `k`, whose
clauses tie the threads' letters, of the first kind. None of these is the term that the committer
makes. None: the bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import Johnson.Desc.ProofFile.Honest.Thread.Door
import Johnson.Desc.ProofFile.Honest.Thread.FileD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.KeyDoorS
open ProofFile.Honest
open VerifiableInference.Desc

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Ky Tr X₀ X : Type}

variable {F : FileDescription Xi} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {x : Xi} {k : Coins Bk}
  {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}
  {S₃ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}

/-- **The door from the pairs.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem doorPairs_of (hah₁ : T₁.ahead = []) (hn₁ : T₁.near = 0) (hah₂ : T₂.ahead = [])
    (hah : T₃.ahead =
      declsTo T₁.bs F.first.blocksInOrder.length ++ declsTo T₂.bs F.shared.blocksInOrder.length)
    (hnear : T₃.near = (declsTo T₁.bs F.first.blocksInOrder.length).length)
    (hst : ∀ v, T₁.valid v → ∀ i p, T₁.stored v i p = T₃.stored R.own i p)
    (htrees : ∀ e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.Trees T₃.taken k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂))
    (hbeg : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.begun k R.own (m₁.st.heard ++ m₂.st.heard) s₃)
    (hForm : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.Form 0 k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) })
    (hItems : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.Items (T₃.opened 0) k s₃ { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (envThird E₁ E₂))
    (hr : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃, ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ → F.start₃ (F.pub x) e₁ e₂ = .ok s₃ →
      T₃.rides 0 R.own s₃)
    (hv : T₃.valid R.own)
    (hS₃ : ∀ m₁ m₂ o₁ o₂, S₁ F.first.blocksInOrder.length k m₁ → S₂ F.shared.blocksInOrder.length k m₂ →
      m₁.opened = some o₁ → m₂.opened = some o₂ → S₃ 0 k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) }) :
    DoorBehindS F H T₁ T₂ T₃ S₁ S₂ S₃ x k R := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs h₁ h₂
  refine ⟨?_, hS₃ m₁ m₂ o₁ o₂ u₁.2 u₂.2 h₁ h₂⟩
  have u₁' := u₁.1
  have u₂' := u₂.1
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
  refine ⟨⟨fun i p => ?_, ?_⟩, ?_, hForm e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs,
    hItems e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ hs, ?_, hr e₁ m₁ E₁ e₂ m₂ E₂ s₃ u₁ u₂ hs, hv⟩
  · show E₁.stored i p = T₃.stored R.own i p
    rw [hst₁ i p]
    exact hst _ hv₁ i p
  · rw [hh]
    exact htrees e₁ m₁ E₁ e₂ m₂ E₂ o₁ o₂ u₁ u₂
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

end AtPublicFiles.KeyDoorS

#print axioms AtPublicFiles.KeyDoorS.doorPairs_of
