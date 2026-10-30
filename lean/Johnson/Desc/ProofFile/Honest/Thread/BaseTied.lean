-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/BaseTied.lean: THE COLUMNS THAT THE LAST CHAIN BEGINS WITH, TIED
TO THE STATE AT WHICH IT BEGAN. `BaseOfEnds` says that the two earlier folds return at a base, and
says nothing of the states at which they return. `BaseTied` adds what a test in the last chain
needs: at these two states the description's `start₃` returns the state that the thread's `begun`
names.

  `BaseTied`, `baseOfEnds_of_tied`   the letter `B` of `SaidField` at the last chain
  `baseTied_kept`   it is carried over a sub-protocol's rounds, with no premise
  `heard_length_seen`   under `Thr`, as many challenges were heard as rounds were seen
  `baseTied_at_door`   it holds at the last chain's start

What these are. Definitions and conditional lemmas on our own definitions. None is one of the
library's goals.

Limits.
  * `htie` of `baseTied_at_door` is a premise: where the two earlier chains' invariants hold, `begun`
    at the last chain names the state that `start₃` returns at their ends. At the last chain's
    `Letters` that is what the letter `ends` has to give.
  * `hb₁` and `hb₂` are premises, as at `baseOfEnds_at_door`.
  * Nothing here says that the two ends are the ends of one run.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BaseAtDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

section
variable {W₀ Rc Xi Tr X V Pb : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)
  (T : Thread Bk F.S₃ F.Cl V (Local W₀ Rc Xi Tr) X Pb)

/-- **The columns of the two earlier chains, and the state that their ends start.** A definition: a
filling of the letter `B` of `SaidField`. -/
def BaseTied (k : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X) (base : List OpenedColumn) : Prop :=
  ∃ r₁ r₂ rest c₁ c₂ e₁ e₂, m.seen = r₁ ++ (r₂ ++ rest) ∧ base = c₁ ++ c₂ ∧
    r₁.length = (F.first.blocksInOrder.flatMap (·.rounds)).length ∧
    c₁.length = owed 0 F.first.blocksInOrder r₁ ∧
    r₂.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length ∧
    c₂.length = owed 0 F.shared.blocksInOrder r₂ ∧
    foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub m.st.input.x)) r₁ c₁ = .ok (e₁, [], []) ∧
    foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub m.st.input.x)) r₂ c₂ = .ok (e₂, [], []) ∧
    T.front ≤ m.st.heard.length ∧
    ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ →
      F.start₃ (F.pub m.st.input.x) e₁ e₂ = .ok s₀

theorem baseOfEnds_of_tied {k : Coins Bk} {m : Mid (Local W₀ Rc Xi Tr) X} {base : List OpenedColumn}
    (h : BaseTied F T k m base) : BaseOfEnds F k m base := by
  obtain ⟨r₁, r₂, rest, c₁, c₂, e₁, e₂, h0, h1, h2, h3, h4, h5, h6, h7, -, -⟩ := h
  exact ⟨r₁, r₂, rest, c₁, c₂, e₁, e₂, h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- **It is carried over a sub-protocol's rounds**: they lie behind what was seen, the input stays,
and what was heard in front of the chain stays. -/
theorem baseTied_kept (b : Nat) : BaseKept T (BaseTied F T) b := by
  intro blk _ k m E ds y cols base hM hB
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  obtain ⟨hi, -, hs⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  obtain ⟨tail, ht⟩ : ∃ t, y.2.seen = m.seen ++ t := ⟨_, hs⟩
  obtain ⟨r₁, r₂, rest, c₁, c₂, e₁, e₂, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hB
  refine ⟨r₁, r₂, rest ++ tail, c₁, c₂, e₁, e₂, ?_, h1, h2, h3, h4, h5, ?_, ?_, ?_, ?_⟩
  · show y.2.seen = _
    rw [ht, h0]
    simp only [List.append_assoc]
  · show foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub y.2.st.input.x)) r₁ c₁ = _
    rw [hi]
    exact h6
  · show foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub y.2.st.input.x)) r₂ c₂ = _
    rw [hi]
    exact h7
  · show T.front ≤ y.2.st.heard.length
    rw [eh, List.length_append]
    omega
  · intro s₀ g
    have g' : T.begun k y.2.st.input (y.2.st.heard.take T.front) s₀ := g
    rw [hi, eh, List.take_append_of_le_length h8] at g'
    show F.start₃ (F.pub y.2.st.input.x) e₁ e₂ = _
    rw [hi]
    exact h9 s₀ g'

end

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- Under `Thr`, as many challenges were heard as rounds were seen. -/
theorem heard_length_seen {T : Thread Bk S Cl V W X Pb} {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid W X} {E : Env} (hA : Thr T b k s m E) : m.st.heard.length = m.seen.length := by
  obtain ⟨hmap, -⟩ := hA.2.2.2.2.1
  rw [← hmap, List.length_map]

end

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
  {S₁ : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop}
  {S₂ : Nat → Coins Bk → Mid (Common W₀ Rc Ky) X₀ → Prop}

/-- **The letter at the last chain's start.** `S₁`, `S₂`: what is said at the two ends, each at least
the field letter (`hS₁`, `hS₂`). `hfront`: the rounds in front of the last chain are the two earlier
chains'. `htie`: see the head. -/
theorem baseTied_at_door (sits : Sits F H T₁ T₂ T₃) (hah₁ : T₁.ahead = [])
    (hah₂ : T₂.ahead = []) (hx : R.own.x = x)
    (hS₁ : ∀ k m, S₁ F.first.blocksInOrder.length k m → SaidField T₁ BaseNil F.first.blocksInOrder.length k m)
    (hS₂ : ∀ k m, S₂ F.shared.blocksInOrder.length k m → SaidField T₂ BaseNil F.shared.blocksInOrder.length k m)
    (hfront : T₃.front =
      (F.first.blocksInOrder.flatMap (·.rounds)).length + (F.shared.blocksInOrder.flatMap (·.rounds)).length)
    (hb₁ : ∀ e m E s₀, Thr T₁ F.first.blocksInOrder.length k e m E → T₁.begun k m.st.input [] s₀ →
      s₀ = F.start₁ (F.pub x))
    (hb₂ : ∀ e m E s₀, Thr T₂ F.shared.blocksInOrder.length k e m E → T₂.begun k m.st.input [] s₀ →
      s₀ = F.start₂ (F.pub x))
    (htie : ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₀,
      ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      T₃.begun k R.own (m₁.st.heard ++ m₂.st.heard) s₀ → F.start₃ (F.pub x) e₁ e₂ = .ok s₀) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      ThrS T₁ S₁ F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ S₂ F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      BaseTied F T₃ k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (o₁ ++ o₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ _ g₁ g₂
  obtain ⟨-, -, f₁, b₁, -⟩ := sits.one
  obtain ⟨-, -, f₂, b₂, -⟩ := sits.two
  have v₁ : Thr T₁ T₁.bs.length k e₁ m₁ E₁ := by
    rw [b₁]
    exact u₁.1
  have w₁ : SaidField T₁ BaseNil T₁.bs.length k m₁ := by
    rw [b₁]
    exact hS₁ _ _ u₁.2
  have v₂ : Thr T₂ T₂.bs.length k e₂ m₂ E₂ := by
    rw [b₂]
    exact u₂.1
  have w₂ : SaidField T₂ BaseNil T₂.bs.length k m₂ := by
    rw [b₂]
    exact hS₂ _ _ u₂.2
  obtain ⟨s₁, bg₁, ln₁, fd₁⟩ := end_of_saidField T₁ hah₁ f₁ v₁ w₁ g₁
  obtain ⟨s₂, bg₂, ln₂, fd₂⟩ := end_of_saidField T₂ hah₂ f₂ v₂ w₂ g₂
  obtain rfl := hb₁ e₁ m₁ E₁ s₁ u₁.1 bg₁
  obtain rfl := hb₂ e₂ m₂ E₂ s₂ u₂.1 bg₂
  rw [b₁] at ln₁ fd₁
  rw [b₂] at ln₂ fd₂
  have hl : T₃.front = (m₁.st.heard ++ m₂.st.heard).length := by
    rw [List.length_append, heard_length_seen v₁, heard_length_seen v₂, ln₁, ln₂, hfront]
  refine ⟨m₁.seen, m₂.seen, [], o₁, o₂, e₁, e₂, ?_, rfl, ln₁,
    cols_length_of_fold 0 _ _ _ _ _ fd₁, ln₂, cols_length_of_fold 0 _ _ _ _ _ fd₂, ?_, ?_, ?_, ?_⟩
  · show m₁.seen ++ m₂.seen = m₁.seen ++ (m₂.seen ++ [])
    rw [List.append_nil]
  · show foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub R.own.x)) m₁.seen o₁ = _
    rw [hx]
    exact fd₁
  · show foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub R.own.x)) m₂.seen o₂ = _
    rw [hx]
    exact fd₂
  · show T₃.front ≤ (m₁.st.heard ++ m₂.st.heard).length
    exact Nat.le_of_eq hl
  · intro s₀ g
    have g' : T₃.begun k R.own ((m₁.st.heard ++ m₂.st.heard).take T₃.front) s₀ := g
    rw [hl, List.take_length] at g'
    show F.start₃ (F.pub R.own.x) e₁ e₂ = _
    rw [hx]
    exact htie e₁ m₁ E₁ e₂ m₂ E₂ s₀ u₁ u₂ g'

end ProofFile.Honest

#print axioms ProofFile.Honest.BaseTied
#print axioms ProofFile.Honest.baseOfEnds_of_tied
#print axioms ProofFile.Honest.baseTied_kept
#print axioms ProofFile.Honest.heard_length_seen
#print axioms ProofFile.Honest.baseTied_at_door
