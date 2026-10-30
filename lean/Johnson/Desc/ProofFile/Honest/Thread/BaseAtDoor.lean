-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/BaseAtDoor.lean: THE PREMISE `hB` OF `door_field` AT
`BaseOfEnds`. Where the two earlier chains end under the letter `SaidField` with nothing in front,
the columns that their fields hold are those at which the description's folds return, so
`BaseOfEnds` holds at the last chain's start.

  `cols_length_of_fold`   a fold that leaves nothing over read as many columns as `owed` counts: the
    converse of `fold_exact` (Honest/Law/WalkFold.lean)
  `end_of_saidField`   at a thread's last border, under the letter: the fold from where it began
  `baseOfEnds_at_door`   `hB`

What these are. Conditional lemmas on our own definitions. None is one of the library's goals.

Limits.
  * `hb₁` and `hb₂` are premises: at the two earlier threads `begun` names the description's start
    at this instance. They are shown here of no thread.
  * Nothing here says that the two ends are the ends of one run, or that any state meets `Thr`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.BaseOfEnds
import Johnson.Desc.ProofFile.Honest.Thread.FromThreadsField
import Johnson.Desc.ProofFile.Honest.Law.WalkFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open VerifiableInference.Desc.Sound (step_ok_iff)

section
variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **A fold that leaves nothing over read as many columns as `owed` counts.** -/
theorem cols_length_of_fold (ft : Nat) : ∀ (l : List (Block S Cl)) (s e : S) (R : List Fmt.RoundView)
    (C : List OpenedColumn), foldBlocks ft l s R C = .ok (e, [], []) → C.length = owed ft l R
  | [], s, e, R, C, h => by
    have q : (Except.ok (s, R, C) : Except String (S × List Fmt.RoundView × List OpenedColumn)) =
        .ok (e, [], []) := h
    cases q
    rw [owed_nil]
    rfl
  | b :: l, s, e, R, C, h => by
    obtain ⟨-, t, k, hs, h'⟩ := foldBlocks_cons_ok.1 h
    obtain ⟨-, hm, hk, -⟩ := (step_ok_iff ft b s t _ C k).1 hs
    have ih := cols_length_of_fold ft l t e _ _ h'
    have hl := congrArg List.length hm
    rw [List.length_map, List.length_take, ← hk] at hl
    rw [List.length_drop] at ih
    have hw : (b.want ft (R.take b.rounds.length)).length = k := hk.symm
    rw [owed_cons, hw]
    omega

/-- **At a thread's last border, under the letter, with nothing in front**: where the field holds
`o`, the description's fold over the thread's blocks, on all that the state has seen and on `o`,
returns the verifier's state with nothing left over. -/
theorem end_of_saidField (T : Thread Bk S Cl V W X Pb) (hah : T.ahead = []) (hft : T.ft = 0)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} {o : List OpenedColumn}
    (hA : Thr T T.bs.length k s m E) (hS : SaidField T BaseNil T.bs.length k m)
    (ho : m.opened = some o) :
    ∃ s₀, T.begun k m.st.input [] s₀ ∧ m.seen.length = (T.bs.flatMap (·.rounds)).length ∧
      foldBlocks 0 T.bs s₀ m.seen o = .ok (s, [], []) := by
  obtain ⟨base, cols, hB, hc, hf⟩ := opened_of_saidField T hA hS
  obtain rfl : base = [] := hB
  obtain rfl : o = cols := by
    rw [ho] at hf
    exact Option.some.inj hf
  obtain ⟨hmap, -, -, -, s₀, cols', hbeg, hc', hfold⟩ := hA.2.2.2.2.1
  obtain rfl : cols' = o := Except.ok.inj (hc'.symm.trans hc)
  have hfr : T.front = 0 := by
    unfold Thread.front
    rw [hah]
    rfl
  rw [hfr, List.take_zero] at hbeg
  rw [hfr, List.drop_zero, List.take_length, hft] at hfold
  have hl := T.heard_length hA.2.1
  rw [hfr, Nat.zero_add] at hl
  refine ⟨s₀, hbeg, ?_, hfold⟩
  have hlen : m.seen.length = m.st.heard.length := by
    rw [← hmap, List.length_map]
  rw [hlen, hl]
  show ((T.bs.take T.bs.length).flatMap (·.rounds)).length = _
  rw [List.take_length]

end

variable {W₀ Rc Xi Ky Tr X₀ X : Type} {Bk : ProverCoinCounts} {F : FileDescription Xi}
  {H : Prover W₀ Rc Xi Ky Tr X₀ X}
  {T₁ : Thread Bk F.S₁ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {T₂ : Thread Bk F.S₂ F.Cl Empty (Common W₀ Rc Ky) X₀ Ky}
  {T₃ : Thread Bk F.S₃ F.Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi}
  {x : Xi} {k : Coins Bk} {R : Ready W₀ Rc Xi Ky Tr X₀ X}

/-- **`hB` of `door_field`, at `BaseOfEnds`.** `hx`: the run's own instance. `hb₁`, `hb₂`: at the
two earlier threads `begun` names the description's start. -/
theorem baseOfEnds_at_door (sits : Sits F H T₁ T₂ T₃) (hah₁ : T₁.ahead = [])
    (hah₂ : T₂.ahead = []) (hx : R.own.x = x)
    (hb₁ : ∀ e m E s₀, Thr T₁ F.first.blocksInOrder.length k e m E → T₁.begun k m.st.input [] s₀ →
      s₀ = F.start₁ (F.pub x))
    (hb₂ : ∀ e m E s₀, Thr T₂ F.shared.blocksInOrder.length k e m E → T₂.begun k m.st.input [] s₀ →
      s₀ = F.start₂ (F.pub x)) :
    ∀ e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂,
      ThrS T₁ (SaidField T₁ BaseNil) F.first.blocksInOrder.length k e₁ m₁ E₁ →
      ThrS T₂ (SaidField T₂ BaseNil) F.shared.blocksInOrder.length k e₂ m₂ E₂ →
      F.start₃ (F.pub x) e₁ e₂ = .ok s₃ → m₁.opened = some o₁ → m₂.opened = some o₂ →
      BaseOfEnds F k { R.start₃ H m₁ m₂ with opened := some (o₁ ++ o₂) } (o₁ ++ o₂) := by
  intro e₁ m₁ E₁ e₂ m₂ E₂ s₃ o₁ o₂ u₁ u₂ _ g₁ g₂
  obtain ⟨-, -, f₁, b₁, -⟩ := sits.one
  obtain ⟨-, -, f₂, b₂, -⟩ := sits.two
  have v₁ : Thr T₁ T₁.bs.length k e₁ m₁ E₁ := by
    rw [b₁]
    exact u₁.1
  have w₁ : SaidField T₁ BaseNil T₁.bs.length k m₁ := by
    rw [b₁]
    exact u₁.2
  have v₂ : Thr T₂ T₂.bs.length k e₂ m₂ E₂ := by
    rw [b₂]
    exact u₂.1
  have w₂ : SaidField T₂ BaseNil T₂.bs.length k m₂ := by
    rw [b₂]
    exact u₂.2
  obtain ⟨s₁, bg₁, ln₁, fd₁⟩ := end_of_saidField T₁ hah₁ f₁ v₁ w₁ g₁
  obtain ⟨s₂, bg₂, ln₂, fd₂⟩ := end_of_saidField T₂ hah₂ f₂ v₂ w₂ g₂
  obtain rfl := hb₁ e₁ m₁ E₁ s₁ u₁.1 bg₁
  obtain rfl := hb₂ e₂ m₂ E₂ s₂ u₂.1 bg₂
  rw [b₁] at ln₁ fd₁
  rw [b₂] at ln₂ fd₂
  refine ⟨m₁.seen, m₂.seen, [], o₁, o₂, e₁, e₂, ?_, rfl, ln₁,
    cols_length_of_fold 0 _ _ _ _ _ fd₁, ln₂, cols_length_of_fold 0 _ _ _ _ _ fd₂, ?_, ?_⟩
  · show m₁.seen ++ m₂.seen = m₁.seen ++ (m₂.seen ++ [])
    rw [List.append_nil]
  · show foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub R.own.x)) m₁.seen o₁ = _
    rw [hx]
    exact fd₁
  · show foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub R.own.x)) m₂.seen o₂ = _
    rw [hx]
    exact fd₂

end ProofFile.Honest

#print axioms ProofFile.Honest.cols_length_of_fold
#print axioms ProofFile.Honest.end_of_saidField
#print axioms ProofFile.Honest.baseOfEnds_at_door
