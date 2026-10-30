-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.FoldKeeps
import Johnson.Desc.Sound.FoldStepsProofs
import Johnson.Desc.K12.Law.CanonOfView
/-
Johnson/Desc/K12/Law/CanonAtFold.lean: FROM A YES OF THE DECISION's COURSE (runCore, Johnson/Desc/Block.lean) TO EACH BLOCK: it has said yes, as a step, at its own stretch of its chain's rounds, AND EVERY ELEMENT DRAWN IN THAT STRETCH IS CANONICAL (canonOk, Johnson/Desc/K12/Law/CanonOk.lean). GENERAL in the three records' and the claims' types: no kind's text is read. THE TIES ARE KEPT: m and cols' are what the fold over the blocks in front leaves of the chain's first record, the view's rounds and THE VIEW's OPENED COLUMNS; the fold behind goes on to the chain's end; the second chain's first record is start₃'s. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
WHAT THIS FILE ADDS IS SMALL. The fold's lemmas LIE IN OTHER FILES and are SPENT, not typed again: foldAt and foldConsOk' (Johnson/Desc/Sound/FoldStepsProofs.lean) · runCore_chains and bind_ok (Johnson/Desc/ChainEndFold.lean) and chainAt_fold (Johnson/Desc/FoldKeeps.lean).
(Where this and lean/THEOREM.md differ,
the page holds.)
  need_ok               a «need» that passed had a true test.
  runCore_views         NEW: a yes of runCore ⇒ viewWordsBelowPrime v₁ ∧ viewWordsBelowPrime v₂ ∧ viewWordsBelowPrime v₃. runCore_chains reads the same course back and lets these three go; THIS PROOF FOLLOWS ITS FIRST LINES CLOSELY.
  fold_step_at          foldBlocks ft (pre ++ b :: l) s rs cols = .ok out ⇒ ∃ m cols' t k: the fold over pre gives (m, the rounds behind pre's, cols') · b.step ft m ‹b's stretch of rs› cols' = .ok (t, k) · the fold over l goes on from (t, the rounds behind b's, cols' less k) to out: two calls (foldAt at the relation that always holds; foldConsOk').
  stretch_sublist       a block's stretch is a sublist of the rounds.
  StepsAt ft bs s s' v  these three and canonOk of the stretch, at every cut bs = pre ++ b :: l, at the view's rounds and opened columns, to the end (s', [], []).
  chain_step_canon      a chain's yes, where canonOk holds of the view's rounds ⇒ StepsAt.
  runCore_steps_canon   runCore's yes ⇒ StepsAt of the first chain (from s₁ to e.1, at the view with the seal's round behind it), of the shared chain (s₂ to e.2.1), and ∃ s₃, start₃ e.1 e.2.1 = .ok s₃ ∧ StepsAt of the second chain (s₃ to e.2.2).
TRIED FOR EMPTINESS: Johnson/Desc/K12/Law/CanonAtFoldToy.lean [not in this library]: a toy course of three chains that says yes at a view whose one round drew one element; at the same view with that element's first word AT the prime it refuses; runCore_steps_canon called at the yes. AT A REAL PLACE: no member is shown in K12's files: that a written description's decision has said yes on a stored proof is the word of runs not shown here.
No sorry and no axiom of our own stands in this file.
LIMITS. (1) m, cols', t, k stand under «there is», each pinned by an equation: values of named folds and of the step. (2) THE BLOCK b IS THE ONE THAT STANDS IN THE FLAT LIST: at the proximity test's four places that is a seat (Block.inside): the seat's step against the block's own is inside_step (Johnson/Top/H0/StepLaws/StepLaws.lean): not called here: Johnson/Desc/K12/Law/AccKAtCourse.lean calls it. (3) Nothing on the items' or the columns' words, which viewWordsBelowPrime also fences.
-/
set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc

theorem need_ok {name : String} {b : Bool} {u : Unit} (h : need name b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => simp [need] at h

/-- A yes of the decision's course: each of the three views has passed the test on its words. -/
theorem runCore_views {Cl S₁ S₂ S₃ : Type} (planWord : Option String) (okStart : Bool) (s₁ : S₁)
    (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : Nat) (b₁ : List (Block S₁ Cl))
    (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl)) (fin : S₁ → S₂ → S₃ → Bool)
    (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    viewWordsBelowPrime v₁ = true ∧ viewWordsBelowPrime v₂ = true ∧ viewWordsBelowPrime v₃ = true := by
  unfold runCore at h
  dsimp only at h
  split at h
  · obtain ⟨_, hx, _⟩ := ChainEnd.bind_ok h
    simp [throw, throwThe, MonadExceptOf.throw] at hx
  · obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
    obtain ⟨_, _, h⟩ := ChainEnd.bind_ok h
    obtain ⟨_, h1, h⟩ := ChainEnd.bind_ok h
    obtain ⟨_, h2, h⟩ := ChainEnd.bind_ok h
    obtain ⟨_, h3, _⟩ := ChainEnd.bind_ok h
    exact ⟨need_ok h1, need_ok h2, need_ok h3⟩

variable {S Cl : Type}

/-- A block of a fold that ends well has said yes at its own stretch of the fold's rounds: AT THE RECORD AND THE COLUMNS THAT THE FOLD OVER THE BLOCKS IN FRONT OF IT LEAVES; and the fold over the blocks behind it goes on from what it leaves. -/
theorem fold_step_at (ft : Nat) (pre : List (Block S Cl)) (b : Block S Cl) (l : List (Block S Cl))
    (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (h : foldBlocks ft (pre ++ b :: l) s rs cols = .ok out) :
    ∃ (m : S) (cols' : List OpenedColumn) (t : S) (k : Nat),
      foldBlocks ft pre s rs cols = .ok (m, behindOf pre rs, cols') ∧
      b.step ft m ((behindOf pre rs).take b.rounds.length) cols' = .ok (t, k) ∧
      foldBlocks ft l t ((behindOf pre rs).drop b.rounds.length) (cols'.drop k) = .ok out := by
  obtain ⟨m, cols', _, hp, h2⟩ := foldAt S Cl (fun _ _ => True)
    ⟨fun _ => trivial, fun _ _ _ _ _ => trivial⟩ ft pre (b :: l) s rs cols out
    (fun _ _ _ _ _ _ _ => trivial) h
  obtain ⟨t, k, _, h3, h4⟩ := foldConsOk' h2
  exact ⟨m, cols', t, k, hp, h3, h4⟩

theorem stretch_sublist (pre : List (Block S Cl)) (n : Nat) (rs : List Fmt.RoundView) :
    ((behindOf pre rs).take n).Sublist rs :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

/-- What is said of a chain's list bs, from the record s to the record s', at the view v: WHEREVER bs = pre ++ b :: l: m and cols' are what the fold over pre leaves of s, the view's rounds and THE VIEW's OPENED COLUMNS; b's step says yes at m, at b's own stretch of the view's rounds, at cols'; the fold over l goes on from what b leaves to s', with nothing left over; every element drawn in the stretch is canonical. -/
def StepsAt (ft : Nat) (bs : List (Block S Cl)) (s s' : S) (v : Fmt.View) : Prop :=
  ∀ (pre : List (Block S Cl)) (b : Block S Cl) (l : List (Block S Cl)), bs = pre ++ b :: l →
    ∃ (m : S) (cols' : List OpenedColumn) (t : S) (k : Nat),
      foldBlocks ft pre s v.rounds v.opened = .ok (m, behindOf pre v.rounds, cols') ∧
      b.step ft m ((behindOf pre v.rounds).take b.rounds.length) cols' = .ok (t, k) ∧
      foldBlocks ft l t ((behindOf pre v.rounds).drop b.rounds.length) (cols'.drop k) =
        .ok (s', [], []) ∧
      canonOk ((behindOf pre v.rounds).take b.rounds.length) = true

/-- A chain that says yes, at a view whose drawn elements are canonical. -/
theorem chain_step_canon (name : String) (ft : Nat) (bs : List (Block S Cl)) (s s' : S)
    (v : Fmt.View) (hc : canonOk v.rounds = true) (h : chainAt name ft bs s v = .ok s') :
    StepsAt ft bs s s' v := by
  intro pre b l hb
  subst hb
  obtain ⟨m, cols', t, k, h0, h1, h2⟩ := fold_step_at ft pre b l s v.rounds v.opened _
    (Keeps.chainAt_fold name ft _ s s' v h)
  exact ⟨m, cols', t, k, h0, h1, h2, canonOk_sublist (stretch_sublist pre _ _) hc⟩

/-- FROM A YES OF THE DECISION's COURSE: StepsAt of each chain, from its own first record to its own end, at its own view (the first chain's with the seal's round behind it, as runCore lays it); the second chain's first record is what start₃ makes of the two other chains' ends. -/
theorem runCore_steps_canon {Cl S₁ S₂ S₃ : Type} (planWord : Option String) (okStart : Bool)
    (s₁ : S₁) (s₂ : S₂) (start₃ : S₁ → S₂ → Except String S₃) (ft : Nat)
    (b₁ : List (Block S₁ Cl)) (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl))
    (fin : S₁ → S₂ → S₃ → Bool) (v₁ v₂ v₃ : Fmt.View) (e : S₁ × S₂ × S₃)
    (h : runCore planWord okStart s₁ s₂ start₃ ft b₁ b₂ b₃ fin v₁ v₂ v₃ = .ok e) :
    StepsAt 0 b₁ s₁ e.1 (withEmptySealRound v₁) ∧ StepsAt 0 b₂ s₂ e.2.1 v₂ ∧
      ∃ s₃, start₃ e.1 e.2.1 = .ok s₃ ∧ StepsAt ft b₃ s₃ e.2.2 v₃ := by
  obtain ⟨w1, w2, w3⟩ := runCore_views _ _ _ _ _ _ _ _ _ _ _ _ _ e h
  obtain ⟨e₁, e₂, e₃⟩ := e
  obtain ⟨c1, c2, ⟨s₃, hs, c3⟩, _⟩ := ChainEnd.runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂ e₃ h
  exact ⟨chain_step_canon _ 0 b₁ s₁ e₁ (withEmptySealRound v₁) (canonOk_withSealW v₁ w1) c1,
    chain_step_canon _ 0 b₂ s₂ e₂ v₂ (canonOk_of_okViewW v₂ w2) c2,
    s₃, hs, chain_step_canon _ ft b₃ s₃ e₃ v₃ (canonOk_of_okViewW v₃ w3) c3⟩

end H2K.First

#print axioms H2K.First.runCore_views
#print axioms H2K.First.fold_step_at
#print axioms H2K.First.chain_step_canon
#print axioms H2K.First.runCore_steps_canon
