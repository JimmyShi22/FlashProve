-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/FoldCut.lean: THE FORMAT's OWN FOLD OVER A CHAIN's SUB-PROTOCOLS
(`foldBlocks`, Johnson/Desc/Block.lean), AT ONE LIST OF ROUNDS: cut at the sub-protocol number j;
and a rule for a sentence that reads the border's number. One definition, and statements with their
proofs. General in the list: no kind is named, and nothing of the frame for the honest side.

THE LIBRARY HAS THE CUT. Johnson/Desc/Sound/FoldSteps.lean and FoldStepsProofs.lean: `foldAt`: a
fold over pre ++ rest that returns: the fold over pre returns a state m and leaves the rounds behind
those that pre has (`behindOf`); the fold over rest returns from there to the same end; `foldJoin`:
the converse; `foldConsOk'`, `foldConsMk`: a list with a first sub-protocol, both ways. All four are
called.
MORE KIN IN THE LIBRARY. The number: `roundsAhead` is, body for body, `K9L.roundsBefore`
(Johnson/Desc/First/Batch/Law/CutAt.lean); it is typed here anew because that file stands on far
more of the library than this one. Weaker cuts by number: `fold_next`, `fold_back`
(Johnson/IMR/FoldTools.lean: the rounds under "there are"), `fold_cut` (IMR/GroupRest.lean). With a
last sub-protocol: `fold_snoc` (Johnson/Top/H0/Walk/Reach.lean: where nothing is left over). Border
by border: `Reach`, `Reach.fold`, `reach_of_fold` (the same file): of no named rounds. The cut
without the rounds that are left: `fold_split` (Reach.lean), `foldBlocks_split`, `foldBlocks_append`
(Johnson/Desc/K15/K15Run.lean). FROM A STEP TO THE DECISION, which no statement here makes:
`decidedAt` (FoldStepsProofs.lean: the decision at `shownAt pre b rs`, which is the slice here, each
round without its digest, by unfolding), `stepOk`, `step_inv`.
WHAT IS ADDED: the slice named by number at ONE list of rounds; one state sj for three equations; a
rule that hands the fold's own equation to the step.
For a law on one field of the state: Johnson/Desc/Sound/FoldHeard.lean: `Block.Leaves`,
`FoldLeaves`: a fold over sub-protocols that all leave a reading h of the state leaves h.
(`Block.Lays`, `FoldLays` ask that h behind be a function of the shown rounds ALONE, at every state
in front.)
Main names:
  `roundsAhead bs j`: how many rounds the first j sub-protocols have: `behindOf (bs.take j) rs` is
    `rs.drop (roundsAhead bs j)`, by unfolding. `roundsAhead_zero`, `roundsAhead_succ`,
    `roundsAhead_take`; `take_take_le`.
  `foldCutAt`: **where the fold returns, at the sub-protocol number j: the fold over those in front
    returns a state sj and leaves the rounds from number `roundsAhead bs j` on; the sub-protocol's
    own step from sj on its own slice of the rounds returns; the fold over those behind, from there,
    returns what the whole fold returned.** ONE sj for all three.
  `foldBlocks_snoc`: the fold over a list with one sub-protocol more behind it, put together.
  `foldStepsAt`: **the rule**: a sentence I on the border's number and the state that each
    sub-protocol's step carries from k to k + 1 goes from the first state to the last. The step is
    asked on the sub-protocol's own slice, at the columns that the fold had left; the fold's own
    equation over the sub-protocols in front, and that the slice is whole, are given with it.
    `foldStepsFrom`: its induction.

What is not claimed. One direction: from a return. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.FoldStepsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open VerifiableInference.Desc (Block OpenedColumn foldBlocks foldAt foldJoin foldConsOk' foldConsMk preTrue
  behindOf)

variable {S Cl : Type}

/-- How many rounds the first j sub-protocols have. -/
def roundsAhead (bs : List (Block S Cl)) (j : Nat) : Nat := ((bs.take j).flatMap (·.rounds)).length

/-- None is in front of the first. -/
theorem roundsAhead_zero (bs : List (Block S Cl)) : roundsAhead bs 0 = 0 := by
  simp [roundsAhead]

/-- One sub-protocol more: its rounds more. -/
theorem roundsAhead_succ {bs : List (Block S Cl)} {j : Nat} {b : Block S Cl}
    (h : bs[j]? = some b) : roundsAhead bs (j + 1) = roundsAhead bs j + b.rounds.length := by
  unfold roundsAhead
  rw [List.take_add_one, h]
  simp

/-- A front of a front. -/
theorem take_take_le (bs : List (Block S Cl)) {k b : Nat} (h : k ≤ b) :
    (bs.take b).take k = bs.take k := by
  rw [List.take_take, Nat.min_eq_left h]

/-- The count at a front of the list is the list's, as far as the front goes. -/
theorem roundsAhead_take (bs : List (Block S Cl)) {k b : Nat} (h : k ≤ b) :
    roundsAhead (bs.take b) k = roundsAhead bs k := by
  unfold roundsAhead
  rw [take_take_le bs h]

/-- **THE FOLD, CUT AT THE SUB-PROTOCOL NUMBER j**: one state sj for the fold in front, the
sub-protocol's own step on its own slice of the rounds, and the fold behind. -/
theorem foldCutAt (ft : Nat) (bs : List (Block S Cl)) (j : Nat) (blk : Block S Cl)
    (hj : bs[j]? = some blk) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (out : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft bs s rs cols = .ok out) :
    ∃ (sj sj' : S) (c₀ : List OpenedColumn) (n : Nat),
      foldBlocks ft (bs.take j) s rs cols = .ok (sj, rs.drop (roundsAhead bs j), c₀) ∧
      blk.step ft sj ((rs.drop (roundsAhead bs j)).take blk.rounds.length) c₀ = .ok (sj', n) ∧
      foldBlocks ft (bs.drop (j + 1)) sj' (rs.drop (roundsAhead bs (j + 1))) (c₀.drop n) =
        .ok out := by
  have e : bs = bs.take j ++ blk :: bs.drop (j + 1) := by
    have hlt : j < bs.length := (List.getElem?_eq_some_iff.1 hj).1
    have hb : bs[j] = blk := (List.getElem?_eq_some_iff.1 hj).2
    have hd : bs.drop j = blk :: bs.drop (j + 1) := by rw [List.drop_eq_getElem_cons hlt, hb]
    rw [← hd, List.take_append_drop]
  have h' : foldBlocks ft (bs.take j ++ blk :: bs.drop (j + 1)) s rs cols = .ok out := by
    rw [← e]
    exact h
  obtain ⟨sj, c₀, -, h1, h2⟩ := foldAt S Cl (fun _ _ => True) preTrue ft (bs.take j) _ s rs cols
    out (fun _ _ _ _ _ _ _ => trivial) h'
  obtain ⟨sj', n, -, h3, h4⟩ := foldConsOk' h2
  refine ⟨sj, sj', c₀, n, h1, h3, ?_⟩
  have hR : rs.drop (roundsAhead bs (j + 1)) =
      (rs.drop (roundsAhead bs j)).drop blk.rounds.length := by
    rw [roundsAhead_succ hj, List.drop_drop]
  rw [hR]
  exact h4

/-- The fold over a list with one sub-protocol more behind it, put together. -/
theorem foldBlocks_snoc (ft : Nat) (b : Block S Cl) (pre : List (Block S Cl)) (s₀ s s' : S)
    (rs r : List Fmt.RoundView) (cols c : List OpenedColumn) (k : Nat)
    (h : foldBlocks ft pre s₀ rs cols = .ok (s, r, c))
    (hl : (r.take b.rounds.length).length = b.rounds.length)
    (hs : b.step ft s (r.take b.rounds.length) c = .ok (s', k)) :
    foldBlocks ft (pre ++ [b]) s₀ rs cols = .ok (s', r.drop b.rounds.length, c.drop k) :=
  foldJoin S Cl ft pre [b] s₀ s rs r cols c _ h (foldConsMk hl hs rfl)

/-- The rule's induction. pre: the sub-protocols that the fold has passed. l: those that are left.
-/
theorem foldStepsFrom (ft : Nat) (I : Nat → S → Prop) (s₀ : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) : ∀ (l pre : List (Block S Cl)) (s : S) (c : List OpenedColumn)
      (out : S × List Fmt.RoundView × List OpenedColumn),
    (∀ k b, (pre ++ l)[k]? = some b → ∀ s c t n,
      foldBlocks ft ((pre ++ l).take k) s₀ rs cols =
        .ok (s, rs.drop (roundsAhead (pre ++ l) k), c) →
      ((rs.drop (roundsAhead (pre ++ l) k)).take b.rounds.length).length = b.rounds.length →
      b.step ft s ((rs.drop (roundsAhead (pre ++ l) k)).take b.rounds.length) c = .ok (t, n) →
      I k s → I (k + 1) t) →
    foldBlocks ft pre s₀ rs cols = .ok (s, rs.drop (roundsAhead (pre ++ l) pre.length), c) →
    foldBlocks ft l s (rs.drop (roundsAhead (pre ++ l) pre.length)) c = .ok out →
    I pre.length s → I (pre ++ l).length out.1
  | [], pre, s, c, out, _, _, h, hI => by
    have e : out = (s, _, c) := (Except.ok.inj h).symm
    rw [e, List.append_nil]
    exact hI
  | b :: l, pre, s, c, out, hk, hp, h, hI => by
    obtain ⟨s', k, hl, hs, h'⟩ := foldConsOk' h
    have hb : (pre ++ b :: l)[pre.length]? = some b := by simp
    have ht : (pre ++ b :: l).take pre.length = pre := by simp
    have h1 : I (pre.length + 1) s' :=
      hk pre.length b hb s c s' k (by rw [ht]; exact hp) hl hs hI
    have e : pre ++ b :: l = (pre ++ [b]) ++ l := by simp
    have hp' := foldBlocks_snoc ft b pre s₀ s s' rs _ cols c k hp hl hs
    rw [List.drop_drop, ← roundsAhead_succ hb] at hp' h'
    have q := foldStepsFrom ft I s₀ rs cols l (pre ++ [b]) s' (c.drop k) out
      (by rw [← e]; exact hk) (by rw [← e, List.length_append]; exact hp')
      (by rw [← e, List.length_append]; exact h') (by rw [List.length_append]; exact h1)
    rw [← e] at q
    exact q

/-- **THE RULE, AT ONE LIST OF ROUNDS AND OF COLUMNS**: what each sub-protocol's step carries from
the border in front of it to the border behind it goes from the first state to the last. The step is
asked ON THE SUB-PROTOCOL's OWN SLICE of the rounds, at the columns c that the fold had left, AND
THE FOLD's OWN EQUATION OVER THE SUB-PROTOCOLS IN FRONT IS GIVEN WITH IT, and that the slice is
whole: just what `foldBlocks_snoc` asks: so a law that is asked of the fold can be spent at the
step. -/
theorem foldStepsAt (ft : Nat) (bs : List (Block S Cl)) (I : Nat → S → Prop) (s₀ : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (out : S × List Fmt.RoundView × List OpenedColumn)
    (hk : ∀ k b, bs[k]? = some b → ∀ s c t n,
      foldBlocks ft (bs.take k) s₀ rs cols = .ok (s, rs.drop (roundsAhead bs k), c) →
      ((rs.drop (roundsAhead bs k)).take b.rounds.length).length = b.rounds.length →
      b.step ft s ((rs.drop (roundsAhead bs k)).take b.rounds.length) c = .ok (t, n) →
      I k s → I (k + 1) t)
    (h : foldBlocks ft bs s₀ rs cols = .ok out) (h0 : I 0 s₀) : I bs.length out.1 :=
  foldStepsFrom ft I s₀ rs cols bs [] s₀ cols out hk
    (by rw [List.nil_append, List.length_nil, roundsAhead_zero]; rfl)
    (by rw [List.nil_append, List.length_nil, roundsAhead_zero]; exact h) h0

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.roundsAhead_zero
#print axioms VerifiableInference.Desc.K13.Honest.roundsAhead_succ
#print axioms VerifiableInference.Desc.K13.Honest.take_take_le
#print axioms VerifiableInference.Desc.K13.Honest.roundsAhead_take
#print axioms VerifiableInference.Desc.K13.Honest.foldCutAt
#print axioms VerifiableInference.Desc.K13.Honest.foldBlocks_snoc
#print axioms VerifiableInference.Desc.K13.Honest.foldStepsFrom
#print axioms VerifiableInference.Desc.K13.Honest.foldStepsAt
