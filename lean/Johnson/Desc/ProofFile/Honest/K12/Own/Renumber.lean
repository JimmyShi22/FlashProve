-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/Renumber.lean: A PROXIMITY TEST WHOSE FIRST FOLD SENDS ITS OWN
MASK: ITS PLACE, RENUMBERED, AND WHAT IS THE SAME AT BOTH PLACES. Two definitions; statements and
proofs. All at a variable place.

Why. The library's laws on a proximity test's later stages (`BodyInv` at `PlanAll`,
Johnson/Prover/Link/BodyInv.lean, BodyCloseB.lean) ask that the first fold's mask has come earlier
(`ownMask = false`, in `PlanFrom`, FormStepPlan.lean) and count the test's own tree behind stage j
as `free + j` (`StepPlan.label`, `FormInv.roots`, `SwitchIn.roots`, `listsOf_later`). Where the
first fold sends its own mask that tree takes the number `free`, and the later ones are `free + 1 +
j`. These laws are general in the place and take the rounds still to be dealt as a letter of their
own. So they can be called at the place `renumP p`, from the first switch on, at the rounds of p.
This file has the place, and what is the same at `renumP p` and at p.

  `renum`, `renumP`   the numbers and the place: "the mask has come earlier"; one tree more in front
  `map_zipIdx_shift`, `sent_renum`, `lists_drop`   behind the first list the two plans lay the same
                 lists of trees
  `lists_own`   the one tree that the renumbered numbers leave out, by name
  `switch_renum`, `fold_renum`, `batBehind_renum`, `stageAt_renum`   four parts of the running text:
                 the same, by `rfl`
  `basePar_renum`, `base_renum`   the base case's numbers; its part, where there are two stages
  `t1At_renum`, `aRec2_renum`, `t3At_renum`, `firstYes_renum`   the first stage's states, and what
                 the first stage delivers (Johnson/Desc/K12/Honest/FirstYes.lean)

Limits.
- AT `renumP p` THE FIRST FOLD's OWN MASK TREE (NUMBER `free`) IS LEFT OUT OF THE LISTS
  (`lists_own`). Unless `first` itself names it, it stands in no list, and it is declared and opened
  by no round that the plan's maker lays at these numbers (`roundsOfNums`,
  Johnson/Desc/K12/TestEntries.lean); the number `free + 1` takes it as one that has come in front.
  SO NOTHING THAT IS DRAWN AT `renumP p` MAY BE QUOTED OF STAGE 0, OF "ALL THE TEST's TREES", OR OF
  ANY COUNT OR BUDGET OVER THEM. THIS FILE's STATEMENTS ARE HELPERS: they conclude at the renumbered
  place: equations between the two places, and one that carries a fact over from p
  (`firstYes_renum`). `renumP p` is to stand in no top: not in the sentence at a member, not in what
  is told, not in what a count could lean on; and in no sentence on hiding.
- `renumP p` IS A TERM OF COMPARISON. No file that we know of has a place with these numbers; the
  rounds that the plan's maker lays at them are not those of p (the first fold's declared entry
  differs), and the front's part is not the same at both (it tests `free` against the roots).
- NOTHING HERE SAYS THAT A PREMISE OF ANY LAW HOLDS AT `renumP p`.
- `base_renum` ASKS TWO STAGES: the part's own test on the plan reads "the test sends a tree" (`1 ≤
  sent.length`, Johnson/Desc/K12/JoinGuarded.lean): at p the mask's tree is one; at `renumP p` there is
  one only where a second stage is.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.K12.Honest.FirstYes
import Johnson.Desc.K12.OpenLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open H2U (TestNums)

/-- The numbers of `renumP`. -/
def renum (N : TestNums) : TestNums := { N with ownMask := false, free := N.free + 1 }

/-- **The renumbered place**: the numbers of a test whose first fold sends its own mask, renumbered
so that the laws for "no own mask" fit from the first switch on: the numbers of p with the first
fold's own mask tree left out of the lists and the later trees renumbered: NOT a test without a
mask; laws at this place speak of the stages from the first switch on. The tree that is left out is
taken as one that has come in front of the test (`free + 1`). No file's plan that we know of has
these numbers. -/
def renumP (p : P12) : P12 := { p with nums := renum p.nums }

/-! ## 1 The lists of trees behind the first -/

theorem map_zipIdx_shift {α β : Type} (g : α → ℕ → β) (l : List α) (n : ℕ) :
    (l.zipIdx (n + 1)).map (fun t => g t.1 t.2) = (l.zipIdx n).map (fun t => g t.1 (t.2 + 1)) := by
  induction l generalizing n with
  | nil => rfl
  | cons a l ih =>
    simp only [List.zipIdx_cons, List.map_cons]
    rw [ih]

/-- What the test sends: at N the mask's tree, then what it sends at the renumbered numbers. -/
theorem sent_renum (N : TestNums) (ho : N.ownMask = true) (s : Fmt.M1.Stage)
    (r : List Fmt.M1.Stage) (hs : N.stages = s :: r) :
    N.sent = (s.Z.a, 3 * 2 ^ s.h) :: (renum N).sent := by
  simp [TestNums.sent, renum, ho, hs]

/-- **Behind the first list the two plans lay the same lists of trees.** -/
theorem lists_drop (N : TestNums) (ho : N.ownMask = true) (s : Fmt.M1.Stage)
    (r : List Fmt.M1.Stage) (hs : N.stages = s :: r) :
    (K12.listsOf (renum N)).drop 1 = (K12.listsOf N).drop 1 := by
  have e := sent_renum N ho s r hs
  have h0 : (renum N).ownMask = false := rfl
  simp only [K12.listsOf, List.drop_succ_cons, List.drop_zero, h0, ho, if_true, if_false,
    Bool.false_eq_true]
  rw [e, List.zipIdx_cons, List.map_cons, List.drop_succ_cons, List.drop_zero]
  congr 1
  have k := map_zipIdx_shift (fun (a : ℕ × ℕ) i => N.own a.1 a.2 (N.free + i)) (renum N).sent 0
  rw [show (0 : ℕ) + 1 = 1 from rfl] at k
  rw [k]
  apply List.map_congr_left
  intro t _
  show (renum N).own t.1.1 t.1.2 (N.free + 1 + t.2) = N.own t.1.1 t.1.2 (N.free + (t.2 + 1))
  rw [Nat.add_assoc, Nat.add_comm 1]
  rfl

/-- **The one tree that the renumbered numbers leave out, by name**: the mask's own tree, number
`free`. At N the first list is the first trees and then that tree; at `renum N` it is the first
trees alone; behind the first list the two are one (`lists_drop`). -/
theorem lists_own (N : TestNums) (ho : N.ownMask = true) (s : Fmt.M1.Stage)
    (r : List Fmt.M1.Stage) (hs : N.stages = s :: r) :
    K12.listsOf N =
        (N.first ++ [N.own s.Z.a (3 * 2 ^ s.h) N.free]) :: (K12.listsOf (renum N)).drop 1 ∧
      K12.listsOf (renum N) = N.first :: (K12.listsOf (renum N)).drop 1 := by
  have e := sent_renum N ho s r hs
  have h0 : (renum N).ownMask = false := rfl
  constructor
  · rw [lists_drop N ho s r hs]
    simp only [K12.listsOf, List.drop_succ_cons, List.drop_zero, ho, if_true]
    rw [e, List.zipIdx_cons, List.map_cons, List.take_succ_cons, List.take_zero]
    rfl
  · simp only [K12.listsOf, List.drop_succ_cons, List.drop_zero, h0, if_false,
      Bool.false_eq_true, List.append_nil]
    rfl

/-! ## 2 The parts of the running text -/

theorem switch_renum (p : P12) (j : ℕ) (cur next : Fmt.M1.Stage) (last : Bool)
    (cut : List Fmt.DeclaredRound) :
    guardedProximityTestParts.switch (renumP p) j cur next last cut = guardedProximityTestParts.switch p j cur next last cut := rfl

theorem fold_renum (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) :
    guardedProximityTestParts.fold (renumP p) j cur cut = guardedProximityTestParts.fold p j cur cut := rfl

theorem batBehind_renum (p : P12) : guardedProximityTestParts.batBehind (renumP p) = guardedProximityTestParts.batBehind p := rfl

theorem stageAt_renum (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) :
    stageAt (renumP p) j cur = stageAt p j cur := rfl

theorem basePar_renum (p : P12) (cur : Fmt.M1.Stage) (ho : p.nums.ownMask = true)
    (a : Fmt.M1.Stage) (r : List Fmt.M1.Stage) (hs : p.nums.stages = a :: r) :
    basePar (renumP p) cur = basePar p cur := by
  simp [basePar, renumP, renum, TestNums.sent, ho, hs]

/-- Two stages are asked: the part's own test on the plan reads "the test sends a tree"
(`1 ≤ sent.length`): at p the mask's tree is one; at the renumbered place there is one only where a
second stage is. -/
theorem base_renum (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound)
    (ho : p.nums.ownMask = true) (a b : Fmt.M1.Stage) (r : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: b :: r) :
    guardedProximityTestParts.base (renumP p) j cur cut = guardedProximityTestParts.base p j cur cut := by
  have e := basePar_renum p cur ho a (b :: r) hs
  have l1 : decide (1 ≤ (renumP p).nums.sent.length) = decide (1 ≤ p.nums.sent.length) := by
    simp [renumP, renum, TestNums.sent, ho, hs]
  show ranged cut (baseJ5 (renumP p) j cur cut) = ranged cut (baseJ5 p j cur cut)
  congr 1
  unfold baseJ5
  rw [e, l1]
  rfl

/-! ## 3 The first stage's states -/

theorem t1At_renum (p : P12) (K : BCoins) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12)
    (P : PS) (D : ℕ → Fmt.Drawn) :
    t1At (renumP p) K j cur l o t P D = t1At p K j cur l o t P D := rfl

theorem aRec2_renum (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) :
    aRec2 (renumP p) K rest j cur next l o t P trees D =
      aRec2 p K rest j cur next l o t P trees D := rfl

theorem t3At_renum (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) :
    t3At (renumP p) K rest j cur next l o t P trees D =
      t3At p K rest j cur next l o t P trees D := rfl

/-- **What the first stage delivers at p it delivers at the renumbered place.** -/
theorem firstYes_renum (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ)
    (cur next : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree)
    (D : ℕ → Fmt.Drawn) (Y : FirstYes p K rest j cur next l o t P trees D) :
    FirstYes (renumP p) K rest j cur next l o t P trees D :=
  ⟨Y.fold, Y.switch, Y.behind, Y.came, Y.nF, Y.oF, Y.nS, Y.oS⟩

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.renum
#print axioms ProofFile.Honest.K12.Own.renumP
#print axioms ProofFile.Honest.K12.Own.map_zipIdx_shift
#print axioms ProofFile.Honest.K12.Own.sent_renum
#print axioms ProofFile.Honest.K12.Own.lists_drop
#print axioms ProofFile.Honest.K12.Own.lists_own
#print axioms ProofFile.Honest.K12.Own.switch_renum
#print axioms ProofFile.Honest.K12.Own.fold_renum
#print axioms ProofFile.Honest.K12.Own.batBehind_renum
#print axioms ProofFile.Honest.K12.Own.stageAt_renum
#print axioms ProofFile.Honest.K12.Own.basePar_renum
#print axioms ProofFile.Honest.K12.Own.base_renum
#print axioms ProofFile.Honest.K12.Own.t1At_renum
#print axioms ProofFile.Honest.K12.Own.aRec2_renum
#print axioms ProofFile.Honest.K12.Own.t3At_renum
#print axioms ProofFile.Honest.K12.Own.firstYes_renum
