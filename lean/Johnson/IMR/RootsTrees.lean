-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RootsTrees.lean: Johnson/IMR/RootsSeat.lean's roots_at_cut_paid
IN THE LETTERS OF Johnson/Desc/First/K8/PlanNames.lean (treesFrom, rootsOfRounds, roundsOfBlocks):
for the four equations on counts of roots that planGives_of_ranges asks
(Johnson/Desc/First/K8/LawWalk.lean: front, behind, reads, draw).

  decl_take: the declared rounds of a list of blocks, cut behind the rounds of its first i blocks,
      are these blocks' rounds.
  treesFrom_eq: treesFrom F i = rootsOf (declOf (F.first.blocksInOrder.take i)). treesFrom_succ:
      F.first.blocksInOrder[i]? = some b → treesFrom F (i + 1) = treesFrom F i + rootsOfRounds b.rounds.
  roots_at_cut_trees: **O · k ≤ (frontOf c).length · the tests on the plan of c.blocksInOrder.take k ·
      s.roots = 0 · foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r ⇒ r.1.roots = treesFrom F k.**
  four_counts: **the four equations**, at the records r₀, r₁, r₃, r₄ of one fold at the cuts iM, iM
      + 1, iR, iR + 1: r₀.1.roots = treesFrom F iM ∧ r₁.1.roots = r₀.1.roots + rootsOfRounds
      bM.rounds ∧ r₁.1.roots = treesFrom F iR ∧ r₄.1.roots = r₁.1.roots + rootsOfRounds bR.rounds.
PREMISES, AND WHO CAN PAY. s.roots = 0: at ProofFile.startS Z p start_empty (Johnson/IMR/BookSeat.lean) ·
hq : r₃.1.roots = r₁.1.roots (between the two entries the count stays): the walk mid_stretch
(Johnson/IMR/ListsAtDraw.lean) · the tests on the plan: F.planOk · the four folds' returns: the
caller's: prefixes of one fold.
OBJECT · USER · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription o's value. User:
namedAt_of_walk, beside walkGives_at (a := the count at cut iM, b := at cut iM + 1,
b' := at cut iR + 1). Letters: none.



Compiled with the whole library.
Limits. Book-keeping. Nothing on soundness.
-/
import Johnson.IMR.RootsSeat
import Johnson.Desc.First.K8.PlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (rootsOfRounds roundsOfBlocks treesFrom)
open Johnson.G.OfPlan (rootsOf)
open H2K.First (declOf)

/-- The declared rounds of a list of blocks, cut behind the rounds of its first i blocks, are these
blocks' rounds. -/
theorem decl_take {T Cl : Type} (l : List (Block T Cl)) (i : Nat) :
    (l.flatMap (·.rounds)).take (roundsOfBlocks (l.take i)) = (l.take i).flatMap (·.rounds) := by
  have e : l.flatMap (·.rounds) =
      (l.take i).flatMap (·.rounds) ++ (l.drop i).flatMap (·.rounds) := by
    rw [← List.flatMap_append, List.take_append_drop]
  rw [e]
  refine List.take_left' ?_
  rw [List.length_flatMap]
  rfl

/-- **treesFrom (Johnson/Desc/First/K8/PlanNames.lean), in the letters rootsOf and declOf.** -/
theorem treesFrom_eq {Xi : Type} (F : FileDescription Xi) (i : Nat) :
    treesFrom F i = rootsOf (declOf (F.first.blocksInOrder.take i)) := by
  unfold treesFrom
  rw [show F.roundsDeclaredByBlocks.1 = F.first.blocksInOrder.flatMap (·.rounds) from rfl, decl_take]
  rfl

/-- One entry more. -/
theorem treesFrom_succ {Xi : Type} (F : FileDescription Xi) {i : Nat} {b : Block F.S₁ F.Cl}
    (h : F.first.blocksInOrder[i]? = some b) :
    treesFrom F (i + 1) = treesFrom F i + rootsOfRounds b.rounds := by
  rw [treesFrom_eq, treesFrom_eq, List.take_add_one, h]
  show rootsOf (declOf (F.first.blocksInOrder.take i ++ [b])) = _
  unfold declOf
  rw [List.flatMap_append, H2K.First.rootsOf_append]
  show _ + rootsOf (b.rounds ++ []) = _
  rw [List.append_nil]
  rfl

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE RECORD AT CUT k COUNTS treesFrom F k ROOTS**, where the fold starts at a record that
counts none. -/
theorem roots_at_cut_trees (O : IM.Open o pol lay KL F Z Bs base c A B) (k : Nat)
    (hk : k ≤ (Meaning.K2.frontOf c).length) (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (ft : Nat)
    (s : S) (h0 : s.roots = 0) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (r : S × List Fmt.RoundView × List OpenedColumn) (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) :
    r.1.roots = treesFrom F k := by
  have e := roots_at_cut_paid O k hk hp ft s rs cols r h
  rw [h0, Nat.zero_add] at e
  rw [e, treesFrom_eq]
  have eF := O.desc
  subst eF
  rfl

/-- **THE FOUR EQUATIONS ON COUNTS OF ROOTS** (K8/LawWalk.lean: planGives_of_ranges' front,
behind, reads, draw), at the records of one fold at four cuts: in front of entry iM, behind it, in
front of entry iR, behind it. hq: between the two entries the count stays (the walk's). -/
theorem four_counts (O : IM.Open o pol lay KL F Z Bs base c A B) (iM iR : Nat)
    (hMR : iM + 1 ≤ iR) (hk : iR + 1 ≤ (Meaning.K2.frontOf c).length)
    (hp : ∀ b ∈ c.blocksInOrder.take (iR + 1), b.planOk = true) (ft : Nat) (s : S) (h0 : s.roots = 0)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) {r₀ r₁ r₃ r₄ : S × List Fmt.RoundView × List OpenedColumn}
    (f₀ : foldBlocks ft (c.blocksInOrder.take iM) s rs cols = .ok r₀)
    (f₁ : foldBlocks ft (c.blocksInOrder.take (iM + 1)) s rs cols = .ok r₁)
    (f₃ : foldBlocks ft (c.blocksInOrder.take iR) s rs cols = .ok r₃)
    (f₄ : foldBlocks ft (c.blocksInOrder.take (iR + 1)) s rs cols = .ok r₄)
    (hq : r₃.1.roots = r₁.1.roots) {bM bR : Block F.S₁ F.Cl}
    (eM : F.first.blocksInOrder[iM]? = some bM) (eR : F.first.blocksInOrder[iR]? = some bR) :
    r₀.1.roots = treesFrom F iM ∧ r₁.1.roots = r₀.1.roots + rootsOfRounds bM.rounds ∧
      r₁.1.roots = treesFrom F iR ∧ r₄.1.roots = r₁.1.roots + rootsOfRounds bR.rounds := by
  have sub : ∀ k, k ≤ iR + 1 → ∀ b ∈ c.blocksInOrder.take k, b.planOk = true := fun k hk' b hb =>
    hp b (List.take_subset_take_left _ hk' hb)
  have t₀ := roots_at_cut_trees O iM (by omega) (sub iM (by omega)) ft s h0 rs cols r₀ f₀
  have t₁ := roots_at_cut_trees O (iM + 1) (by omega) (sub _ (by omega)) ft s h0 rs cols r₁ f₁
  have t₃ := roots_at_cut_trees O iR (by omega) (sub iR (by omega)) ft s h0 rs cols r₃ f₃
  have t₄ := roots_at_cut_trees O (iR + 1) hk hp ft s h0 rs cols r₄ f₄
  refine ⟨t₀, ?_, hq ▸ t₃, ?_⟩
  · rw [t₁, t₀, treesFrom_succ F eM]
  · rw [t₄, ← hq, t₃, treesFrom_succ F eR]

end

#print axioms four_counts
#print axioms treesFrom_eq
#print axioms treesFrom_succ
#print axioms roots_at_cut_trees

end Meaning.Carry
