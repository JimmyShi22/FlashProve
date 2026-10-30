-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.FoldKeeps
import Johnson.G.RoundsOfPlan
/-
Johnson/Desc/K12/Law/RootsFold.lean: THE RULE THAT JOINS «MY BLOCK's YES ADDS THE ROOTS THAT ITS OWN ROUNDS DECLARE», BLOCK BY BLOCK, ALONG A CHAIN's FOLD. General in the state S and in the reader «roots : S → ℕ». For the row book_numbers_first_chain's second law. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  RootsStep roots b    the sentence of one block: its test on the plan · a yes of its decision from s to s' ⇒ roots s' = roots s + rootsOf b.rounds
  rootsOf_append       rootsOf over two lists in a row
  declOf bs            the declared rounds of a list of blocks, in a row
  foldBlocks_roots     every block of the list has the sentence and passes its test on the plan · a yes of foldBlocks over the list from s ⇒ the record behind counts roots s + rootsOf (declOf bs)
  chainAt_roots        the same of a chain's decision
  rootsStep_quiet      a block whose rounds declare no root and whose yes leaves the count has the sentence
Neighbours in the library, none of which says this: foldBlocks_keeps | chainAt_keeps (Johnson/Desc/FoldKeeps.lean: ONE relation for all blocks: what a block adds cannot hang on the block there) · foldl_roots (Johnson/Desc/BlockSlotProofs.lean; Johnson/Desc/Sound/ReadsOfData.lean) · rootsIn_decl (Johnson/Desc/Sound/ToldCount.lean): on the plan's and the view's side alone.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's end.
-/
set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc
open Johnson.G.OfPlan (rootsOf)

variable {S Cl : Type}

/-- The sentence of one block. -/
def RootsStep (roots : S → Nat) (b : Block S Cl) : Prop :=
  b.planOk = true → ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    b.decide s rs gs = .ok s' → roots s' = roots s + rootsOf b.rounds

theorem rootsOf_append (a b : List Fmt.DeclaredRound) : rootsOf (a ++ b) = rootsOf a + rootsOf b := by
  unfold rootsOf
  rw [List.map_append, List.sum_append]

/-- The declared rounds of a list of blocks, in a row. -/
def declOf (bs : List (Block S Cl)) : List Fmt.DeclaredRound := bs.flatMap (·.rounds)


theorem foldBlocks_roots (roots : S → Nat) (ft : Nat) : ∀ (bs : List (Block S Cl)),
    (∀ b ∈ bs, RootsStep roots b) → (∀ b ∈ bs, b.planOk = true) →
    ∀ (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : S × List Fmt.RoundView × List OpenedColumn),
      foldBlocks ft bs s rs cols = .ok r → roots r.1 = roots s + rootsOf (declOf bs) := by
  intro bs
  induction bs with
  | nil =>
    intro _ _ s rs cols r h
    simp only [foldBlocks, Except.ok.injEq] at h
    subst h
    rfl
  | cons b l ih =>
    intro hb hp s rs cols r h
    simp only [foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s' k hs
        obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s s' _ cols k hs
        have e1 := hb b List.mem_cons_self (hp b List.mem_cons_self) _ _ _ _ hd
        have e2 := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
          (fun x hx => hp x (List.mem_cons_of_mem _ hx)) _ _ _ _ h
        have e3 : declOf (b :: l) = b.rounds ++ declOf l := rfl
        rw [e2, e1, e3, rootsOf_append, Nat.add_assoc]

/-- The same of a chain's decision. -/
theorem chainAt_roots (roots : S → Nat) (name : String) (ft : Nat) (bs : List (Block S Cl))
    (hb : ∀ b ∈ bs, RootsStep roots b) (hp : ∀ b ∈ bs, b.planOk = true) (s s' : S) (v : Fmt.View)
    (h : chainAt name ft bs s v = .ok s') : roots s' = roots s + rootsOf (declOf bs) :=
  foldBlocks_roots roots ft bs hb hp s _ _ _ (Keeps.chainAt_fold name ft bs s s' v h)

/-- A block whose rounds declare no root and whose yes leaves the count. -/
theorem rootsStep_quiet (roots : S → Nat) (b : Block S Cl) (h0 : rootsOf b.rounds = 0)
    (hl : ∀ (s s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      b.decide s rs gs = .ok s' → roots s' = roots s) : RootsStep roots b :=
  fun _ s s' rs gs h => by rw [hl s s' rs gs h, h0, Nat.add_zero]

end H2K.First

#print axioms H2K.First.foldBlocks_roots
#print axioms H2K.First.chainAt_roots
#print axioms H2K.First.rootsStep_quiet
