-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Small/FreshNoCoin.lean: the condition `fresh` of `Good`
(Honest/Side.lean) holds at every part for which the book of coins has no coin, at every book that
passes its own tests. Lemmas with their proofs; no definition. No kind of sub-protocol is named.

What `fresh` asks. It is a condition on a part as the OWNER of coins: the blocks of its own coins
that another part spends are uniform and independent of what the owner shows and of its other coins
that are passed on. A part that only borrows coins owns none, so the condition should ask nothing of
it. By its text it still asks one thing: that every entry of the book by which another part spends
of this part's coins names a block of no coin that starts at 0. This file shows that the book's own
fourth test ("an entry's run is not within its owner's count", `ProverCoinCounts.clauses`, Honest/Frame.lean)
gives that, wherever the book's tables have no coin for the part.

Why it is needed. The test `noneSpent` (Honest/Small/Field.lean: no spending entry names the part as
its owner) also gives `fresh` (`fresh_of_nil`, Honest/Law/ToyLaw.lean), but it does not follow from
the book's tests: an entry of no coin passes them. So a statement that takes `noneSpent` as a
hypothesis leaves something to be evaluated at the book. The statements here take instead that the
book passes its tests and that its tables have no coin for the part.

  `due_zero`, `cs_zero_one`, `csAll_zero_one`   coins at the count zero, and blocks that all have
     the count zero, have one value
  `fresh_of_zero`   the two distributions of `fresh` are the same where every spent block starts at
     0 and has no coin
  `spentBy_zero`   at a book that passes its tests, every block that is spent of a part without a
     coin is such a block
  `freshMember_of_no_coin`   so `fresh` holds at that part (`FreshMember`: the condition's own text
     at one member). The count is read in the book's three tables joined; how many coins the part
     itself takes is not read
  `freshMember_in_chain`   the same with the count read in the table of the part's own chain
  `freshMember_of_lent`   the same for a part that takes no coin, where `lendPart` returns once:
     that return gives the count, and nothing else

Limits.
  * These statements say nothing about the coins that such a part borrows. That a borrowed block is
    still uniform when the part spends it is the condition `fresh` at the block's owner, at the
    borrower's address; it is not shown here.
  * They do not serve a part that has coins of its own, whether or not another part spends of them.
  * Hypotheses of all three: the book passes its tests at some description F. Of the first two: the
    count is zero. Of the last two: F passes the test `placesOk`, and the part's place is in the
    chain named. `lendPart` does not ask the book's tests, so they stay a hypothesis of the third.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookLends
import Johnson.Desc.ProofFile.Honest.Small.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open Prob
open VerifiableInference.Desc (FileDescription Place)

/-! ## 1 Blocks of no coin -/

/-- A count whose two numbers are 0 is the count zero. -/
theorem due_zero (n : Due) (hf : n.f = 0) (he : n.e = 0) : n = ⟨0, 0⟩ := by
  obtain ⟨a, b⟩ := n
  have ha : a = 0 := hf
  have hb : b = 0 := he
  rw [ha, hb]

/-- Coins at the count zero have one value. -/
theorem cs_zero_one {n : Due} (hn : n = ⟨0, 0⟩) (x y : Cs n) : x = y := by
  subst hn
  obtain ⟨xf, xe⟩ := x
  obtain ⟨yf, ye⟩ := y
  have h1 : xf = yf := funext fun i => i.elim0
  have h2 : xe = ye := funext fun i => i.elim0
  rw [h1, h2]

/-- Blocks that all have the count zero have one value. -/
theorem csAll_zero_one : ∀ es : List Ahead, (∀ e ∈ es, e.count = ⟨0, 0⟩) →
    ∀ x y : CsAll (es.map Ahead.named), x = y
  | [], _, x, y => by
    have key : ∀ a b : Unit, a = b := fun _ _ => rfl
    exact key x y
  | e :: es, h, x, y => by
    have key : ∀ a b : Cs e.count × CsAll (es.map Ahead.named), a = b := fun a b =>
      Prod.ext (cs_zero_one (h e (List.mem_cons.2 (Or.inl rfl))) a.1 b.1)
        (csAll_zero_one es (fun e' he' => h e' (List.mem_cons_of_mem _ he')) a.2 b.2)
    exact key x y

/-- **Where every spent block starts at 0 and has no coin, the two distributions of `Good.fresh` are
the same.** `S`: what the owner shows. `K`: its other coins that are passed on. At every count d of
the owner's coins. -/
theorem fresh_of_zero {γ δ : Type} {d : Due} (es : List Ahead)
    (hz : ∀ e ∈ es, e.start = ⟨0, 0⟩ ∧ e.count = ⟨0, 0⟩) (S : Cs d → γ) (K : Cs d → δ) :
    (unif (Cs d)).map (fun c => (cutAll c es, S c, K c)) =
      (unif (CsAll (es.map Ahead.named) × Cs d)).map fun a => (some a.1, S a.2, K a.2) := by
  have hc : ∀ (c : Cs d) (x : CsAll (es.map Ahead.named)), cutAll c es = some x := by
    intro c x
    obtain ⟨y, hy⟩ := cutAll_some c es fun e he => by
      rw [(hz e he).1, (hz e he).2]
      exact ⟨Nat.zero_le _, Nat.zero_le _⟩
    rw [hy, csAll_zero_one es (fun e he => (hz e he).2) y x]
  have hf : (fun a : CsAll (es.map Ahead.named) × Cs d => (some a.1, S a.2, K a.2)) =
      (fun c : Cs d => (cutAll c es, S c, K c)) ∘ Prod.snd := by
    funext a
    show (some a.1, S a.2, K a.2) = (cutAll a.2 es, S a.2, K a.2)
    rw [hc a.2 a.1]
  have h : (unif (CsAll (es.map Ahead.named) × Cs d)).map
        ((fun c : Cs d => (cutAll c es, S c, K c)) ∘ Prod.snd) =
      (unif (Cs d)).map fun c => (cutAll c es, S c, K c) := by
    rw [← PMF.map_comp, map_snd_unif]
  rw [hf]
  exact h.symm

/-! ## 2 At a book that passes its tests -/

variable {Xi S Cl V W X Pb : Type}

/-- **At a book that passes its tests: every block that is spent of a part for which the three
tables have no coin starts at 0 and has no coin.** By the book's fourth test (`ProverCoinCounts.within`,
Honest/Law/Rule/Tests.lean). -/
theorem spentBy_zero {F : FileDescription Xi} {Bk : ProverCoinCounts} (hw : Bk.word F = none) {o : Addr}
    (hd : dueAt (Bk.first ++ Bk.shared ++ Bk.second) o = ⟨0, 0⟩) (p : Addr) :
    ∀ e ∈ Bk.spentBy o p, e.start = ⟨0, 0⟩ ∧ e.count = ⟨0, 0⟩ := by
  intro e he
  unfold ProverCoinCounts.spentBy at he
  obtain ⟨hm, hq⟩ := List.mem_filter.1 he
  simp only [Bool.and_eq_true, beq_iff_eq] at hq
  have hin := ProverCoinCounts.within hw e hm
  rw [hq.1.1, hd] at hin
  have h1 : e.start.f + e.count.f ≤ 0 := hin.1
  have h2 : e.start.e + e.count.e ≤ 0 := hin.2
  exact ⟨due_zero _ (by omega) (by omega), due_zero _ (by omega) (by omega)⟩

/-- **The condition `fresh` at a part for which the book has no coin**, at every book that passes
its tests at some description; at every face, order of places and `bud`. It says nothing about the
coins that the part borrows: see the head. -/
theorem freshMember_of_no_coin {F : FileDescription Xi} {Bk : ProverCoinCounts} (hw : Bk.word F = none)
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb)
    (hd : dueAt (Bk.first ++ Bk.shared ++ Bk.second) ⟨σ.block.place, u.number⟩ = ⟨0, 0⟩) :
    FreshMember φ σ Bk ord bud u :=
  fun p sp ca m ds asks _ _ _ =>
    fresh_of_zero _ (spentBy_zero hw hd p) (fun c => σ.shows φ u (c, sp, ca) m ds asks)
      fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p)

/-- The same with the count read in the table of the part's own chain. `ch`: the number, from 0, of
a chain in which the part's place is. -/
theorem freshMember_in_chain {F : FileDescription Xi} {Bk : ProverCoinCounts} (hw : Bk.word F = none)
    (hp : F.placesOk = true) {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2)
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (ha : σ.block.place ∈ placesAt F ch)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (u : Member V W X Pb) (hd : dueAt (Bk.rowsOf ch) ⟨σ.block.place, u.number⟩ = ⟨0, 0⟩) :
    FreshMember φ σ Bk ord bud u :=
  freshMember_of_no_coin hw φ σ ord bud u
    ((ProverCoinCounts.dueInChain hw hp (a := ⟨σ.block.place, u.number⟩) hch ha).1.trans hd)

/-- **The same for a part that takes no coin of its own, where the book lends it its coins** at one
run's coins: `lendPart` returns only where the part takes as many coins as the book has for it. -/
theorem freshMember_of_lent {F : FileDescription Xi} {Bk : ProverCoinCounts} (hw : Bk.word F = none)
    (hp : F.placesOk = true) {ch : Nat} (hch : ch = 0 ∨ ch = 1 ∨ ch = 2)
    (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (ha : σ.block.place ∈ placesAt F ch)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (u : Member V W X Pb) (ht : u.part.takes = ⟨0, 0⟩)
    {look : Addr → (d : Due) × Cs d} {c : u.part.Coins}
    (hl : lendPart Bk (Bk.rowsOf ch) look ⟨σ.block.place, u.number⟩ u.part = .ok c) :
    FreshMember φ σ Bk ord bud u :=
  freshMember_in_chain hw hp hch φ σ ha ord bud u ((lendPart_ok hl).1.symm.trans ht)

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.due_zero
#print axioms ProofFile.Honest.Small.cs_zero_one
#print axioms ProofFile.Honest.Small.csAll_zero_one
#print axioms ProofFile.Honest.Small.fresh_of_zero
#print axioms ProofFile.Honest.Small.spentBy_zero
#print axioms ProofFile.Honest.Small.freshMember_of_no_coin
#print axioms ProofFile.Honest.Small.freshMember_in_chain
#print axioms ProofFile.Honest.Small.freshMember_of_lent
