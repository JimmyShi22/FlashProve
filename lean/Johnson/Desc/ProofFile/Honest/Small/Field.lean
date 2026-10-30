-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Field.lean defines `ExactMemberAt` and `FreshMember`, which
are the two fields `exact` and `fresh` of `Good` (Honest/Side.lean) at one member of a row, each
under one name, and proves, conditional on a term of `Good`, that the two names are the two fields.
It defines `ExactMember`, which is the field `exact` without its hypothesis on the opened columns,
and proves how the two stand to each other. It also defines `statedOf`, a reader of declared rounds,
of which the premises of this folder's theorems on parts are made, and two tests on the book of
coins that can be evaluated, for callers. It is not a theorem on any part, and it asserts nothing of
any side.

  1  `ExactMemberAt`, `FreshMember`: the fields' own texts behind "∀ u ∈ σ.members,", with u as the
     last argument: copied from the fields `exact` and `fresh` in Honest/Side.lean.
     `ExactMember`: the text of `ExactMemberAt` without the line
     "m.opened = front.opened (readsBefore pre front) →", and so without `pre`. It is not the
     field's text
  2  `exactAt_of_exact`: `ExactMember` gives `ExactMemberAt`, at every `pre`.
     `exactAt_iff_exact`: `ExactMemberAt` at On is `ExactMember` at "On and that line".
     `members_of_good`, `good_of_membersAt`: `ExactMemberAt` and `FreshMember` are the two fields:
     from `Good`, and to it. They compile only if the texts are the fields', up to unfolding.
     `good_of_members`: to `Good` from `ExactMember` and `FreshMember`. Conditional: the last three
     each take a term of `Good`
  3  `statedOf`, `roots_of_shaped`: what declared rounds state of the prover's messages; at a block
     that passes `Block.shaped` a round without an oracle message counts no root
  4  `lendsNone`, `noneSpent`, `noneSpent_of_lendsNone`: no entry of the book names a part as its
     owner; none that spends does; the first gives the second. What they give:
     Honest/Small/Book.lean

Terms, as the frame defines them. The frame is the files directly under Honest/ (Frame.lean,
Side.lean, Sum.lean, Rule.lean, ForKinds.lean among them) and those under Honest/Law/; the library
is the rest of the tree outside Honest/. A part (`Part`) is what the prover does in a stretch of a
sub-protocol's rounds. A side (`Side`) is a sub-protocol with its row: the list of its parts, each
with its simulator. A member (`Member`) is one part of the row with its number, its own declared
rounds and its simulator. A face (`Face`) says how a chain's parts are handed their input: which
part of it is public, and what a stop of the second sort may read. Coins (`Cs`) are field elements
that a part or a simulator is handed. The book (`ProverCoinCounts`) is public data: how many coins of its own
each part has, and its entries (`Ahead`): each is a run of coins: a stretch of one part's coins, its
owner's, that one other part is handed too, to spend or to carry; and the cut: how many rounds each
part of a place's row has. A run of the protocol is another thing: one play of a chain's rounds; the
fold is `play`, which plays them round by round. The one symbol is `none`, which `Side.shows` gives
where a part stops or is at fault. A stop is one of a part's two tests on challenges at which it
does not go on (`Part.bad`; `Part.hid`, the second sort, which may read the input too). A part is at
fault where its move refuses, or says a message of another shape than its round states. A round's
entry (`DeclaredRound.entry`) is its line of the plan: another thing than an entry of the book. A
description is a `FileDescription` (Johnson/Desc/Block.lean). A view is what a verifier is shown of a
chain: each round's items in the clear and its challenge, and the columns that are read; no root.
The plan's test is `FileDescription.planOkCore` (Johnson/Desc/Block.lean). A state (`Mid`, the letter m) is
what a chain's run holds between two rounds: the prover's state, and what a part may read of the run
so far. Its field `opened` is a list of opened columns, or `none` where no columns are handed; a
part's move is handed it with the rounds shown (`Mid.shown`). Which columns it holds is the player's
to lay: the frame's `runC` (Honest/Walk.lean) lays, in the first and in the shared chain, those that
this chain's own sub-protocols before have read, and in the second chain all of the first chain's,
then all of the shared chain's, then its own. The letter front (`Before`) is what a simulator is
given of the run so far. `pre` is a free letter here. The frame means it to list, for each chain
whose columns are handed, the chain's number, the number of its first own tree and the declared
rounds before the place; `readsBefore pre front` is the reads that these rounds make at the
challenges in front, and `front.opened` of them is the columns that front holds for these reads, or
`none` if one is lacking. Of `Good`'s five fields `exact` alone reads `pre`.

Why the names. A row's field is "at every member u of the row": so it follows from its parts' by
cases on `List.mem`. With the text under one name a theorem on one part is one line, and a part can
be rewritten under it without a cast. Why a second name for `exact`: this folder's theorems on parts
end in `ExactMember`, and `exactAt_of_exact` gives the field's text from each, at whatever `pre`.
What parts the two names is the range of `m.opened`: Limits.

All names stand in the namespace ProofFile.Honest.Small: a caller opens it.

Limits. No hypothesis of `ExactMember` itself speaks of `m.opened`, but On is handed m whole: so its
equation is asked at every value of `m.opened` at which On holds. The right side of the equation is
given front and, of m, `m.st.input` alone: not `m.opened`. So where its hypotheses hold at two
states that differ in `opened` alone, with one front, it asks that what the part shows has one law
at both; of the six On alone can tell two such states apart. If at a part that reads the columns the
two laws differ, `ExactMember` fails at every On that holds at both states: at an On that is always
true "asks more than the field" then means "is never met". It can hold there only at an On that does
not hold at both, as one that ties `m.opened` to front. `ExactMemberAt` is the form for a part at
which the law of what it shows depends on `m.opened`. At an On that does not read `m.opened`,
`ExactMember` asks the field's equation at more states than the field `exact` does; at an On that
implies `m.opened = none` it is asked at states without columns alone, and what `good_of_members`
builds of it is a `Good` at that On, whose `exact` is asked only where front lacks a column. Nothing
here leads back from the field to `ExactMember` at the same On. `FreshMember` has no On and no
front: it is asked at every value of `m.opened`. `pre` is idle in `exactAt_of_exact`.

What `statedOf` lets through. It filters the roots out, as `Sending.fits` does: so a round
whose entry counts roots, with an empty list of oracle messages, states "no item but roots".
`Block.shaped`, which the plan's test asks, refuses such a round (`roots_of_shaped`); `Good` does
not: of `rounds` and `oracles` `Side.fits` compares the lengths alone. And `Entry.cut`
(Decl/Declared.lean) rounds down: an entry whose bytes do not add up (8 bytes, no item) states the
same as one without these bytes: the format's `Round.ok` (Fmt/Rules8.lean) refuses it; nothing here
does. What it does not read: a round's name, work bits, rows, what it draws, and what it opens
(`DeclaredRound.stored`, `DeclaredRound.opens`). It holds a round's oracle messages whole, where
`Sending.fits` reads of each its length and width alone: at the empty list, which is all that this
folder's theorems ask, the two agree. Neither test on the book follows from `ProverCoinCounts.clauses`, not even
at a part that has no coin of its own (an entry of the book whose run has no coin passes there):
each has to be evaluated at the book. Nothing is claimed on any property of the protocol: not
soundness, completeness, binding, hiding or any other.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block Place Oracle)

variable {S Cl V W X Pb : Type}

/-! ## 1 Three conditions at one member -/

/-- The field `exact` of `Good` at one member u: the field's text behind "∀ u ∈ σ.members,". -/
def ExactMemberAt (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    m.opened = front.opened (readsBefore pre front) →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- The text of `ExactMemberAt` without its hypothesis on `m.opened`, and so without `pre`. It is
not a field of `Good`. It is asked at every value of `m.opened` at which On holds. -/
def ExactMember (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks

/-- The field `fresh` of `Good` at one member u: the field's text behind "∀ u ∈ σ.members,". It is
asked at every value of `m.opened`. -/
def FreshMember (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (u : Member V W X Pb) : Prop :=
  ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-! ## 2 The names and the two fields -/

/-- One hypothesis more: `ExactMember` gives `ExactMemberAt`, at every member and every `pre`. -/
theorem exactAt_of_exact {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {chain firstTree : Nat}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} {u : Member V W X Pb}
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (h : ExactMember φ σ chain firstTree On bud u) :
    ExactMemberAt pre φ σ chain firstTree On bud u :=
  fun ca m front ds asks hO hs _ hd hB hh hst => h ca m front ds asks hO hs hd hB hh hst

/-- `ExactMemberAt` at On is `ExactMember` at the condition "On, and `m.opened` is what front holds
for the reads of `pre`". It compiles only if the two texts differ in that hypothesis alone, up to
unfolding. -/
theorem exactAt_iff_exact {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {chain firstTree : Nat}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop} {u : Member V W X Pb}
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ExactMemberAt pre φ σ chain firstTree On bud u ↔
      ExactMember φ σ chain firstTree
        (fun u ca m front => On u ca m front ∧ m.opened = front.opened (readsBefore pre front))
        bud u :=
  ⟨fun h ca m front ds asks hO hs => h ca m front ds asks hO.1 hs hO.2,
    fun h ca m front ds asks hO hs ho => h ca m front ds asks ⟨hO, ho⟩ hs⟩

/-- Conditional on a term of `Good`: its two fields, as they stand, are `ExactMemberAt` and
`FreshMember` at every member. -/
theorem members_of_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W X → Env → Prop}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre φ σ Bk ord chain firstTree A B On bud) :
    (∀ u ∈ σ.members, ExactMemberAt pre φ σ chain firstTree On bud u) ∧
      ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u := ⟨g.exact, g.fresh⟩

/-- Conditional on a term g of `Good` at whatever pre', On' and bud': it builds a term of `Good` at
pre, On and bud: the fields `exact` and `fresh` are he and hf as they stand; the three other fields,
which read none of the three, are taken off g. -/
theorem good_of_membersAt {pre pre' : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W X → Env → Prop}
    {On On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud bud' : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre' φ σ Bk ord chain firstTree A B On' bud')
    (he : ∀ u ∈ σ.members, ExactMemberAt pre φ σ chain firstTree On bud u)
    (hf : ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u) :
    Good pre φ σ Bk ord chain firstTree A B On bud :=
  { fits := g.fits, plays := g.plays, acc := g.acc, exact := he, fresh := hf }

/-- The same from `ExactMember`, which asks at least as much: `good_of_membersAt` behind
`exactAt_of_exact`. -/
theorem good_of_members {pre pre' : List (Nat × Nat × List Fmt.DeclaredRound)} {φ : Face V W Pb}
    {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid W X → Env → Prop}
    {On On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud bud' : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre' φ σ Bk ord chain firstTree A B On' bud')
    (he : ∀ u ∈ σ.members, ExactMember φ σ chain firstTree On bud u)
    (hf : ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u) :
    Good pre φ σ Bk ord chain firstTree A B On bud :=
  good_of_membersAt g (fun u hu => exactAt_of_exact pre (he u hu)) hf

/-! ## 3 What declared rounds state -/

/-- What declared rounds state of the prover's messages, round by round: the items but the roots;
the oracle messages. -/
def statedOf (rs : List (Fmt.DeclaredRound × List Oracle)) : List (List Fmt.Item × List Oracle) :=
  rs.map fun r => (r.1.items.filter (· != .root), r.2)

/-- Conditional on `Block.shaped`: at a block that passes that test, which is the plan's test on
shapes, a round with no oracle message has an entry that counts no root. -/
theorem roots_of_shaped {b : Block S Cl} (hb : b.shaped = true)
    {r : Fmt.DeclaredRound × List Oracle} (hr : r ∈ b.rounds.zip b.oracles) (h : r.2 = []) :
    r.1.entry.roots = 0 := by
  unfold Block.shaped at hb
  have h1 := List.all_eq_true.1 (Bool.and_eq_true_iff.1 hb).2 r hr
  have h2 : r.2.length = r.1.entry.roots := eq_of_beq (Bool.and_eq_true_iff.1 h1).1
  rw [← h2, h]
  rfl

/-! ## 4 Two tests on the book -/

/-- No entry of the book names the part at o as its owner. -/
def lendsNone (B : ProverCoinCounts) (o : Addr) : Bool := B.ahead.all fun e => e.owner != o

/-- No entry of the book by which a part spends names the part at o as its owner. -/
def noneSpent (B : ProverCoinCounts) (o : Addr) : Bool := B.ahead.all fun e => !(e.once && e.owner == o)

/-- The first test gives the second. -/
theorem noneSpent_of_lendsNone {B : ProverCoinCounts} {o : Addr} (h : lendsNone B o = true) :
    noneSpent B o = true := by
  refine List.all_eq_true.2 fun e he => ?_
  have h1 : e.owner ≠ o := bne_iff_ne.1 (List.all_eq_true.1 h e he)
  have h2 : (e.owner == o) = false := beq_eq_false_iff_ne.2 h1
  rw [h2, Bool.and_false]
  rfl

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.exactAt_of_exact
#print axioms ProofFile.Honest.Small.exactAt_iff_exact
#print axioms ProofFile.Honest.Small.members_of_good
#print axioms ProofFile.Honest.Small.good_of_membersAt
#print axioms ProofFile.Honest.Small.good_of_members
#print axioms ProofFile.Honest.Small.roots_of_shaped
#print axioms ProofFile.Honest.Small.noneSpent_of_lendsNone
#print axioms ProofFile.Honest.Small.ExactMemberAt
#print axioms ProofFile.Honest.Small.ExactMember
#print axioms ProofFile.Honest.Small.FreshMember
#print axioms ProofFile.Honest.Small.statedOf
#print axioms ProofFile.Honest.Small.lendsNone
#print axioms ProofFile.Honest.Small.noneSpent
