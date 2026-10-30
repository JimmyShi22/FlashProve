-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/GoodCalls.lean: kind K14: CONDITIONAL. THE FIELDS exact AND fresh
OF THE STRUCTURE Good (Honest/Side.lean) AT A SIDE WHOSE ROW IS ONE OF THE KIND's FOUR OWN ROWS
(Honest/K14/PartsCalls.lean: quietRow, splitRow), WHERE THE SIDE's SUB-PROTOCOL DECLARES ONE ROUND
THAT CUTS WHAT THE ROW SENDS AND STATES ONE EMPTY LIST OF ORACLE MESSAGES, AND, FOR fresh, WHERE THE
BOOK PASSES THE TEST noneSpent AT THE PART: BY CALLING LAWS THAT LIE ELSEWHERE: no argument over a
distribution is made here: exact_quiet, exact_split and fresh_at are one call each. exact:
quietPart_exact_lift (Honest/Small/Quiet.lean) and scalarsPart_exact_lift
(Honest/Small/Scalars.lean). fresh: fresh_of_nil (Honest/Law/ToyLaw.lean) with spentBy_of_noneSpent
(Honest/Small/Book.lean).

  members_quiet, members_split   a side with one of the kind's rows, beside a sub-protocol that
                  declares one round, has one member, written out: its number is 0
  split_reads     what the value at "SPLIT" reads, BY TYPE: the index and the challenges heard alone
  exact_quiet, exact_split   **the field exact**, at the kind's On and bud, which ask nothing
  fresh_at        **the field fresh** at any side: its one premise is on the book: at each member's
                  own number no entry by which another part spends names that part as its owner
                  (noneSpent, Honest/Small/Field.lean: a test with code). No kind is named
  fresh_quiet, fresh_split   so at the kind's rows: ONE evaluation of that test, at the part 0

WHAT IS ASKED OF THE SIDE. Of σ.row: that it is the kind's row. OF σ.block NOTHING BUT: one declared
round, one empty list of oracle messages, and what the round cuts (no item; at "SPLIT" one element
of the extension field). Its place is not asked, and i is any number. WHERE THESE THREE ARE MET: at
the library's own eight sub-protocols of a plan (declares3, declares_split: Honest/K14/Debts.lean);
and, in Honest/K14/GoodSeated.lean, which calls this file's laws at the side that Side.seated makes:
MET AT THE MEMBER OF ANY LIST OF THE FORM FlatOf (Johnson/Desc/K14/Honest/FlatForm.lean), WHERE THE
LIBRARY MAKES ITS EIGHT OF THE PLAN: A PREMISE. THAT THE SHARED LIST OF WHAT onlineDescription RETURNS HAS
THAT FORM IS flat_pure's (Johnson/Desc/K14/Honest/FlatPure.lean), UNDER THE SAME PREMISE AT THE
PLANNER's OWN PARAMETERS. good_rows_shared (Honest/K14/GoodSeatedShared.lean) CALLS
GoodSeated.lean's LAWS AT THE LIST OF MEMBERS OF THE SHARED CHAIN's LETTERS AT THE IOP AS WRITTEN IN
LEAN, UNDER FOUR PREMISES ON PUBLIC DATA (every member's own test on the plan, linOk, sendingsFit,
noneSpent): THAT THE LIBRARY MAKES ITS EIGHT IS NOT AMONG THEM: THERE IT FOLLOWS FROM THE LIST's OWN
TESTS ON THE PLAN (the library's eight_of_pass, Johnson/Desc/K14/Law/K14SitsPlan.lean). NONE OF THE
FOUR IS SHOWN AT ANY PUBLIC FILE (one of them, sendingsFit, is had at the shared chain's own
parameters under the library's head: sendings_at_head, Honest/K14/SendingsAtHead.lean). THAT THE
LIBRARY MAKES ITS EIGHT IS SHOWN AT SIZES WRITTEN OUT (Plan2.eight, Honest/K14/Debts2.lean, at
plan2_key and plan2_real, Honest/K14/Thread2Member.lean); AT THE SHARED CHAIN's OWN PARAMETERS IT IS
HAD UNDER A PREMISE, THE LIBRARY's HEAD (plan2_at_head, Honest/K14/PlanAtHead.lean, with
Plan2.eight). SO THE THREE ARE MET AT NO ROUND OF WHAT onlineDescription RETURNS WITHOUT A PREMISE. The one
face at these type parameters is the shared chain's (Face.shared, Honest/Frame.lean), at Pb := Ky.

WHAT THE STATEMENTS AMOUNT TO: ONE EQUATION WITH A COIN (exact_split: the spender's half) · THREE
QUIET ONES (exact_quiet at the three quiet rows: two constants are compared) · THE FIELD fresh AT
THE FOUR ROWS: TRUE AND EMPTY: the four parts own no coin: both sides are one law.

THE CALLED LAWS' OWN LIMITS HOLD HERE: THEIR HEADS ARE TO BE READ WITH THIS FILE. In short, in this
file's words. At a quiet row: bookkeeping; no law on a coin or an input. At "SPLIT": THE SPENDER's
HALF ALONE, one part at a time, all else fixed before the coins. That the one spent coin is uniform,
and apart from where the run stands, is TAKEN by the order of the field's own quantifiers: it is no
premise and is shown of no run. NOT SHOWN HERE (where another file has it, the file is named):
· the owner's fresh for this spender (the owner is the part that sends the split's mask message): a
law in the frame's form, at a test on the book, is sp_owner_law (Honest/K14/FreshOwnerLaw.lean, at
the test spOwnerTest of Honest/K14/FreshOwner.lean); at the side that Side.seated returns at the
owner's place it is called, as sp_owner_law', in rowsServe_of (Honest/K14/SendingRowsLaw.lean),
under hypotheses of its own; that the book of a public file passes it is claimed in none of the
three
· that the book lends the part just that coin: one_coin (Honest/K14/SplitCoin.lean): where lendRow
returns, and under premises on the book's entry (its owner and its start); that a book has such an
entry, and which entry of which message stands at that number, is not claimed there; the book's own
tests (ProverCoinCounts.clauses, Honest/Frame.lean) are shown of no book here
· the rule for a row (Honest/Rule.lean)
· that no part in front has been handed the coin
· THAT WHOEVER CARRIES THE COIN BEHIND THIS PART MEETS ITS OWN exact AT EACH FIXED CARRIED RUN,
beside a simulator that is not handed it: THESE ARE THE PARTS OF BOTH PROXIMITY TESTS BEHIND "SPLIT"
IN THE CHAIN, which carry the split's mask message whole: what this part shows and the carried run
together give the value (the part sends its value plus the coin: scalarsPart, Honest/ForKinds.lean):
exact_split treats this one part, with the carried runs fixed, and reaches no part that carries the
same coin; that these tests' own coins cover the value there is shown nowhere: NOTHING OF THAT IS IN
LEAN: IT IS NAMED HERE AND NOT MET; and such a part's On may tie what it carries to what was shown
in front only by an identity that holds at every value of the carried run's coins
· that nothing which the value reads hangs on the coin: by split_reads the value is a function of
the index and of the challenges heard alone (and of the public data A and the reader weights, which
stand outside that function; the equation fixes it as far as the one scalar that is sent can tell);
that these do not hang on the coin in a run is not said: of the two challenges that the value reads,
that of "LIN zeta" is sampled BEHIND the owner's two rounds, whose root and OOD answer hang on the
coin: exact_split does not reach that stretch: it is the matter of the owner's fresh (above).
The equation holds at every value that the part adds the coin to, right or wrong. What a part shows
holds no root, nonce, path or salt, and no column read at positions that this round samples: of the
four rows that matters at "LOC" alone, whose round samples the locations at which the committed
table is opened: these columns are no part of what the quiet part shows. Nothing is said on what a
part hands on. The laws hold AT THESE LITERALS ALONE: not with a stop laid into the part, not joined
with another part by Part.andThen, not beside another simulator or another number of scalars. hd
shuts roots and answers out; it does not shut left-over bytes: the format's test on a round is to be
asked beside it, and is not asked here. fresh_at's one premise is on the book and names no part's
text: without it fresh can fail at a part that takes no coin (said here without a theorem).

What is not claimed. The structure Good at any row: its fields plays and acc are not treated (as one
term, at letters from which these two follow vacuously: good_rows, Honest/K14/GoodSeated.lean).
That a book passes noneSpent. The two sendings' fields. Nothing on what is or is not hidden; no
property.
-/
import Johnson.Desc.ProofFile.Honest.K14.PartsCalls
import Johnson.Desc.ProofFile.Honest.Small.Quiet
import Johnson.Desc.ProofFile.Honest.Small.Scalars
import Johnson.Desc.ProofFile.Honest.Small.Book

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (ExactMember FreshMember statedOf noneSpent quietPart_exact_lift
  scalarsPart_exact_lift spentBy_of_noneSpent)

variable {S Cl X Pb W₀ Rc Ky : Type}

/-- The one member of a side with a quiet row. -/
theorem members_quiet (A : Data) (weights : W₀ → Weights) (i : Nat)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb) (hrow : σ.row = quietRow A weights i)
    (d : Fmt.DeclaredRound) (hr : σ.block.rounds = [d]) (ho : σ.block.oracles = [[]]) :
    σ.members = [{ number := 0, rounds := [(d, [])], part := liftK14 A weights quietPart
                   sim := quietSim { place := place i, part := 0 } }] := by
  unfold Side.members
  rw [hrow, hr, ho]
  rfl

/-- The one member of a side with the row of "SPLIT". -/
theorem members_split (A : Data) (weights : W₀ → Weights)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb) (hrow : σ.row = splitRow A weights)
    (d : Fmt.DeclaredRound) (hr : σ.block.rounds = [d]) (ho : σ.block.oracles = [[]]) :
    σ.members = [{ number := 0, rounds := [(d, [])], part := liftK14 A weights (splitPart A)
                   sim := splitSim }] := by
  unfold Side.members
  rw [hrow, hr, ho]
  rfl

/-- **What the value at "SPLIT" reads, by type**: the lifted part IS the frame's scalarsPart at a
list of values that is a function of the index and of the challenges heard ALONE: not of the index
committer's coins, not of the key, not of what was seen, not of what was handed on. -/
theorem split_reads (A : Data) (weights : W₀ → Weights) :
    ∃ f : W₀ → List Fmt.Drawn → List OnBytes.E,
      (liftK14 A weights (splitPart A) : Part Empty (Common W₀ Rc Ky) X) =
        scalarsPart splitRun 1 fun c fr => f c.w₀ fr.heard :=
  ⟨fun w h => [splitValue A { rows := entriesOf A.S (weights w) } h], rfl⟩

/-- CONDITIONAL. **The field exact at a side with a quiet row**: quietPart_exact_lift, called. hd:
the one round cuts no item. -/
theorem exact_quiet (A : Data) (weights : W₀ → Weights) (i : Nat)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (chain firstTree : Nat) (hrow : σ.row = quietRow A weights i) (d : Fmt.DeclaredRound)
    (hr : σ.block.rounds = [d]) (ho : σ.block.oracles = [[]]) (hd : d.items = []) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree k14On k14Bud u := by
  intro u hu
  rw [members_quiet A weights i σ hrow d hr ho] at hu
  obtain rfl := List.mem_singleton.1 hu
  exact quietPart_exact_lift φ σ chain firstTree k14On k14Bud 0 1 [(d, [])] _ _ _ _ _
    (by simp [statedOf, hd])

/-- CONDITIONAL. **The field exact at a side with the row of "SPLIT"**: scalarsPart_exact_lift,
called. hd: the one round cuts one element of the extension field. -/
theorem exact_split (A : Data) (weights : W₀ → Weights)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (chain firstTree : Nat) (hrow : σ.row = splitRow A weights) (d : Fmt.DeclaredRound)
    (hr : σ.block.rounds = [d]) (ho : σ.block.oracles = [[]]) (hd : d.items = [.e]) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree k14On k14Bud u := by
  intro u hu
  rw [members_split A weights σ hrow d hr ho] at hu
  obtain rfl := List.mem_singleton.1 hu
  exact scalarsPart_exact_lift φ σ chain firstTree k14On k14Bud 0 1 [(d, [])] _ splitRun _ _ _ _ _
    (by simp [statedOf, hd])

/-- CONDITIONAL. **The field fresh**, at any side: at each member's own number no entry by which
another part spends names that part as its owner: fresh_of_nil, called. No kind is named. -/
theorem fresh_at {V W : Type} (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop)
    (hB : ∀ u ∈ σ.members, noneSpent Bk { place := σ.block.place, part := u.number } = true) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord bud u :=
  fun u hu p sp ca m ds asks _ _ _ =>
    fresh_of_nil _ (spentBy_of_noneSpent (hB u hu) p)
      (fun c => σ.shows φ u (c, sp, ca) m ds asks)
      fun c => cutAll c (Bk.knownBy ord { place := σ.block.place, part := u.number } p)

/-- CONDITIONAL. The field fresh at a side with a quiet row: one evaluation of the test on the
book. -/
theorem fresh_quiet (A : Data) (weights : W₀ → Weights) (i : Nat)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (hrow : σ.row = quietRow A weights i) (d : Fmt.DeclaredRound)
    (hr : σ.block.rounds = [d]) (ho : σ.block.oracles = [[]])
    (hB : noneSpent Bk { place := σ.block.place, part := 0 } = true) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord k14Bud u :=
  fresh_at φ σ Bk ord k14Bud fun u hu => by
    rw [members_quiet A weights i σ hrow d hr ho] at hu
    obtain rfl := List.mem_singleton.1 hu
    exact hB

/-- CONDITIONAL. The field fresh at a side with the row of "SPLIT": the like. -/
theorem fresh_split (A : Data) (weights : W₀ → Weights)
    (φ : Face Empty (Common W₀ Rc Ky) Pb) (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (hrow : σ.row = splitRow A weights) (d : Fmt.DeclaredRound)
    (hr : σ.block.rounds = [d]) (ho : σ.block.oracles = [[]])
    (hB : noneSpent Bk { place := σ.block.place, part := 0 } = true) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk ord k14Bud u :=
  fresh_at φ σ Bk ord k14Bud fun u hu => by
    rw [members_split A weights σ hrow d hr ho] at hu
    obtain rfl := List.mem_singleton.1 hu
    exact hB

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.members_quiet
#print axioms ProofFile.Honest.K14.members_split
#print axioms ProofFile.Honest.K14.split_reads
#print axioms ProofFile.Honest.K14.exact_quiet
#print axioms ProofFile.Honest.K14.exact_split
#print axioms ProofFile.Honest.K14.fresh_at
#print axioms ProofFile.Honest.K14.fresh_quiet
#print axioms ProofFile.Honest.K14.fresh_split
