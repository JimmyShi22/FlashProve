-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Fresh.lean: the field fresh of Good at the honest sender, stated under a public
condition on the book, and that condition. It claims no property of the protocol: not hiding, not
zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, the paragraph "Terms of the book" below. Limits of
the folder: Johnson/SendSim/Defs.lean.

What this file has. Definitions, two named propositions, and three small theorems that exchange two
quantifiers or weaken a premise.
  Spec.sendFreshAtP
                    fresh at every Seated side, for one address p at a time. If the entries that
                    concern p are within the sender's number of coins (WithinAt) and p is clear
                    (SpenderClear), then the field fresh holds at p (FreshAtP), with the bound
                    budAt. Written out: for all challenges that the rounds can sample and all
                    positions within the bound, over the sender's uniform coins the tuple (the runs
                    that p spends, what the sender discloses, the known runs) has the distribution
                    in which the runs that p spends are replaced by fresh uniform values,
                    independent of the rest. Statement only; proved as sendFreshAtP.
  Spec.sendFreshAt  The field fresh of Good itself (FreshAt: FreshAtP at every address) at every
                    Seated side, if the book is clear at the sender (BookClear). Statement only;
                    proved as sendFreshAt.
  sendFreshAt_of_each
                    The first statement implies the second.
  freshAt_iff_each  FreshAt holds exactly if FreshAtP holds at every address.
  withinAt_of_takes
                    WithinTakes implies WithinAt at every address.

Terms of the book.
  book          ProverCoinCounts (Johnson/Desc/ProofFile/Honest/Frame.lean): public data that go with a
                description. It says how many coins each part of the honest prover samples, and it
                has a list of entries.
  address       Addr: a place of the description and the number of a part in the row at that place.
                One address is earlier than another if its place is earlier in the order ord, or if
                the places are equal and its number is smaller (Addr.before). A place that is not in
                ord counts as the last.
  entry, run    Ahead: a run of consecutive coins of one part, the owner, given by its start and its
                length in each field, that one other part is given too. cutAll cuts the runs of a
                list of entries off a value of the owner's coins; it is none if a run is not within
                the number of coins. "Run" always means a run of coins; a run of the protocol is
                called an execution.
  spends, carries
                An entry either spends its run (once := true) or carries it. The library means the
                first for a run with which the other part, the spender, masks a value that it sends,
                and the second for a run on which the other part computes; Lean does not enforce
                this. Both words are the library's field names. ProverCoinCounts.spentBy o p lists the entries
                by which the part at p spends coins of the owner at o.
  known         ProverCoinCounts.knownBy ord o p: the other entries that give coins of o to p, or to a part
                earlier than p, whether spent by earlier parts or carried. A coin is known (at p) if
                such an entry holds it.
  fresh         the field of Good (FreshAt, Johnson/SendSim/At/Sim.lean): for each address p, under
                the field's three premises, the runs that p spends of a part's coins are uniform and
                independent of what the part discloses together with the known runs.
  clear         SpenderClear P ride Bk ord o p has three cases. (a) The address p spends nothing of
                the owner o's coins. (b) MaskSpender: p spends free entries of sampled oracle
                messages that are not sent along; these are coins of the extension field only, and
                no coin is in two entries. No spent coin is known (p does not also carry it, and no
                earlier part is given it); nor is a pad of an oracle message from which p spends, or
                a tail coin of a spent entry's row or of the last mask row. (c) FoldSpender: p
                spends, by one entry, all coefficients of a one-row table that is sent along. No
                spent coin and no tail coin of that table is known. Without the clauses on what is
                not known, the equation fails at small examples (said here without a theorem).
                BookClear: every entry on o's coins is within the sender's number of coins
                (WithinTakes), and every address is clear. The wider conditions SpenderClearAny
                (Johnson/SendSim/At/FreshWide.lean) and BookClearAny
                (Johnson/SendSim/At/BookWide.lean) admit a table of any number of rows, where
                FoldSpender admits a table of one row alone. A head says "clear" of either and names
                the condition, or points to the Terms that name it; in Johnson/SendSim/Defs.lean,
                result (3), and in Johnson/SendSim/Seat/AtDescLots.lean it is BookClearAny. The
                model's Sender.Clear (Johnson/SendSim/Pads.lean) is another condition, on sets of
                coins.

Limits.
  - The conditions on the book are public: they speak only of the book's entries (owner, start,
    length, spender, spent or carried) and of the place's public parameters. With a coin spent, the
    wider condition BookClearAny is proved in this folder at one made-up book (guardTried_filled
    with ownerOkB_iff, Johnson/SendSim/At/GuardTestTie.lean); the narrower ones (SpenderClear,
    BookClear) are evaluated at made-up books by #guard lines (Johnson/SendSim/At/FilledBooks.lean),
    and a #guard leaves no theorem: with a coin spent they are proved in this folder at no book,
    made-up or of the release. (At the code switches, senders of another kind: the test `bookFits`
    accepts at the book that `bookWhole` returns (`book_at_place`, AtFullSide/K2/BookAtPlace.lean),
    and from it `clear_of_bookFits` (Honest/K2/Law/BookFromFits.lean) gives SpenderClear under three
    premises more: no one statement joins the two.) Of the wider conditions at the book that the
    maker returns and at the key file's book: the table of premises in Johnson/SendSim/Defs.lean,
    "the book is clear". A book without entries is clear, since no address spends anything. Whoever
    makes a book has to prove them for it. Where they fail the statements hold vacuously. The book's
    own checks (ProverCoinCounts.clauses) do not look at pads or tails.
  - The statements speak of what the sender itself discloses, the symbols and the answers, and of
    nothing after it. An execution discloses more of the spent coins. Of a free entry: its row's
    symbols at the positions queried of the sender's tree; the answers of its oracle message; the
    value that its spender masks with it; and, after the spender, whatever a folding step or a code
    switch that carries the whole oracle message makes of it. Of the coefficients of a table that is
    sent along: the symbols of the table's rows at the queried positions; the scalars that the
    folding step sends; and what the code switch after that step puts into its own message.
  - Two owners. A part that spends runs of two owners has two instances of the statement, one for
    each owner. No instance says that the two runs together are uniform. That also needs that the
    owners' coins are sampled independently, that the owner in between is given nothing of the
    other's spent run, and that its data read none of it. Whoever joins the parts has to prove this.
  - Spec.sendFreshAt is all or nothing. It takes BookClear, so one address that is not clear makes
    it vacuous for every spender of that owner. There Spec.sendFreshAtP alone has content: an
    address that is not clear makes that statement vacuous for itself alone.
  - A table of more than one row that is sent along is excluded by a premise of FoldSpender. The
    wider condition (see "clear") admits it.
  - MaskSpender requires more than "free entries": only coins of the extension field, of a sampled
    oracle message that is not sent along. So a part that spends mask entries of an oracle message
    without an answer, or the main rows of such an oracle message, is outside the statement:
    SpenderClear is false there. It is excluded by a premise, not because the equation is known to
    fail there.
  - The reason for that restriction (in MaskSpender's fields free and clear): freeNo numbers free
    entries correctly only at sampled oracle messages that are not sent along. At an oracle message
    that is sent along, freeMaskEntries counts the entries of the rows, not the 2k + 1 coins of
    which they are made, so the numbers can reach the table's tails and the next oracle message's
    coins. At one without an answer that is not sent along and has two mask rows or more, they reach
    its own tails.
  - With two answers or more, the mask rows other than the last have entries after the free ones
    that are neither free nor a pad. No clear address spends them; they may be known.
  - The clause on known pads (padNo) names only pads in the last mask row. A pad in a main row needs
    none: an oracle message whose pads are in a main row has no mask row, so no entry of it is spent
    under these conditions.
  - One address may not spend both free entries and the coefficients of a table.
  - FoldSpender connects the job's own ride with the book's entry. That the spender is declared with
    that number of coins, and that the job's ride is the one due at the place, is not required here.
  - sendFits is not a premise. Where the job does not fit its place, what is disclosed is the error
    value on both sides, and the equation speaks of the sender's coins alone.
  - That the conditions suffice is a theorem (rowsFresh). They are not claimed to be necessary
    clause by clause.

How it fits. The two statements are proved in Johnson/SendSim/At/FreshAtMember.lean. At the level of
rows the statement is Spec.rowsFresh (Johnson/SendSim/At/CutTie.lean), proved in
Johnson/SendSim/At/RowsFresh.lean; Johnson/SendSim/At/JoinFresh.lean carries it to a Seated side.
Executable tests for the conditions are in Johnson/SendSim/At/BookTest.lean.

The other names.
  eOf, fOf, eAll, fAll  the numbers of the coins, in the extension field and in the base field, that
                        an entry holds; the same for a list of entries.
  maskCodeAt      the mask code of oracle message k.
  freeNo          the numbers of the coins at the free entries of a sampled oracle message. No pad
                  is among them.
  padNo           the number of the coin that is the pad of answer i, where the pads are in the last
                  mask row.
  maskTailNo      the number of the coin at entry q of the tail of mask row r.
  WithinTakes     every entry with this owner is within the sender's number of coins.
  WithinAt        the same for the entries that concern one address: those by which it spends, and
                  the known ones.
  MaskSpender     the second case of "clear". Its fields: noF (no coin of the base field is spent),
                  free, apart (no two entries share a coin), unknown (no spent coin is known), clear
                  (the pads and tails that are not known).
  FoldSpender     the third case of "clear". Its fields: one (the one entry: the first coins of that
                  oracle message, as many as Ride.count; the table has one row, R.h = 0; no tail
                  coin of the table is known) and unknown.
  FreshAtP        the field fresh at one address p.

Notes.
  - The known entries may hold all other coins: other oracle messages whole, with their pads and
    tails.
  - A coin that two addresses spend does not make SpenderClear false at the earlier address. It does
    at the later address, where the coin is known, if ord orders the two. Such a book is rejected by
    the book's own check that no coin is in two entries that spend it (ProverCoinCounts.clauses), which is not a
    premise here.
  - The fields apart and unknown speak only of coins of the extension field. They rely on the field
    noF.
  - The sender passes no coin on through its state (both rounds keep the state). So a coin of its
    own leaves it in two ways only: through the book, and through what it discloses.
  - WithinAt's half on the known entries is used by no proof. It is kept so that the statement is
    not applied where a known run is beyond the number of coins: there the third component of the
    tuple would be none at every value of the coins, and the statement would say nothing about any
    known coin.
-/
import Johnson.SendSim.At.Sim
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {S Cl V W X Pb : Type}

/-- The numbers of the owner's coins of the extension field that the entry e holds. -/
def eOf (e : Ahead) : Finset ℕ := Finset.Ico e.start.e (e.start.e + e.count.e)

/-- The numbers of the owner's coins of the base field that the entry e holds. -/
def fOf (e : Ahead) : Finset ℕ := Finset.Ico e.start.f (e.start.f + e.count.f)

/-- The numbers of the coins of the extension field that a list of entries holds; fAll is the same
for the base field. -/
def eAll (l : List Ahead) : Finset ℕ := l.foldr (fun e s => eOf e ∪ s) ∅
def fAll (l : List Ahead) : Finset ℕ := l.foldr (fun e s => fOf e ∪ s) ∅

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- The mask code of oracle message number k. -/
abbrev maskCodeAt (k : Nat) : OnBytes.Code := P.codes.mask.getD (shapeAt P k).maskCode default

/-- The numbers of the coins at the free entries of the mask rows of oracle message number k. -/
def freeNo (k : Nat) : Finset ℕ :=
  (Finset.range (OnBytes.Send.freeMaskEntries (shapeAt P k).maskRows (maskCodeAt P k).ell
    (shapeAt P k).answers)).image (maskStart P ride k + ·)

/-- The number of the coin that is the pad of answer i of oracle message number k, in its last mask
row. -/
def padNo (k i : Nat) : ℕ :=
  maskStart P ride k + (((maskCodeAt P k).ell - (shapeAt P k).answers + i) *
    (shapeAt P k).maskRows + ((shapeAt P k).maskRows - 1))

/-- The number of the coin at entry q of the tail of mask row r of oracle message number k. -/
def maskTailNo (k r q : Nat) : ℕ :=
  maskStart P ride k + (stepsOf P.codes (shapeAt P k) (ride k)).mask + r * (maskCodeAt P k).r + q

/-- Every entry of the book with the owner o is within the sender's number of coins. -/
def WithinTakes (Bk : ProverCoinCounts) (o : Addr) : Prop :=
  ∀ e ∈ Bk.ahead, e.owner = o →
    e.start.f + e.count.f ≤ (dueR P ride).f ∧ e.start.e + e.count.e ≤ (dueR P ride).e

/-- The entries that concern the one address p, those by which p spends coins of o and the known
ones, are within the sender's number of coins. -/
def WithinAt (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Prop :=
  ∀ e, e ∈ Bk.spentBy o p ∨ e ∈ Bk.knownBy ord o p →
    e.start.f + e.count.f ≤ (dueR P ride).f ∧ e.start.e + e.count.e ≤ (dueR P ride).e

/-- WithinTakes implies WithinAt at every order and every address. -/
theorem withinAt_of_takes {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {o : Addr}
    (h : WithinTakes P ride Bk o) (ord : List Place) (p : Addr) : WithinAt P ride Bk ord o p := by
  rintro e (he | he)
  · have h1 := List.mem_filter.1 he
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h e h1.1 h1.2.1.1
  · have h1 := List.mem_filter.1 he
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact h e h1.1 h1.2.1.1

/-- The address p spends free entries of mask rows. noF: no coin of the base field. free: each spent
coin is at a free entry of a sampled oracle message that is not sent along. apart: no two entries
share a coin. unknown: no spent coin is known. clear: for each oracle message with a spent entry, no
pad of it is known, and no coin of the tail of the row with the spent entry or of the last mask row
is known. -/
structure MaskSpender (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Prop where
  noF : fAll (Bk.spentBy o p) = ∅
  free : ∀ n ∈ eAll (Bk.spentBy o p), ∃ k, k < P.sent.size ∧ ride k = none ∧
    (shapeAt P k).answers ≠ 0 ∧ n ∈ freeNo P ride k
  apart : (Bk.spentBy o p).Pairwise fun e e' => Disjoint (eOf e) (eOf e')
  unknown : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p))
  clear : ∀ k j, k < P.sent.size → ride k = none → (shapeAt P k).answers ≠ 0 →
    maskStart P ride k + j ∈ freeNo P ride k → maskStart P ride k + j ∈ eAll (Bk.spentBy o p) →
    (∀ i < (shapeAt P k).answers, padNo P ride k i ∉ eAll (Bk.knownBy ord o p)) ∧
    ∀ q < (maskCodeAt P k).r,
      maskTailNo P ride k (j % (shapeAt P k).maskRows) q ∉ eAll (Bk.knownBy ord o p) ∧
      maskTailNo P ride k ((shapeAt P k).maskRows - 1) q ∉ eAll (Bk.knownBy ord o p)

/-- The address p spends the coefficients of a table that is sent along. one: it spends by one
entry, the first Ride.count coins of that oracle message; the table has one row (R.h = 0); no coin
of the tail of any of its rows is known. unknown: no spent coin is known. -/
structure FoldSpender (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Prop where
  one : ∃ k R e, k < P.sent.size ∧ ride k = some R ∧ R.h = 0 ∧ Bk.spentBy o p = [e] ∧
    e.count = ⟨0, R.count⟩ ∧ e.start.e = maskStart P ride k ∧
    ∀ r < (shapeAt P k).maskRows, ∀ q < (maskCodeAt P k).r,
      maskTailNo P ride k r q ∉ eAll (Bk.knownBy ord o p)
  unknown : Disjoint (eAll (Bk.spentBy o p)) (eAll (Bk.knownBy ord o p))

/-- The condition on the book at the owner o and one address p: p spends nothing of o, or free
entries (MaskSpender), or the coefficients of a table that is sent along (FoldSpender). The two
structures also say which coins are not known at p: the spent coins, the pads and the tails
concerned. -/
def SpenderClear (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr) : Prop :=
  Bk.spentBy o p = [] ∨ MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p

/-- The book is clear at the owner o: all of o's entries are within the sender's number of coins,
and every address is clear. -/
def BookClear (Bk : ProverCoinCounts) (ord : List Place) (o : Addr) : Prop :=
  WithinTakes P ride Bk o ∧ ∀ p, SpenderClear P ride Bk ord o p

/-- The field fresh of Good at one address p. -/
def FreshAtP (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (p : Addr) : Prop :=
  ∀ u ∈ σ.members, ∀ sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-- The field fresh (FreshAt) holds exactly if FreshAtP holds at every address. -/
theorem freshAt_iff_each (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts) (ord : List Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) :
    FreshAt φ σ Bk ord bud ↔ ∀ p, FreshAtP φ σ Bk ord bud p :=
  ⟨fun h p u hu sp ca m ds asks => h u hu p sp ca m ds asks,
    fun h u hu p sp ca m ds asks => h p u hu sp ca m ds asks⟩

/-- At every Seated side and every address p: if the entries that concern p are within the sender's
number of coins and p is clear, then the field fresh holds at p, with the bound budAt. Statement
only; proved as sendFreshAtP in Johnson/SendSim/At/FreshAtMember.lean. -/
def Spec.sendFreshAtP : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place) (p : Addr), Seated σ J →
    WithinAt J.P J.ride Bk ord ⟨σ.block.place, 0⟩ p →
    SpenderClear J.P J.ride Bk ord ⟨σ.block.place, 0⟩ p →
    FreshAtP φ σ Bk ord (fun _ _ asks => budAt J.P asks) p

/-- At every Seated side: if the book is clear at the sender, then the field fresh of Good holds,
with the bound budAt. Statement only; proved as sendFreshAt in
Johnson/SendSim/At/FreshAtMember.lean. -/
def Spec.sendFreshAt : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place), Seated σ J → BookClear J.P J.ride Bk ord ⟨σ.block.place, 0⟩ →
    FreshAt φ σ Bk ord fun _ _ asks => budAt J.P asks

/-- Spec.sendFreshAtP implies Spec.sendFreshAt. -/
theorem sendFreshAt_of_each (H : Spec.sendFreshAtP) : Spec.sendFreshAt :=
  fun S Cl V W X Pb φ σ J Bk ord h hB => (freshAt_iff_each φ σ Bk ord _).2 fun p =>
    H S Cl V W X Pb φ σ J Bk ord p h (withinAt_of_takes hB.1 ord p) (hB.2 p)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.withinAt_of_takes
#print axioms OnBytes.SendSim.At.freshAt_iff_each
#print axioms OnBytes.SendSim.At.sendFreshAt_of_each
