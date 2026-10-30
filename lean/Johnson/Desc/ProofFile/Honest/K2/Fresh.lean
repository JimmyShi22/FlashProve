-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Fresh.lean: the kind "the code switch" (K2): A SECOND STATEMENT,
NOT PROVED HERE: at a side that is seated with the kind's row (`switchRow`, Honest/K2/Sim.lean), the
field `fresh` of the frame's `Good` (Honest/Side.lean). Definitions; and one line that holds this
file's copy of that field against the frame's own text. The statement is none of the library's
goals.

THE STATEMENT IS AN IMPLICATION FROM THE PREMISES NAMED HERE (`FreshAsks`). THE IMPLICATION IS
PROVED IN Honest/K2/Law/FreshAtProof.lean (`switchFresh`). ITS PREMISES ARE NOT SHOWN HERE: see the
limits.

  `FreshOf`         the field `fresh` of `Good`, letter for letter, at the face of the first and the
                    second chain
  `freshOf_of_good`   that copy is the frame's own field: the two texts are one to Lean
WHAT THE BOOK MUST MEET, AS TESTS WITH CODE on public data: the sending's shapes and two lists of
the book's entries on the sending's coins: es, what one part spends; ks, what is known:
  `Run`, `Run.meets`, `Run.inside`, `runOf`   a run of coins: where it begins, how many, by field;
                    two runs share a coin; one lies inside the other; an entry's run
  `wholeRun`, `entriesFrom`, `freeRun`, `coefficientsRun`, `freshTailsRun`   in the sending's count:
                    a message's whole run · where its mask rows' entries begin · its FREE mask
                    entries: those below the pad's first place, as the verifier's ledger counts them
                    (`OnBytes.Send.freeMaskEntries`) · a fresh mask's 2 k + 1 coefficients · its
                    rows' tails
  `bookFits`        THE TEST: every entry can be cut off the sending's coins, IN THE VERY WORDS OF
                    THE FRAME's `Cs.cut`: in each field its start and its count together lie within
                    the sending's count, where it has no coin of that field too · no coin of es
                    stands in ks, and no coin in two entries of es · AND ONE OF THREE: nothing is
                    spent · WHAT IS SPENT IS JUST THE FRESH MASK's COEFFICIENTS, in one entry (the
                    same coins: where the entry begins in the base field, of which it has no coin,
                    is not asked), and ks holds no coin of its rows' tails · ALL THAT IS SPENT LIES
                    INSIDE ONE SAMPLED MESSAGE's FREE MASK ENTRIES, and of that message's coins ks
                    holds free entries alone: none of its pad, none of its tails
  `SendFreshLaw`    THE SHARED SENDING's SECOND LAW, AS A NAMED PREMISE, at es and ks: where the
                    sending passes the shared sending's public test, the table that rides has one
                    row AND `bookFits` SAYS YES: at every data, at seeds that fit and lists within
                    the count: over uniform coins c of the sending, (the runs that es cuts off c ·
                    what the sending shows at c · the runs that ks cuts off c) has the law of
                    (uniform runs of their own · what the sending shows at c · the runs that ks cuts
                    off c)
  `FreshAsks`       ALL PREMISES, by name: seated · blocks · two · fits · seeds · oneRow, as in
                    Honest/K2/Exact.lean; and
                    book       PUBLIC: FOR EVERY ADDRESS q: `bookFits` at the entries by which q
                               spends coins of the switch's part, and at the other entries that hand
                               such coins to q or to a part in front of q
                    sendFresh  FOR EVERY ADDRESS q: `SendFreshLaw` at these two lists
  `SwitchFresh`     THE STATEMENT, AT ALL ITS LETTERS: `FreshAsks` gives `FreshOf` at `switchBud`

NO PREMISE ON THE CLOSING: what the part shows stands on both sides of the equation at one input,
one stand and the same carried coins: where the closing refuses, both sides show nothing, and the
equation that is left, on the runs alone, follows from `sendFresh` at any data.

Limits. THE PREMISES ARE NOT SHOWN HERE. UNDER THE LIBRARY's HEAD (`P5J.AtMgA`, at the format's
second hash function) AND THE OPENED DESCRIPTION, BOTH HYPOTHESES: at each switch of the plan all
eight, and the statement's conclusion, follow from the one premise `book` (`freshAsks_of_book`,
`freshOf_of_book`, Honest/K2/Law/FreshOfBook.lean); `book` is had at each of the kind's 25 places,
at whatever book `bookWhole` returns at the description and at that description's order of places
(`book_at_place`, AtFullSide/K2/BookAtPlace.lean); the two are joined as one statement at the eleven
switches of the links 2, 4, …, 22 (`freshAsks_at_switch`, `freshOf_at_switch`,
AtFullSide/K2/BookAtSwitches.lean). The limits of these three files hold, but for what
BookAtSwitches.lean says of the other fourteen. That the maker's own book is what `bookWhole`
returns there: `return_at_head`; all 25 joined, at public files in scope at which the gate accepts,
where the maker returns, at that book: `simulatorAtTheBase`
(AtFullSide/K2/SimulatorAtTheBaseProof.lean; the clause SidesMeetGood of SimulatorAtTheBase.lean,
with that file's limits). `SendFreshLaw` is not shown here: Honest/K2/Law/AtCore.lean shows it of
the core's sender, under its own named premises, over another writer's theorem. `bookFits` ASKS MORE
THAN MAY BE NEEDED: of the message whose free entries are spent it lets ks hold no main row's tail
either. That the number of coefficients in the book's entry is the fold's own is in it only as far
as the entry's run is `coefficientsRun` at the place's number of row variables. Nothing here says
what the statement would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Oracle Place)

variable {W₀ Rc Xi Tr X S Cl : Type}

/-- The field `fresh` of `Good`, letter for letter. -/
def FreshOf (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts)
    (ord : List Place) (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows .own u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows .own u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

/-- The copy is the frame's own field. -/
theorem freshOf_of_good {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    {σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi} {Bk : ProverCoinCounts}
    {ord : List Place} {chain firstTree : Nat}
    {A B : Coins Bk → S → Mid (Local W₀ Rc Xi Tr) X → Env → Prop}
    {On : (u : Member (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) → CsAll u.part.carries →
      Mid (Local W₀ Rc Xi Tr) X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (g : Good pre .own σ Bk ord chain firstTree A B On bud) : FreshOf σ Bk ord bud := g.fresh

/-! ## What the book must meet -/

/-- A run of coins: where it begins, and how many, by field. -/
abbrev Run : Type := Due × Due

/-- Two runs share a coin. -/
def Run.meets (a b : Run) : Bool :=
  (decide (a.1.f < b.1.f + b.2.f) && decide (b.1.f < a.1.f + a.2.f) && a.2.f != 0 && b.2.f != 0) ||
    (decide (a.1.e < b.1.e + b.2.e) && decide (b.1.e < a.1.e + a.2.e) && a.2.e != 0 && b.2.e != 0)

/-- Every coin of a is a coin of b. -/
def Run.inside (a b : Run) : Bool :=
  (a.2.f == 0 || (decide (b.1.f ≤ a.1.f) && decide (a.1.f + a.2.f ≤ b.1.f + b.2.f))) &&
    (a.2.e == 0 || (decide (b.1.e ≤ a.1.e) && decide (a.1.e + a.2.e ≤ b.1.e + b.2.e)))

/-- An entry's run. -/
def runOf (e : Ahead) : Run := (e.start, e.count)

/-- The whole run of the message number n. -/
def wholeRun (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n : Nat) : Run :=
  (dueBefore codes sent fresh n, messageDue codes (sent.getD n default).shape (foldAt fresh n))

/-- Where, among the sending's coins of the extension field, the entries of message number n's mask
rows begin: behind its main rows' tails and pad, where these lie over that field. -/
def entriesFrom (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n : Nat) : Nat :=
  let s := (sent.getD n default).shape
  (dueBefore codes sent fresh n).e +
    if s.mainDeg == 3 then
      s.mainRows * (codes.base.getD s.code default).r + (if s.maskRows != 0 then 0 else s.answers)
    else 0

/-- The free mask entries of the message number n. -/
def freeRun (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n : Nat) : Run :=
  let s := (sent.getD n default).shape
  (⟨0, entriesFrom codes sent fresh n⟩,
    ⟨0, OnBytes.Send.freeMaskEntries s.maskRows (codes.mask.getD s.maskCode default).ell s.answers⟩)

/-- The coefficients of the fresh mask number n, of a fold with k row variables. -/
def coefficientsRun (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n k : Nat) : Run :=
  (⟨0, (dueBefore codes sent fresh n).e⟩, ⟨0, 2 * k + 1⟩)

/-- Its rows' tails. -/
def freshTailsRun (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (n k : Nat) : Run :=
  let s := (sent.getD n default).shape
  (⟨0, (dueBefore codes sent fresh n).e + (2 * k + 1)⟩,
    ⟨0, s.maskRows * (codes.mask.getD s.maskCode default).r⟩)

/-- **THE TEST ON THE BOOK.** es: what one part spends. ks: what is known. -/
def bookFits (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (es ks : List Ahead) : Bool :=
  (es ++ ks).all (fun e =>
      decide (e.start.f + e.count.f ≤ (sendingDue codes sent fresh).f) &&
        decide (e.start.e + e.count.e ≤ (sendingDue codes sent fresh).e)) &&
    es.all (fun e => ks.all fun k => !(runOf e).meets (runOf k)) &&
    es.zipIdx.all (fun x => es.zipIdx.all fun y => x.2 == y.2 || !(runOf x.1).meets (runOf y.1)) &&
    (es.isEmpty ||
      fresh.any (fun x =>
        es.length == 1 &&
          es.all (fun e => (runOf e).inside (coefficientsRun codes sent fresh x.1 x.2) &&
            (coefficientsRun codes sent fresh x.1 x.2).inside (runOf e)) &&
          ks.all fun k => !(runOf k).meets (freshTailsRun codes sent fresh x.1 x.2)) ||
      (List.range sent.size).any fun n =>
        (foldAt fresh n).isNone && (sent.getD n default).shape.answers != 0 &&
          es.all (fun e => (runOf e).inside (freeRun codes sent fresh n)) &&
          ks.all fun k => !(runOf k).meets (wholeRun codes sent fresh n) ||
            (runOf k).inside (freeRun codes sent fresh n))

/-- **The shared sending's second law, as a named premise.** es: what is spent. ks: what is known.
-/
def SendFreshLaw (Sd : Sender) (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (es ks : List Ahead) : Prop :=
  K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true →
  (∀ x ∈ fresh, (sent.getD x.1 default).shape.maskRows = 1) →
  bookFits codes sent fresh es ks = true →
  ∀ (data : Nat → Nat → Nat → Cb.Gl.E) (seeds : List Fmt.Ext3) (asks : List (List Nat)),
    seedsFit codes sent seeds → asksWithin codes sent asks →
    (Prob.unif (Cs (sendingDue codes sent fresh))).map (fun c =>
        (cutAll c es, senderShows Sd codes sent fresh data seeds asks c, cutAll c ks)) =
      (Prob.unif (CsAll (es.map Ahead.named) × Cs (sendingDue codes sent fresh))).map fun a =>
        (some a.1, senderShows Sd codes sent fresh data seeds asks a.2, cutAll a.2 ks)

/-- **All premises.** -/
structure FreshAsks (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place) :
    Prop where
  seated : Side.seated bs p.place (switchRow Sd D readers closing p ok rounds) fs = some σ
  blocks : σ.block.rounds.zip σ.block.oracles = rounds
  two : rounds.length = 2
  fits : K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others))
    (rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) = true
  seeds : ∀ r ∈ rounds.head?, ∀ d : Fmt.Drawn, drawFit r.1 d = true →
    seedsFit p.sizes.codes (switchSent p.sizes p.others) d.elems
  oneRow : ∀ x ∈ switchFresh p.sizes p.others p.foldVars,
    ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows = 1
  book : ∀ q : Addr, bookFits p.sizes.codes (switchSent p.sizes p.others)
    (switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
    (Bk.knownBy ord ⟨p.place, 0⟩ q) = true
  sendFresh : ∀ q : Addr, SendFreshLaw Sd p.sizes.codes (switchSent p.sizes p.others)
    (switchFresh p.sizes p.others p.foldVars) (Bk.spentBy ⟨p.place, 0⟩ q)
    (Bk.knownBy ord ⟨p.place, 0⟩ q)

/-- **THE STATEMENT**, meant at all its letters. Not proved here: `switchFresh`,
Honest/K2/Law/FreshAtProof.lean. -/
def SwitchFresh (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (Bk : ProverCoinCounts) (ord : List Place) :
    Prop :=
  FreshAsks Sd D readers closing p ok rounds bs fs σ Bk ord → FreshOf σ Bk ord (switchBud p)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.FreshOf
#print axioms ProofFile.Honest.K2.freshOf_of_good
#print axioms ProofFile.Honest.K2.Run
#print axioms ProofFile.Honest.K2.Run.meets
#print axioms ProofFile.Honest.K2.Run.inside
#print axioms ProofFile.Honest.K2.runOf
#print axioms ProofFile.Honest.K2.wholeRun
#print axioms ProofFile.Honest.K2.entriesFrom
#print axioms ProofFile.Honest.K2.freeRun
#print axioms ProofFile.Honest.K2.coefficientsRun
#print axioms ProofFile.Honest.K2.freshTailsRun
#print axioms ProofFile.Honest.K2.bookFits
#print axioms ProofFile.Honest.K2.SendFreshLaw
#print axioms ProofFile.Honest.K2.FreshAsks
#print axioms ProofFile.Honest.K2.SwitchFresh
