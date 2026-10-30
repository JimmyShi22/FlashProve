-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorAtTheHead.lean: AT ANY FILLING. The kind
"lookup" (K3): what a kind's author hands in for its lot of rows with simulators
(`lookupSimulatorLot`, LookupSimulatorLot.lean), under the library's hypothesis at the full size,
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean). GENERAL IN THE FILLING F, which may read the public part; in
the face, the input's type and the sides' own state; in the book, under one named premise on it. One
definition; theorems.

  `LookupsOwnNoCoin`              THE PREMISE ON THE BOOK: by the book no part spends a coin of a
                                  part at a lookup's place
  `lookupSimulatorRowsAreFifty`   the lot has fifty rows
  `lookupSimulatorRowIsSeated`    every row is seated at the first chain's flat list
  `lookupSimulatorRowIsStated`    at every seated side: `RowStated` (the declared rounds are the
                                  stages' own) and `Side.fits`
  `lookupSimulatorIsExactOverFreshMaskEntries`
                                  THE FIELD exact of `Good` at every member of every row's side,
                                  at the row's own On and bud, in the form without the hypothesis
                                  on the opened columns (`ExactMember`, Honest/Small/Field.lean).
                                  OVER MASK ENTRIES TAKEN AS FRESH: the spender's half alone
  `lookupSimulatorIsFresh`        THE FIELD fresh there (`FreshMember`), under the premise on the
                                  book
  `lookupSimulatorIsGood`         `Good` at every row's side, at every `pre`, at the row's own On
                                  and bud, at A and B "false": the premise `h` of `hand_of_seated`
                                  (Honest/Thread/RowsMore.lean), so `hand₁` of `file_owed_rows`
                                  (Honest/Thread/Rows.lean) at these rows
  `lookupOnAndBudHoldEverywhere`  On and bud alone: `OnFromS` (Honest/Thread/OnSaid.lean) at every
                                  row as laid, at every thread; and bud at every number, challenges
                                  and positions. TWO OF THE FOUR CLAUSES of `Lettered.owedAt`
                                  (Honest/Rule.lean), and none of `Owed`'s other fields
  `lookupSimulatorNeverStops`     no part of a row has a stop: `rowStopAt` answers `none` everywhere

How to read them.
  * exact IS THE SPENDER'S HALF ALONE. The two blocks of coins that a part with a sumcheck spends
    are taken as uniform and independent of all that is fixed (Honest/SumLaw/SumExact.lean, head).
    That they are so in a run is the field fresh at the parts that OWN them: the senders of the
    segments' mask rows. By the written book (AtFullSide/K14/RawFactsWritten.lean) these are part 0
    of a place of the kind K1 at link 0, and part 0 of a place of the kind K2 at links 1 to 24: so
    a part of K2 for 48 of the fifty rows. NOTHING HERE PAYS THAT, AND IN THIS TREE NOTHING DOES:
    fresh at K2's part is a statement (`SwitchFresh`, Honest/K2/Fresh.lean) whose proof lies in no
    file of this tree; fresh at K1's part is proved under a test on the book
    (Johnson/SendSim/Seat/AtDescLots.lean) that is evaluated at no book of a proof file. UNTIL BOTH
    ARE PAID, exact AT A LOOKUP SAYS NOTHING OF A RUN.
  * WHAT IS TAKEN OF THE OWNER IS ITS fresh, NOT "THE STATE HOLDS NO COIN". The state before a
    lookup's part need not be free of the coins that the part spends: what the owner has shown
    stands among the rounds shown (by the design, its out-of-domain answer reads the mask row; not
    shown in these files). That what the owner shows is independent IN LAW of the entries that are
    lent is what the field fresh at the owner ASKS, once for each spender (the place and the number
    of the lookup's part), together with what the book gives to that part or to a part before it
    (`ProverCoinCounts.knownBy`, Honest/Frame.lean). It is meant to come from the row's pad. THIS FILE DOES
    NOT PROVE IT.
  * NO PART OF A LOOKUP READS WHAT AN EARLIER PART HAS SENT, of the same lookup or of any other
    place: of what stands in front its jobs read the challenges alone
    (`lookupRowReadsNothingShown`, LookupPartsReadNothingShown.lean). So the warning in the head of
    Honest/SumLaw/SumExact.lean on a job that reads an item sent under a coin which its part spends
    does not touch a lookup.
  * THAT NO TWO PARTS SPEND ONE COIN is in no statement here. At the book that the maker returns it
    is the seventh test of `ProverCoinCounts.clauses` (Honest/Frame.lean), which passes at every return
    (`atPure_tests`, Honest/AtPureLaw.lean). The rule that joins rows does not read that test: what
    bars a second spending there is the owner's fresh (Honest/Law/Rule/Row.lean, head).
  * PARTS BEHIND A LOOKUP MAY CARRY THE SAME COINS (Honest/Frame.lean, `Ahead.once`): those that
    close the lookup's linear claims. What ties what they carry to what the lookup has shown is
    their On: their authors' debt. A lookup's parts carry nothing.
  * fresh IS TRUE AND EMPTY here: a lookup's parts take no coin of their own.
  * On AND bud ARE "TRUE". So exact is proved at every state, at every `front` that agrees with the
    state on the rounds seen, and at every list of positions; and what `Owed` asks of On and bud is
    paid by `trivial`. The two count together (Honest/Law/OwedRule.lean, head, way 4). A test "On is
    false at a cheating front" or "bud is false at one position too many" cannot be met at "true".
    In its place stand two theorems: exact holds at such a front and at such positions too; and
    whatever On lets into `front`, no simulator of a row reads it: each reads its own coins alone
    (`lookupSimulatorReadsItsCoinsAlone`, LookupSimulatorReadsItsCoinsAlone.lean). A lookup sends no
    table.
  * `Good` IS AT A AND B "FALSE": its fields plays and acc are met for nothing. They are what the
    statements on completeness ask, and are not spoken of here.
  * THE TWO OTHER CLAUSES OF `Lettered.owedAt` (Honest/Rule.lean) ARE NOT SHOWN HERE. That the book
    lends a called part its empty carried block is generic (`PartsStand`,
    Honest/Law/StandsFile.lean). That the walk's state is there before a called part comes, in
    `file_owed_rows`, from `ready` and from the threads' debts: at the lookups' own fifty borders
    these are the lookups' authors' own to pay, in other files than these (that the rows play, what
    stands behind them, the exchange, what rides past; and that the book lends the rows their
    coins).

Empty or not: NOT SHOWN IN THIS FILE. Under the hypothesis `P5J.AtMgA` the rows are fifty and each
is seated; that anything meets the hypothesis is other files'. It follows at a set of public files
that is in scope, is read and passes the library's test `protocolDataWellFormed` (`P5J.head_of_live`,
Johnson/P5J/HeadOfLive.lean). That SOME files meet these three: the full-size public files
(`VerifierAndGoals.filesRead`, Johnson/Goal/Files/FilesReadProof.lean; `theLive_zFull`,
AtFullSide/Top/LiveAtFull.lean); the three are joined, with a return of the maker, in
E2E/Lookup/LookupSimulatorAtTheTerm.lean. `LookupsOwnNoCoin` at the book that `onlineProverFromPublicFiles` returns:
AtFullSide/Honest/K3/LookupSimulatorAtAnyFilling.lean.

What may be said of these sentences is not this file's to say.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. Under the hypothesis, at the first chain of the hypothesis: that a maker's return has this
chain, and these sentences at the return's own fields: LookupSimulatorHandIn.lean,
AtFullSide/Honest/K3/LookupSimulatorAtAnyFilling.lean; at the online prover:
E2E/Lookup/LookupSimulatorAtTheTerm.lean. At jobs right or wrong: nothing on what is sent. One part
at a time. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OnSaid
import Johnson.Desc.ProofFile.Honest.K3.Law.Good.K3RowStated
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExactKeptHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StandAtMember
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupRowIsExactAndFresh
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain Place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest.Small (ExactMember FreshMember exactAt_of_exact)
open Johnson.AtFull.Shape (face_ok_site)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

/-- **THE PREMISE ON THE BOOK**: by the book no part spends a coin of a part at a lookup's place. -/
def LookupsOwnNoCoin (Bk : ProverCoinCounts) (publicPart : Pub) : Prop :=
  ∀ s ∈ lookSites publicPart, ∀ (number : Nat) (spender : Addr),
    Bk.spentBy ⟨s.at_.place, number⟩ spender = []

variable {files : VerifierAndGoals.PublicFiles} {description : WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place} {V W X Pb : Type}

/-- **The lot has fifty rows.** -/
theorem lookupSimulatorRowsAreFifty
    (head : AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (F : Pub → Fill W) (ground : Ground) :
    ((lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).rows publicPart ground).length = 50 := by
  show ((lookSites publicPart).map fun s =>
    lookupSimulatorRow (V := V) (X := X) (Pb := Pb) (F publicPart) s).length = 50
  rw [List.length_map]
  exact sites_fifty_head head

/-- **Every row of the lot is seated at the first chain's flat list.** -/
theorem lookupSimulatorRowIsSeated
    (head : AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (F : Pub → Fill W) (ground : Ground) (falls : List (Fall TS)) (row : Unlettered V W X Pb)
    (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground) :
    ∃ σ : Side TS ProofFile.Cl V W X Pb,
      Side.seated firstChain.blocksInOrder row.place row.row falls = some σ := by
  obtain ⟨s, hs, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  exact seated_head head (rowPairs (F publicPart) s) falls s hs

/-- **At a seated side the declared rounds are the stages' own, and the side fits.** -/
theorem lookupSimulatorRowIsStated
    (head : AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (A : Fill W)
    (s : Site) (site : s ∈ lookSites publicPart) (falls : List (Fall TS))
    (σ : Side TS ProofFile.Cl V W X Pb)
    (seated : Side.seated firstChain.blocksInOrder s.at_.place (rowPairs A s) falls = some σ) :
    RowStated s.at_.face σ ∧ σ.fits = true ∧ σ.block.place = s.at_.place := by
  obtain ⟨Bs, base, O⟩ := head.laid.opened
  obtain ⟨b, hb, hbs⟩ := lot_of_site _ _ _ _ _ publicPart Bs base firstChain _ _ O s site
  obtain ⟨hf, _, _⟩ := block_of_seated _ firstChain.blocksInOrder s.at_.place falls σ seated
  have hm : σ.block ∈ firstChain.blocksInOrder := List.mem_of_find?_eq_some hf
  have hp : σ.block.place = s.at_.place := by simpa using List.find?_some hf
  have hmp : σ.block.place = b.place := hp.trans hbs.symm
  have hk : σ.block.planOk = true := IM.plan_flat O head.laid.planOk _ hm
  obtain ⟨_, e1, _, e3, e4⟩ :=
    site_block _ _ _ _ _ publicPart Bs base firstChain _ _ O s site b σ.block hb hbs hm hmp hk
  obtain ⟨_, g1, g2, _⟩ := memberAtSite _ _ _ _ _ publicPart Bs base firstChain _ _ O b hb σ.block
      hm hmp
  exact ⟨rowStated_of A s firstChain.blocksInOrder falls σ seated (s.p.entries.getD []) (g1.trans e3)
      (g2.trans e4)
      e1 (face_ok_site publicPart s site),
    fits_k3 (Bk := ⟨[], [], [], [], []⟩) A s (fun _ _ _ _ => False) (fun _ _ _ _ => False)
        firstChain.blocksInOrder
      falls σ seated (s.p.entries.getD []) (g1.trans e3) (g2.trans e4) e1 (face_ok_site publicPart s
          site),
    hp⟩

/-- **THE LOOKUPS' SIMULATOR IS EXACT: THE SPENDER'S HALF ALONE**: the field exact of `Good`,
without its hypothesis on the
opened columns, at every member of every row's side, at the row's own On and bud. The spender's half
alone: see the head. -/
theorem lookupSimulatorIsExactOverFreshMaskEntries
    (head : AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (φ : Face V W Pb)
    (F : Pub → Fill W) (ground : Ground) (chain firstTree : Nat) (falls : List (Fall TS))
    (row : Unlettered V W X Pb) (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground)
    (σ : Side TS ProofFile.Cl V W X Pb)
    (seated : Side.seated firstChain.blocksInOrder row.place row.row falls = some σ) :
    ∀ u ∈ σ.members, ExactMember φ σ chain firstTree row.On row.bud u := by
  obtain ⟨s, hs, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  exact lookupRowIsExact φ chain firstTree (F publicPart) s firstChain.blocksInOrder falls σ seated
    (lookupSimulatorRowIsStated head (F publicPart) s hs falls σ seated).1

/-- **THE LOOKUPS' SIMULATOR IS FRESH: TRUE AND EMPTY**: the field fresh of `Good` there. True and
empty: see the
head. Conditional on the premise on the book. -/
theorem lookupSimulatorIsFresh
    (head : AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (φ : Face V W Pb)
    (F : Pub → Fill W) (ground : Ground) (Bk : ProverCoinCounts) (order : List Place)
    (ownNoCoin : LookupsOwnNoCoin Bk publicPart) (falls : List (Fall TS))
    (row : Unlettered V W X Pb)
    (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground) (σ : Side TS ProofFile.Cl V W X Pb)
    (seated : Side.seated firstChain.blocksInOrder row.place row.row falls = some σ) :
    ∀ u ∈ σ.members, FreshMember φ σ Bk order row.bud u := by
  obtain ⟨s, hs, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  have hp := (lookupSimulatorRowIsStated head (F publicPart) s hs falls σ seated).2.2
  refine lookupRowIsFresh φ Bk order (F publicPart) s firstChain.blocksInOrder falls σ seated fun u _ p => ?_
  rw [hp]
  exact ownNoCoin s hs u.number p

/-- **`Good` AT EVERY ROW'S SIDE**, at every `pre`, at the row's own On and bud, at A and B "false":
what `hand_of_seated` (Honest/Thread/RowsMore.lean) takes. Conditional on the premise on the book.
-/
theorem lookupSimulatorIsGood
    (head : AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (φ : Face V W Pb)
    (F : Pub → Fill W) (ground : Ground) (Bk : ProverCoinCounts) (order : List Place)
    (ownNoCoin : LookupsOwnNoCoin Bk publicPart) (chain firstTree : Nat) (falls : List (Fall TS))
    (row : Unlettered V W X Pb) (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∀ σ, Side.seated firstChain.blocksInOrder row.place row.row falls = some σ →
      ∃ A' B', Good pre φ σ Bk order chain firstTree A' B' row.On row.bud := by
  intro σ seated
  have exactAll := lookupSimulatorIsExactOverFreshMaskEntries head φ F ground chain firstTree falls
      row inLot σ seated
  have freshAll := lookupSimulatorIsFresh head φ F ground Bk order ownNoCoin falls row inLot σ
      seated
  obtain ⟨s, hs, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  exact ⟨fun _ _ _ _ => False, fun _ _ _ _ => False,
    { fits := (lookupSimulatorRowIsStated head (F publicPart) s hs falls σ seated).2.1
      plays := fun _ _ _ _ _ never => never.elim
      acc := fun _ _ _ _ _ never => never.elim
      exact := fun u member => exactAt_of_exact pre (exactAll u member)
      fresh := freshAll }⟩

/-- **On AND bud HOLD EVERYWHERE**: On follows from every thread and every `Said`, at every row as
laid; bud holds at every number, challenges and positions. No premise: both are "true". Two of the
four clauses of `Lettered.owedAt`: see the head. -/
theorem lookupOnAndBudHoldEverywhere {Bk : ProverCoinCounts} {S Cl : Type} (F : Pub → Fill W) (publicPart : Pub)
    (ground : Ground)
    (row : Unlettered V W X Pb) (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground) :
    (∀ (thread : Thread Bk S Cl V W X Pb) (said : Nat → Coins Bk → Mid W X → Prop)
        (threads : W → Thread Bk S Cl V W X Pb) (saids : W → Nat → Coins Bk → Mid W X → Prop)
        (blocks : List (Block S Cl)) (border : Nat) (depth : Nat → Nat → Nat),
        OnFromS thread said (row.lay threads saids blocks) border depth) ∧
      ∀ (number : Nat) (challenges : List Fmt.Drawn) (positions : List (List (List Nat))),
        row.bud number challenges positions :=
  ⟨fun _ _ _ _ _ _ _ _ _ u _ _ m _ ca front _ _ _ =>
      lookupSimulatorOnHolds F publicPart ground row inLot u ca m front,
    lookupSimulatorBudHolds F publicPart ground row inLot⟩

/-- A list of parts whose stops never answer stops nowhere. -/
theorem neverStopsOfNoStops : ∀ (parts : List (Part V W X)), NoStops parts →
    ∀ (v : Option V) (before own : List Fmt.Drawn), rowStopAt v parts before own = none
  | [], _, _, _, _ => rfl
  | p :: ps, h, v, before, own => by
    show (p.stopAt v before (own.take p.moves.length)).or
      (rowStopAt v ps (before ++ own.take p.moves.length) (own.drop p.moves.length)) = none
    rw [stopAt_none p (h p List.mem_cons_self).1 (h p List.mem_cons_self).2,
      neverStopsOfNoStops ps fun q hq => h q (List.mem_cons_of_mem _ hq)]
    rfl

/-- **NO PART OF A ROW HAS A STOP**, public or private. No premise. -/
theorem lookupSimulatorNeverStops (F : Pub → Fill W) (publicPart : Pub) (ground : Ground)
    (row : Unlettered V W X Pb) (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground)
    (v : Option V)
    (before own : List Fmt.Drawn) : rowStopAt v row.half.parts before own = none := by
  obtain ⟨s, _, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  rw [lookupSimulatorRowHalf]
  refine neverStopsOfNoStops _ (fun q hq => ?_) v before own
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
  have h := noStops_old (V := Unit) theReads ((F publicPart).jobs s).asked s.at_ p hp
  exact ⟨h.1, fun _ f o => h.2 () f o⟩

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.LookupsOwnNoCoin
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorRowsAreFifty
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorRowIsSeated
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorRowIsStated
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorIsExactOverFreshMaskEntries
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorIsFresh
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorIsGood
#print axioms ProofFile.Honest.K3.Term.lookupOnAndBudHoldEverywhere
#print axioms ProofFile.Honest.K3.Term.neverStopsOfNoStops
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorNeverStops
