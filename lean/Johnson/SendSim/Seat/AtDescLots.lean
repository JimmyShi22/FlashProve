-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescLots.lean: wherever the maker returns (IM.Open), at each job of the lists
lotJobs and wJobs (the first segment's opening, each segment's reads and digits, the request's own
table) the description has a member. The side of the honest sender and its simulator there satisfies
the field fits and ExactAt, and the field fresh if the book is clear (BookClearAny). It claims no
property of the protocol: not hiding, not zero knowledge.
Terms of the files in this folder that point here: the paragraph "Terms" below. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has. The premise of the main statements is IM.Open, which holds wherever the maker of
the proof file's description returns F at three public files (IM.seat_open).
  Spec.fieldsAtLots   The main statement; proved as fieldsAtLots in AtDescLotsProof.lean. It speaks
                      of every job J of the two lists lotJobs and wJobs. In the scope of the
                      release's goals, at the format's second hash function, these are 52 entries
                      (jobs_52_in_scope, LotCount.lean), at different places (jobPlaces_nodup,
                      LotPlaces.lean). (1) The first chain's list of sub-protocols has a member at
                      J's place. (2) Every side that Side.seated returns there for our row has fits
                      and exact; no book is mentioned. (3) For every book and order at which the
                      book is clear at J's sender, that side has fresh. (At the example sets part
                      (3) has content at two jobs alone: Limits.) It is stated for every way to read
                      the input (wit), every numbering of new messages (no) and all data (D); which
                      values a prover takes is said in no file that this folder imports.
  seat_of_lots        Proved here. Part (1) in the form of the rule's premise seat₁, at every row of
                      our two lots (sendLots) at the ground Bs.G₀.
  Spec.handAtLots     Parts (2) and (3) in the form that the rule's premise hand₁ asks of one row;
                      proved as handAtLots in AtDescLotsProof.lean. For every job J, if the book is
                      clear at J's sender, then every side of our row, with the rule's predicates
                      substituted (Unlettered.lay), has Good for some A₁ and B₁. It says no more
                      than the main statement; the parameters T and Sd are not read.
  fieldsAtLots_of     Spec.sendExactAt and Spec.sendFreshAtWide imply Spec.fieldsAtLots. Both are
                      theorems: sendExactAt (Johnson/SendSim/At/ExactAt.lean) and sendFreshAtWide
                      (Johnson/SendSim/Seat/HandedWideProofs.lean).
  handAtLots_of_fields   Spec.fieldsAtLots implies Spec.handAtLots.
  hand_of_lots        Spec.handAtLots implies the rule's premise hand₁ at every row of our two lots,
                      if the book is clear at every job's sender.
  fieldsAtFirst_of_lots  Spec.fieldsAtLots implies Spec.fieldsAtFirst (AtDescHand.lean), without
                         using that statement's two premises on the public part.

Terms.
  description   F : FileDescription, the value of the maker ProofFile.onlineDescription at three public files (policy.txt,
                layout.txt, KL.bin), where it returns one and does not refuse: three chains of
                sub-protocols (Block). F.first.blocksInOrder is the first chain as one list.
  IM.Open       (Johnson/IMR/SeatOpen.lean) names what onlineDescription made on the way to F: the public
                part Z, read off the files; the ground Bs.G₀, the segments' data computed from Z at
                a request of zeros (IM.Open.blank); the first chain c. IM.seat_open derives it from
                ProofFile.onlineDescription o pol lay KL = .ok F.
  place         the address of a sub-protocol (Place): its chain; its segment (Lean: link), one of
                the consecutive sections of the first chain, one for each part of the model; its
                piece, the sub-protocol's number in the segment; its kind.
  kind, lot     K1 is one of the kinds of sub-protocol in which new tables are sent; K2 (a code
                switch) and K12 (a proximity test) send tables too. A lot (Lot) is a named list of
                sub-protocols that the maker puts at their places. K1's own lot (ProofFile.k1Pure) has the
                first segment's opening (its first sub-protocol; every other segment opens with a
                code switch) and each segment's two later sendings: its reads, in front of the
                segment's smallness test, and its digits, behind that test's round
                (Johnson/Desc/First/Driver/Chain.lean, head). The sending of the request's own table
                comes behind the last segment, where the pending claims on the weight table have
                been joined. The protocol calls that table W; it is not the type variable W below.
                It is of the kind K1 and is in the lot K13.lot4.
  job           SendJob: what the honest sender is given at one place: the place's public numbers P,
                the number first of its first new message, the data, and ride: which of its messages
                is the fresh mask table of a later folding step of a proximity test, sent along
                ahead of that step (Ride: two public numbers k and h; the table itself is made of
                the sender's coins).
  mask row      a row of a message that holds random values alone (OracleShape.maskRows). Its free
                entries are those that the sending's own answers do not use (freeMaskEntries,
                OnBytes/Iop/Send.lean); later parts may spend them.
  lotJobs, wJobs
                (Lot.lean, LotW.lean) the jobs at the places of these two lots, as the honest sides
                lotSide (Johnson/Desc/ProofFile/Honest/K1/PlaceJob.lean) and wSide (PlaceW.lean
                beside it) of these lots have them: sendLots_toHLot. They are terms of Z, Bs.G₀, no
                and D. No prover of the whole chain that takes these two sides is among the files
                that this folder imports.
  row           an honest part paired with its simulator. jobRow wit J is our row at J: the sender
                sendPart at J, its data read through wit, with the simulator sendSim. That simulator
                is built from J.P, J.first and J.ride alone, which do not depend on the data
                (jobs_public, LotsPublic.lean). Of what it is given when it runs it reads the
                challenges, the positions and its own coins.
  side          Side: a sub-protocol of the description with a row. Side.seated bs a row fs returns
                the side at the first member of bs at the place a.
  Seated        (Johnson/SendSim/At/Sim.lean) the side's row is our sender alone with its simulator;
                the side fits; its rounds and oracle messages agree with the sender's in what a run
                reads; the challenges that its rounds can sample are just the sender's seeds, and no
                seed's factor is 0.
  discloses     what a part discloses (Shown, Johnson/Desc/ProofFile/Honest/Frame.lean) is its items
                in the clear and the opened columns of its tables.
  Good          the structure of Johnson/Desc/ProofFile/Honest/Side.lean (lean/GLOSSARY.md has
                another structure under that name). It has a parameter pre, a list of declared
                rounds, which its field exact alone reads. fits says that the row has one move for
                each round, and that each simulator names its part's address. exact says that what a
                part discloses, over its own coins and those it spends, at fixed runs that it
                carries, under the premises of ExactAt (Johnson/SendSim/At/Sim.lean) and one more,
                that the columns handed to the parts (m.opened) are what the front holds for the
                reads of pre, has the distribution of its simulator's output. fresh says that, at
                every fixing of what the part is given, the coins that an address spends are uniform
                and independent of what the part discloses and of its other coins that this address,
                or a part in front of it, is given. Of its other two fields, plays speaks of the
                row's run and acc of the verifier's acceptance.
  book          ProverCoinCounts: public data beside a description. Its entries say which runs of a part's coins
                a later part is given too. An entry either spends the run (meant for masking a
                value) or carries it (meant for computing on it). ord orders the places.
  clear         BookClearAny P ride Bk ord a (Johnson/SendSim/At/BookWide.lean): every entry on the
                sender's coins is within the sender's number of coins, and each address p spends
                nothing of them, or free mask entries of sampled messages that are not sent along
                (of the extension field alone, in runs that are pairwise apart), or all coefficients
                of one table that is sent along. In the last two cases it also says what p and the
                parts in front of p (by ord) are not given: none of the spent coins; no pad of an
                answer of a message that holds a spent entry; no tail coin of that entry's row or of
                the last mask row; no tail coin of any row of the table that is sent along
                (MaskSpender, Johnson/SendSim/At/Fresh.lean; FoldSpenderAny, FoldAny.lean). Without
                these the equation fails at small examples (said here without a theorem).
  face          Face: how a chain's parts are given their input, and which part of it is public.
                There are two: .own in the first and second chain, .shared in the shared chain.
  example sets  the two sets of public files that the library stores, a small one and the full-size
                one in the goals' scope (VerifierAndGoals.InScope).
  the rule      file_owed_rows (Johnson/Desc/ProofFile/Honest/Thread/Rows.lean). Of every row of the
                first chain it asks seat₁ (a member of the chain is at the row's place) and hand₁
                (every side of the row has Good for some A' and B'). Its conclusion Owed is a
                structure of premises. From it and more premises the frame's files derive, at each
                part's cell of a run, the equations of exact and fresh again (cells₁,
                Johnson/Desc/ProofFile/Honest/Law/Rule/FileCells.lean). No file that this folder
                imports concludes that a whole run's view has the distribution of the simulators run
                in a row.

How it fits. The statements rest on AtDescStands.lean (a member is at the place; the side is Seated)
and on Spec.sendExactAt and Spec.sendFreshAtWide, which speak of every Seated side. Of a row's Good
the rule reads fits, exact and fresh alone (good_at_pair,
Johnson/Desc/ProofFile/Honest/Thread/Hands.lean). Meant as steps toward index privacy
(Johnson/WholeKey/Statement.lean); nothing in this folder derives index privacy from them. Not one
of the release's goal statements.

The other names.
  jobRow, sendLots       our row at a job; our two lots, under the names of lotSide and wSide.
  sendLots_toHLot        without the simulators, our two lots are lotSide and wSide.
  row_of_lots            every row of our two lots is jobRow at a job of the two lists.
  clearAny_of_no_entry   a book without entries is clear at every sender. So the premise on the book
                         is satisfiable at every job; such a book lends nothing.
  budAtLots              for any list of jobs: if the test readsWithinB
                         (Johnson/SendSim/Seat/ReadsTest.lean) accepts at each job's place, then our
                         clause of the rule's premise on queried positions (BudClause, Bud.lean)
                         holds at each job.

Limits. These are also the limits of the other files that point here.
At the senders of the two lists the premise on the book is proved in this folder at books without
entries (clearAny_of_no_entry) and, at the later jobs, where laterNoMaskB accepts, at every book in
which the owner's entries are within its coins and nobody spends one (clear_at_later,
LotsTestTie.lean). With a coin spent it is proved at these senders, in this folder, at no book. At
the book that the maker returns it is proved at the opening's sender (`clear_at_opening`,
AtFullSide/K1/BookAtOpening.lean; its premises, and the rest: the table of premises in
Johnson/SendSim/Defs.lean, "the book is clear"). In the rule the book is a parameter that the caller
picks. A narrower form of the premise (bookClearB, Johnson/SendSim/At/BookTest.lean) was checked by
running the compiled test, outside Lean's kernel, at a book that a program outside this library
makes of an example set's files. It accepts at the opening's sender at both example sets, and at the
ten later jobs of the small set, where no address spends a coin. At the full-size set's 50 later
jobs and at the request's own table it has not been run. At that table the narrower form cannot
accept at the full size if a spender of the table that is sent along is listed: that table has two
rows (said here without a theorem), and the narrower form asks one (FoldSpender,
Johnson/SendSim/At/Fresh.lean). That the book is the right one for an honest run is neither a
premise nor a conclusion. An entry that spends no coin, alone at its spender or beside entries of
free mask entries, passes the premise if it starts within the sender's coins (by inspection, not
proved); it is not rejected as malformed.
Oracle messages alone. What is disclosed holds no root, no nonce, no salt and no proof of work:
these are the compiler's (Johnson/Desc/ProofFile/Honest/Frame.lean, Limits). So exact and fresh say
nothing about the hashed proof.
Not every sending of the first chain. By a count over the written list of full-size sendings
(Johnson/G/SendsLit.lean; by inspection, not proved) that chain has 82 sendings under the entry
"SEND seed": these 52, 25 of the kind K2 (every segment but the first opens with a code switch; one
more is behind the last) and five inside K12. Each of those 30 has a mask row; of these 52 two have.
They are not covered. A fold's own fresh mask that is sent under another entry is in neither of that
file's lists (its Limits), so 82 is a lower bound.
That the two lists hold all places of the kind K1 on the first chain is by inspection of the
driver's list of kinds (kindsBeforeBatching, backKinds, Johnson/Desc/First/Driver/Chain.lean), not proved.
At the two example sets part (3) has content at two jobs alone, the opening's and the one at the
request's own table. At a segment's reads and digits no table is sent along (later_no_ride,
FitsAtLots.lean) and, at the library's full-size shape, no message has a mask row
(shapeLaterNoMask_full, LotsTestTie.lean, checked by evaluation in Lean's kernel; at the small set
by inspection, not proved). In the goals' scope, where the library's gate accepts, the request's
shape is this value (likeFull_in_scope, Johnson/HB/LLHARD/PlanInScope.lean, as ReadsAtLive.lean
calls it). A book is then clear at that sender exactly if the sender's entries are within its number
of coins and no address spends a coin of it (clearAny_iff_nothing,
Johnson/SendSim/At/ClearNothing.lean; clear_at_later_open, LotsTestTie.lean). fresh then holds
trivially: proved where no entry spends (freshAtLots_idle, AtDescLotsSpenders.lean; nothingSpent,
Johnson/SendSim/At/NothingSpent.lean); by inspection, not proved, where entries of length 0 do.
exact alone does not catch every fault of a sender that fresh catches (the head of
Johnson/SendSim/At/ExactAt.lean names two), so part (2) is not to be quoted without part (3).
That a job fits its place (sendFits) is no premise. Where it does not fit, what is disclosed is the
error value on both sides of both equations: exact then says nothing, and fresh then speaks of the
sender's coins alone. Where F passes its own tests on the plan, every job of the two lists fits
(fits_at_lots_plan, RideFitsW.lean; on the way: FitsAtLots.lean, RideFits.lean). That F passes these
tests is a premise of the rule.
Which table is sent along, and at which k and h, is a term of the public part (firstFold, wFold).
RideTies.lean ties these numbers to the verifier's sub-protocol that is made to fold with the table.
At the request's own table, where F passes its tests on the plan, they are those of the first stage
of the proximity test on the request's own group (w_ride_tie, w_member_tie). At the opening they are
those of the closing of segment 0 (first_ride_tie; at the member under two more public premises,
first_member_tie). The ties reach the verifier's sub-protocols alone: among the files that this
folder imports there is no honest part of the kinds K10 and K12 and no made book, so nothing rules
out a book that is clear while it names another part, or none, as the spender. With a smaller k the
table would hold zeros where random values are due; exact would still hold; a book that lets the
folding step spend the whole table would fail the premise on the book (argued, not proved).
What the rule still asks. Its premises range over every row of the first chain; this file gives
seat₁ and hand₁ at the rows of our two lots. The rule asks hand₁ at the face .own, the order orderOf
F, chain number 0, first-tree number 0, its own pre (preOf at the row's place) and the book that its
caller picks. hand_of_lots holds at every such choice, so its premise on the book is owed at that
book and order, at all jobs at once. Row by row the rule also asks its premise on queried positions
and that the row's condition On follows from the thread (AtDescLotsRule.lean has both at our rows:
the first if the test lotsReadsB accepts, the second outright). Member by member it asks that each
part can be played, what is passed on and that the verifier accepts (OwesS, SaidNext, YesS, Sits),
among others (AtDescLotsRule.lean, Limits): those are not this folder's. The rule names no ground:
whoever takes its rows at another ground than Bs.G₀ must connect the two.
Good has five fields. plays and acc hold here vacuously: in the proof A₁ and B₁ are the predicates
that never hold (good_of_fields).
One sender at a time: nothing is said on the coins of two senders together. The book and the order
are free: a coin that two addresses spend is caught only as far as ord orders them.
The bound on queried positions (budAt, Johnson/SendSim/At/Sim.lean) is a premise inside exact and
fresh. They also speak only of lists of challenges that the member's two rounds can sample; the
kind's own two rounds can sample one (draws_some, Johnson/SendSim/At/DrawsSome.lean). exact also
speaks only of a front whose rounds are those that the part has been given (m.seen = front.seen) and
that has a column for every read; Good's field exact has one premise more, on the opened columns
(ExactAt's docstring, Johnson/SendSim/At/Sim.lean). In the goals' scope, wherever the library's gate
accepts, the
positions that the description's rounds read of these senders' trees meet the bound (bud_of_live,
ReadsAtLive.lean).
The premise on the book has no clause for a spender of the coins of a message that has main rows and
no sample (such a message is made of coins alone). At the two example sets no job of the two lists
has such a message (by inspection, not proved).
Under the name of K1's lot there is a second honest side, firstLot; a description takes one of the
two (PlaceJob.lean, Limits). At the opening the number that no gives must be 0 for the sender there
to send what that other side's job sends. Which honest sides a prover of the whole chain takes is
said in no file that this folder imports. A prover that takes no side at the request's own table has
no half beside our row there.
The first chain alone. By the same count this kind has 60 sendings under that entry at the full
size: beside these 52, two in the shared chain, five in the key file's description and one in the
description of a copy's file (the list calls it the entry file). Those eight are not covered.
That the maker returns at given public files, and that F passes its tests on the plan, is proved in
this folder only where the gate accepts: returns_of_live (AtDesc.lean) and plan_of_live
(ReadsAtLive.lean) derive them, by the library's pseat_name
(Johnson/Goal/Description/ProofSeat.lean), from the library's gate FlashProve.protocolDataWellFormed. At the
full-size files as Ladder/Stored.lean spells them, the side library proves both with no premise
(proofPlanOk_zFull, AtFullSide/Top/PlanOkAtFull.lean, with that file's limits); many closed facts
beneath it are checked by evaluation in Lean's kernel.
-/
import Johnson.SendSim.Seat.AtDescOwn
import Johnson.SendSim.Seat.ReadsTestTie

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {V W X Xi Pb : Type}

/-- Our row at a job: the part that sends, at the job read through wit, with its simulator. -/
abbrev jobRow (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) : Unlettered V W X Pb :=
  sendRow J.P.place (jobOver J wit)

/-- Our two lots, under the names of the honest sides lotSide and wSide. -/
def sendLots (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) : List (SLot V W X Pb) :=
  [sendLot "K1: the first segment's opening, each link's reads and digits" wit
      (lotJobs (X := X) no D),
    sendLot "K1 and K13: W's commitment, the request's own group and the row (Eval)" wit
      (wJobs (X := X) no D)]

/-- Without the simulators, our two lots are the honest sides lotSide and wSide of these lots. -/
theorem sendLots_toHLot (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    (sendLots (V := V) (X := X) (Pb := Pb) wit no D).map SLot.toHLot =
      [lotSide wit no D, wSide wit no D] := by
  show [_, _] = _
  rw [sendLot_is_lotSide, sendLot_is_wSide]

/-- Every row of our two lots is our row at a job of the two lists. -/
theorem row_of_lots (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    {r : Unlettered V W X Pb} (h : r ∈ rowsOfLots Z G (sendLots (X := X) wit no D)) :
    ∃ J ∈ lotJobs (X := X) no D Z G ++ wJobs (X := X) no D Z G, r = jobRow wit J := by
  obtain ⟨l, hl, hr⟩ := List.mem_flatMap.1 h
  unfold sendLots at hl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl
  · have hr' : r ∈ (lotJobs (X := X) no D Z G).map fun J => jobRow wit J := hr
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr'
    exact ⟨J, List.mem_append_left _ hJ, rfl⟩
  · have hr' : r ∈ (wJobs (X := X) no D Z G).map fun J => jobRow wit J := hr
    obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr'
    exact ⟨J, List.mem_append_right _ hJ, rfl⟩

/-- The main statement. Statement only; proved as fieldsAtLots in AtDescLotsProof.lean. Where the
description's maker returns, for every job of the two lots: the first chain's list has a member at
the job's place; every side that Side.seated returns there for our row has fits and exact; and if a
book is clear at that sender, the side has fresh at that book. The bound on queried positions is a
premise inside exact and fresh. At the example sets the last part has content at two jobs alone (the
head's Limits). -/
def Spec.fieldsAtLots : Prop :=
  ∀ (V W X Xi Pb : Type) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (_ : IM.Open o pol lay KL F Z Bs base c A B) (φ : Face V W Pb) (wit : W → PlaceIn Xi)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (chain ft : Nat)
    (fs : List (Fall F.S₁)),
    ∀ J ∈ lotJobs (X := X) no D Z Bs.G₀ ++ wJobs (X := X) no D Z Bs.G₀,
      F.first.blocksInOrder.any (fun b => b.place == (jobRow (V := V) (Pb := Pb) wit J).place) = true ∧
      ∀ σ : Side F.S₁ F.Cl V W X Pb, Side.seated F.first.blocksInOrder
          (jobRow (V := V) (Pb := Pb) wit J).place (jobRow wit J).row fs = some σ →
        σ.fits = true ∧
          ExactAt φ σ chain ft (jobRow (V := V) (Pb := Pb) wit J).On
            (jobRow (V := V) (Pb := Pb) wit J).bud ∧
          ∀ (Bk : ProverCoinCounts) (ord : List Place), BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
            FreshAt φ σ Bk ord (jobRow (V := V) (Pb := Pb) wit J).bud

/-- Statement only; proved as handAtLots in AtDescLotsProof.lean. Parts (2) and (3) of the main
statement in the form that the rule asks of one row. Where the description's maker returns, for
every job of the two lots: if the book is clear at that sender, every side of our row, with the
rule's predicates substituted, has the structure Good for some A₁ and B₁.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
def Spec.handAtLots : Prop :=
  ∀ (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (V W X Xi Pb : Type) (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription ProofFile.Inst)
    (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
    (_ : IM.Open o pol lay KL F Z Bs base c A B) (φ : Face V W Pb) (wit : W → PlaceIn Xi)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place)
    (chain ft : Nat) (T : W → Thread Bk F.S₁ F.Cl V W X Pb)
    (Sd : W → Nat → Coins Bk → Mid W X → Prop) (fs : List (Fall F.S₁)),
    ∀ J ∈ lotJobs (X := X) no D Z Bs.G₀ ++ wJobs (X := X) no D Z Bs.G₀,
      BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩ →
      ∀ σ, ((jobRow (V := V) (Pb := Pb) wit J).lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs =
          some σ →
        ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ ((jobRow wit J).lay T Sd F.first.blocksInOrder).On
          ((jobRow wit J).lay T Sd F.first.blocksInOrder).bud

/-- Spec.sendExactAt and Spec.sendFreshAtWide imply Spec.fieldsAtLots. -/
theorem fieldsAtLots_of (He : At.Spec.sendExactAt) (Hf : At.Spec.sendFreshAtWide) :
    Spec.fieldsAtLots := by
  intro V W X Xi Pb o pol lay KL F Z Bs base c A B O φ wit no D chain ft fs J hJ
  refine ⟨seat_at_job O no D hJ, fun σ hσ => ?_⟩
  obtain ⟨h1, h2, h3⟩ := fields_of_seated He Hf φ (seatedAt_job O wit no D hJ hσ) chain ft
  exact ⟨h1, h2, fun Bk ord hB => h3 Bk ord (by rw [place_of_seated hσ]; exact hB)⟩

/-- Spec.fieldsAtLots implies Spec.handAtLots. -/
theorem handAtLots_of_fields (H : Spec.fieldsAtLots) : Spec.handAtLots := by
  intro _ V W X Xi Pb o pol lay KL F Z Bs base c A B O φ wit no D Bk ord chain ft T Sd fs J hJ hB σ
    hσ
  obtain ⟨-, h⟩ := H V W X Xi Pb o pol lay KL F Z Bs base c A B O φ wit no D chain ft fs J hJ
  obtain ⟨hf, he, hfr⟩ := h σ hσ
  exact ⟨_, _, good_of_fields hf he (hfr Bk ord hB)⟩

/-- **Where the description's maker returns: the rule's premise on a row's place, at every row of
our two lots.** -/
theorem seat_of_lots {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) :
    ∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      F.first.blocksInOrder.any (fun b => b.place == r.place) = true := by
  intro r hr
  obtain ⟨J, hJ, rfl⟩ := row_of_lots wit no D Z Bs.G₀ hr
  exact seat_at_job O no D hJ

/-- Where the description's maker returns: the rule's premise on a row's side, at every row of our
two lots, if the book is clear at every job's sender. The premise H is proved as handAtLots in
AtDescLotsProof.lean.
pre is tied to no description; of Good's fields exact alone reads it, and at each pre that field
says no more than ExactAt. -/
theorem hand_of_lots {pre : List (Nat × Nat × List Fmt.DeclaredRound)}
    (H : Spec.handAtLots) {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block First.S ProofFile.Cl)} {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    (φ : Face V W Pb) (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) (Bk : ProverCoinCounts) (ord : List Place) (chain ft : Nat)
    (T : W → Thread Bk F.S₁ F.Cl V W X Pb) (Sd : W → Nat → Coins Bk → Mid W X → Prop)
    (fs : List (Fall F.S₁))
    (hB : ∀ J ∈ lotJobs (X := X) no D Z Bs.G₀ ++ wJobs (X := X) no D Z Bs.G₀,
      BookClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩) :
    ∀ r ∈ rowsOfLots Z Bs.G₀ (sendLots (V := V) (X := X) (Pb := Pb) wit no D),
      ∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
        ∃ A₁ B₁, Good pre φ σ Bk ord chain ft A₁ B₁ (r.lay T Sd F.first.blocksInOrder).On
          (r.lay T Sd F.first.blocksInOrder).bud := by
  intro r hr
  obtain ⟨J, hJ, rfl⟩ := row_of_lots wit no D Z Bs.G₀ hr
  exact H pre V W X Xi Pb o pol lay KL F Z Bs base c A B O φ wit no D Bk ord chain ft T Sd fs J hJ
    (hB J hJ)

/-- A book without entries is clear at every sender. -/
theorem clearAny_of_no_entry (P : K1.Par) (ride : Nat → Option Ride) {Bk : ProverCoinCounts}
    (ord : List Place) (a : Addr) (h : Bk.ahead = []) : BookClearAny P ride Bk ord a :=
  ⟨fun e he => (by rw [h] at he; cases he),
    fun _ => Or.inl (spentBy_nil_of_not (by rw [h]; exact List.not_mem_nil))⟩

/-- The main statement gives the earlier statement at the opening, and does not use that statement's
two premises on the public part. -/
theorem fieldsAtFirst_of_lots (H : Spec.fieldsAtLots) : Spec.fieldsAtFirst := by
  intro V W X Xi Pb o pol lay KL F Z Bs base c A B O _ _ _ φ wit first D Bk ord chain ft fs hB
  obtain ⟨hs, h⟩ := H V W X Xi Pb o pol lay KL F Z Bs base c A B O φ wit (fun _ => first)
    (fun _ _ => D) chain ft fs (openJob (X := X) Z Bs.G₀ first D)
    (List.mem_append_left _ (List.mem_cons_self ..))
  refine ⟨?_, fun σ hσ => ?_⟩
  · obtain ⟨m, hm, hp⟩ := List.any_eq_true.1 hs
    exact seated_of_member _ fs ⟨m, hm, beq_iff_eq.1 hp⟩
  · obtain ⟨hf, he, hfr⟩ := h σ hσ
    exact ⟨hf, he, hfr Bk ord hB⟩

/-- For any list of jobs: if the test on the description's queries accepts at each job's place, our
clause of the rule's premise on queried positions holds at each job. -/
theorem budAtLots (F : FileDescription ProofFile.Inst) (wit : W → PlaceIn Xi)
    (Js : List (SendJob (PlaceIn Xi) X))
    (h : ∀ J ∈ Js, ∀ pre b t, F.first.blocksInOrder = pre ++ b :: t → b.place = J.P.place →
      readsWithinB F J.P (treesOf F.first.blocksInOrder pre) = true) :
    ∀ J ∈ Js, BudClause (V := V) (Pb := Pb) F J.P.place (jobOver J wit) :=
  fun J hJ => budClause_of_light F J.P.place (jobOver J wit) (h J hJ)

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.sendLots_toHLot
#print axioms OnBytes.SendSim.Seat.row_of_lots
#print axioms OnBytes.SendSim.Seat.fieldsAtLots_of
#print axioms OnBytes.SendSim.Seat.handAtLots_of_fields
#print axioms OnBytes.SendSim.Seat.seat_of_lots
#print axioms OnBytes.SendSim.Seat.hand_of_lots
#print axioms OnBytes.SendSim.Seat.clearAny_of_no_entry
#print axioms OnBytes.SendSim.Seat.fieldsAtFirst_of_lots
#print axioms OnBytes.SendSim.Seat.budAtLots
#print axioms OnBytes.SendSim.Seat.jobRow
#print axioms OnBytes.SendSim.Seat.sendLots
#print axioms OnBytes.SendSim.Seat.Spec.fieldsAtLots
#print axioms OnBytes.SendSim.Seat.Spec.handAtLots
