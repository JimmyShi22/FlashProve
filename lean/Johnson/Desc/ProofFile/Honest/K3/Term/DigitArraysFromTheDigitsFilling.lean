-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT, UNDER THE LIBRARY's HEAD ON THE PUBLIC INPUT.
Johnson/Desc/ProofFile/Honest/K3/Term/DigitArraysFromTheDigitsFilling.lean: the honest side of the
kind "lookup" (K3): THE NAMED PREMISE `ScriptHoldsTheDigitArrays`
(Term/ScriptHoldsTheHonestValues.lean) AS THE END OF A LEMMA: from one sentence on the `Script`'s
field `msg` alone, one named premise on public data, and the head (`P5J.AtMgA`). Two definitions
(forms of premises), one closed test with its control, theorems.

Why. The named premise speaks through the lookup's own reader of the witness (`digMu`: the written
list of arrays, the seats, the pad, the member's number). Whoever lays the `Script`'s message that
holds a link's arrays ZZ and BZ knows the frame's filling of that message (`K1.digitsFill`,
Honest/K1/LotFill.lean), not that reader. So the sentence that is asked there is cut on
`Q.msg`, in the frame's letters; the reader's half is public and is shown here.

  `ScriptLaysTheFillingAtTheLink`       THE SENTENCE ON THE SCRIPT, general in the filling and its
                                        seat
  `PublicDataServeTheDigitsAtTheLink`   THE PUBLIC PREMISE on the ground that the filling reads
  `digitArraysAddressesAreFound`        from the head: all tau × 2 mz addresses of ZZ and all
                                        32 × bzColumns addresses of BZ are entries of the place's
                                        list
  `digitArraysBearTheirNames`           from the head: these two arrays bear (link, "ZZ"), (link,
                                        "BZ")
  `ownArrayEntryIsSeatedAtTheDigits`    from the head: the array, the layout's place, the seat, in
                                        the main rows, inside, off the pad; the member's number
  `ownMessageBearsThePlansNumber`       from the head: that number is `P5J.At.num Zp link message`
  `digitsReadingIsTheMessagesEntry`     general: the caller's reading at such an entry is
                                        `Wit.msg`'s
  `digitsFillingAnswersTheCounts`, `digitsFillingAnswersTheDigits`   what the filling's total call
                                        answers at the layout's place of an entry of BZ, of ZZ
  `digitArraysFromTheDigitsFilling`     THE END
  Tools: `takeWhileKeepsItsEntries`, `fillingAnswerSaysItLays`, `joinedFillingAnswersAsTheFirst`,
  `joinedFillingAnswersAsTheSecond`, `sampledEntriesOfAFirstStretch`,
  `countsArrayIsNamedWhereItIsDeclared`; the closed test
  `ownMessagesBearTheirNumbersAtWrittenValues`, that it accepts, and a control that it can refuse.

WHY THE TOTAL CALL `RowData.at_`, NOT THE CALL THAT ASKS FIRST. The kind K5's form `LaysFilling`
(Honest/K5/Law/LaysFilling.lean) speaks through `RowData.ask`, which refuses where the filling's
`ready` says no. At the digits `ready` reads the challenges: the round must have sampled just as
many entries as the digits read, each of them -1, 0 or 1 (`BzAt.ready`,
Johnson/HonestTrace/BZVals.lean; `zzVals`, Honest/K8/ZzData.lean). The named premise speaks at EVERY
list of at least `challengesHeard` challenges. At a list of another form a sentence through `ask`
says nothing of `Q.msg`, and the end could not follow. The total call is what the sender's job is
handed (`placeJob`'s field data is `forSend`, Honest/K1/PlaceJob.lean).

How. `K3Asks.asks_digB` (the verifier's own entry test on the digits, under the head) with
`findJ_cell`, `cell_resolves`; `digAt_is` (Johnson/Desc/First/Look/DigitsShapeAt.lean);
`IM.Own.zz_of_made`, `IM.Own.of_made` (Johnson/IMR/ZzNamed.lean, OwnOfMade.lean); `Q38.j_tl_built`
(Johnson/HB/LLHARD/Q38J/ZzBuilt.lean); `laidAt_room`, `padB_of_room` (Honest/Law/LaysRoom.lean);
`K2Ties.at_written` (Johnson/Top/H0/K2Ties/WrittenAt.lean) with `P5T.arrOf_is_num`;
`K5.laidData_at` (Honest/K5/Law/WayBackFill.lean); `K1.over_left`, `over_right`, `not_lays`
(Honest/K1/PlaceSent.lean); `bzValsAt_val`, `zzVals_val`, `drawn_of_sampled` (Honest/K3/BzTie.lean);
`laidBZ_digitsOf` (Johnson/HonestTrace/DigitsAtTrace.lean).

Limits. CONDITIONAL on the head, on the sentence and on the public premise: NO FILE SHOWS THE
SENTENCE OF ANY SCRIPT, AND NONE SHOWS THE PUBLIC PREMISE OF ANY GROUND; who can pay each field is
said at the field, by reading. THE SENTENCE CAN HOLD ONLY OF A SCRIPT WHOSE `fixedMsg` AT THE
MESSAGE's NUMBER LIES BEYOND THE ROUND: the message is handed the first `fixedMsg` challenges alone,
the filling's entry reads the round's sampled entries. For the same reason the end's digits read no
challenge but the round's. The laws of the kind K1 on what a job sends (`sent_at_shape`,
Honest/K1/PlaceSent.lean; `place_sent`, `later_job_sent`, Honest/K1/PlaceJobSent.lean
[not in this library]) have `readyAt` at the list heard as a premise: to pay the sentence at every
list a fellow of them without that premise is wanted, which no file has. One closed fact is decided
by Lean's kernel by evaluation at the library's written values. The full size and the earlier hash
alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.ScriptHoldsTheHonestValues
import Johnson.Desc.ProofFile.Honest.K5.Law.LaysFilling
import Johnson.Desc.ProofFile.Honest.K1.LaterOffPad
import Johnson.Desc.ProofFile.Honest.K1.PlaceSent
import Johnson.Desc.ProofFile.Honest.K3.BzTie
import Johnson.Desc.ProofFile.Honest.K3.Law.TiesSealed
import Johnson.Desc.First.Look.DigitsShapeAt
import Johnson.P5J.K03RidesDigLeft
import Johnson.IMR.OwnOfMade
import Johnson.Second.K08.BlocksInOfLayout
import Johnson.Top.H0.K2Ties.WrittenAt
import Johnson.P2LawR.LaidArrAtHead
import Johnson.HB.LLHARD.Q38J.ZzBuilt
import Johnson.P1K8R.Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (seatsOf pairOf heardOf bzAtOf bzVals bzRows digitsOf laidBZ_digitsOf)
open VerifiableInference.Desc (Chain Wit padB laidAt arrayOf)
open VerifiableInference.Desc.Sound (MsgT msgsOf)
open VerifiableInference.Desc.First.Look (Sent Seat digAt enOf digList seatOf findJ msgAt msgAt_of
  valAt readAt finOf_some messagesAt lastMoment arrB cell_resolves findJ_cell)
open VerifiableInference.OnPublicFiles (digMu)
open Johnson.Pack (pMain)
open VerifiableInference.Desc.First.K8.Honest (allRows)
open ProofFile.Honest.K8 (parOfTail zzOf zzVals zzPubOf bearsZz)
open ProofFile.Honest.K2 (roundNumbers)
open ProofFile.Honest.K1 (digitsFill)
open ProofFile.Honest.FirstThread (Script)
open P5J (AtMgA TS CellsM)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-! ## 1 The sentence on the Script, and the public premise -/

/-- **THE SCRIPT LAYS THE FILLING, AT ONE LINK**: a premise's form, ON `Q.msg` ALONE, in the frame's
own letters. Asked of whoever lays the `Script`'s messages of that link at the addresses that `seat`
names.

`plan`: the proof file's public part, read for the messages' numbers alone. `readers`: the readers
of an input. `filling`: the data of the main rows. `seat`: of an address: the link and the message's
number in the link's list.

What it asks. At every run's coins, every input at which `valid` holds and every list of at least
`challengesHeard` challenges, of whatever form: where the filling's total call (`RowData.at_`)
answers an element at a main row and place of a message seated at (link, message), the `Script`'s
message with the plan's number of (link, message) holds that element, read into the extension field.

Where it asks nothing. Where the filling lays nothing; of mask rows; of addresses that `seat` does
not lay at the link; of inputs and lists outside the guards. The filling's own test `ready` is not
asked: see the head. It can hold only of a `Script` whose `fixedMsg` at the number reaches behind
the last challenge that the filling's entries there read. A definition: nothing here shows that it
is met. -/
def ScriptLaysTheFillingAtTheLink (plan : ProofFile.Pub) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (challengesHeard : ℕ)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (filling : RowData)
    (seat : MsgAddr → Option (ℕ × ℕ)) (link : ℕ) : Prop :=
  ∀ (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (heard : List Fmt.Drawn), valid v →
    challengesHeard ≤ heard.length → ∀ (address : MsgAddr) (message : ℕ),
    seat address = some (link, message) → ∀ (row place : ℕ) (entry : Cb.Gl.F ⊕ Cb.Gl.E),
    filling.at_ (readers v) heard address row place = some entry →
    Q.msg (P5J.At.num plan link message) k v
        (heard.take (Q.fixedMsg (P5J.At.num plan link message))) false row place =
      asE (some entry)

/-- **ON PUBLIC DATA: what the digits' filling reads of the ground is the plan's, at one link.** A
premise's form: no coin, no input, no challenge stands in it. `round`: the number, among the first
chain's rounds, of the round that samples the matrix of the link's smallness test. `tl`: the plan's
record of that test. Who can pay a field is said by reading; no file pays one at this form. UNDER
THE HEAD a ground is at hand by reading: `Bs.G₀` of `h.laid.opened` (`IM.Open`). -/
structure PublicDataServeTheDigitsAtTheLink (plan : ProofFile.Pub) (ground : ProofFile.Ground)
    (link round challengesHeard : ℕ) (tl : HTailF2) : Prop where
  /-- the ground's codes, shape and layout are the plan's. Payer: `blankBy_first`
  (Johnson/Desc/K1/Law/FirstMakeFacts.lean), at every ground that `blankBy` returns -/
  groundHasThePlansFirstChain : ground.first = plan.first
  /-- the ground's public record is the plan's. Payer: `ProofFile.Law.blankBy_W`
  (Johnson/Desc/ProofFile/Law/MakerPublic.lean) -/
  groundHasThePlansPublicPart : ground.W = P5J.At.X plan
  /-- the ground has built the link, with the record tl. Payers under the head: `P1K8T.built_at`
  (Johnson/P1K8R/Tied.lean), `Q38.j_tl_built` (Johnson/HB/LLHARD/Q38J/ZzBuilt.lean) -/
  groundHasTheLinksTail : (ground.built[link]?).map (·.tl) = some tl
  /-- the public data of BZ's values at the link: the round, the record, the list of where the
  matrices are read. Payer under the head: the term in the proof of `bzAt_at_head`
  (Honest/K2/Law/DigitsLightAtHead.lean), which names the round as `rngAt`'s -/
  countsPublicDataAreTheLinks : ∃ declared,
    bzAtOf plan ground (matsOwn ground.W) link = some ⟨round, declared, tl, matsOwn ground.W link⟩
  /-- ZZ's values find the same round, as entry number link of the rounds named "RNG". Payer: a
  closed test at the written rounds (`oneRoundB`, Honest/K3/BzTie.lean, is its form; run by nobody)
  -/
  digitsRoundIsTheRound : (roundNumbers plan.D.1 "RNG")[link]? = some round
  /-- half of ZZ's columns are as many as all rows of cells of the test's matrices: ZZ's values
  state their size by the second number. Payers: `K8.mz_allRows` (Honest/K8/AddressLaw.lean), whose
  first premise `Q38.cols_at_head` (Johnson/HB/LLHARD/Q38E/TiesAtHead.lean) has under the head -/
  digitsWidthIsAllRows : tl.mz = allRows (parOfTail tl)
  /-- the message of either array is seated among the seats of "BZ" (so both lie in one message),
  its sending begins behind the round, when no more than `challengesHeard` challenges have been
  heard. Payers under the head: `seatsBZ_at_head` (Honest/K2/Law/DigitsLightAtHead.lean: the seats
  are the written ones) and a closed test at them and the written layout -/
  arraysMessageIsSeated : ∀ (name : String) (array : OnBytes.Params.ReqArray),
    name = "BZ" ∨ name = "ZZ" →
    VerifiableInference.Desc.arrayOf plan.first.layout link name = some array →
    ∃ address : MsgAddr, pairOf (seatsOf plan ground "BZ") address = some (link, array.message) ∧
      round < heardOf (seatsOf plan ground "BZ") address ∧
      heardOf (seatsOf plan ground "BZ") address ≤ challengesHeard

/-! ## 2 Tools, general -/

/-- A first stretch of a list, cut by a test, keeps its entries at their numbers. -/
theorem takeWhileKeepsItsEntries {α : Type} (test : α → Bool) :
    ∀ (list : List α) (number : ℕ) (entry : α),
      (list.takeWhile test)[number]? = some entry → list[number]? = some entry
  | [], _, _, found => by simp at found
  | first :: rest, number, entry, found => by
    rw [List.takeWhile_cons] at found
    split at found
    · cases number with
      | zero => simpa using found
      | succ number =>
        have inner : (rest.takeWhile test)[number]? = some entry := by simpa using found
        simpa using takeWhileKeepsItsEntries test rest number entry inner
    · simp at found

section fillings
variable {first second filling : RowData} {readers : Readers} {heard : List Fmt.Drawn}
  {address : MsgAddr} {row place : ℕ} {entry : Cb.Gl.F ⊕ Cb.Gl.E}

/-- Where the total call answers an element, the filling lays there, and the element is its entry
at the challenges cut to its own count. -/
theorem fillingAnswerSaysItLays
    (answer : filling.at_ readers heard address row place = some entry) :
    filling.lays address row place = true ∧
      filling.entry readers (heard.take (filling.heardAt address)) address row place = entry := by
  unfold RowData.at_ at answer
  split at answer
  · rename_i laysThere
    exact ⟨laysThere, Option.some.inj answer⟩
  · cases answer

/-- Two fillings joined by place answer as the first where the first answers. -/
theorem joinedFillingAnswersAsTheFirst
    (answer : first.at_ readers heard address row place = some entry) :
    (first.over second).at_ readers heard address row place = some entry := by
  obtain ⟨laysThere, isEntry⟩ := fillingAnswerSaysItLays answer
  obtain ⟨joinedLays, joinedEntry⟩ :=
    ProofFile.Honest.K1.over_left first second address row place laysThere
  unfold RowData.at_
  rw [if_pos joinedLays, joinedEntry]
  show some (first.entry readers
    ((heard.take (max (first.heardAt address) (second.heardAt address))).take
      (first.heardAt address)) address row place) = some entry
  rw [List.take_take, Nat.min_eq_left (Nat.le_max_left _ _), isEntry]

/-- They answer as the second where the first lays nothing and the second answers. -/
theorem joinedFillingAnswersAsTheSecond (firstLaysNothing : first.lays address row place = false)
    (answer : second.at_ readers heard address row place = some entry) :
    (first.over second).at_ readers heard address row place = some entry := by
  obtain ⟨laysThere, isEntry⟩ := fillingAnswerSaysItLays answer
  obtain ⟨joinedLays, joinedEntry⟩ :=
    ProofFile.Honest.K1.over_right first second address row place firstLaysNothing laysThere
  unfold RowData.at_
  rw [if_pos joinedLays, joinedEntry]
  show some (second.entry readers
    ((heard.take (max (first.heardAt address) (second.heardAt address))).take
      (second.heardAt address)) address row place) = some entry
  rw [List.take_take, Nat.min_eq_left (Nat.le_max_right _ _), isEntry]

end fillings

/-- The entries that a round sampled are read off a first stretch that holds the round. -/
theorem sampledEntriesOfAFirstStretch (heard : List Fmt.Drawn) {round count : ℕ}
    (roundBelow : round < count) (roundHeard : round < heard.length) :
    ((heard.take count)[round]?).map (·.trits) = some (tritsAt heard round) := by
  rw [List.getElem?_take_of_lt roundBelow]
  unfold tritsAt
  rw [List.getElem?_eq_getElem roundHeard]
  rfl

/-- **What the digits' caller reads at an entry of an array is an entry of a message of the
witness**, where the entry is found, its address has a seat in the main rows, inside its message's
table and off the pad. General in the public data, the seats' table and the witness. -/
theorem digitsReadingIsTheMessagesEntry {CellsW Tok : Type} (x : PlaceL) (sent : Sent)
    (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (digList x sent rad).length → ℕ × ℕ)
    (arr : ℕ → ℕ → ℕ) (witness : Wit CellsW Tok MsgT) {tree row column : ℕ} {s : Seat}
    (entryIsFound : (findJ x.arrays (.cell tree row column)).isSome = true)
    (seatIsFound : seatOf sent x.link (.cell tree row column) = some s)
    (seatInMainRows : s.mask = false) (memberInTheList : s.msg < (digList x sent rad).length)
    (rowInside : s.row < ((digList x sent rad).get ⟨s.msg, memberInTheList⟩).1.mainRows)
    (placeInside :
      s.place < (pMain sent.codes ((digList x sent rad).get ⟨s.msg, memberInTheList⟩).1).ell)
    (offThePad : padB sent.codes ((digList x sent rad).get ⟨s.msg, memberInTheList⟩).1 false s.row
      s.place = false) :
    digMu x sent rad seatT arr witness (enOf x.arrays (tree, row, column)) =
      witness.msg (arr (seatT ⟨s.msg, memberInTheList⟩).1 (seatT ⟨s.msg, memberInTheList⟩).2) false
        s.row s.place := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 entryIsFound
  show msgAt sent.codes (digList x sent rad) (seatOf sent x.link) x.arrays
    (msgsOf sent.codes (digList x sent rad) seatT arr witness)
    (findJ x.arrays (.cell tree row column)) = _
  rw [msgAt_of _ _ _ _ hj]
  unfold valAt
  rw [seatIsFound]
  show (readAt sent.codes (digList x sent rad) _ s).getD 0 = _
  unfold readAt
  rw [dif_pos memberInTheList, if_neg (by rw [seatInMainRows]; exact Bool.false_ne_true),
    finOf_some rowInside, finOf_some placeInside]
  show (witness.tab sent.codes _ _ _ _ false s.row s.place) = _
  unfold VerifiableInference.Desc.Wit.tab
  rw [offThePad]
  rfl

/-! ## 3 On public data -/

section names
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages

/-- Behind the maker's step that declares a link's own arrays, the array of the counts' bits bears
the link's number and the name "BZ". The fellow of `IM.Own.declareOwn_zz`
(Johnson/IMR/ZzNamed.lean). -/
theorem countsArrayIsNamedWhereItIsDeclared {X : LinkH} {l : Nat} {d : Declaring}
    (declared : declareOwn X l = .ok d) : d.arrayOf[X.tl.ix.BZ]? = some (l, "BZ") := by
  unfold declareOwn at declared
  dsimp only at declared
  replace declared := exc_guard declared
  obtain ⟨d1, h1, declared⟩ := exc_bind declared
  obtain ⟨d2, h2, declared⟩ := exc_bind declared
  obtain ⟨d3, h3, declared⟩ := exc_bind declared
  obtain ⟨d4, h4, declared⟩ := exc_bind declared
  obtain ⟨d5, h5, declared⟩ := exc_bind declared
  obtain rfl := Except.ok.inj declared
  exact (IM.Own.own_keeps h5).2

end names

/-- **A CLOSED TEST, at the library's written values**: at each of the 25 links, at each of the
link's own messages: the first seat of the written list of all three chains' seats that stands at
the tree and tenant which the digits' table of seats (`P6T.seatT`) gives the message has the key
"own message of that link, of that number". -/
def ownMessagesBearTheirNumbersAtWrittenValues : Bool :=
  (List.range 25).all fun link =>
    (List.range
      (((VerifiableInference.PlanWritten.proofSizedFull.request.link[link]?).map (·.messages)).getD
        []).length).all
      fun member =>
        (P5T.seatsAllFull.find? fun p =>
          p.j == (P6T.seatT P5T.psFull link member).1 &&
            p.t == (P6T.seatT P5T.psFull link member).2).any fun p =>
          P5T.keyOf p == (0, link, member)

set_option maxRecDepth 1000000 in
/-- The closed test accepts: decided by Lean's kernel by evaluation. -/
theorem ownMessagesBearTheirNumbersAtWrittenValuesAccepts :
    ownMessagesBearTheirNumbersAtWrittenValues = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: the test can refuse: asked for the key of the next message at each place, it says no.
-/
theorem ownMessagesBearTheirNumbersControl :
    ((List.range 25).all fun link =>
      (List.range
        (((VerifiableInference.PlanWritten.proofSizedFull.request.link[link]?).map
          (·.messages)).getD []).length).all
        fun member =>
          (P5T.seatsAllFull.find? fun p =>
            p.j == (P6T.seatT P5T.psFull link member).1 &&
              p.t == (P6T.seatT P5T.psFull link member).2).any fun p =>
            P5T.keyOf p == (0, link, member + 1)) = false := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)

/-! ## 4 On public data, under the head -/

/-- **The member's number.** Under the head, at a link below 25 and at an own message of the link:
the number that the letters of the lookup on the digits give the message in the witness is the
plan's number of (link, message). -/
theorem ownMessageBearsThePlansNumber {link member : ℕ} (linkBelow : link < 25)
    (memberIsAMessage : member < (messagesAt h.𝔇.sent link).length) :
    h.𝔇.l3.arr (h.𝔇.l3.seat link true member).1 (h.𝔇.l3.seat link true member).2 =
      P5J.At.num Zp link member := by
  have pinned : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first
      Zp.made = true :=
    VerifiableInference.PlanWritten.pinnedAt_of_row (by rw [h.toAtMg.pins.1, Bool.or_true])
  have written := VerifiableInference.Desc.First.K2Ties.at_written h.scope h.laid pinned
  have memberBelow : member <
      (((VerifiableInference.PlanWritten.proofSizedFull.request.link[link]?).map
        (·.messages)).getD []).length := by
    rw [← written.shape]
    exact memberIsAMessage
  have accepts := ownMessagesBearTheirNumbersAtWrittenValuesAccepts
  unfold ownMessagesBearTheirNumbersAtWrittenValues at accepts
  have test := List.all_eq_true.1 (List.all_eq_true.1 accepts link (List.mem_range.2 linkBelow))
    member (List.mem_range.2 memberBelow)
  show P5J.At.arr Zp (P6T.seatT (P5J.At.pseats Zp) link member).1
    (P6T.seatT (P5J.At.pseats Zp) link member).2 = P5J.At.num Zp link member
  rw [written.arr, written.num, written.pseats]
  cases found : (P5T.seatsAllFull.find? fun p =>
      p.j == (P6T.seatT P5T.psFull link member).1 &&
        p.t == (P6T.seatT P5T.psFull link member).2) with
  | none =>
    rw [found] at test
    cases test
  | some p =>
    rw [found] at test
    exact P5T.arrOf_is_num _ _ _ link member p found (eq_of_beq test)

/-- **The names.** Under the head, at a link below 25 with the record tl of its smallness test: in
the link's list of arrays the array number tl.ix.ZZ bears (link, "ZZ"), and number tl.ix.BZ bears
(link, "BZ"). -/
theorem digitArraysBearTheirNames {link : ℕ} (linkBelow : link < 25) {tl : HTailF2}
    (tailIsTheLinks : VerifiableInference.Desc.First.Look.tlAt (P5J.At.X Zp) link = some tl) :
    (h.𝔇.sent.arrayOf.getD link #[])[tl.ix.ZZ]? = some (link, "ZZ") ∧
      (h.𝔇.sent.arrayOf.getD link #[])[tl.ix.BZ]? = some (link, "BZ") := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Y, hY⟩ := P1K8T.built_at h.scope h.reads O (Nat.le_of_lt_succ linkBelow)
  have eT : tl = Y.tl := Q38.j_tl_built h O.blank (Nat.le_of_lt_succ linkBelow) hY tailIsTheLinks
  obtain ⟨links, eB⟩ := _root_.Meaning.K2.blank_built O.blank
  rw [eB] at hY
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 hY
  have hl1 : link < Zp.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  have hb : Zp.p.built.links[link]? = some (Zp.p.built.links[link]'hl1) :=
    Array.getElem?_eq_getElem hl1
  have eT' : tl = (Zp.p.built.links[link]'hl1).tl := by rw [eT, ← e']
  have eA : h.𝔇.sent.arrayOf.getD link #[] = (Zp.p.built.links[link]'hl1).arrayOf := by
    show (Zp.p.built.links.map (·.arrayOf)).getD link #[] = _
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, hb]
    rfl
  rw [eA, eT']
  exact ⟨IM.Own.zz_of_made h.laid.pub link _ hb,
    IM.Own.of_made (Φ := fun l tl A => A[tl.ix.BZ]? = some (l, "BZ"))
      (fun _ _ _ declared => countsArrayIsNamedWhereItIsDeclared declared)
      (fun _ _ _ _ keeps e => keeps _ _ _ e (by decide)) h.laid.pub link _ hb⟩

/-- **(b), FIRST HALF: EVERY ADDRESS IS FOUND.** Under the head, at what `digAt` answers at a link
below 25: the place is at the link; the record is the plan's own; the caller's test on an array
accepts at ZZ and at BZ; and ALL tau × 2 mz addresses of ZZ and ALL 32 × bzColumns addresses of BZ
are entries of the place's written list of arrays. -/
theorem digitArraysAddressesAreFound {link : ℕ} (linkBelow : link < 25) {x : PlaceL}
    {tl : HTailF2} (placeAndTail : digAt (P5J.At.X Zp) link = some (x, tl)) :
    x.link = link ∧ VerifiableInference.Desc.First.Look.tlAt (P5J.At.X Zp) link = some tl ∧
      arrB x.arrays h.𝔇.sent (digList x h.𝔇.sent h.𝔇.l3.rad) x.link tl.ix.ZZ = true ∧
      arrB x.arrays h.𝔇.sent (digList x h.𝔇.sent h.𝔇.l3.rad) x.link tl.ix.BZ = true ∧
      (∀ combination column, combination < tl.tau → column < 2 * tl.mz →
        (findJ x.arrays (.cell tl.ix.ZZ combination column)).isSome = true) ∧
      ∀ row column, row < 32 → column < tl.bzColumns →
        (findJ x.arrays (.cell tl.ix.BZ row column)).isSome = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hX := O.public
  rw [O.W] at hX
  have tailIs := VerifiableInference.Desc.First.Look.digAt_is
    (VerifiableInference.Desc.First.Look.shapeZAll_of_public hX) placeAndTail
  have atLink : x.link = link := by
    have q := placeAndTail
    unfold digAt at q
    obtain ⟨x', hx', q⟩ := Option.bind_eq_some_iff.1 q
    obtain ⟨tl', -, q⟩ := Option.bind_eq_some_iff.1 q
    obtain ⟨sh, -, q⟩ := Option.map_eq_some_iff.1 q
    obtain rfl : x' = x := congrArg Prod.fst q
    exact VerifiableInference.OnPublicFiles.lookAt_link hx'
  obtain ⟨k4, kN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  have hlk : VerifiableInference.Desc.K3Asks.linksOf (P5J.At.X Zp) = 25 :=
    VerifiableInference.Desc.K3Asks.links_25 (by rw [k4, kN]; rfl)
  have hr : VerifiableInference.Desc.K3Asks.digRow (P5J.At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true :=
    (LPFD.asks_rest h.laid.asks h.laid.pub).1
  obtain ⟨y, tl₂, e, B⟩ := VerifiableInference.Desc.K3Asks.asks_digB hr h.𝔇.l3.rad link
    (by rw [hlk]; exact linkBelow)
  have ex := Option.some.inj (e.symm.trans placeAndTail)
  obtain rfl : y = x := congrArg Prod.fst ex
  obtain rfl : tl₂ = tl := congrArg Prod.snd ex
  unfold VerifiableInference.Desc.First.Look.digB at B
  rw [Bool.and_eq_true] at B
  have B4 := B.2
  simp only [VerifiableInference.Desc.First.Look.digAddrB, Bool.and_eq_true,
    decide_eq_true_eq] at B4
  obtain ⟨⟨⟨⟨⟨hZ, hB⟩, aZ⟩, aB⟩, -⟩, -⟩ := B4
  refine ⟨atLink, tailIs, aZ, aB, fun combination column hu hc => ?_, fun row column hr hc => ?_⟩
  · split at hZ
    · rename_i T hT
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hZ
      exact findJ_cell hT (Nat.lt_of_lt_of_le hu hZ.1) (Nat.lt_of_lt_of_le (by omega) hZ.2)
    · cases hZ
  · split at hB
    · rename_i T hT
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hB
      have eC : ∀ t : HTailF2, t.bzColumns = 2 ^ t.f9.kT * 2 ^ t.f9.cK :=
        fun _ => Nat.pow_add 2 _ _
      have rows : 2 ^ 5 ≤ T.R := by
        have q := hB.2
        rw [← eC] at q
        exact Nat.le_of_mul_le_mul_left q (Nat.two_pow_pos _)
      exact findJ_cell hT (Nat.lt_of_lt_of_le hr rows) (Nat.lt_of_lt_of_le hc hB.1)
    · cases hB

/-- **(b), SECOND HALF: THE SEAT, THE ROOM, THE PAD, THE NUMBER**, at an entry of an own array of
the link that bears a name, passes the caller's test on an array and is found. Under the head: the
layout has the array; the address has a seat; the seat is where the layout's rule lays the entry, in
the main rows of the array's own message, which is a member of the digits' list; it lies inside that
message's table and off its pad; and the member's number in the witness is the plan's number of
(link, the array's message). -/
theorem ownArrayEntryIsSeatedAtTheDigits {link : ℕ} (linkBelow : link < 25) {x : PlaceL}
    (placeIsAtTheLink : x.link = link) {tree : ℕ} {name : String}
    (arrayIsNamed : (h.𝔇.sent.arrayOf.getD link #[])[tree]? = some (link, name))
    (arrayIsTested :
      arrB x.arrays h.𝔇.sent (digList x h.𝔇.sent h.𝔇.l3.rad) x.link tree = true)
    {row column : ℕ} (entryIsFound : (findJ x.arrays (.cell tree row column)).isSome = true) :
    ∃ (array : OnBytes.Params.ReqArray) (s : Seat)
      (memberInTheList : s.msg < (digList x h.𝔇.sent h.𝔇.l3.rad).length),
      arrayOf h.𝔇.sent.layout link name = some array ∧
      laidAt array row column = some (s.row, s.place) ∧
      seatOf h.𝔇.sent x.link (.cell tree row column) = some s ∧ s.mask = false ∧
      s.msg = array.message ∧
      s.row < ((digList x h.𝔇.sent h.𝔇.l3.rad).get ⟨s.msg, memberInTheList⟩).1.mainRows ∧
      s.place < (pMain h.𝔇.sent.codes
        ((digList x h.𝔇.sent h.𝔇.l3.rad).get ⟨s.msg, memberInTheList⟩).1).ell ∧
      padB h.𝔇.sent.codes ((digList x h.𝔇.sent h.𝔇.l3.rad).get ⟨s.msg, memberInTheList⟩).1 false
        s.row s.place = false ∧
      h.𝔇.l3.arr (h.𝔇.l3.seat link true s.msg).1 (h.𝔇.l3.seat link true s.msg).2 =
        P5J.At.num Zp link array.message := by
  subst placeIsAtTheLink
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have layoutOk : OnBytes.reqLayoutOk h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout = true :=
    _root_.Meaning.K2.pub_layoutOk h.laid.pub
  have shapeOk : OnBytes.reqShapeOk h.𝔇.sent.shape = true := P1K2.hok_open O
  have lengthsOk : h.𝔇.sent.codes.lengthsOk = true := Second.K08.pub_lengthsOk h.laid.pub
  obtain ⟨s, hs, hk, hfit⟩ := cell_resolves arrayIsTested entryIsFound
  obtain ⟨bn, hbn, h1⟩ := Option.bind_eq_some_iff.1 hs
  obtain rfl := Option.some.inj (hbn.symm.trans arrayIsNamed)
  rw [if_pos (show ((x.link, name).1 == x.link) = true from beq_self_eq_true _)] at h1
  obtain ⟨A, hA, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨rp, hrp, rfl⟩ := Option.map_eq_some_iff.1 h2
  rw [if_neg (by simp)] at hfit
  have hA' : arrayOf h.𝔇.sent.layout x.link name = some A := hA
  have hlaid : laidAt A row column = some rp := by
    rw [← _root_.Meaning.laidPlace_eq_laidAt]
    exact hrp
  obtain ⟨As, hl, hf⟩ := Option.bind_eq_some_iff.1 hA'
  have memA : A ∈ As := List.mem_of_find?_eq_some hf
  obtain ⟨M, hM, hOk⟩ := _root_.Meaning.message_of_layout layoutOk hl memA
  have room := laidAt_room h.𝔇.sent.codes M.shape (As.filter fun a => a.message == A.message)
    (by rw [VerifiableInference.Desc.Own.reqMessageLaid_eq]; exact hOk) lengthsOk
    (List.mem_filter.2 ⟨memA, beq_self_eq_true _⟩) hlaid
  have sampled : M.shape.answers ≠ 0 :=
    Nat.one_le_iff_ne_zero.1 (_root_.Meaning.answers_of_shape shapeOk hM)
  have off := padB_of_room h.𝔇.sent.codes M.shape room.2.1 room.2.2 sampled
  obtain ⟨L, hL, hj⟩ := Option.bind_eq_some_iff.1 hM
  have eMsgs : messagesAt h.𝔇.sent x.link = L.messages := by
    unfold messagesAt
    rw [hL]
    rfl
  have eShape : ((digList x h.𝔇.sent h.𝔇.l3.rad).get ⟨A.message, hk⟩).1 = M.shape := by
    have g : (((messagesAt h.𝔇.sent x.link).takeWhile fun m =>
        decide (m.moment ≤ lastMoment h.𝔇.sent x.link)).map fun m =>
          (m.shape, h.𝔇.l3.rad m.shape))[A.message]? =
        some ((digList x h.𝔇.sent h.𝔇.l3.rad).get ⟨A.message, hk⟩) :=
      List.getElem?_eq_getElem hk
    rw [List.getElem?_map] at g
    obtain ⟨m, hm, e⟩ := Option.map_eq_some_iff.1 g
    have hm' := takeWhileKeepsItsEntries _ _ _ _ hm
    rw [eMsgs, hj] at hm'
    obtain rfl := Option.some.inj hm'
    rw [← e]
  refine ⟨A, ⟨A.message, false, rp.1, rp.2⟩, hk, hA', hlaid, hs, rfl, rfl, hfit.1, hfit.2, ?_, ?_⟩
  · show padB _ ((digList x h.𝔇.sent h.𝔇.l3.rad).get ⟨A.message, hk⟩).1 false rp.1 rp.2 = false
    rw [eShape]
    exact off
  · exact ownMessageBearsThePlansNumber h linkBelow
      (by rw [eMsgs]; exact (List.getElem?_eq_some_iff.1 hj).1)

/-! ## 5 What the digits' filling answers -/

section filling
variable {plan : ProofFile.Pub} {ground : ProofFile.Ground} {link round challengesHeard : ℕ} {tl : HTailF2}

/-- **At the place where the layout's rule lays an entry of BZ the digits' filling answers the
counts' bit**, at every list of at least `challengesHeard` challenges, whatever the round has
sampled. CONDITIONAL: the public premise; the programs' two public tests on the plan's shape and
layout. -/
theorem digitsFillingAnswersTheCounts
    (publicData : PublicDataServeTheDigitsAtTheLink plan ground link round challengesHeard tl)
    (layoutOk : OnBytes.reqLayoutOk plan.first.codes plan.first.shape plan.first.layout = true)
    (shapeOk : OnBytes.reqShapeOk plan.first.shape = true) {array : OnBytes.Params.ReqArray}
    (arrayIsTheCounts : arrayOf plan.first.layout link "BZ" = some array) {row column : ℕ}
    {seat : ℕ × ℕ} (laid : laidAt array row column = some seat) (rowBelow : row < 32)
    (columnBelow : column < tl.bzColumns) (readers : Readers) {heard : List Fmt.Drawn}
    (enough : challengesHeard ≤ heard.length) :
    ∃ address : MsgAddr, pairOf (seatsOf plan ground "BZ") address = some (link, array.message) ∧
      (digitsFill plan ground (matsOwn ground.W)).at_ readers heard address seat.1 seat.2 =
        some (.inl ((digitsOf tl (matsOwn ground.W link) readers.cells
          (tritsAt heard round)).bz row column)) := by
  obtain ⟨address, seated, roundBelow, heardBelow⟩ :=
    publicData.arraysMessageIsSeated "BZ" array (Or.inl rfl) arrayIsTheCounts
  obtain ⟨declared, counts⟩ := publicData.countsPublicDataAreTheLinks
  obtain ⟨As, hl, hf⟩ := Option.bind_eq_some_iff.1 arrayIsTheCounts
  have nameIs : array.name = "BZ" := by simpa using List.find?_some hf
  obtain ⟨M, hM, -⟩ := _root_.Meaning.message_of_layout layoutOk hl (List.mem_of_find?_eq_some hf)
  have sampled : M.shape.answers ≠ 0 :=
    Nat.one_le_iff_ne_zero.1 (_root_.Meaning.answers_of_shape shapeOk hM)
  have sizeIs : (bzVals plan ground (matsOwn ground.W)).size link array.name =
      some (32, tl.bzColumns) := by
    rw [nameIs]
    show (if ("BZ" == "BZ") = true then
      (bzAtOf plan ground (matsOwn ground.W) link).map fun b => (32, b.tl.bzColumns)
      else none) = _
    rw [if_pos (by decide), counts]
    rfl
  refine ⟨address, seated, joinedFillingAnswersAsTheFirst ?_⟩
  show (laidData ground.first.codes ground.first.shape ground.first.layout
    (pairOf (seatsOf plan ground "BZ")) (heardOf (seatsOf plan ground "BZ"))
    (bzVals plan ground (matsOwn ground.W))).at_ readers heard address seat.1 seat.2 = _
  rw [publicData.groundHasThePlansFirstChain]
  refine (K5.laidData_at layoutOk arrayIsTheCounts laid hM sampled _ seated sizeIs rowBelow
    columnBelow readers heard).trans (congrArg some ?_)
  exact bzValsAt_val (bzAtOf plan ground (matsOwn ground.W)) readers _ link
    ⟨round, declared, tl, matsOwn ground.W link⟩ (tritsAt heard round) counts
    (sampledEntriesOfAFirstStretch heard roundBelow
      (Nat.lt_of_lt_of_le roundBelow (Nat.le_trans heardBelow enough))) array.name row column

/-- **At the place where the layout's rule lays an entry of ZZ the digits' filling answers the
digit**, at every list of at least `challengesHeard` challenges. CONDITIONAL as above. -/
theorem digitsFillingAnswersTheDigits
    (publicData : PublicDataServeTheDigitsAtTheLink plan ground link round challengesHeard tl)
    (layoutOk : OnBytes.reqLayoutOk plan.first.codes plan.first.shape plan.first.layout = true)
    (shapeOk : OnBytes.reqShapeOk plan.first.shape = true) {array : OnBytes.Params.ReqArray}
    (arrayIsTheDigits : arrayOf plan.first.layout link "ZZ" = some array)
    {combination column : ℕ} {seat : ℕ × ℕ} (laid : laidAt array combination column = some seat)
    (combinationBelow : combination < tl.tau) (columnBelow : column < 2 * tl.mz)
    (readers : Readers) {heard : List Fmt.Drawn} (enough : challengesHeard ≤ heard.length) :
    ∃ address : MsgAddr, pairOf (seatsOf plan ground "BZ") address = some (link, array.message) ∧
      (digitsFill plan ground (matsOwn ground.W)).at_ readers heard address seat.1 seat.2 =
        some (.inl (zzOf tl (matsOwn ground.W link) readers.cells (tritsAt heard round)
          combination column)) := by
  obtain ⟨address, seated, roundBelow, heardBelow⟩ :=
    publicData.arraysMessageIsSeated "ZZ" array (Or.inr rfl) arrayIsTheDigits
  obtain ⟨As, hl, hf⟩ := Option.bind_eq_some_iff.1 arrayIsTheDigits
  have memA : array ∈ As := List.mem_of_find?_eq_some hf
  have nameIs : array.name = "ZZ" := by simpa using List.find?_some hf
  obtain ⟨M, hM, -⟩ := _root_.Meaning.message_of_layout layoutOk hl memA
  have sampled : M.shape.answers ≠ 0 :=
    Nat.one_le_iff_ne_zero.1 (_root_.Meaning.answers_of_shape shapeOk hM)
  have roundHeard : round < heard.length :=
    Nat.lt_of_lt_of_le roundBelow (Nat.le_trans heardBelow enough)
  have bears : bearsZz plan.first.layout (pairOf (seatsOf plan ground "BZ")) address =
      some (link, array.message) := by
    unfold bearsZz
    rw [seated, Option.filter_some, if_pos]
    refine List.any_eq_true.2 ⟨array, ?_, ?_⟩
    · show array ∈ plan.first.layout.link.getD link []
      rw [List.getD_eq_getElem?_getD, hl]
      exact memA
    · show (array.name == "ZZ" && array.message == array.message) = true
      rw [nameIs, beq_self_eq_true, beq_self_eq_true]
      rfl
  have sizeIs : (zzVals (zzPubOf ground plan.D.1 (matsOwn ground.W))).size link array.name =
      some (tl.tau, 2 * allRows (parOfTail tl)) := by
    rw [nameIs]
    show (if ("ZZ" == "ZZ") = true then
      ((ground.built[link]?).map (·.tl)).map fun tl => (tl.tau, 2 * allRows (parOfTail tl))
      else none) = _
    rw [if_pos (by decide), publicData.groundHasTheLinksTail]
    rfl
  refine ⟨address, seated, joinedFillingAnswersAsTheSecond ?_ ?_⟩
  · show (laidData ground.first.codes ground.first.shape ground.first.layout
      (pairOf (seatsOf plan ground "BZ")) (heardOf (seatsOf plan ground "BZ"))
      (bzVals plan ground (matsOwn ground.W))).lays address seat.1 seat.2 = false
    rw [publicData.groundHasThePlansFirstChain]
    refine ProofFile.Honest.K1.not_lays _ _ _ _ _ _ seated
      (K5.laidBack_of_laidAt layoutOk arrayIsTheDigits laid) ?_
    rw [nameIs]
    show (if ("ZZ" == "BZ") = true then
      (bzAtOf plan ground (matsOwn ground.W) link).map fun b => (32, b.tl.bzColumns)
      else none) = none
    rw [if_neg (by decide)]
  · show (laidData ground.first.codes ground.first.shape ground.first.layout
      (bearsZz ground.first.layout (pairOf (seatsOf plan ground "BZ")))
      (fun a =>
        match (bearsZz ground.first.layout (pairOf (seatsOf plan ground "BZ")) a).bind fun x =>
          (zzPubOf ground plan.D.1 (matsOwn ground.W)).rng[x.1]? with
        | some n => n + 1
        | none => 0)
      (zzVals (zzPubOf ground plan.D.1 (matsOwn ground.W)))).at_ readers heard address seat.1
        seat.2 = _
    rw [publicData.groundHasThePlansFirstChain]
    refine (K5.laidData_at layoutOk arrayIsTheDigits laid hM sampled _ bears sizeIs
      combinationBelow (by rw [← publicData.digitsWidthIsAllRows]; exact columnBelow) readers
      heard).trans (congrArg some ?_)
    have count : (match (bearsZz plan.first.layout (pairOf (seatsOf plan ground "BZ"))
          address).bind fun x => (zzPubOf ground plan.D.1 (matsOwn ground.W)).rng[x.1]? with
        | some n => n + 1
        | none => 0) = round + 1 := by
      rw [bears]
      show (match (roundNumbers plan.D.1 "RNG")[link]? with
        | some n => n + 1
        | none => 0) = round + 1
      rw [publicData.digitsRoundIsTheRound]
    show (zzVals (zzPubOf ground plan.D.1 (matsOwn ground.W))).val readers
      (heard.take (match (bearsZz plan.first.layout (pairOf (seatsOf plan ground "BZ"))
          address).bind fun x => (zzPubOf ground plan.D.1 (matsOwn ground.W)).rng[x.1]? with
        | some n => n + 1
        | none => 0)) link array.name combination column = _
    rw [count, nameIs]
    exact zzVals_val (zzPubOf ground plan.D.1 (matsOwn ground.W)) readers _ link tl
      (tritsAt heard round) publicData.groundHasTheLinksTail
      (drawn_of_sampled _ ⟨round, 0, tl, []⟩ _ link _ publicData.digitsRoundIsTheRound
        (sampledEntriesOfAFirstStretch heard (Nat.lt_succ_self round) roundHeard))
      combination column

end filling

/-! ## 6 The end -/

/-- **THE END: THE NAMED PREMISE ON THE DIGITS' ARRAYS, FROM THE SENTENCE ON `Q.msg`.** At a link
below 25, at the place x and the record tl that `digAt` answers there. The digits are CLOSED:
`zzOwn` (Honest/K3/WitOwner.lean) at the input's trace and at the entries that round number `round`
sampled: the array of `fills_digits` (Honest/K3/Law/Thread/ExchangeFillAt.lean). They read no
challenge but that round's. CONDITIONAL: under the head h; `readersReadTheTrace`: the frame's reader
of the cells is `cells` of the input's trace; `publicData`: the public premise at a ground; `lays`:
THE SENTENCE at the digits' filling of that ground (`K1.digitsFill` at `matsOwn`: the term of
`K1.lotData`, Honest/K1/LotData.lean) and at the seats of "BZ". It moves the debt: neither is shown
here. -/
theorem digitArraysFromTheDigitsFilling {link : ℕ} (linkBelow : link < 25) {x : PlaceL}
    {tl : HTailF2} (placeAndTail : digAt (P5J.At.X Zp) link = some (x, tl))
    {valid : Local W₀ Rc ProofFile.Inst Tr → Prop} {challengesHeard round : ℕ} {cells : Tr → Cells}
    {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
    (readersReadTheTrace : ∀ v, (readers v).cells = cells v.trace) {ground : ProofFile.Ground}
    (publicData : PublicDataServeTheDigitsAtTheLink Zp ground link round challengesHeard tl)
    (lays : ScriptLaysTheFillingAtTheLink Zp Q valid challengesHeard readers
      (digitsFill Zp ground (matsOwn ground.W)) (pairOf (seatsOf Zp ground "BZ")) link) :
    ScriptHoldsTheDigitArrays Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x tl
      (fun w heard => zzOwn (P5J.At.X Zp) link (cells w.trace) (tritsAt heard round)) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have layoutOk : OnBytes.reqLayoutOk Zp.first.codes Zp.first.shape Zp.first.layout = true :=
    _root_.Meaning.K2.pub_layoutOk h.laid.pub
  have shapeOk : OnBytes.reqShapeOk Zp.first.shape = true := P1K2.hok_open O
  obtain ⟨atLink, tailIs, testedDigits, testedCounts, foundDigits, foundCounts⟩ :=
    digitArraysAddressesAreFound h linkBelow placeAndTail
  obtain ⟨namedDigits, namedCounts⟩ := digitArraysBearTheirNames h linkBelow tailIs
  have tailOf : tlOf (P5J.At.X Zp) link = tl := by
    rw [Ties.tlOf_eq_tlAt, tailIs]
    rfl
  refine ⟨fun k w heard isValid enough row rowBelow column columnBelow => ?_,
    fun k w heard isValid enough combination column combinationBelow columnBelow => ?_⟩
  · obtain ⟨array, s, memberInTheList, hA, hlaid, hs, hmask, hmsg, h1, h2, hp, hnum⟩ :=
      ownArrayEntryIsSeatedAtTheDigits h linkBelow atLink namedCounts testedCounts
        (foundCounts row column rowBelow columnBelow)
    obtain ⟨address, seated, answer⟩ := digitsFillingAnswersTheCounts publicData layoutOk shapeOk
      hA hlaid rowBelow columnBelow (readers w) enough
    have said := lays k w heard isValid enough address array.message seated s.row s.place _ answer
    refine (digitsReadingIsTheMessagesEntry x h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr (Q.wit k w heard)
      (foundCounts row column rowBelow columnBelow) hs hmask memberInTheList h1 h2 hp).trans ?_
    show Q.msg (h.𝔇.l3.arr (h.𝔇.l3.seat x.link true s.msg).1 (h.𝔇.l3.seat x.link true s.msg).2) k w
      (heard.take (Q.fixedMsg
        (h.𝔇.l3.arr (h.𝔇.l3.seat x.link true s.msg).1 (h.𝔇.l3.seat x.link true s.msg).2)))
      false s.row s.place = _
    rw [atLink, hnum, said, K5.asE_inl, publicData.groundHasThePlansPublicPart,
      readersReadTheTrace]
    have whole := laidBZ_digitsOf tl (matsOwn (P5J.At.X Zp) link) (cells w.trace)
      (tritsAt heard round) row rowBelow column columnBelow
    refine whole.trans ?_
    show ((OnBytes.HonestTrace.bzOf tl (inExt (zzOf tl (matsOwn (P5J.At.X Zp) link) (cells w.trace)
      (tritsAt heard round))) row column : ℕ) : Cb.Gl.E) = _
    unfold zzOwn
    rw [tailOf]
  · obtain ⟨array, s, memberInTheList, hA, hlaid, hs, hmask, hmsg, h1, h2, hp, hnum⟩ :=
      ownArrayEntryIsSeatedAtTheDigits h linkBelow atLink namedDigits testedDigits
        (foundDigits combination column combinationBelow columnBelow)
    obtain ⟨address, seated, answer⟩ := digitsFillingAnswersTheDigits publicData layoutOk shapeOk
      hA hlaid combinationBelow columnBelow (readers w) enough
    have said := lays k w heard isValid enough address array.message seated s.row s.place _ answer
    refine (digitsReadingIsTheMessagesEntry x h.𝔇.sent h.𝔇.l3.rad _ h.𝔇.l3.arr (Q.wit k w heard)
      (foundDigits combination column combinationBelow columnBelow) hs hmask memberInTheList h1 h2
      hp).trans ?_
    show Q.msg (h.𝔇.l3.arr (h.𝔇.l3.seat x.link true s.msg).1 (h.𝔇.l3.seat x.link true s.msg).2) k w
      (heard.take (Q.fixedMsg
        (h.𝔇.l3.arr (h.𝔇.l3.seat x.link true s.msg).1 (h.𝔇.l3.seat x.link true s.msg).2)))
      false s.row s.place = _
    rw [atLink, hnum, said, K5.asE_inl, publicData.groundHasThePlansPublicPart,
      readersReadTheTrace]
    show _ = algebraMap Cb.Gl.F Cb.Gl.E (zzOf (tlOf (P5J.At.X Zp) link)
      (matsOwn (P5J.At.X Zp) link) (cells w.trace) (tritsAt heard round) combination column)
    rw [tailOf]

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.ScriptLaysTheFillingAtTheLink
#print axioms ProofFile.Honest.K3.Term.PublicDataServeTheDigitsAtTheLink
#print axioms ProofFile.Honest.K3.Term.takeWhileKeepsItsEntries
#print axioms ProofFile.Honest.K3.Term.fillingAnswerSaysItLays
#print axioms ProofFile.Honest.K3.Term.joinedFillingAnswersAsTheFirst
#print axioms ProofFile.Honest.K3.Term.joinedFillingAnswersAsTheSecond
#print axioms ProofFile.Honest.K3.Term.sampledEntriesOfAFirstStretch
#print axioms ProofFile.Honest.K3.Term.digitsReadingIsTheMessagesEntry
#print axioms ProofFile.Honest.K3.Term.countsArrayIsNamedWhereItIsDeclared
#print axioms ProofFile.Honest.K3.Term.ownMessagesBearTheirNumbersAtWrittenValues
#print axioms ProofFile.Honest.K3.Term.ownMessagesBearTheirNumbersAtWrittenValuesAccepts
#print axioms ProofFile.Honest.K3.Term.ownMessagesBearTheirNumbersControl
#print axioms ProofFile.Honest.K3.Term.ownMessageBearsThePlansNumber
#print axioms ProofFile.Honest.K3.Term.digitArraysBearTheirNames
#print axioms ProofFile.Honest.K3.Term.digitArraysAddressesAreFound
#print axioms ProofFile.Honest.K3.Term.ownArrayEntryIsSeatedAtTheDigits
#print axioms ProofFile.Honest.K3.Term.digitsFillingAnswersTheCounts
#print axioms ProofFile.Honest.K3.Term.digitsFillingAnswersTheDigits
#print axioms ProofFile.Honest.K3.Term.digitArraysFromTheDigitsFilling
