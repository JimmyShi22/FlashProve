-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT AND ANY BOOK: no filling of the maker, prover or thread is named.
Johnson/Desc/ProofFile/Honest/K3/Term/LaterJobSendsTheFillingAtEveryList.lean: the honest side of the
kind "lookup" (K3): what a later job of the kind K1 sends, at EVERY list of challenges: the sentence
that the lookups on the digits ask of a Script (`ScriptLaysTheFillingAtTheLink` at the digits'
filling, Honest/K3/Term/DigitArraysFromTheDigitsFilling.lean) follows from `OwnMsgs` at the job's own
text. The three statements are from the work on the lookups; the proofs, with three helpers, from the work
on the kind K1.

  `senderLaysWhatTheFillingAnswersAtEveryList`   where the filling's total call answers an entry of
        the base field, the sender's row holds it: no premise that the filling is ready at the list.
        CUT TO ENTRIES OF THE BASE FIELD: over a message of the base field an entry of the extension
        field is sent as 0, so the like is false there
  `digitsFillingAnswersInTheBaseField`           the digits' filling answers in the base field
  `digitsSentenceFromOwnMessagesAtTheDigitsJob`  from `OwnMsgs` at the later job's text at each seated
        address, and public premises: the sentence
  helpers: `laidEntryInTheBaseField`, `mainEntryOfAJobsMessage`, `roomAtTheDigitsJob`

Limits. Conditional. No Script is named here; that a Script meets `OwnMsgs` at these texts is shown by
other files. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.DigitArraysFromTheDigitsFilling
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie
import Johnson.Desc.ProofFile.Honest.Law.LaidSent
import Johnson.Desc.ProofFile.Honest.K1.DataLaw
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K1.LaterOffPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.HonestTrace (seatsOf seatAt pairOf)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.K1 (digitsFill lotData laterJobAt msgTxt bookCovers dueR rowsR rowsMsg momentIs
  PlaceIn firstAddr)
open ProofFile.Honest.FirstThread (Script OwnMsgs)
open Johnson.Prover.Send (shapeAt)
open P5J (CellsM)

/-- **STATEMENT 1: WHERE A FILLING's TOTAL CALL ANSWERS AN ELEMENT OF THE BASE FIELD, THE SENDER
LAYS IT, AT EVERY LIST.** The fellow of `sent_of_lays` (Honest/Law/LaidSent.lean) with no `readyAt`:
of any filling, any place's numbers, any riding tables, any coins: at a main row and place of a
sampled message, inside its rows and its length and off the places of its pad. AT AN ELEMENT OF THE
BASE FIELD ALONE: at a message over the base field an element of the extension field is sent as 0.
-/
theorem senderLaysWhatTheFillingAnswersAtEveryList (filling : RowData) (readers : Readers)
    (heard : List Fmt.Drawn) (numbers : VerifiableInference.Desc.K1.Par)
    (ride : ℕ → Option ProofFile.Honest.K1.Ride) (sender : Addr) (member : ℕ)
    (coins : Cs (dueR numbers ride)) (row place : ℕ) {value : Cb.Gl.F}
    (answer : filling.at_ readers heard ⟨sender, member⟩ row place = some (.inl value))
    (rowInside : row < (shapeAt numbers member).mainRows)
    (placeInside : place < (numbers.codes.base.getD (shapeAt numbers member).code default).ell)
    (sampled : (shapeAt numbers member).answers ≠ 0)
    (offThePad : (row, place) ∉
      padInMain (numbers.codes.base.getD (shapeAt numbers member).code default).ell
        (shapeAt numbers member)) :
    rowsMsg (shapeAt numbers member)
        (rowsR numbers ride (filling.forSend readers sender heard) coins member) false row place =
      asE (some (.inl value)) := by
  have hdat : filling.forSend readers sender heard member row place = some (.inl value) := answer
  show (rowsR numbers ride (filling.forSend readers sender heard) coins member).main
    ((shapeAt numbers member).mainDeg == 3) row place = _
  unfold Johnson.Prover.Send.Rows.main
  by_cases h3 : ((shapeAt numbers member).mainDeg == 3) = true
  · rw [if_pos h3, ProofFile.Honest.K1.main_data_e numbers ride _ coins member row place h3 rowInside
      placeInside sampled offThePad, hdat]
    exact (ProofFile.Honest.K5.asE_inl value).symm
  · rw [if_neg h3, ProofFile.Honest.K1.main_data_f numbers ride _ coins member row place
      (Bool.eq_false_iff.2 h3) rowInside placeInside sampled offThePad, hdat]
    exact (ProofFile.Honest.K5.asE_inl value).symm

/-- A filling that lays arrays' values answers in the base field where the values do. -/
theorem laidEntryInTheBaseField (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (layout : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (heardAt : MsgAddr → ℕ)
    (values : ArrayVals)
    (inBase : ∀ R h l n i c, ∃ value : Cb.Gl.F, values.val R h l n i c = .inl value)
    (readers : Readers) (heard : List Fmt.Drawn) (address : MsgAddr) (row place : ℕ) :
    ∃ value : Cb.Gl.F,
      (laidData codes shape layout seat heardAt values).entry readers heard address row place =
        .inl value := by
  unfold laidData
  dsimp only
  repeat' split
  all_goals first
    | exact ⟨_, rfl⟩
    | exact inBase _ _ _ _ _ _

/-- **STATEMENT 2: THE DIGITS' FILLING ANSWERS ELEMENTS OF THE BASE FIELD ALONE.** -/
theorem digitsFillingAnswersInTheBaseField (plan : ProofFile.Pub) (ground : ProofFile.Ground)
    (mats : ℕ → List (ℕ × String × ℕ)) (readers : Readers) (heard : List Fmt.Drawn)
    (address : MsgAddr) (row place : ℕ) {entry : Cb.Gl.F ⊕ Cb.Gl.E}
    (answer : (digitsFill plan ground mats).at_ readers heard address row place = some entry) :
    ∃ value : Cb.Gl.F, entry = .inl value := by
  have bzBase : ∀ R h l n i c, ∃ value : Cb.Gl.F,
      (OnBytes.HonestTrace.bzVals plan ground mats).val R h l n i c = .inl value := by
    intro R h l n i c
    unfold OnBytes.HonestTrace.bzVals OnBytes.HonestTrace.bzValsAt
    dsimp only
    generalize OnBytes.HonestTrace.bzAtOf plan ground mats l = o
    cases o <;> exact ⟨_, rfl⟩
  have zzBase : ∀ (P : ProofFile.Honest.K8.ZzPub) R h l n i c, ∃ value : Cb.Gl.F,
      (ProofFile.Honest.K8.zzVals P).val R h l n i c = .inl value := by
    intro P R h l n i c
    unfold ProofFile.Honest.K8.zzVals
    dsimp only
    split <;> exact ⟨_, rfl⟩
  unfold RowData.at_ at answer
  by_cases hl : (digitsFill plan ground mats).lays address row place = true
  · rw [if_pos hl] at answer
    rw [← Option.some.inj answer]
    show ∃ value : Cb.Gl.F,
      (if (OnBytes.HonestTrace.bzRows plan ground mats).lays address row place = true then
        (OnBytes.HonestTrace.bzRows plan ground mats).entry readers _ address row place
      else (ProofFile.Honest.K8.zzDataAt ground plan.D.1 (pairOf (seatsOf plan ground "BZ")) mats).entry
        readers _ address row place) = .inl value
    split
    · exact laidEntryInTheBaseField ground.first.codes ground.first.shape ground.first.layout
        (pairOf (seatsOf plan ground "BZ")) (fun _ => 0) (OnBytes.HonestTrace.bzVals plan ground mats)
        bzBase _ _ _ _ _
    · exact laidEntryInTheBaseField ground.first.codes ground.first.shape ground.first.layout
        (ProofFile.Honest.K8.bearsZz ground.first.layout (pairOf (seatsOf plan ground "BZ"))) (fun _ => 0)
        (ProofFile.Honest.K8.zzVals (ProofFile.Honest.K8.zzPubOf ground plan.D.1 mats)) (zzBase _) _ _ _ _ _
  · rw [if_neg hl] at answer
    cases answer

/-- A helper, general in the job: where the job's datum at a main entry off the pad is an element of the base
field, the Script's message at the number at which it holds the job's text holds that element. -/
theorem mainEntryOfAJobsMessage {Bk : ProverCoinCounts} {Wl Xi OwnState Cells' Tok' : Type}
    (Q : Script Bk Wl Cells' Tok' MsgT) (valid : Wl → Prop) (challengesHeard : ℕ)
    (wit : Wl → PlaceIn Xi) (job : ProofFile.Honest.K1.SendJob (PlaceIn Xi) OwnState) (ownStateAtStart : OwnState)
    (number front member : ℕ)
    (ownMessage : OwnMsgs Q valid challengesHeard number front
      (msgTxt 0 wit job ownStateAtStart member))
    (bookCoversTheJob : bookCovers Bk 0 ⟨job.P.place, 0⟩ (dueR job.P job.ride) = true)
    (k : Coins Bk) (v : Wl) (heard : List Fmt.Drawn) (isValid : valid v)
    (enough : challengesHeard ≤ heard.length) (row place : ℕ) {value : Cb.Gl.F}
    (datum : job.data (wit v) { heard := heard.take front, own := ownStateAtStart, seen := .bare [] }
      member row place = some (.inl value))
    (rowInside : row < (shapeAt job.P member).mainRows)
    (placeInside : place < (job.P.codes.base.getD (shapeAt job.P member).code default).ell)
    (sampled : (shapeAt job.P member).answers ≠ 0)
    (offThePad : (row, place) ∉
      padInMain (job.P.codes.base.getD (shapeAt job.P member).code default).ell
        (shapeAt job.P member)) :
    Q.msg number k v (heard.take (Q.fixedMsg number)) false row place = asE (some (.inl value)) := by
  have hcov : (ProofFile.Honest.K1.lentCut k 0 ⟨job.P.place, 0⟩ (dueR job.P job.ride)).isSome = true := by
    rw [ProofFile.Honest.K1.lentCut_isSome k 0 (Nat.zero_le 1)]
    exact bookCoversTheJob
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hcov
  rw [ownMessage k v heard isValid enough false row place _
    (ProofFile.Honest.K1.msgTxt_some 0 wit job ownStateAtStart member k c hc v (heard.take front) false row
      place)]
  show (rowsR job.P job.ride
    (job.data (wit v) { heard := heard.take front, own := ownStateAtStart, seen := .bare [] }) c
    member).main ((shapeAt job.P member).mainDeg == 3) row place = _
  unfold Johnson.Prover.Send.Rows.main
  by_cases h3 : ((shapeAt job.P member).mainDeg == 3) = true
  · rw [if_pos h3, ProofFile.Honest.K1.main_data_e job.P job.ride _ c member row place h3 rowInside
      placeInside sampled offThePad, datum]
    exact (ProofFile.Honest.K5.asE_inl value).symm
  · rw [if_neg h3, ProofFile.Honest.K1.main_data_f job.P job.ride _ c member row place
      (Bool.eq_false_iff.2 h3) rowInside placeInside sampled offThePad, datum]
    exact (ProofFile.Honest.K5.asE_inl value).symm

/-- A helper, on public data: where the digits' filling lays an element at member number member of the sending
at a later place of moment 2, the entry lies in the sender's main rows, off the pad, in a sampled message. -/
theorem roomAtTheDigitsJob (plan : ProofFile.Pub) (ground : ProofFile.Ground) (link piece member row place : ℕ)
    (lengthsAreLawful : ground.first.codes.lengthsOk = true)
    (ofMomentTwo : ∀ s, seatAt (seatsOf plan ground "BZ")
      ⟨⟨⟨1, some link, piece, .K1⟩, 0⟩, member⟩ = some s → momentIs s 2 = true)
    (lays : (digitsFill plan ground (matsOwn ground.W)).lays
      ⟨⟨⟨1, some link, piece, .K1⟩, 0⟩, member⟩ row place = true) :
    row < (shapeAt (VerifiableInference.Desc.K1.parLater ground.first
        (VerifiableInference.Desc.K1.gpOf plan) link piece 2) member).mainRows ∧
      place < (ground.first.codes.base.getD (shapeAt (VerifiableInference.Desc.K1.parLater
        ground.first (VerifiableInference.Desc.K1.gpOf plan) link piece 2) member).code default).ell ∧
      (shapeAt (VerifiableInference.Desc.K1.parLater ground.first
        (VerifiableInference.Desc.K1.gpOf plan) link piece 2) member).answers ≠ 0 ∧
      (row, place) ∉ padInMain (ground.first.codes.base.getD (shapeAt
        (VerifiableInference.Desc.K1.parLater ground.first (VerifiableInference.Desc.K1.gpOf plan) link
          piece 2) member).code default).ell (shapeAt (VerifiableInference.Desc.K1.parLater
        ground.first (VerifiableInference.Desc.K1.gpOf plan) link piece 2) member) := by
  obtain ⟨s, hs, q1, q2, q3, q4⟩ := ProofFile.Honest.K1.digitsFilling_room plan ground (matsOwn ground.W)
    lengthsAreLawful lays
  have hm := ofMomentTwo s hs
  obtain ⟨e1, e2⟩ : shapeAt (VerifiableInference.Desc.K1.parLater ground.first
        (VerifiableInference.Desc.K1.gpOf plan) link piece 2) member = s.shape ∧
      s.ell = (ground.first.codes.base.getD s.shape.code default).ell := by
    unfold seatAt at hs
    have hmem := List.mem_of_find?_eq_some hs
    have hadr : s.addr = ⟨⟨⟨1, some link, piece, .K1⟩, 0⟩, member⟩ := by
      have q := List.find?_some hs
      exact beq_iff_eq.1 q
    obtain ⟨sps, seg, hso⟩ := ProofFile.Honest.K1.seats_text hmem
    have hseg := ProofFile.Honest.K1.seat_seg hso
    rw [hadr] at hseg
    have hl : link = seg := Option.some.inj hseg
    subst hl
    have hsh := ProofFile.Honest.K1.seat_shape_later hso (VerifiableInference.Desc.K1.gpOf plan) piece 2 hm
    rw [hadr] at hsh
    obtain ⟨M, -, -, e3, e4, -, -, -⟩ := ProofFile.Honest.K1.seat_text hso
    exact ⟨hsh, by rw [e4, e3]⟩
  rw [e1, ← e2]
  exact ⟨q1, q2, q4, q3⟩

/-- **STATEMENT 3: THE SENTENCE, FROM `OwnMsgs` AT THE TEXT OF K1's JOB "digits".** The job is the
lot's own term at the link's moment 2 (`lotHalves`, Honest/K1/PlaceJob.lean) at the lot's data
(`lotData`, Honest/K1/LotData.lean); the input is handed it as its instance and `readers`.
CONDITIONAL, ON PUBLIC DATA: `lengthsAreLawful`; `bookCoversTheJob`; `seatsStandAtTheJob`: whatever
the seats of "BZ" seat at the link stands at the job's place, part 0, and is of moment 2;
`frontReaches`: the filling reads no challenge from `front` on. ON THE SCRIPT: `ownMessages`: the
frame's form, at the plan's number of (link, message), at the job's text of the seat's member. -/
theorem digitsSentenceFromOwnMessagesAtTheDigitsJob (plan : ProofFile.Pub) (ground : ProofFile.Ground)
    {Bk : ProverCoinCounts} {W₀ Rc Tr OwnState : Type}
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (challengesHeard : ℕ)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (link piece firstNumber front : ℕ)
    (sizes : OnBytes.HonestTrace.Sz) (ownStateAtStart : OwnState)
    (lengthsAreLawful : ground.first.codes.lengthsOk = true)
    (bookCoversTheJob : bookCovers Bk 0 ⟨⟨1, some link, piece, .K1⟩, 0⟩
      (dueR (laterJobAt (X := OwnState) ground.first (VerifiableInference.Desc.K1.gpOf plan) link
          piece 2 firstNumber (lotData sizes plan ground)).P
        (laterJobAt (X := OwnState) ground.first (VerifiableInference.Desc.K1.gpOf plan) link piece
          2 firstNumber (lotData sizes plan ground)).ride) = true)
    (seatsStandAtTheJob : ∀ address message,
      pairOf (seatsOf plan ground "BZ") address = some (link, message) →
      address.sender = ⟨⟨1, some link, piece, .K1⟩, 0⟩ ∧ address.sender ≠ firstAddr ∧
        ∀ s, seatAt (seatsOf plan ground "BZ") address = some s → momentIs s 2 = true)
    (frontReaches : ∀ address message,
      pairOf (seatsOf plan ground "BZ") address = some (link, message) →
      (digitsFill plan ground (matsOwn ground.W)).heardAt address ≤ front)
    (ownMessages : ∀ address message,
      pairOf (seatsOf plan ground "BZ") address = some (link, message) →
      OwnMsgs Q valid challengesHeard (P5J.At.num plan link message) front
        (msgTxt 0 (fun v => (⟨v.x, readers v⟩ : PlaceIn ProofFile.Inst))
          (laterJobAt (X := OwnState) ground.first (VerifiableInference.Desc.K1.gpOf plan) link
            piece 2 firstNumber (lotData sizes plan ground)) ownStateAtStart address.msg)) :
    ScriptLaysTheFillingAtTheLink plan Q valid challengesHeard readers
      (digitsFill plan ground (matsOwn ground.W)) (pairOf (seatsOf plan ground "BZ")) link := by
  intro k v heard isValid enough address message seated row place entry answer
  obtain ⟨value, rfl⟩ := digitsFillingAnswersInTheBaseField plan ground (matsOwn ground.W)
    (readers v) heard address row place answer
  obtain ⟨hsender, hne, hmom⟩ := seatsStandAtTheJob address message seated
  have hfront := frontReaches address message seated
  have hown := ownMessages address message seated
  obtain ⟨sd, ms⟩ := address
  have hsd : sd = ⟨⟨1, some link, piece, .K1⟩, 0⟩ := hsender
  subst hsd
  have hlay : (digitsFill plan ground (matsOwn ground.W)).lays
      ⟨⟨⟨1, some link, piece, .K1⟩, 0⟩, ms⟩ row place = true := by
    unfold RowData.at_ at answer
    by_contra hc
    rw [if_neg hc] at answer
    cases answer
  have hmine : OnBytes.HonestTrace.mineOf (seatsOf plan ground "BZ")
      ⟨⟨⟨1, some link, piece, .K1⟩, 0⟩, ms⟩ = true := by
    unfold pairOf at seated
    obtain ⟨s, hs, -⟩ := Option.map_eq_some_iff.1 seated
    unfold OnBytes.HonestTrace.mineOf
    rw [hs]
    rfl
  have hat : (lotData sizes plan ground v.x).at_ (readers v) (heard.take front)
      ⟨⟨⟨1, some link, piece, .K1⟩, 0⟩, ms⟩ row place = some (.inl value) := by
    rw [ProofFile.Honest.K1.data_digits sizes plan ground v.x (readers v) (heard.take front) _ row place hne
      hmine]
    unfold RowData.at_ at answer ⊢
    rw [List.take_take, Nat.min_eq_left hfront]
    exact answer
  obtain ⟨h1, h2, h3, h4⟩ := roomAtTheDigitsJob plan ground link piece ms row place lengthsAreLawful
    hmom hlay
  exact mainEntryOfAJobsMessage Q valid challengesHeard
    (fun v => (⟨v.x, readers v⟩ : PlaceIn ProofFile.Inst))
    (laterJobAt (X := OwnState) ground.first (VerifiableInference.Desc.K1.gpOf plan) link piece 2
      firstNumber (lotData sizes plan ground)) ownStateAtStart _ front ms hown bookCoversTheJob k v
    heard isValid enough row place hat h1 h2 h3 h4

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.senderLaysWhatTheFillingAnswersAtEveryList
#print axioms ProofFile.Honest.K3.Term.digitsFillingAnswersInTheBaseField
#print axioms ProofFile.Honest.K3.Term.digitsSentenceFromOwnMessagesAtTheDigitsJob

#print axioms ProofFile.Honest.K3.Term.laidEntryInTheBaseField
#print axioms ProofFile.Honest.K3.Term.mainEntryOfAJobsMessage
#print axioms ProofFile.Honest.K3.Term.roomAtTheDigitsJob
