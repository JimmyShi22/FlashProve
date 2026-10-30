-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillSwitch.lean: CONDITIONAL: THE FILLING's LOT AT AN OWN
MESSAGE OF A CODE SWITCH's SENDING AND THE SWITCH's WHOLE-MESSAGE LOT OF THAT MESSAGE ANSWER ONE
ELEMENT WHEREVER BOTH ANSWER (`agree2_fill_switch`): under the library's hypothesis on the public
input and public premises; no premise on the book or on a run. AND WHERE THE TWO BEAR ONE NUMBER AND
THE SWITCH's TEXT ANSWERS WHEREVER THE FILLING's DOES, THE SWITCH's LOT COVERS THE FILLING's
(`covers_fill_switch`): these two are premises more (hnum, hS), and hS is none on public data. At a
message that has a mask row. No definition; ten theorems, and a small helper that stays in the file.

What it is for. The list of lots of which the frame's `Script.ofLots`
(Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) makes a Script is meant to hold the senders'
whole-message lots alone. The form `LaysCells` (LaysCells.lean in this folder) asks the frame's form
`OwnMsgs` at the filling's text `fillTxt`, for each address that is seated in a segment. `Covers`
(Covers.lean in this folder) hands the form over from a sender's lot. Here the sender's lot is a
code switch's (kind K2), with the text `K2.switchMsgTxt`
(Johnson/Desc/ProofFile/Honest/K2/ScriptLots.lean). That every segment's own messages of moment 0
but the first's are sent by the switch that leads into it is that kind's authors' word (the head of
Johnson/Desc/ProofFile/Honest/K2/OwnData.lean), and no theorem here; `typedSeat` (LotsJoined.lean in
this folder) seats them so: at `K2.switchSeat` at every segment but the first.

Main names:
  `own_is_fill`: what the switch's part reads of the input as the next segment's own data is the
    filling's lot's answer, where that lot answers.
  `handed_of_txt`: where the switch's text answers, `K2.handed` returns. `rows_of_txt`: what stands
    behind an answer of the switch's text: the main rows' data and the rows, at what `K2.handed`
    hands the part.
  `messageRows_main`: in one message with a mask row, on which no table rides: inside the rows a
    main entry is the data's.
  `agree2_fill_switch`: `Agree2 (fillLot h S rd (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l
    m') ⟨num, fx, K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p (1 +
    p.sizes.kept.length + m)⟩`.
  `covers_fill_switch`: `Covers Vd N` of these two, its last premise in the weakest form: wherever
    the filling's text answers.
  `covers_fill_switch_at`: the same, with that premise asked at the public test `fillAnswers`.
  `at_no_challenge`, `base_back`, `lays_of_ask`: small steps.

THE PREMISES OF THE THREE TOPS, ALL OF THEM.
  h: the library's hypothesis on the public input (`P5J.AtMgA`): of it the letters `h.𝔇.sent` are
    read. h IS A HYPOTHESIS: it has a member at the library's written copy of the full-size public
    files (`AtFullSide.Top.headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean), which is tied
    to the package's files by no theorem: ONE EXAMPLE.
  hG: PUBLIC: G is the maker's own ground.
  hAd: PUBLIC: the address of the switch's own message number m is seated at (l, m').
  hn, hl: PUBLIC: that message is one of the switch's sending, and not the last: so no table rides
    on it.
  hmk: PUBLIC: it has a mask row. With that and "no table rides on it" `messageRows_main` has a main
    entry inside the rows as the data's: by `K2.messageRows`' text no pad lies in the main rows of a
    message with a mask row. AT A MESSAGE WITHOUT ONE NOTHING IS SAID: BY COUNTS OFF THE LIBRARY's
    WRITTEN SHAPE, WHICH NO THEOREM HERE HAS, 22 of the 46 own messages of moment 0 at the plan's
    switches have none (the second and the third of each even segment from 2 to 22): THERE THE THREE
    TOPS ARE TRUE AND IDLE. The covering without hmk is `covers_fill_switch_head`
    (FillSwitchHead.lean in this folder): not called here.
  hIn: PUBLIC: what the filling lays there lies inside the message's rows and the code's message
    length: outside them, by `K2.messageRows`' text, a main entry is zero. NOT PROVED HERE. The
    filling lays nothing where its own test `msgFits` (Johnson/Desc/ProofFile/Honest/LaidData.lean)
    says no; by that test's docstring it asks the like at the plan's shape of message (l, m'): no
    law is drawn from it here, and that the switch's notice bears that shape and these codes is not
    said here.
  hnum (the two coverings): the two lots bear one number. num IS A LETTER: nothing here says which
    number the switch's lot bears in a list.
  hS (the two coverings): AT EVERY RUN AND INPUT OF WHICH `Covers` SPEAKS: wherever the filling's
    text answers, the switch's does: that a text answers, not what. NAMED, NOT PAID. The switch's
    own files say where its text answers: under the library's head and an opening, at a place of
    their list and at their lot's own closing: just where the frame hands the part its stretches and
    `publicOk` holds at the input's public instance (`msgTxt_two_head`,
    Johnson/Desc/ProofFile/Honest/K2/Law/LotsAnswerAtHead.lean): NOT CALLED: that file is dear to
    build.
  D₀, rd, closing, p, m, S, ch, fx ARE LETTERS. The switch's filling is `K2.withSwitchData S D₀ Zp
    G`: the frame's own `widerRows S` (Johnson/Desc/ProofFile/Honest/AtPureWider.lean) is that at D₀
    := `K1.lotData S`, by definition.

How. `rows_of_txt` opens the switch's text once. `K2.rowsAll_at`
(Johnson/Desc/ProofFile/Honest/K2/Law/MaskCoin.lean): a message's rows are `K2.messageRows` of its
own cut; `messageRows_main` opens that, after the pattern of `K2.messageRows_reads` there. The
sealed `mainRows` (Johnson/Desc/K2/Honest/Carrying.lean): behind the carrying message and the kept
copies the data is the part's own. `own_is_fill`: `K2.with_own`
(Johnson/Desc/ProofFile/Honest/K2/OwnData.lean), `switchData_at` (FillAtHead.lean in this folder)
and `ask_is_array` (KeysCover.lean in this folder); no challenge is heard on either side.
`base_back`: over the base field an entry is read at its first coordinate and mapped back.

Which of the two texts takes the run's letter k is read off their definitions, and is no theorem
here: `fillTxt` does not (its first argument is `_`); `K2.switchMsgTxt` does, through `K2.handed`.
What the tops say is the equation alone. In `rows_of_txt` what the part is handed is a named term's
value: c is what `K2.handed ch p k` returns, by the premise hc: it stands under no "there is"; its
two parts are handed on to the switch's routines; the data M and the rows V stand under "there is".

Limits. CONDITIONAL. THEY MAY HOLD EMPTILY: `Agree2` asks nothing where the two numbers differ, or
where one of the two texts does not answer; the switch's text answers nowhere where the frame hands
the part nothing, a public test of the switch's fails or the closing refuses; `Covers` asks the
numbers' equation alone where the filling's text answers nowhere; at a book at which the frame hands
the switch's part nothing hS fails as soon as the filling's text answers at one input and list of
challenges of which `Covers` speaks, and the coverings then hold of nothing. AT AN OWN MESSAGE
WITHOUT A MASK ROW hmk FAILS AND THE THREE TOPS SAY NOTHING: at how many of the written plan's the
entry hmk above tells. NOT AT THE FIRST SEGMENT: there `typedSeat` seats the shared sending's
addresses (kind K1), not a switch's. Not at the last message of a sending. No lot is put into a list
here, and no Script is spoken of. `rows_of_txt` says more than the switch's own `rows_of_laid`
(Johnson/Desc/ProofFile/Honest/K2/Law/MaskTxt.lean: not imported): which data the rows are made of:
so the text is opened here once more. `ok_of_toOption` is a twin of a sealed lemma of that name
(Johnson/Desc/Plain/StartThree.lean), typed again and kept in the file, so that no further file is
imported; MaskSwitch.lean in this folder keeps the like. The file stands over files of the frame's,
of K1's and of K2's folders, and over LotsK5.lean, LaysCells.lean and FillAtHead.lean in this
folder: none lies in a seal. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean,
and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the
earlier hash `OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Covers
import Johnson.Desc.ProofFile.Honest.K5.Law.AgreeK5
import Johnson.Desc.ProofFile.Honest.K5.Law.FillAtHead
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Desc.ProofFile.Honest.K2.ScriptLots
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskCoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K1 (cellsVals firstData labelNo)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers covers_of_agree)
open P5J (AtMgA TS)

/-- A result that is read as "some" is no refusal. -/
private theorem ok_of_toOption {ε α : Type} {x : Except ε α} {a : α} (h : x.toOption = some a) :
    x = .ok a := by
  cases x with
  | error e => simp [Except.toOption] at h
  | ok b =>
    have e : b = a := by simpa [Except.toOption] using h
    rw [e]

/-- With no challenge heard the filling's one call reads none. -/
theorem at_no_challenge (S : Sz) (codes : OnBytes.Codes) (s : OnBytes.Params.ReqShape)
    (ly : OnBytes.Params.ReqLayout) (seat : MsgAddr → Option (ℕ × ℕ)) (R : Readers)
    (hd : List Fmt.Drawn) (a : MsgAddr) (r j : ℕ) :
    (firstData S codes s ly seat fun _ => 0).at_ R hd a r j =
      (firstData S codes s ly seat fun _ => 0).at_ R [] a r j := by
  have e0 : (firstData S codes s ly seat fun _ => 0).heardAt a = 0 := rfl
  unfold RowData.at_
  rw [e0, List.take_zero, List.take_zero]

/-- An element of the base field, laid as an entry, read at its first coordinate and mapped back. -/
theorem base_back (x : Cb.Gl.F) :
    algebraMap Cb.Gl.F Cb.Gl.E (asE (some (.inl x))).c0 = asE (some (.inl x)) := by
  show algebraMap Cb.Gl.F Cb.Gl.E (OnBytes.Slice.toF (OnBytes.Slice.ofF x)) =
    OnBytes.Slice.toE (OnBytes.Slice.ofF x, 0, 0)
  exact (OnBytes.Slice.toE_ofF (OnBytes.Slice.ofF x)).symm

/-- **In one message with a mask row, on which no table rides: inside the rows a main entry is the
data's.** -/
theorem messageRows_main {table : K2.FreshTable} {codes : OnBytes.Codes}
    {s : OnBytes.OracleShape} {fold : Option ℕ} {data : ℕ → ℕ → Cb.Gl.E} {k : K2.Stretch}
    {R : Johnson.Prover.Send.Rows} (hf : fold = none) (hm : s.maskRows ≠ 0)
    (h : K2.messageRows table codes s fold data k = .ok R) {b j : ℕ} (hb : b < s.mainRows)
    (hj : j < (codes.base.getD s.code default).ell) :
    R.main (s.mainDeg == 3) b j =
      if (s.mainDeg == 3) = true then data b j
      else algebraMap Cb.Gl.F Cb.Gl.E (data b j).c0 := by
  subst hf
  have hm' : (s.maskRows != 0) = true := bne_iff_ne.2 hm
  unfold K2.messageRows at h
  rcases K2.Reads.ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  rcases K2.Reads.ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  rcases K2.Reads.ite_eq h with ⟨_, h⟩ | ⟨_, h⟩
  · cases h
  obtain ⟨_, _, h⟩ := K2.Reads.bind_ok h
  obtain rfl := Except.ok.inj h
  unfold Johnson.Prover.Send.Rows.main
  by_cases hE : (s.mainDeg == 3) = true
  · simp [hE, hm', hb]
    intro hle
    exact absurd hj (Nat.not_lt.2 (by simpa using hle))
  · simp [hE, hm', hb]
    intro hle
    exact absurd hj (Nat.not_lt.2 (by simpa using hle))

/-- Where the call that asks first answers an element, the filling lays one. -/
theorem lays_of_ask {D : RowData} {R : Readers} {hd : List Fmt.Drawn} {a : MsgAddr} {r j : ℕ}
    {z : Cb.Gl.F ⊕ Cb.Gl.E} (q : D.ask R hd a r j = .ok (some z)) : D.lays a r j = true := by
  unfold RowData.ask at q
  split at q
  · cases q
  · split at q
    · cases q
    · have q1 := Except.ok.inj q
      unfold RowData.at_ at q1
      split at q1
      · assumption
      · cases q1

section
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr : Type}

/-- **Where the switch's text answers, `K2.handed` returns.** -/
theorem handed_of_txt {ch : ℕ} {D : RowDataOf Xi} {rd : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {n : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {mask : Bool} {row place : ℕ} {y : Cb.Gl.E}
    (q : K2.switchMsgTxt ch D rd closing p n k w hd mask row place = some y) :
    (K2.handed ch p k).isSome = true := by
  unfold K2.switchMsgTxt at q
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.1 q
  rw [hc]
  rfl

/-- **What stands behind an answer of the switch's text**: the main rows' data and the rows, at what
`K2.handed` hands the part: c is that term's value, by the premise hc. -/
theorem rows_of_txt {ch : ℕ} {D : RowDataOf Xi} {rd : Local W₀ Rc Xi Tr → Readers}
    {closing : K2.Closing} {p : K2.SwitchPlace} {n : ℕ} {k : Coins Bk} {w : Local W₀ Rc Xi Tr}
    {hd : List Fmt.Drawn} {mask : Bool} {row place : ℕ} {y : Cb.Gl.E}
    {c : K2.Law.SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hc : K2.handed ch p k = some c)
    (q : K2.switchMsgTxt ch D rd closing p n k w hd mask row place = some y) :
    ∃ (M : ℕ → ℕ → ℕ → Cb.Gl.E) (V : ℕ → Johnson.Prover.Send.Rows),
      K2.switchRowsAt p.sizes p.carries c.2.2 ⟨K2.switchWit D rd closing p w, hd, ()⟩ 0 = .ok M ∧
      K2.rowsAll K2.freshTable p.sizes.codes (K2.switchSent p.sizes p.others)
        (K2.switchFresh p.sizes p.others p.foldVars) M c.1 = .ok V ∧
      y = K1.rowsMsg ((K2.switchSent p.sizes p.others).getD n default).shape (V n) mask row
        place := by
  unfold K2.switchMsgTxt at q
  obtain ⟨c', hc', q⟩ := Option.bind_eq_some_iff.1 q
  obtain rfl : c = c' := Option.some.inj (hc.symm.trans hc')
  obtain ⟨V, hV, rfl⟩ := Option.map_eq_some_iff.1 q
  have hV' := ok_of_toOption hV
  unfold K2.switchRowsLaid at hV'
  rcases K2.Reads.ite_eq hV' with ⟨_, e⟩ | ⟨_, hV'⟩
  · cases e
  rcases K2.Reads.ite_eq hV' with ⟨_, e⟩ | ⟨_, hV'⟩
  · cases e
  obtain ⟨M, hM, hR⟩ := K2.Reads.bind_ok' hV'
  exact ⟨M, V, hM, hR, rfl⟩

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **WHAT THE SWITCH's PART READS AS THE NEXT SEGMENT's OWN DATA IS THE FILLING's LOT's ANSWER,
WHERE THAT LOT ANSWERS.** CONDITIONAL: under the hypothesis h; hG: G is the maker's own ground; hAd:
the address of the switch's own message number m is seated; q: the lot's text answers y. -/
theorem own_is_fill (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) {m l m' : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) {k : Coins Bk}
    {v : Local W₀ Rc ProofFile.Inst Tr} {hd : List Fmt.Drawn} {mask : Bool} {row place : ℕ}
    {y : OnBytes.Slice.GE}
    (q : fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd (K2.switchSeat Zp G)
      (fun _ => 0) (p.ownAddr m) l m' k v hd mask row place = some y) :
    (K2.switchWit (K2.withSwitchData S D₀ Zp G) rd closing p v).own m row place = y := by
  obtain ⟨-, z, hz, rfl⟩ := fillTxt_some (Bk := Bk) (k := k) q
  obtain ⟨A, i, c, -, -, -, ez⟩ := ask_is_array hAd hz
  have hat : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp G)
      fun _ => 0).at_ (rd v) hd (p.ownAddr m) row place = some z := by
    unfold RowData.ask at hz
    split at hz
    · cases hz
    · split at hz
      · cases hz
      · exact Except.ok.inj hz
  rw [at_no_challenge] at hat
  show K2.asRow _ ((K2.withSwitchData S D₀ Zp G v.x).at_ (rd v) [] (p.ownAddr m) row place) = _
  rw [K2.with_own S D₀ Zp G v.x (rd v) [] (p.ownAddr m) row place (by rw [hAd]; rfl),
    switchData_at h S hG, hat, ez]
  unfold cellsVals
  dsimp only
  cases labelNo A.name <;> rfl

/-- **THE FILLING's LOT AT THE SWITCH's OWN MESSAGE NUMBER m AND THE SWITCH's LOT OF THAT MESSAGE
AGREE.** CONDITIONAL: under the hypothesis h; hG: G is the maker's own ground; hAd: the address is
seated; hn, hl, hmk: public: the message is one of the sending, not the last, and has a mask row;
hIn: public: what the filling lays there lies inside the message's rows and the code's length. -/
theorem agree2_fill_switch (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) {m l m' : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) (num fx ch : ℕ)
    (hn : 1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size)
    (hl : 1 + p.sizes.kept.length + m ≠ (K2.switchSent p.sizes p.others).size - 1)
    (hmk : ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.maskRows ≠ 0)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr m) row place = true →
      row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
        default).shape.mainRows ∧
      place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
        (1 + p.sizes.kept.length + m) default).shape.code default).ell) :
    Agree2 (fillLot (Bk := Bk) h S rd (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m')
      ⟨num, fx, K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
        (1 + p.sizes.kept.length + m)⟩ := by
  intro _ k w hd mask row place y y' q q'
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (handed_of_txt q')
  obtain ⟨M, V, hM, hR, rfl⟩ := rows_of_txt hc q'
  have q0 : fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd (K2.switchSeat Zp G)
      (fun _ => 0) (p.ownAddr m) l m' k w (hd.take 0) mask row place = some y := q
  have ho := own_is_fill h S hG D₀ rd closing p hAd q0
  obtain ⟨rfl, z, hz, ey⟩ := fillTxt_some (Bk := Bk) (k := k) q0
  obtain ⟨A, i, cc, -, -, -, ez⟩ := ask_is_array hAd hz
  obtain ⟨hb, hj⟩ := hIn _ _ (lays_of_ask hz)
  unfold K2.switchRowsAt at hM
  obtain ⟨W, -, rfl⟩ := K2.Reads.map_ok hM
  obtain ⟨c', -, hmr⟩ := K2.rowsAll_at hR hn
  have hmain := messageRows_main (K2.foldAt_switchFresh p.sizes p.others p.foldVars hl) hmk hmr
    hb hj
  have eM : VerifiableInference.Desc.K2.Honest.mainRows p.sizes W
      (K2.switchWit (K2.withSwitchData S D₀ Zp G) rd closing p w).own
      (1 + p.sizes.kept.length + m) row place = y := by
    unfold VerifiableInference.Desc.K2.Honest.mainRows
    rw [if_neg (by rw [beq_iff_eq]; omega), if_neg (by omega)]
    have e : 1 + p.sizes.kept.length + m - 1 - p.sizes.kept.length = m := by omega
    rw [e]
    exact ho
  show (V (1 + p.sizes.kept.length + m)).main _ row place = y
  rw [hmain, eM]
  by_cases hE : (((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3) = true
  · rw [if_pos hE]
  · rw [if_neg hE, ey, ez]
    unfold cellsVals
    dsimp only
    cases labelNo A.name <;> exact base_back _

/-- **THE SWITCH's LOT OF ITS OWN MESSAGE NUMBER m COVERS THE FILLING's LOT THERE.** CONDITIONAL:
under the hypothesis h; hnum: the two lots bear one number; hG, hAd, hn, hl, hmk, hIn: as
`agree2_fill_switch`: public; hS: wherever the filling's text answers, the switch's does. -/
theorem covers_fill_switch (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) {m l m' num : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp l m')
    (hn : 1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size)
    (hl : 1 + p.sizes.kept.length + m ≠ (K2.switchSent p.sizes p.others).size - 1)
    (hmk : ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.maskRows ≠ 0)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr m) row place = true →
      row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
        default).shape.mainRows ∧
      place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
        (1 + p.sizes.kept.length + m) default).shape.code default).ell)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ k w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      (fillTxt (Bk := Bk) S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd
        (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m' k w (hd.take 0) mask row
        place).isSome = true →
      (K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
        (1 + p.sizes.kept.length + m) k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N
      ⟨num, fx, K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
        (1 + p.sizes.kept.length + m)⟩
      (fillLot (Bk := Bk) h S rd (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m') :=
  covers_of_agree hnum
    (agree2_fill_switch h S hG D₀ rd closing p hAd num fx ch hn hl hmk hIn) hS

/-- **THE SAME, WITH THE LAST PREMISE ASKED AT THE PUBLIC TEST.** CONDITIONAL: as
`covers_fill_switch`; hS: wherever `fillAnswers` says yes at no challenge, the switch's text
answers. -/
theorem covers_fill_switch_at (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) {m l m' num : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp l m')
    (hn : 1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size)
    (hl : 1 + p.sizes.kept.length + m ≠ (K2.switchSent p.sizes p.others).size - 1)
    (hmk : ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.maskRows ≠ 0)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr m) row place = true →
      row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
        default).shape.mainRows ∧
      place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
        (1 + p.sizes.kept.length + m) default).shape.code default).ell)
    {Vd : Local W₀ Rc ProofFile.Inst Tr → Prop} {N : ℕ}
    (hS : ∀ (k : Coins Bk) w (hd : List Fmt.Drawn), Vd w → N ≤ hd.length → ∀ mask row place,
      fillAnswers S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout (K2.switchSeat Zp G)
        (fun _ => 0) (p.ownAddr m) l m' 0 mask row place = true →
      (K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
        (1 + p.sizes.kept.length + m) k w (hd.take fx) mask row place).isSome = true) :
    Covers Vd N
      ⟨num, fx, K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
        (1 + p.sizes.kept.length + m)⟩
      (fillLot (Bk := Bk) h S rd (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m') :=
  covers_fill_switch h S hG D₀ rd closing p hAd fx ch hnum hn hl hmk hIn
    fun k w hd hv hl' mask row place q => by
      refine hS k w hd hv hl' mask row place ?_
      have e := fillTxt_isSome S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd
        (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m' k w (hd.take 0) mask row place
      rw [List.take_zero] at e q
      exact e.symm.trans q

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.ok_of_toOption
#print axioms ProofFile.Honest.K5.at_no_challenge
#print axioms ProofFile.Honest.K5.base_back
#print axioms ProofFile.Honest.K5.messageRows_main
#print axioms ProofFile.Honest.K5.lays_of_ask
#print axioms ProofFile.Honest.K5.handed_of_txt
#print axioms ProofFile.Honest.K5.rows_of_txt
#print axioms ProofFile.Honest.K5.own_is_fill
#print axioms ProofFile.Honest.K5.agree2_fill_switch
#print axioms ProofFile.Honest.K5.covers_fill_switch
#print axioms ProofFile.Honest.K5.covers_fill_switch_at
