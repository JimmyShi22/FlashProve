-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/WordIsDataAt.lean: THE SHARED "SENDING" (the kind K1): UNDER THE
RECORD OF PREMISES K1Seated (Honest/K1/Seated.lean) AT A MEMBER b: THE WORD THAT THE SCRIPT's WITNESS
GIVES THROUGH A STATEMENT AND BOOK OF A LATER BORDER, IN THE MAIN TABLE OF A MESSAGE OF THE JOB's,
INSIDE THE MESSAGE's RANGES AND OFF ITS SAMPLE's PAD, OVER THE EXTENSION FIELD, IS WHAT THE JOB's DATA
SAY THERE. word_is_data_behind (WordIsData.lean), one or more borders on. A JOIN OF LAWS THAT LIE.

For whom. The hash build's door (lane) stands at border 358 of the first chain, and
from the thread at 358 no stand at 356 can be had back. The tie (R.msgs, R.pads) is border-free and
what is read of the state is public, so words_at (WordsAtFour.lean) carries the law over.

  - word_is_data_at: at ANY statement and book with words_at's four public facts, any admitted
    input and any long enough list of challenges. The right side reads the list's front alone.
  - word_is_data_later: the same at a later border b' of the thread: the list of challenges is what
    the thread has heard, and the seat is asked of the book's list of places.
  - word_is_data_at_358: at lettersHead, b := 356, b' := 358, at W's plan: EVERY PUBLIC FACT IS PAID.
    It speaks of W's own message 0 alone: the plan's message 1 has no main row, so hr is empty there
    (w_side_real). hP is rfl at K1.wJobAt (wJobAt_plan), the text of the job at number 356.
  - stand_at_358: what the door reads at that stand: the statement's codes are the public ones, and
    the last record's number of W (w₁Of, Johnson/Desc/Third/Law/Row0AtWords.lean) is 197.
  - w_written, w_sent, w_side_real, w_seat_written, ps_358: closed facts, in Lean's kernel.

An equation at one run's coins, every k: THE RIGHT SIDE NAMES NO COIN: off the pad a main entry holds
data alone (main_data_e). THE 0 WHERE THE DATA ARE SILENT IS A DEFAULT AT A DATUM, as in
word_is_data_behind; whoever spends this law says where the data answer. The data on the right are
read at own₀, at nothing seen.

Limits. THE TIE (msgs, pads) IS A PREMISE HERE: R is handed in, and that it can be met at W's sending
is not said. The job's plan at 356 is a premise (hP). THE FULL SIZE ALONE in word_is_data_at_358.
What the data are is the caller's. Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WordsAtFour
import Johnson.Desc.ProofFile.Honest.K1.Law.WordIsDataHead
import Johnson.Desc.ProofFile.Honest.K1.Law.SeatsAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtHead
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.AtSeats.K01FactsAtAll
import Johnson.Desc.AtSeats.K13KindRowB
import Johnson.Desc.First.Look.K3MaskOkTools
import Johnson.AtFull.Shape.Numbers
import Johnson.P5J.PlanSitsCore
import Johnson.Flat.Last.WSitsOpenAtAll
import Johnson.Desc.Third.Law.Row0AtWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means Cb Cb.Ood Johnson.Pack VerifiableInference.Desc
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT Mem)
open ProofFile.Honest.FirstThread (Letters)
open Johnson.Prover.Send (Rows shapeAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

section General
variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}
variable {L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT} {b : Nat} {blk : Block S Cl}
  {wit : Local W₀ Rc Xi Tr → PlaceIn Xi} {J : SendJob (PlaceIn Xi) X} {own₀ : X}
  {sort : K1Sort} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)} {ms : List Mem}
  {rad : ℕ → ℕ}

/-- **THE WITNESS's WORD AT A MAIN ENTRY IS THE JOB's DATUM, AT ANY STATEMENT AND BOOK WITH THE FOUR
FACTS.** THE TIE (R.msgs, R.pads) IS SPENT. The cut is no premise: R.hasCoins gives it. The 0 where
the data are silent is a default at a datum. -/
theorem word_is_data_at (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (hw : L.valid w) (hd : List Fmt.Drawn)
    (hN : L.thread.front + roundsTo L.bs b ≤ hd.length) (st : Statement) (book : TreeBook)
    (o n : ℕ) (hn : n < J.P.sent.size) (hcodes : st.codes = J.P.codes) (x : _)
    (hx : st.oracles[o]? = some x) (hxs : x.shape = shapeAt J.P n)
    (hseat : Sound.seatBy Sound.noFirst book o = some (seatAtMember L.bs b J.P n)) (r j : ℕ)
    (hr : r < (shapeAt J.P n).mainRows)
    (hj : j < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hp : (r, j) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n))
    (h3 : ((shapeAt J.P n).mainDeg == 3) = true) :
    Sound.wordsFirst arr st book (L.Q.wit k w hd) o .main (r + 2 ^ k1 (shapeAt J.P n) * j) =
      match J.data (wit w)
          { heard := hd.take (L.thread.front + roundsTo L.bs b), own := own₀, seen := .bare [] }
          n r j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
    ((lentCut_isSome k 0 (Nat.zero_le 1) ⟨J.P.place, 0⟩ (dueR J.P J.ride)).trans R.covers)
  rw [words_at R k c hc w hw hd hN st book o n hn hcodes x hx hxs hseat (fun _ _ _ => 0) 0 .main _,
    held_at_main J.P _ 0 _ n hn r j hr]
  show Rows.main (rowsLaid J own₀ c (wit w) (hd.take (L.thread.front + roundsTo L.bs b)) n)
    ((shapeAt J.P n).mainDeg == 3) r j = _
  unfold Rows.main rowsLaid
  rw [if_pos h3]
  exact main_data_e J.P J.ride _ c n r j h3 hr hj ha hp

/-- A list of places and the two public premises on a book seat a message by its tree's own number.
-/
theorem seatBy_of_place {book : TreeBook} (hFits : Book.BookFits book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), book.trees[z]? = some T → T.number = z) {o : ℕ}
    {q : ℕ × ℕ} (hpl : book.place[o]? = some q) :
    Sound.seatBy Sound.noFirst book o = some q := by
  obtain ⟨T, hTr, -⟩ := hFits _ _ hpl
  unfold Sound.seatBy
  rw [hpl, Option.bind_some, hTr, Option.map_some]
  show some (T.number, _) = _
  rw [hNum _ _ hTr]

/-- More borders, at least as many rounds. -/
theorem roundsTo_mono {S' Cl' : Type} (bs : List (Block S' Cl')) {b b' : ℕ} (h : b ≤ b') :
    roundsTo bs b ≤ roundsTo bs b' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold roundsTo declsTo
  rw [List.take_add, List.flatMap_append, List.length_append]
  omega

/-- **AT A LATER BORDER OF THE THREAD.** The thread stands at b' ≥ b, at s; the list of challenges is
what it has heard, at every continuation. The premises on s are public. THE TIE (R.msgs, R.pads) IS
SPENT. The right side reads of what was heard the rounds in front of the member alone. The 0 where
the data are silent is a default at a datum. -/
theorem word_is_data_later (R : K1Seated L b blk wit J own₀ sort arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop) {b' : ℕ} {k : Coins Bk} {s : S}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hA : ThrS L.thread Said b' k s m E) (hb : b ≤ b')
    (hFits : Book.BookFits s.book)
    (hNum : ∀ (z : ℕ) (T : OnBytes.Tree), s.book.trees[z]? = some T → T.number = z)
    (n : ℕ) (hn : n < J.P.sent.size) (hcodes : s.st.codes = J.P.codes) (x : _)
    (hx : s.st.oracles[J.first + n]? = some x) (hxs : x.shape = shapeAt J.P n)
    (hpl : s.book.place[J.first + n]? = some (seatAtMember L.bs b J.P n))
    (ds' : List Fmt.Drawn) (r j : ℕ)
    (hr : r < (shapeAt J.P n).mainRows)
    (hj : j < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hp : (r, j) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n))
    (h3 : ((shapeAt J.P n).mainDeg == 3) = true) :
    Sound.wordsFirst arr s.st s.book (L.Q.wit k m.st.input (m.st.heard ++ ds')) (J.first + n) .main
        (r + 2 ^ k1 (shapeAt J.P n) * j) =
      match J.data (wit m.st.input)
          { heard := m.st.heard.take (L.thread.front + roundsTo L.bs b), own := own₀,
            seen := .bare [] } n r j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  have hlen : m.st.heard.length = L.thread.front + roundsTo L.bs b' := by
    have e := drawsFit_length _ _ hA.1.2.1
    rw [e, List.length_append]
    rfl
  have hle : L.thread.front + roundsTo L.bs b ≤ m.st.heard.length := by
    have := roundsTo_mono L.bs hb
    omega
  have E₁ := word_is_data_at R k m.st.input hA.1.2.2.2.2.2.2 (m.st.heard ++ ds')
    (by rw [List.length_append]; omega) s.st s.book (J.first + n) n hn hcodes x hx hxs
    (seatBy_of_place hFits hNum hpl) r j hr hj ha hp h3
  rwa [List.take_append_of_le_length hle] at E₁

end General

/-! ## At lettersHead, from 356 to 358 -/

/-- The written data at W's messages: their shapes at 197 + n and their seats behind 82 trees. -/
theorem w_written : ((List.range K1.parWF.sent.size).all fun n =>
    decide (K13.Law.MFull[197 + n]? = some (shapeAt K1.parWF n)) &&
      decide (K13.Law.LFull.places[197 + n]? = some (K1.seatOfMsg K1.parWF 82 n))) = true := by
  decide +kernel

/-- W's plan has two messages. -/
theorem w_sent : K1.parWF.sent.size = 2 := by decide +kernel

/-- The side conditions can be met at the written plan: W's own message 0 is sampled and is over the
extension field. -/
theorem w_side_real : 0 < K1.parWF.sent.size ∧ (shapeAt K1.parWF 0).answers ≠ 0 ∧
    ((shapeAt K1.parWF 0).mainDeg == 3) = true ∧ (shapeAt K1.parWF 1).mainRows = 0 := by
  decide +kernel

/-- W's seat stands at message 197 of the written list of places. -/
theorem w_seat_written : K13.Law.LFull.places[197]? = some P5T.N0Full.w := by decide +kernel

/-- The list of places ends at 358. -/
theorem ps_358 : P5J.At.ps[358]? = none := by decide +kernel

section Head
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : VerifiableInference.Desc.Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
  {J : SendJob (PlaceIn ProofFile.Inst) X} {own₀ : X} {sort : K1Sort} {arr : ℕ → ℕ → ℕ}
  {seats₀ : List (ℕ × ℕ)} {ms : List Mem} {rad : ℕ → ℕ}

/-- The plan of the job at W's place is the lot's own parW: word_is_data_at_358's hP, by rfl. -/
theorem wJobAt_plan (Zq : ProofFile.Pub) (first : ℕ) (Dt : RowDataOf ProofFile.Inst) :
    (wJobAt (X := X) Zq.first (wGp Zq) 4 VerifiableInference.Desc.K13.Law.wMsgFull first Dt).P =
      K1.parW Zq.first (wGp Zq) 4 VerifiableInference.Desc.K13.Law.wMsgFull := rfl

/-- **WHAT STANDS AT BORDER 358, AT lettersHead**: the statement's codes are the public ones, and the
record's number of W, which the door reads, is 197: the record is there: 197 is no default of w₁Of.
Public: nothing here reads a witness. -/
theorem stand_at_358 (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 358 k s m E) :
    s.st.codes = Zp.first.codes ∧ VerifiableInference.Desc.Third.Law.w₁Of s = 197 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hbl : 358 ≤ cF.blocksInOrder.length := (Johnson.AtFull.Shape.flat_len h).ge
  have hT := hA.1
  have hm := head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  have hrc := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl hT
  have Fk := K13.Law.factsK13_reached h (K1.pin1_atAll h) _ _ hrc hm
  constructor
  · have hc : K13.Law.inOrderK13 _ _ _ s = true := Fk.order
    unfold K13.Law.inOrderK13 at hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have e1 : s.st.codes = P5J.At.cs Zp := hc.1.1.2
    have e2 : P5J.At.cs Zp = Johnson.G.codesFull2 :=
      (codes_at_head O).symm.trans (K1.atAll_letters h O (K1.pin1_atAll h)).2.2.1
    rw [e1, e2]
    exact (K13.Law.likeFull_in_scope h.scope h.laid.pub (K1.pin1_atAll h)).codes.symm
  · have Pts := (ProofFile.Honest.Small.partsAt_of_thrS
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said hA).2
    have hq : K13.Law.wSitsItem ∈ Sound.pubQ (P5J.mgAtAll h).more P5J.At.links P5J.At.ps 358 := by
      have e := VerifiableInference.OnPublicFiles.Last.h3_atAll h
      have el : (VerifiableInference.Desc.First.flatPlaces true P5J.At.links true).length = 358 := by
        decide +kernel
      rw [el] at e
      exact e
    have hp₀ : (P5J.mgAtAll h).pub K13.Law.wSitsItem (m.st.input.x.pub, s) = true :=
      Pts.pub _ (List.mem_append_left _ hq)
    unfold P5J.mgAtAll at hp₀
    rw [Sound.mgAll_pub] at hp₀
    have hp : (K13.wSitsC h.𝔇.pubD.cs h.𝔇.pubD.P13 s && K13.wSeatC h.𝔇.pubD.N.w s) = true :=
      (First.pubAll_more_wSits h.𝔇.pubD _ _).symm.trans hp₀
    rw [K13.Law.wSitsC_eq, K13.Law.wSeatC_eq, Bool.and_eq_true] at hp
    have hseat := hp.2
    unfold K13.Law.wSeatB at hseat
    cases hl : K13.Law.linAt s with
    | none =>
      have hs' := hseat
      simp only [hl] at hs'
      cases hs'
    | some l =>
      have hs' := hseat
      simp only [hl, Option.any_some, beq_iff_eq] at hs'
      have eW : h.𝔇.pubD.N.w = P5T.N0Full.w :=
        congrArg (·.w) (K1.atAll_letters h O (K1.pin1_atAll h)).1
      have hs₂ : s.book.place[l.w]? = some P5T.N0Full.w := hs'.trans (congrArg some eW)
      have hsz : (P5J.At.N Zp cF).msgsAt P5J.At.ps[358]? = 199 := by
        rw [ps_358]
        exact h.toAtMg.msgs_end
      have h197 : s.book.place[197]? = some P5T.N0Full.w :=
        VerifiableInference.OnPublicFiles.book_place Pts.book
          (show K12.Door.atFirstSeats K13.Law.d12Full.L s = true from Fk.seats)
          (by show 197 < (P5J.At.N Zp cF).msgsAt P5J.At.ps[358]?; omega) w_seat_written
      have hw : l.w = 197 :=
        head_placesApart h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl hT _ _ _ hs₂ h197
      have hfe : s.firstEnd? = some ⟨s.st, s.book, l⟩ := by
        unfold First.S.firstEnd?
        unfold K13.Law.linAt at hl
        split at hl
        next a hh =>
          rw [hh]
          show (a.lin.bind _) = _
          rw [hl, Option.bind_some]
          have hne : (l.w != OnBytes.noId) = true := by
            rw [hw]
            decide
          rw [if_pos hne]
        next => cases hl
      unfold VerifiableInference.Desc.Third.Law.w₁Of VerifiableInference.Desc.Third.firstOfS
      rw [hfe]
      exact hw

/-- **AT lettersHead, FROM W's MEMBER 356 TO THE BORDER 358: EVERY PUBLIC FACT IS PAID.** hP: the job's
plan is W's plan. THE TIE (R.msgs, R.pads) IS SPENT. The 0 where the data are silent is a default at
a datum. The data: at nothing seen and no column (.bare []). -/
theorem word_is_data_at_358
    (R : K1Seated (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) 356 blk wit J own₀
      sort arr seats₀ ms rad)
    (hP : J.P = K1.parW Zp.first (wGp Zp) 4 VerifiableInference.Desc.K13.Law.wMsgFull)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hA : ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 358 k s m E)
    (n : ℕ) (hn : n < J.P.sent.size) (ds' : List Fmt.Drawn) (r₀ j : ℕ)
    (hr : r₀ < (shapeAt J.P n).mainRows)
    (hj : j < (J.P.codes.base.getD (shapeAt J.P n).code default).ell)
    (ha : (shapeAt J.P n).answers ≠ 0)
    (hp : (r₀, j) ∉ padInMain (J.P.codes.base.getD (shapeAt J.P n).code default).ell
      (shapeAt J.P n))
    (h3 : ((shapeAt J.P n).mainDeg == 3) = true) :
    Sound.wordsFirst arr s.st s.book (Q.wit k m.st.input (m.st.heard ++ ds')) (197 + n) .main
        (r₀ + 2 ^ k1 (shapeAt J.P n) * j) =
      match J.data (wit m.st.input)
          { heard := m.st.heard.take
              ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.front +
                roundsTo cF.blocksInOrder 356),
            own := own₀, seen := .bare [] } n r₀ j with
      | some (.inr x) => x
      | some (.inl x) => algebraMap GF GE x
      | none => 0 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hPW : J.P = K1.parWF := hP.trans (parW_written h O)
  have hbl : 358 ≤ cF.blocksInOrder.length := (Johnson.AtFull.Shape.flat_len h).ge
  have hT := hA.1
  have hm := head_noMark h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hT
  have hrc := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl hT
  have Fk := K13.Law.factsK13_reached h (K1.pin1_atAll h) _ _ hrc hm
  have hfirst : J.first = 197 := by
    have e := R.firstNo
    rw [hP] at e
    exact e.symm.trans (nums_w h O).1
  have hnW : n < 2 := by
    rw [hPW, w_sent] at hn
    exact hn
  have hbook := (ProofFile.Honest.Small.partsAt_of_thrS
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said hA).2.book
  have hsz : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).N.msgsAt
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).ps[358]? = 199 := by
    show (P5J.At.N Zp cF).msgsAt P5J.At.ps[358]? = 199
    rw [ps_358]
    exact h.toAtMg.msgs_end
  have hoz : 197 + n < s.st.oracles.size := by
    have e := (book_at_border (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) Said
      hA).2.2
    omega
  have hall := List.all_eq_true.1 w_written n
    (List.mem_range.2 (by rw [w_sent]; exact hnW))
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hall
  obtain ⟨hM, hL⟩ := hall
  have hcodes : s.st.codes = J.P.codes := by
    rw [(stand_at_358 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said hA).1, hP]
    rfl
  have hx : ∃ x₀, s.st.oracles[197 + n]? = some x₀ :=
    ⟨_, Array.getElem?_eq_getElem hoz⟩
  obtain ⟨x₀, hx₀⟩ := hx
  have hsh := K12.Door.msgShape_at
    (show K12.Door.msgShapesB K13.Law.d12Full.M s.st = true from Fk.shapes) (197 + n) hoz
  rw [hx₀] at hsh
  have hxs : x₀.shape = shapeAt J.P n := by
    rw [hPW]
    exact Option.some.inj (hsh.trans hM)
  have hpl : s.book.place[197 + n]? =
      some (seatAtMember (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs 356 J.P n) := by
    have e : seatAtMember (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).bs 356 J.P n =
        K1.seatOfMsg K1.parWF 82 n := by
      show K1.seatOfMsg J.P (treesTo cF.blocksInOrder 356) n = _
      rw [(nums_w h O).2, hPW]
    rw [e]
    exact VerifiableInference.OnPublicFiles.book_place hbook
      (show K12.Door.atFirstSeats K13.Law.d12Full.L s = true from Fk.seats)
      (by rw [hsz]; omega) hL
  have E₁ := word_is_data_later R Said hA (by omega)
    (head_bookFits h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl hT)
    (head_treeNumber h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hbl hT)
    n hn hcodes x₀ (by rw [hfirst]; exact hx₀) hxs (by rw [hfirst]; exact hpl) ds' r₀ j hr hj ha
    hp h3
  rw [hfirst] at E₁
  exact E₁

end Head

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.word_is_data_at
#print axioms ProofFile.Honest.K1.word_is_data_later
#print axioms ProofFile.Honest.K1.word_is_data_at_358
#print axioms ProofFile.Honest.K1.stand_at_358
#print axioms ProofFile.Honest.K1.wJobAt_plan
#print axioms ProofFile.Honest.K1.w_seat_written
#print axioms ProofFile.Honest.K1.w_written
#print axioms ProofFile.Honest.K1.w_sent
#print axioms ProofFile.Honest.K1.w_side_real
#print axioms ProofFile.Honest.K1.ps_358
