-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/AgreeFar.lean: THE SHARED "SENDING" (the kind K1): K1's LOTS AT
ALL 52 AGREE WITH EVERY LOT THAT STANDS FAR FROM THEM: UNDER THE LIBRARY's HEAD: a lot of messages
whose number is the witness's at a seat of the plan's list (all three chains') IN NONE OF OUR 52
SENDINGS AND OF NO KEPT COPY's ROLE; a lot of pads at such a seat's tree and tenant (no premise on
roles). BECAUSE THEY BEAR ANOTHER NUMBER | ANOTHER SEAT: NO TEXT IS OPENED. Thirteen theorems; no
definition.

WHY. Whoever joins the houses' lots into one list pays MsgsAgree | PadsAgree of the appended list by
msgsAgree_append | padsAgree_append (Honest/Small/AgreeParts.lean, AgreePartsPads.lean): the first
list's own; the second's own; AND EACH LOT OF THE FIRST AGAINST THE SECOND. Our own part:
k1MsgLotsW_agree, k1PadLotsW_agree (LotsAtAll.lean). HERE IS THE THIRD PART, WITH OURS AS THE FIRST.

"FAR", WRITTEN OUT, BY THE SENDING's NUMBER (W's two seats bear no link: K1NumOthersW.lean): three
binders on a seat q: q.send ≠ 0; q.send ≠ 3 * l + momL d at l < 25 and both d; q.send ≠ 81.

  seat_of_find   a tool
  k1_num_far     n below the member's plan's number of messages; q the seat that the plan's list
                 holds at (j, t); the witness's number there is that message's; q far; hr: q's role
                 is no kept copy's: FALSE. Three arms: the opening (k1Num_met_two, K1NumOthers.lean;
                 k1Seat_alone_two, K1SeatAlone.lean): hr IS SPENT HERE ALONE; the fifty and W
                 (K1NumOthersW.lean)
  k1_agree2_far  so Agree2 L L' at each lot L of ours and each such L' (agree2_of_ne)
  k1_lotsAgree_far   THE THIRD PART, in the form that msgsAgree_append spends
  k1_msgsAgree_with  MsgsAgree ml' and all of ml' far: MsgsAgree (ours ++ ml')
  k1_seat_far, k1_padAgree2_far, k1_padLotsAgree_far, k1_padsAgree_with   the like for pads, by tree
                 and tenant: a kept copy sits at a seat of its own: SO NO PREMISE ON ROLES
  keptWit, keptWit_bites   a closed fact in Lean's kernel at the written list, and its twin that
                 says no: the seat at place 1 of sending 3 bears the key of the opening's message 1
  kept_bears_ours, far_wants_hr   A NEGATIVE TEST ON hr, UNDER THE HEAD: at that seat and the
                 opening's message 1 the witness's number is ours and the seat is far
                 (kept_bears_ours, at the opening's plan); SO ALL OF k1_num_far's PREMISES BUT hr
                 ARE MET AT ONCE, at its own letters, at the member (2, J₂) (far_wants_hr): without
                 hr the law would end in False at every member of the head: it would say that the
                 head has none: hr is not idle

THE KEPT COPIES. hr SHUTS THEM OUT. Just three seats of the written list bear a key of ours and are
not our own (keptAt2, K1NumOthersW.lean): place 1 of sending 3; place 2 of sending 3; place 1 of
sending 6: copies of the opening's messages 1, 2, 2. A LOT OF MESSAGES AT ONE OF THEM BEARS A NUMBER
OF OURS, AND NOTHING HERE SAYS THAT IT AGREES WITH OURS: that is a matter of the two texts. hfar
ASKS FOR SOME SEAT THAT BEARS THE LOT's NUMBER: so a lot at a kept copy of ANOTHER sender's message
is not shut out: a kept copy and its original have one key (keyOf's text), so that message's first
seat bears the same number (P5T.arrOf_same_key), and it is no kept copy's (argued; not tried here).

THE COINS. A book's coins stand inside Agree2, PadAgree2 and the four forms over them alone, as a
bound letter handed on whole to a lot's text. No proof here reaches them: each goes by agree2_of_ne
or padAgree2_of_ne. OUR OWN LOTS ARE NO LETTERS: their texts are msgTxt and padTxt
(Honest/K1/ScriptLots.lean, laid into lots in Honest/K1/LotsLaid.lean), WHICH DO READ A RUN's COINS:
no proof here opens them. Nothing is said on how coins are laid out or drawn.

THE BOOK. THAT LOTS AGREE IS NO TIE, AND SAYS OF NO TEXT THAT IT ANSWERS: at a book that does not
cover a part's count its lots answer nothing (msgTxt_isSome, padTxt_isSome: LotsAtAll.lean), and
they agree with every lot.

KIN, TOLD. k5_agree_cut (Honest/K5/Law/AgreeK5.lean): the like cut for that kind's
OWN lots; against other kinds' it leaves the premise. agree_first_main (Honest/K1/AgreeFirst.lean):
two TEXTS at one number give one element, at the opening's main rows: the other road to Agree2. That
one key has one number: the library's P5T.arrOf_same_key (Johnson/P5T/KeptAlign.lean).

Limits. THAT ANOTHER HOUSE's LOTS STAND AT SUCH SEATS IS THAT HOUSE's TO SAY: hfar IS A PREMISE,
PAID BY NOBODY HERE. NO SCRIPT IS NAMED. THE PLANS ARE THE DESCRIPTION's GROUND's. THE FULL SIZE
ALONE; the format's second hash function alone. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.LotsAtAll
import Johnson.Desc.ProofFile.Honest.K1.Law.K1NumOthersW
import Johnson.Desc.ProofFile.Honest.Small.AgreeParts
import Johnson.Desc.ProofFile.Honest.Small.AgreePartsPads
import Johnson.P5T.KeptAlign

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K1 (parGF seatOfMsg momL)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open P5T (PSeat Role seatsAllFull keyOf)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile.Honest.FirstThread (MsgLot PadLot LotsAgree PadLotsAgree MsgsAgree PadsAgree Agree2
  PadAgree2 agree2_of_ne padAgree2_of_ne lotsAgree_iff padLotsAgree_iff msgsAgree_append
  padsAgree_append)

/-! ## 1 Tools and the closed fact -/

/-- What find? returns at a tree and tenant sits there. -/
theorem seat_of_find {ps : List PSeat} {j t : ℕ} {q : PSeat}
    (hq : (ps.find? fun p => p.j == j && p.t == t) = some q) : (q.j, q.t) = (j, t) := by
  have hq₀ := List.find?_some hq
  have hq' : (q.j == j && q.t == t) = true := hq₀
  obtain ⟨q1, q2⟩ := Bool.and_eq_true_iff.1 hq'
  rw [eq_of_beq q1, eq_of_beq q2]

/-- The seat at place 1 of sending 3 bears the key of the opening's message 1. -/
theorem keptWit : ((seatsAllFull.find? fun p => p.send == 3 && p.idx == 1).any fun q₀ =>
    (seatsAllFull.find? fun p => p.j == q₀.j && p.t == q₀.t).any fun q =>
      (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 1).1 &&
        p.t == (seatOfMsg parGF 0 1).2).any fun s => keyOf q == keyOf s && q.send == 3) = true := by
  decide +kernel

/-- A NEGATIVE TEST: asked whether that seat stands in sending 0 the test says no. -/
theorem keptWit_bites : ((seatsAllFull.find? fun p => p.send == 3 && p.idx == 1).any fun q₀ =>
    (seatsAllFull.find? fun p => p.j == q₀.j && p.t == q₀.t).any fun q =>
      (seatsAllFull.find? fun p => p.j == (seatOfMsg parGF 0 1).1 &&
        p.t == (seatOfMsg parGF 0 1).2).any fun s => keyOf q == keyOf s && q.send == 0) =
    false := by
  decide +kernel

/-! ## 2 Under the head -/

variable {Xi X : Type}

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **A NEGATIVE TEST ON hr: ALL OF k1_num_far's PREMISES BUT hr ARE MET AT ONCE**, at the opening's
message 1 and a seat of sending 3. -/
theorem kept_bears_ours (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    ∃ (j t : ℕ) (q : PSeat), 1 < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size ∧
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
      P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder 2 (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) 1 ∧
      q.send ≠ 0 ∧ (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  have any_some : ∀ {o : Option PSeat} {p : PSeat → Bool}, o.any p = true →
      ∃ x, o = some x ∧ p x = true := by
    intro o p hp
    cases o with
    | none => simp at hp
    | some x => exact ⟨x, rfl, hp⟩
  obtain ⟨q₀, -, c1⟩ := any_some keptWit
  obtain ⟨q, f, c2⟩ := any_some c1
  obtain ⟨s, g, c3⟩ := any_some c2
  obtain ⟨ck, cs⟩ := Bool.and_eq_true_iff.1 c3
  have hk : keyOf q = keyOf s := eq_of_beq ck
  have hs : q.send = 3 := eq_of_beq cs
  have hn : 1 < (K1.firstPar Bs.G₀.first (K1.gpOf Zp)).sent.size := by
    rw [K1.eG_atAll h O (K1.pin1_atAll h)]
    decide +kernel
  obtain ⟨p, f1, g1⟩ := find_two h O hn
  obtain rfl : s = p := Option.some.inj (g.symm.trans g1)
  have f' : ((P5J.At.pseatsAll Zp).find? fun p => p.j == q₀.j && p.t == q₀.t) = some q := by
    rw [pseatsAll_written h]
    exact f
  refine ⟨q₀.j, q₀.t, q, hn, f', P5T.arrOf_same_key _ _ _ _ _ q s f' f1 hk, ?_, ?_, ?_⟩
  · rw [hs]
    decide
  · intro l _ d
    rw [hs]
    cases d with
    | true =>
      show (3 : ℕ) ≠ 3 * l + 2
      omega
    | false =>
      show (3 : ℕ) ≠ 3 * l + 1
      omega
  · rw [hs]
    decide

section
variable {Bk : ProverCoinCounts} {Wl : Type}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  {J₂ : SendJob (PlaceIn Xi) X} {Jl : ℕ → Bool → SendJob (PlaceIn Xi) X}
  {Jw : SendJob (PlaceIn Xi) X}
  (hP₂ : J₂.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp))
  (hPl : ∀ l, l < 25 → ∀ d, (Jl l d).P = K1.parL Zp Bs.G₀ l d)
  (hPw : Jw.P = K1.parW Zp.first (wGp Zp) 4 wMsgFull)
include h O hP₂ hPl hPw

/-- **NO FAR SEAT THAT IS NO KEPT COPY's BEARS A NUMBER OF OURS.** -/
theorem k1_num_far {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ k1MembersW J₂ Jl Jw) {n : ℕ}
    (hn : n < x.2.P.sent.size) {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (e : P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder x.1 x.2.P n)
    (hr : ∀ l' k', q.role ≠ .kept l' k')
    (h0 : q.send ≠ 0) (h50 : ∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d)
    (hW : q.send ≠ 81) : False := by
  have hm := List.mem_of_find?_eq_some hq
  have e0 := seat_of_find hq
  rcases mem_k1MembersW.1 hx with hx | rfl
  · obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;> dsimp only at hn e
    · rw [hP₂] at hn e
      rcases k1Num_met_two h O hn hq e with e1 | ⟨l', k', hk⟩
      · exact h0 (k1Seat_alone_two h O hn hm (e0.trans e1)).1
      · exact hr l' k' hk
    · rw [hPl l hl d] at hn e
      exact h50 l hl d
        (k1Seat_alone_fifty h O hl d hn hm (e0.trans (k1Num_met_fifty_own h O hl d hn hq e))).1
  · dsimp only at hn e
    rw [hPw] at hn e
    exact hW (k1Num_send_w h O hn hq e).1

omit hPl hPw in
/-- **THE NEGATIVE TEST AT k1_num_far's OWN LETTERS: ALL ITS PREMISES BUT hr ARE MET AT ONCE**, at
the member (2, J₂) and its message 1. -/
theorem far_wants_hr : ∃ x ∈ k1MembersW J₂ Jl Jw, ∃ (n j t : ℕ) (q : PSeat),
    n < x.2.P.sent.size ∧
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
      P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder x.1 x.2.P n ∧
      q.send ≠ 0 ∧ (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81 := by
  obtain ⟨j, t, q, hn, hq, e, h0, h50, hW⟩ := kept_bears_ours h O
  refine ⟨(2, J₂), mem_k1MembersW.2 (Or.inl (mem_k1Members.2 (Or.inl rfl))), 1, j, t, q, ?_, hq,
    ?_, h0, h50, hW⟩
  · show 1 < J₂.P.sent.size
    rw [hP₂]
    exact hn
  · show P5J.At.arr Zp j t = k1Num Zp cF.blocksInOrder 2 J₂.P 1
    rw [hP₂]
    exact e

/-- **EACH LOT OF MESSAGES OF OURS AGREES WITH EACH FAR LOT**: they bear two numbers. -/
theorem k1_agree2_far (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X) {L : MsgLot Bk Wl}
    (hL : L ∈ k1MsgLots (Bk := Bk) cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw))
    {L' : MsgLot Bk Wl} {j t : ℕ} {q : PSeat}
    (hq : ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q)
    (hn' : L'.n = P5J.At.arr Zp j t) (hr : ∀ l' k', q.role ≠ .kept l' k')
    (h0 : q.send ≠ 0) (h50 : ∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d)
    (hW : q.send ≠ 81) : Agree2 L L' := by
  refine agree2_of_ne fun e => ?_
  obtain ⟨x, hx, hm⟩ := List.mem_flatMap.1 hL
  obtain ⟨n, hr', rfl⟩ := List.mem_map.1 hm
  exact k1_num_far h O hP₂ hPl hPw hx (List.mem_range.1 hr') hq (hn'.symm.trans e) hr h0 h50 hW

/-- **THE THIRD PART OF msgsAgree_append, WITH OURS AS THE FIRST LIST.** -/
theorem k1_lotsAgree_far (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X)
    {ml' : List (MsgLot Bk Wl)}
    (hfar : ∀ L' ∈ ml', ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) :
    ∀ L ∈ k1MsgLots (Bk := Bk) cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw),
      LotsAgree ml' L := by
  intro L hL
  refine lotsAgree_iff.2 fun L' hL' => ?_
  obtain ⟨j, t, q, hq, hn', hr, h0, h50, hW⟩ := hfar L' hL'
  exact k1_agree2_far h O hP₂ hPl hPw front wit own₀ hL hq hn' hr h0 h50 hW

/-- **OURS IN FRONT OF A LIST OF FAR LOTS THAT AGREES IN ITSELF: THE WHOLE AGREES.** -/
theorem k1_msgsAgree_with (front : Nat) (wit : Wl → PlaceIn Xi) (own₀ : X)
    {ml' : List (MsgLot Bk Wl)} (hml : MsgsAgree ml')
    (hfar : ∀ L' ∈ ml', ∃ j t q,
      ((P5J.At.pseatsAll Zp).find? fun p => p.j == j && p.t == t) = some q ∧
        L'.n = P5J.At.arr Zp j t ∧ (∀ l' k', q.role ≠ .kept l' k') ∧ q.send ≠ 0 ∧
        (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) :
    MsgsAgree
      (k1MsgLots (Bk := Bk) cF.blocksInOrder front (P5J.At.arr Zp) wit own₀ (k1MembersW J₂ Jl Jw) ++ ml') :=
  msgsAgree_append.2 ⟨k1MsgLotsW_agree h O hP₂ hPl hPw front wit own₀, hml,
    k1_lotsAgree_far h O hP₂ hPl hPw front wit own₀ hfar⟩

/-- **NO FAR SEAT SITS AT A TREE AND TENANT OF OURS.** -/
theorem k1_seat_far {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ k1MembersW J₂ Jl Jw) {n : ℕ}
    (hn : n < x.2.P.sent.size) {q : PSeat} (hm : q ∈ P5J.At.pseatsAll Zp)
    (e : (q.j, q.t) = seatAtMember cF.blocksInOrder x.1 x.2.P n)
    (h0 : q.send ≠ 0) (h50 : ∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d)
    (hW : q.send ≠ 81) : False := by
  rcases mem_k1MembersW.1 hx with hx | rfl
  · obtain rfl | ⟨l, hl, d, rfl⟩ := mem_k1Members.1 hx <;> dsimp only at hn e
    · rw [hP₂] at hn e
      exact h0 (k1Seat_alone_two h O hn hm e).1
    · rw [hPl l hl d] at hn e
      exact h50 l hl d (k1Seat_alone_fifty h O hl d hn hm e).1
  · dsimp only at hn e
    rw [hPw] at hn e
    exact hW (k1Seat_alone_w h O hn hm e).1

/-- **EACH LOT OF PADS OF OURS AGREES WITH EACH FAR LOT**: they sit at two seats. -/
theorem k1_padAgree2_far {L : PadLot Bk Wl}
    (hL : L ∈ k1PadLots (Bk := Bk) (Wl := Wl) cF.blocksInOrder (k1MembersW J₂ Jl Jw))
    {L' : PadLot Bk Wl} {q : PSeat} (hm : q ∈ P5J.At.pseatsAll Zp) (hj : L'.j = q.j)
    (ht : L'.t = q.t)
    (h0 : q.send ≠ 0) (h50 : ∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d)
    (hW : q.send ≠ 81) : PadAgree2 L L' := by
  obtain ⟨x, hx, hm'⟩ := List.mem_flatMap.1 hL
  obtain ⟨n, hr', rfl⟩ := List.mem_map.1 hm'
  by_cases ej : L'.j = (seatAtMember cF.blocksInOrder x.1 x.2.P n).1
  · by_cases et : L'.t = (seatAtMember cF.blocksInOrder x.1 x.2.P n).2
    · exact (k1_seat_far h O hP₂ hPl hPw hx (List.mem_range.1 hr') hm
        (Prod.ext (hj.symm.trans ej) (ht.symm.trans et)) h0 h50 hW).elim
    · exact padAgree2_of_ne (Or.inr et)
  · exact padAgree2_of_ne (Or.inl ej)

/-- **THE THIRD PART OF padsAgree_append, WITH OURS AS THE FIRST LIST.** -/
theorem k1_padLotsAgree_far {pl' : List (PadLot Bk Wl)}
    (hfar : ∀ L' ∈ pl', ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) :
    ∀ L ∈ k1PadLots (Bk := Bk) (Wl := Wl) cF.blocksInOrder (k1MembersW J₂ Jl Jw), PadLotsAgree pl' L := by
  intro L hL
  refine padLotsAgree_iff.2 fun L' hL' => ?_
  obtain ⟨q, hm, hj, ht, h0, h50, hW⟩ := hfar L' hL'
  exact k1_padAgree2_far h O hP₂ hPl hPw hL hm hj ht h0 h50 hW

/-- **OURS IN FRONT OF A LIST OF FAR LOTS OF PADS THAT AGREES IN ITSELF: THE WHOLE AGREES.** -/
theorem k1_padsAgree_with {pl' : List (PadLot Bk Wl)} (hpl : PadsAgree pl')
    (hfar : ∀ L' ∈ pl', ∃ q ∈ P5J.At.pseatsAll Zp, L'.j = q.j ∧ L'.t = q.t ∧ q.send ≠ 0 ∧
      (∀ l, l < 25 → ∀ d, q.send ≠ 3 * l + momL d) ∧ q.send ≠ 81) :
    PadsAgree (k1PadLots (Bk := Bk) (Wl := Wl) cF.blocksInOrder (k1MembersW J₂ Jl Jw) ++ pl') :=
  padsAgree_append.2 ⟨k1PadLotsW_agree h O hP₂ hPl hPw, hpl,
    k1_padLotsAgree_far h O hP₂ hPl hPw hfar⟩

end

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.seat_of_find
#print axioms ProofFile.Honest.K1.keptWit
#print axioms ProofFile.Honest.K1.keptWit_bites
#print axioms ProofFile.Honest.K1.kept_bears_ours
#print axioms ProofFile.Honest.K1.k1_num_far
#print axioms ProofFile.Honest.K1.far_wants_hr
#print axioms ProofFile.Honest.K1.k1_agree2_far
#print axioms ProofFile.Honest.K1.k1_lotsAgree_far
#print axioms ProofFile.Honest.K1.k1_msgsAgree_with
#print axioms ProofFile.Honest.K1.k1_seat_far
#print axioms ProofFile.Honest.K1.k1_padAgree2_far
#print axioms ProofFile.Honest.K1.k1_padLotsAgree_far
#print axioms ProofFile.Honest.K1.k1_padsAgree_with
