-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K5/Law/FillSwitchHead.lean: CONDITIONAL, under the library's
hypothesis h on the public input (`P5J.AtMgA`): AT EVERY OWN MESSAGE OF EVERY CODE SWITCH OF THE
PLAN THE SWITCH's LOT OF THAT MESSAGE COVERS THE FILLING's LOT THERE (`Covers`), UNDER THE ADDRESS's
SEAT, ONE CLAUSE ON NUMBERS, AND THAT THE SWITCH's TEXT ANSWERS. It is the sister of
`covers_fill_switch` (FillSwitch.lean in this folder) WITHOUT THAT LAW's FOUR PUBLIC PREMISES hn,
hl, hmk, hIn. One premise comes: hp: the place is one of the plan's. No definition; seven theorems.

Why it is wanted. hmk says that the own message has a mask row. BY COUNTS OFF THE LIBRARY's WRITTEN
SHAPE, WHICH NO THEOREM HERE HAS, 22 of the 46 own messages of moment 0 at the plan's switches have
none: the second and the third of each even segment from 2 to 22. There the elder law is true and
idle, and a form that asks hmk at every seated address cannot be met.

Main names:
  `seated_at_switch_msg`: general in the plan: a seated address is an own message's of one of the
    plan's switches, AND ITS NUMBER IS `msgNo`'s: `seated_at_switch` (SeatedSwitch.lean in this
    folder) with the equation that its proof has and its statement drops.
  `notice_at_own`: no plan: where a list of messages has M at m, the switch's announcements have M's
    notice at 1 + the kept ones + m.
  `switch_notice_shape`: general in the plan: THE TIE: at a switch of the plan the notice of own
    message m bears the shape of the plan's message that `msgNo` names; the place's codes are the
    ground's; the index lies below the sending's size.
  `in_at_switch`: under h: WHERE THE FILLING LAYS SOMETHING at the switch's own address: the row and
    place lie inside the message's main rows and its code's length and off the places of the pad of
    its sample, and the message has a sample.
  `agree2_fill_switch_all`, `covers_fill_switch_all`: at a free place p: `agree2_fill_switch`,
    `covers_fill_switch` with hl and hmk struck; hw comes (`K2.NoWord`: every message with a main
    row has a sample), and hIn has two conjuncts more (off the pad; a sample).
  `covers_fill_switch_head`: THE COVERING, under h, hG, hp, hAd, hnum, hS alone.

THE PREMISES OF `covers_fill_switch_head`, ALL OF THEM.
  h: the library's hypothesis: a letter of `fillLot`; HERE IT IS ALSO SPENT: `laid.opened`,
    `laid.pub`.
  hG: G is the maker's own ground. hp: p is one of the plan's switches. hAd: the seat answers (l,
    m') at p's own address number m.
  hnum: the lot's number is the plan's number of (l, m').
hS: AT EVERY RUN AND INPUT OF WHICH `Covers` SPEAKS: where the filling's text answers, the switch's
text answers: THAT it answers, not what. It is not derived here; whether it can be met is not said.
  S, D₀, rd, closing, m, l, m', num, fx, ch, Vd, N ARE LETTERS, as in FillSwitch.lean.

THE BOUND THAT GOES WITH THE TWO LAWS OF THE CODE SWITCH's AUTHORS THAT BEAR THIS
(`K2.Law.msgTxt_main_e_of`, `K2.Law.msgTxt_main_f_of`, Honest/K2/Law/MainTxt.lean): they speak OFF
THE PADS' PLACES, AT MOMENT 0, AT AN OWN MESSAGE, WHERE THE TEXT ANSWERS. Here hIn's third conjunct
has the first, hAd the second and third, the switch's own answer the fourth.

How. `switch_notice_shape`: the plan's maker's text; the sealed `notices_other` (where the
announcements hold the own messages), `prep_facts` (the sizes' request and codes are the ground's);
the shared sending's authors' `K1.msgNo_at`, `K1.atMoment_filter` (Honest/K1/SeatShape.lean).
`in_at_switch`: the seat takes the first member of the plan's list whose address fits: that it is p:
under an opening the plan's switches stand at pairwise different places (the first step of
`ownSeats_apart`, SwitchReach.lean in this folder: called in the same words); then the tie; then the
shared sending's authors' `lays_room` (Honest/Law/LaysRoom.lean) and `msgFits_pub`
(Honest/Law/LaysRoomPub.lean). `agree2_fill_switch_all`: `agree2_fill_switch`'s proof as far as
`ask_is_array`; then, where hl and hmk were spent, the code switch's authors' two laws;
`own_is_fill` and `base_back` (FillSwitch.lean) close both cases. `covers_fill_switch_head`: hw by
the code switch's authors' `K2.noWord_open` (Honest/K2/Law/SampledOpen.lean) at h's own opening; hn
by the tie; hIn by `in_at_switch`.

Kin. The code switch's authors have `place_alone` (Honest/K2/Law/PublicAtHead.lean): two switches of
the plan at one place are one: not called here: the three lines here go by our own SwitchReach.lean.
`handed_of_txt`, `rows_of_txt`, `messageRows_main` of FillSwitch.lean are not called here.

Limits. CONDITIONAL. AGAINST `covers_fill_switch`: FOUR PREMISES GO AND ONE COMES; p IS NARROWED TO
THE PLAN's LIST. At a free p neither law gives the other.
THEY MAY HOLD EMPTILY: where the filling's text is silent at every entry (`Covers` is one-way);
where hAd or hS fails. That the switch's text answers, that a lot with that number and text stands
in the frame's list: not said. The elder laws stay: true, and idle where hmk fails.
`seated_at_switch_msg`'s proof is `seated_at_switch`'s but for two lines: two texts of one proof in
one house. Through its imports it stands above Cb/Bridge/CodeListRSProved.lean, and so above the
files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines. At the earlier hash
`OnBytes.secondHashFunction` alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.FillSwitch
import Johnson.Desc.ProofFile.Honest.K5.Law.SwitchReach
import Johnson.Desc.ProofFile.Honest.K1.SeatShape
import Johnson.Desc.ProofFile.Honest.Law.LaysRoom
import Johnson.Desc.ProofFile.Honest.Law.LaysRoomPub
import Johnson.Desc.ProofFile.Honest.K2.Law.MainTxt
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledOpen
import Johnson.Desc.K2.Honest.Returns.SentOwn
import Johnson.IMR.MsgsPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.K1 (cellsVals firstData labelNo)
open ProofFile.Honest.FirstThread (MsgLot Agree2 Covers covers_of_agree)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A SEATED ADDRESS IS AN OWN MESSAGE's OF ONE OF THE PLAN's SWITCHES, AND ITS NUMBER IS
`msgNo`'s.** q: the seat's answer. -/
theorem seated_at_switch_msg {Z : Pub} {G : Ground} {a : MsgAddr} {l m' : ℕ}
    (q : K2.switchSeat Z G a = some (l, m')) :
    ∃ p ∈ K2.switchPlaces Z G, ∃ m, a = p.ownAddr m ∧ l = p.link ∧
      msgNo G.first.shape p.link 0 m = some m' := by
  unfold K2.switchSeat K2.seatBy at q
  obtain ⟨x, hx, hq⟩ := List.exists_of_findSome?_eq_some q
  unfold K2.ownSeats at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  have hq' : K1.momentSeat G.first.shape ⟨p.place, 0⟩ p.link 0 (1 + p.sizes.kept.length) a =
      some (l, m') := hq
  unfold K1.momentSeat at hq'
  split at hq'
  · rename_i hc
    obtain ⟨m₀, hm₀, e⟩ := Option.map_eq_some_iff.1 hq'
    have hs : a.sender = ⟨p.place, 0⟩ := eq_of_beq hc.1
    have hm : 1 + p.sizes.kept.length ≤ a.msg := hc.2
    have e2 : m₀ = m' := congrArg Prod.snd e
    refine ⟨p, hp, a.msg - (1 + p.sizes.kept.length), ?_, (congrArg Prod.fst e).symm, ?_⟩
    · cases a with
      | mk sd ms =>
        have hs' : sd = ⟨p.place, 0⟩ := hs
        have hm' : 1 + p.sizes.kept.length ≤ ms := hm
        subst hs'
        show (⟨⟨p.place, 0⟩, ms⟩ : MsgAddr) =
          ⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + (ms - (1 + p.sizes.kept.length))⟩
        congr 1
        omega
    · rw [← e2]
      exact hm₀
  · cases hq'

/-- **Where the switch's announcements hold an own message's notice.** hF: the list has M at m. -/
theorem notice_at_own (T : OnBytes.SwitchTarget) (L : List OnBytes.Params.ReqMessage)
    (rest : Array OnBytes.OracleNotice) {m : ℕ} {M : OnBytes.Params.ReqMessage}
    (hF : L[m]? = some M) :
    (Tw.K2.switchNotices T (OnBytes.ReqFrame.notices L ++ rest))[1 + T.kept.size + m]? =
      some ⟨M.shape, M.leafClass⟩ := by
  have hlt : m < L.length := (List.getElem?_eq_some_iff.1 hF).1
  rw [VerifiableInference.Desc.K2.Honest.Returns.notices_other]
  unfold OnBytes.ReqFrame.notices
  rw [Array.getElem?_append_left (by simpa using hlt)]
  simp [hF]

/-- **THE TIE: AT A SWITCH OF THE PLAN THE NOTICE OF OWN MESSAGE m BEARS THE PLAN's OWN SHAPE OF
THAT MESSAGE AND THE PLAN's CODES; ITS INDEX LIES BELOW THE SENDING's SIZE.** hp: p is one of the
plan's switches; hm: `msgNo` names m'. -/
theorem switch_notice_shape {Z : Pub} {G : Ground} {p : K2.SwitchPlace}
    (hp : p ∈ K2.switchPlaces Z G) {m m' : ℕ}
    (hm : msgNo G.first.shape p.link 0 m = some m') :
    ∃ M, (G.first.shape.link.getD p.link default).messages[m']? = some M ∧
      ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
        default).shape = M.shape ∧
      p.sizes.codes = G.first.codes ∧
      1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size := by
  unfold K2.switchPlaces at hp
  split at hp
  · rename_i P sps hP hsp
    obtain ⟨eR, eC, -⟩ := _root_.Meaning.Carry.prep_facts hP
    obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hp
    dsimp only at hm ⊢
    obtain ⟨M, hM, hF⟩ := K1.msgNo_at _ _ _ _ _ hm
    rw [← eR] at hF
    have hF' := (congrArg (·[m]?) (K1.atMoment_filter P.z.request
      (OnBytes.reqGroups P.z.request) (sp.place.link.getD P.z.request.link.length) 0)).trans hF
    refine ⟨M, hM, ?_, eC, ?_⟩
    · unfold K2.switchSent
      dsimp only
      rw [List.length_map, Array.length_toList, Array.getD_eq_getD_getElem?]
      erw [notice_at_own _ _ _ hF']
      rfl
    · unfold K2.switchSent
      dsimp only
      rw [List.length_map, Array.length_toList]
      exact (Array.getElem?_eq_some_iff.1 (notice_at_own _ _ _ hF')).1
  · cases hp

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **WHERE THE FILLING LAYS AT A SWITCH's OWN ADDRESS THERE IS ROOM, OFF THE PAD, IN A SAMPLED
MESSAGE.** CONDITIONAL: under the hypothesis h; hG; hp; hAd: the address is seated; q: the filling
lays something there. -/
theorem in_at_switch (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) {m l m' : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) {row place : ℕ}
    (q : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
      (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr m) row place = true) :
    row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
        default).shape.mainRows ∧
      place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
        (1 + p.sizes.kept.length + m) default).shape.code default).ell ∧
      (row, place) ∉ padInMain (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
        (1 + p.sizes.kept.length + m) default).shape.code default).ell
        ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape ∧
      ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
        default).shape.answers ≠ 0 := by
  obtain ⟨p', hp', m₂, ea, el, hmn⟩ := seated_at_switch_msg hAd
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hN : ((K2.switchPlaces Zp G).map (·.place)).Nodup :=
    (SwitchPlaces.k2_places_sub Zp G).nodup (H2K12.places_apart (H2K12.table_apart O).1)
  have e1 : p.place = p'.place := congrArg (fun a : MsgAddr => a.sender.place) ea
  have ep : p = p' := List.inj_on_of_nodup_map hN hp hp' e1
  subst ep
  have e2 : 1 + p.sizes.kept.length + m = 1 + p.sizes.kept.length + m₂ :=
    congrArg MsgAddr.msg ea
  have em : m = m₂ := by omega
  subst em
  subst el
  obtain ⟨M, hM, eS, eC, -⟩ := switch_notice_shape hp hmn
  have eG : G.first = Zp.first := _root_.Meaning.K2.blank_first hG
  rw [eG] at hM eC
  obtain ⟨hm, -⟩ := List.getElem?_eq_some_iff.1 hM
  have hpub : ProofFile.pureRoad.pub OnBytes.secondHashFunction Z.pol Z.lay Z.KL = .ok Zp := h.toAtMg.laid.pub
  have hlen : Zp.first.codes.lengthsOk = true := (msgFits_pub hpub hm).2
  have R := lays_room Zp.first.codes Zp.first.shape Zp.first.layout (K2.switchSeat Zp G)
    (fun _ => 0) (cellsVals S) hlen hAd hM q
  rw [eS, eC]
  exact R

/-- **THE FILLING's LOT AT THE SWITCH's OWN MESSAGE NUMBER m AND THE SWITCH's LOT OF THAT MESSAGE
AGREE: WITH OR WITHOUT A MASK ROW.** CONDITIONAL: under the hypothesis h; hG; hAd; hw, hn: public;
hIn: public: what the filling lays there lies inside, off the pad, in a sampled message. -/
theorem agree2_fill_switch_all (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) {m l m' : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) (num fx ch : ℕ)
    (hw : K2.NoWord (K2.switchSent p.sizes p.others))
    (hn : 1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr m) row place = true →
      row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
          default).shape.mainRows ∧
        place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
          (1 + p.sizes.kept.length + m) default).shape.code default).ell ∧
        (row, place) ∉ padInMain (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
          (1 + p.sizes.kept.length + m) default).shape.code default).ell
          ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape ∧
        ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
          default).shape.answers ≠ 0) :
    Agree2 (fillLot (Bk := Bk) h S rd (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m')
      ⟨num, fx, K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
        (1 + p.sizes.kept.length + m)⟩ := by
  intro _ k w hd mask row place y y' q q'
  have q0 : fillTxt S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout rd (K2.switchSeat Zp G)
      (fun _ => 0) (p.ownAddr m) l m' k w (hd.take 0) mask row place = some y := q
  have ho := own_is_fill h S hG D₀ rd closing p hAd q0
  obtain ⟨rfl, z, hz, ey⟩ := fillTxt_some (Bk := Bk) (k := k) q0
  obtain ⟨A, i, cc, -, -, -, ez⟩ := ask_is_array hAd hz
  obtain ⟨hb, hj, hpd, ha⟩ := hIn _ _ (lays_of_ask hz)
  have q1 : K2.switchMsgTxt ch (K2.withSwitchData S D₀ Zp G) rd closing p
      (1 + p.sizes.kept.length + m) k w (hd.take fx) false row place = some y' := q'
  have ho' : K2.Law.senderOwn (K2.withSwitchData S D₀ Zp G w.x) (rd w) p m row place = y := ho
  by_cases hE : (((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
      default).shape.mainDeg == 3) = true
  · rw [K2.Law.msgTxt_main_e_of ch _ rd closing p k w (hd.take fx) hw hn hE hb hj ha hpd q1]
    exact ho'
  · rw [K2.Law.msgTxt_main_f_of ch _ rd closing p k w (hd.take fx) hw hn
      (Bool.eq_false_iff.2 hE) hb hj ha hpd q1, ho', ey, ez]
    unfold cellsVals
    dsimp only
    cases labelNo A.name <;> exact base_back _

/-- **The covering at a free place.** CONDITIONAL: as `agree2_fill_switch_all`; hnum; hS: THAT the
switch's text answers. -/
theorem covers_fill_switch_all (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace) {m l m' num : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp l m')
    (hw : K2.NoWord (K2.switchSent p.sizes p.others))
    (hn : 1 + p.sizes.kept.length + m < (K2.switchSent p.sizes p.others).size)
    (hIn : ∀ row place, (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout
        (K2.switchSeat Zp G) fun _ => 0).lays (p.ownAddr m) row place = true →
      row < ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
          default).shape.mainRows ∧
        place < (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
          (1 + p.sizes.kept.length + m) default).shape.code default).ell ∧
        (row, place) ∉ padInMain (p.sizes.codes.base.getD ((K2.switchSent p.sizes p.others).getD
          (1 + p.sizes.kept.length + m) default).shape.code default).ell
          ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m) default).shape ∧
        ((K2.switchSent p.sizes p.others).getD (1 + p.sizes.kept.length + m)
          default).shape.answers ≠ 0)
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
    (agree2_fill_switch_all h S hG D₀ rd closing p hAd num fx ch hw hn hIn) hS

/-- **THE COVERING AT EVERY OWN MESSAGE OF EVERY SWITCH OF THE PLAN.** CONDITIONAL: under the
hypothesis h; hG; hp; hAd; hnum; hS: THAT the switch's text answers. -/
theorem covers_fill_switch_head (S : Sz) {G : Ground} (hG : blankBy pureRoad.links Zp = some G)
    (D₀ : Pub → Ground → RowDataOf ProofFile.Inst) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (closing : K2.Closing) {p : K2.SwitchPlace} (hp : p ∈ K2.switchPlaces Zp G) {m l m' num : ℕ}
    (hAd : K2.switchSeat Zp G (p.ownAddr m) = some (l, m')) (fx ch : ℕ)
    (hnum : num = P5J.At.num Zp l m')
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
      (fillLot (Bk := Bk) h S rd (K2.switchSeat Zp G) (fun _ => 0) (p.ownAddr m) l m') := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have eG0 : Bs.G₀ = G := Option.some.inj (O.blank.symm.trans hG)
  have hw : K2.NoWord (K2.switchSent p.sizes p.others) :=
    K2.noWord_open O p (by rw [eG0]; exact hp)
  obtain ⟨p', hp', m₂, ea, -, hmn⟩ := seated_at_switch_msg hAd
  have hN : ((K2.switchPlaces Zp G).map (·.place)).Nodup :=
    (SwitchPlaces.k2_places_sub Zp G).nodup (H2K12.places_apart (H2K12.table_apart O).1)
  have ep : p = p' := List.inj_on_of_nodup_map hN hp hp'
    (congrArg (fun a : MsgAddr => a.sender.place) ea)
  subst ep
  have e2 : 1 + p.sizes.kept.length + m = 1 + p.sizes.kept.length + m₂ :=
    congrArg MsgAddr.msg ea
  have em : m = m₂ := by omega
  subst em
  obtain ⟨_, -, -, -, hn⟩ := switch_notice_shape hp hmn
  exact covers_fill_switch_all h S hG D₀ rd closing p hAd fx ch hnum hw hn
    (fun _ _ q => in_at_switch h S hG hp hAd q) hS

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.seated_at_switch_msg
#print axioms ProofFile.Honest.K5.notice_at_own
#print axioms ProofFile.Honest.K5.switch_notice_shape
#print axioms ProofFile.Honest.K5.in_at_switch
#print axioms ProofFile.Honest.K5.agree2_fill_switch_all
#print axioms ProofFile.Honest.K5.covers_fill_switch_all
#print axioms ProofFile.Honest.K5.covers_fill_switch_head
