-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchAtHead.lean: THE CODE SWITCH's 25 PLACES IN THE PROOF FILE's OWN FIRST
CHAIN (kind K2: the first place of the links 1 to 23, the second place of the head's link, the first
place behind the links), under the head at which the library's laws on that chain speak (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean): for each the update on the chain's shape with the rows' makes beside it
(ChainF, Johnson/Desc/First/Shape/ChainF.lean), NAMED, its numbers tied to values, and "CARRIES" IN
THE STRONG FORM: a yes of the seated member from s to t gives: the update returns chainF t at chainF
s. A joining of laws; nothing is evaluated.

"CARRIES" ALONE. THAT THE MEMBER's DECISION RETURNS WHERE THE UPDATE DOES IS NOT STATED HERE:
THESE 25 PLACES DO NOT COUNT AS SEATS THAT ARE PAID.

WHICH DRESS STANDS AT A LINK's PLACE IS NOT SAID HERE. The library's law on the switch's lot
(IM.K2Is, Johnson/IMR/K2Seat.lean) leaves two dresses at a place inside a link: the switch alone; or
the switch with the head's "opened" behind it. What decides is the head of the place's name in the
plan (P1K2.standsOf). So switchU bears both and chooses by the shape's own "here": between two
links: the switch alone; in the head's link, entered and unopened: the switch, then "opened". Which
dress stands is said elsewhere: at the links 1 to 23 in SwitchDress.lean (link_arm), at the head's
place in SwitchSeatEnds.lean (head_arm), both with SwitchReturns.lean's stands_at. AT THESE 23 LINKS
THE HEAD's ARM OF THE WHOLE STEP IS DEAD, AND HP IS AN IDLE LETTER: headOpenU leaves "here" at 3,
and openAttG | openLayG behind it ask 0.

  `andThen_ok`: a yes of two sub-protocols as one, cut.
  `nameless`: the three updates read no name: at any name they are the update at the empty name.
  **`switchU Z a n HP`**: THE STEP AT A PLACE INSIDE A LINK.
  **`dress_carries`**: from the library's K2Is at a place inside a link, past the mute's arm: a yes
    of the lot's sub-protocol from s to m gives switchU … (chainF s) = some (chainF m).
  `openAtt_strong`, `openLay_strong`: a yes of the frame's "opened" gives: its step returns the
    shape behind.
  **`switch_finish_at`**: the first place behind the links: finFrontU, finU, finBehindU in a row.
  **`switch_head_at`**: the second place of the head's link: switchU.
  **`switch_att_at`**, **`switch_lay_at`**: the first place of a link l, 1 ≤ l < 24: switchU, then
    the frame's "opened" on the pair (it leaves the statement: quietF).
  `quietE`, `letters_at`, `arms_at`, `switch_link`: tools for these.

Limits. As said above. switchU reads neither its place a nor a name. In switch_att_at and
switch_lay_at nothing ties Lk to the member b; in switch_att_at the premise 1 ≤ l follows from the
link's sort. switch_finish_at names its member by cF.back[0]?, with no number in the flat list (the
number, 353, is the library's IM.back_numbers'). UNDER THE HEAD: that it has a member is shown in
scope, where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean);
that these three hold together, at two named sets of public files, in a side library. At the earlier
hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Shape.SwitchEnds
import Johnson.IMR.K2Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind finishPlace headOpened decideWith finishFrontQ
  finishBehindQ headOpenQ HeadPar)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame pubOf)
open OnBytes.Maker (WholeD)
open IM (subAt k2P under K2Is k2PlaceF)
open P5J (AtMgA)

/-! ## 1 Small laws -/

theorem andThen_ok {Cl : Type} {nm : String} {p q : Block S Cl} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (Block.andThen nm p q).decide s rs gs = .ok t) :
    ∃ m, p.decide s (rs.take p.rounds.length) (gs.take p.openings) = .ok m ∧
      q.decide m (rs.drop p.rounds.length) (gs.drop p.openings) = .ok t := by
  have h' : (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind (fun s' =>
    q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok t := h
  cases hp : p.decide s (rs.take p.rounds.length) (gs.take p.openings) with
  | error e => rw [hp] at h'; exact nomatch h'
  | ok m =>
    rw [hp] at h'
    exact ⟨m, rfl, h'⟩

/-- The updates read no name. -/
theorem nameless (Z : ProofFile.Pub) (a : Place) (nm : String) (n : P1K2.Nums) :
    linkU (k2P Z a nm .link n) = linkU (k2P Z a "" .link n) ∧
      headU (k2P Z a nm .head n) = headU (k2P Z a "" .head n) ∧
      finU (k2P Z a nm .finish n) = finU (k2P Z a "" .finish n) := ⟨rfl, rfl, rfl⟩

/-! ## 2 The step at a place inside a link -/

/-- **THE STEP AT A PLACE INSIDE A LINK**: it chooses the dress by the shape's own "here". -/
def switchU (Z : ProofFile.Pub) (a : Place) (n : P1K2.Nums) (HP : HeadPar) (x : ChainF) : Option ChainF :=
  match x.1.here with
  | 0 => linkU (k2P Z a "" .link n) x
  | 4 => (headU (k2P Z a "" .head n) x).bind (headOpenU HP)
  | _ => none

theorem dress_carries {Z : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {x : Block S Unit}
    {l : Nat} {HP : HeadPar} {n : P1K2.Nums} (ha : a.link = some l)
    (hHP : P1K2.pureLetters G l = some HP)
    (harm : (∃ l' HP', a.link = some l' ∧ P1K2.pureLetters G l' = some HP' ∧
        x = under nm a ((codeSwitchKind (k2P Z a nm .head n) : Block S Unit).andThen nm
          (headOpened nm a HP'))) ∨
      (∃ l', a.link = some l' ∧ x = under nm a (codeSwitchKind (k2P Z a nm .link n))))
    {s m : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : x.decide s rs gs = .ok m) : switchU Z a n HP (chainF s) = some (chainF m) := by
  rcases harm with ⟨l', HP', hl', hH', rfl⟩ | ⟨l', -, rfl⟩
  · obtain rfl : l = l' := Option.some.inj (ha.symm.trans hl')
    obtain rfl : HP = HP' := Option.some.inj (hHP.symm.trans hH')
    obtain ⟨m₁, h1, h2⟩ := andThen_ok (nm := nm)
      (p := (codeSwitchKind (k2P Z a nm .head n) : Block S Unit)) (q := headOpened nm a HP) h
    have h1' : decideWith _root_.Tw.K2.sendByL8 (k2P Z a nm .head n) s _ _ = .ok m₁ := h1
    have h2' : headOpenQ HP m₁ = .ok m := h2
    obtain ⟨r₁, r₂, a0, G0, w, roots, -, R⟩ :=
      VerifiableInference.Desc.First.K2.head_inv (rfl : (k2P Z a nm .head n).stands = .head) h1'
    obtain ⟨a1, _, _, _, _, _, _, _, _, _, A⟩ :=
      (VerifiableInference.Desc.First.K2.headOpenQ_iff HP m₁ m).1 h2'
    have e1 : m₁.here = .head { a0 with kept := w.out.kept, ids := w.out.others } := by
      rw [R.hOut]
    have e2 : a1 = { a0 with kept := w.out.kept, ids := w.out.others } := by
      have := A.here.symm.trans e1
      injection this
    have ho : a0.opened = false := by
      have := A.fresh
      rw [e2] at this
      exact this
    have hh : (chainF s).1.here = 4 := by
      show hereNo s.here = 4
      rw [R.hHere]
      show (if a0.opened then 3 else 4) = 4
      rw [ho]
      rfl
    unfold switchU
    rw [hh]
    show (headU (k2P Z a "" .head n) (chainF s)).bind (headOpenU HP) = _
    rw [← (nameless Z a nm n).2.1, head_carries rfl h1']
    exact headOpen_carries h2'
  · have h' : decideWith _root_.Tw.K2.sendByL8 (k2P Z a nm .link n) s rs gs = .ok m := h
    obtain ⟨r₁, r₂, y, w, roots, S', f, mine, -, R⟩ :=
      VerifiableInference.Desc.First.K2.link_inv (rfl : (k2P Z a nm .link n).stands = .link) h'
    have hh : (chainF s).1.here = 0 := by
      show hereNo s.here = 0
      rw [R.hHere]
      rfl
    unfold switchU
    rw [hh]
    show linkU (k2P Z a "" .link n) (chainF s) = _
    rw [← (nameless Z a nm n).1]
    exact link_carries rfl h'

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 3 The first place behind the links -/

theorem switch_finish_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P none = some n ∧ cF.back[0]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        ((finFrontU (chainF s)).bind (finU (k2P Zp k2PlaceF "" .finish n))).bind finBehindU =
          some (chainF t) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b, y, e1, -, -, hla, harm⟩ := IM.k2_finish_of O
  have hm : b ∈ cF.back := List.mem_of_getElem? e1
  have hmem : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S ProofFile.Cl) ∈ cF.blocksInOrder := by
    unfold Chain.blocksInOrder
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, hm, rfl⟩)))
  have hp : (b.planOk && b.hasNoClaimsAndNothingAfter) = true := plans_at h _ hmem
  rw [Bool.and_eq_true] at hp
  rcases harm with ⟨h0, -⟩ | ⟨P, n, hP, hn, ex⟩
  · exfalso
    have e := hp.1
    rw [IM.alone_planOk hla] at e
    have := (IM.retype_planOk y e).1
    rw [h0] at this
    exact nomatch this
  · refine ⟨Bs, P, n, b, O.made, hP, hn, e1, fun s rs gs t hy => ?_⟩
    have h1 : y.decide s rs gs = .ok t := (IM.alone_underR hla).2 s rs gs t hy
    rw [ex] at h1
    have h1' : (finishPlace (k2P Zp k2PlaceF y.name .finish n) : Block S Unit).decide s rs gs =
      .ok t := h1
    obtain ⟨m₂, a2, a3⟩ := andThen_ok (nm := y.name) h1'
    obtain ⟨m₁, a0, a1⟩ := andThen_ok (nm := y.name) a2
    have c0 : finishFrontQ s = .ok m₁ := a0
    have c1 : decideWith _root_.Tw.K2.sendByL8 (k2P Zp k2PlaceF y.name .finish n) m₁ _ _ =
      .ok m₂ := a1
    have c2 : finishBehindQ m₂ = .ok t := a3
    rw [finFront_carries c0]
    show ((finU (k2P Zp k2PlaceF "" .finish n) (chainF m₁))).bind finBehindU = _
    rw [← (nameless Zp k2PlaceF y.name n).2.2, fin_carries rfl c1]
    exact finBehind_carries c2

/-! ## 4 The places inside the links -/

/-- The head's letters at a link that has a record. -/
theorem letters_at {G : ProofFile.Ground} {l : Nat} {X : Stages.LinkH} (h : G.built[l]? = some X) :
    ∃ HP, P1K2.pureLetters G l = some HP := by
  unfold P1K2.pureLetters
  rw [h]
  exact ⟨_, rfl⟩

/-- Past the mute's arm and the finish's, at a place inside a link. -/
theorem arms_at {Zq : ProofFile.Pub} {G : ProofFile.Ground} {a : Place} {nm : String} {y : Block S Unit}
    {l : Nat} (ha : a.link = some l) (his : K2Is Zq G a nm y) (hp : y.planOk = true) :
    ∃ P n, P1K2.prepOf Zq G = some P ∧ P1K2.numsAt P (some l) = some n ∧
      ((∃ l' HP', a.link = some l' ∧ P1K2.pureLetters G l' = some HP' ∧
        y = under nm a ((codeSwitchKind (k2P Zq a nm .head n) : Block S Unit).andThen nm
          (headOpened nm a HP'))) ∨
      (∃ l', a.link = some l' ∧ y = under nm a (codeSwitchKind (k2P Zq a nm .link n)))) := by
  obtain ⟨P, n, hP, hn, harm⟩ := his.live hp
  rw [ha] at hn
  refine ⟨P, n, hP, hn, ?_⟩
  rcases harm with ⟨h0, -⟩ | h1 | h2
  · rw [ha] at h0
    exact nomatch h0
  · exact Or.inl h1
  · exact Or.inr h2

/-- **THE SECOND PLACE OF THE HEAD's LINK.** -/
theorem switch_head_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Lk : Link S ProofFile.Cl)
        (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧ cF.links[24]? = some Lk ∧ Lk.hear[1]? = some b ∧
      cF.blocksInOrder[14 * 24 + 1 + 2]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        switchU Zp { chain := 1, link := some 24, piece := 2, kind := .K2 } n HP (chainF s) =
          some (chainF t) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, -, hla, his⟩ := IM.k2_head_of h.scope h.reads O
  have hb : b.planOk = true := plans_at h b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  have hy : y.planOk = true := by
    rw [IM.alone_planOk hla] at hb
    exact (IM.retype_planOk y hb).1
  obtain ⟨P, n, hP, hn, harm⟩ := arms_at rfl his hy
  obtain ⟨-, -, Xl, -, -, hX, -⟩ := IM.k8_alone O 24 (subAt 24)
    (IM.subs_scope h.scope h.reads O 24 (by omega)) (k8No (subAt 24)) (k8_index _ _)
    (by cases subAt 24 <;> exact ⟨by decide, by decide⟩)
  obtain ⟨HP, hHP⟩ := letters_at hX
  have q := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 24 ≤ 24) 1] at q
  refine ⟨Bs, P, n, HP, Lk, b, O.made, hP, hn, hHP, e1, e2, q, fun s rs gs t hd => ?_⟩
  exact dress_carries rfl hHP harm ((IM.alone_underR hla).2 s rs gs t hd)

/-- A yes of the frame's "opened" at an attention link: its step returns the shape behind. -/
theorem openAtt_strong (P : AttPar) (s t : S) (h : openAtt P s = .ok t) :
    openAttG P (chainSh s) = .ok (chainSh t) := by
  obtain ⟨hB, hR, a, ⟨-, ⟨f1, f2, -, -⟩, -, -⟩, he⟩ := Props.openAtt_iff.1 h
  have hfail : s.failed = none := by
    have h2 := ((S.unmarked_ok _ _).1 he).2
    rw [(openAtt_lays h).2] at h2
    exact h2
  have hb := (openB_iff P.l P.X.kind s).2 ⟨hB, hR, hfail, f1, f2⟩
  obtain ⟨-, rfl⟩ := openAtt_lays h
  unfold openAttG
  rw [if_pos hb, chainSh_att s hB]

/-- The like at a layers' link behind link 0. -/
theorem openLay_strong (P : LayPar) (s t : S) (h : openLay P s = .ok t) :
    openLayG P (chainSh s) = .ok (chainSh t) := by
  obtain ⟨hB, hR, a, ⟨-, ⟨f1, f2, -, -⟩, -, -, -, -⟩, he⟩ := Props.openLay_iff.1 h
  have hfail : s.failed = none := by
    have h2 := ((S.unmarked_ok _ _).1 he).2
    rw [(openLay_lays h).2] at h2
    exact h2
  have hb := (openB_iff P.l P.X.kind s).2 ⟨hB, hR, hfail, f1, f2⟩
  obtain ⟨-, rfl⟩ := openLay_lays h
  unfold openLayG
  rw [if_pos hb, chainSh_lay s hB]

/-- A step on the shape that may refuse by name, as a step on the pair that turns no make. -/
def quietE (g : ChainSh → Except String ChainSh) : ChainF → Option ChainF :=
  quietF fun a => (g a).toOption

/-- What stands at the first place of a link l, 1 ≤ l < 24: the letters, and the cut from a yes. -/
theorem switch_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Lk : Link S ProofFile.Cl)
        (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ cF.links[l]? = some Lk ∧
      cF.blocksInOrder[14 * l + 0 + 2]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        ∃ (fs : List LinkFrame) (f : LinkFrame) (m : S),
          framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs ∧ fs[l]? = some f ∧
          switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP (chainF s) =
            some (chainF m) ∧ f.opened m = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, -, hj, his⟩ := IM.k2_link_sits h.scope h.reads O l h1 h24
  have hb : b.planOk = true := plans_at h b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  have hy : y.planOk = true := by
    obtain ⟨fs, f, -, -, e⟩ := hj.planOk
    rw [e, Bool.and_eq_true] at hb
    exact (IM.retype_planOk y hb.1).1
  obtain ⟨P, n, hP, hn, harm⟩ := arms_at rfl his hy
  obtain ⟨-, -, Xl, -, -, hX, -⟩ := IM.k8_alone O l (subAt l)
    (IM.subs_scope h.scope h.reads O l (by omega)) (k8No (subAt l)) (k8_index _ _)
    (by cases subAt l <;> exact ⟨by decide, by decide⟩)
  obtain ⟨HP, hHP⟩ := letters_at hX
  have q := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) 0] at q
  refine ⟨Bs, P, n, HP, Lk, b, O.made, hP, hn, hHP, e1, q, fun s rs gs t hd => ?_⟩
  obtain ⟨fs, f, m, hfs, hf, d1, -, d2, -, -⟩ := hj.yes hd
  exact ⟨fs, f, m, hfs, hf, dress_carries rfl hHP harm d1, d2⟩

/-- **THE FIRST PLACE OF AN ATTENTION LINK.** -/
theorem switch_att_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .attention) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (p : Attention.Plan) (Lk : Link S ProofFile.Cl) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.A[Y.g]? = some p ∧ cF.links[l]? = some Lk ∧ cF.blocksInOrder[14 * l + 0 + 2]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP (chainF s)).bind
          (quietE (openAttG (attPar Y p l))) = some (chainF t) := by
  obtain ⟨Bs, P, n, HP, Lk, b, a1, a2, a3, a4, a5, a6, hc⟩ := switch_link h l h1 h24
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain ⟨-, fs₀, hfs₀, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨-, f₀, -, -, -, -, -, hf₀, -⟩ := hall l (by omega)
  obtain ⟨Y, p, hY, hA, -, eo, -⟩ := row_att h (by omega : l < 25) hs hfs₀ hf₀
  refine ⟨Bs, P, n, HP, Y, p, Lk, b, a1, a2, a3, a4, hY, hA, a5, a6, fun s rs gs t hd => ?_⟩
  obtain ⟨fs, f, m, hfs, hf, c1, c2⟩ := hc s rs gs t hd
  obtain rfl : fs₀ = fs := Except.ok.inj (hfs₀.symm.trans hfs)
  obtain rfl : f₀ = f := Option.some.inj (hf₀.symm.trans hf)
  rw [eo] at c2
  rw [c1]
  show quietE (openAttG (attPar Y p l)) (chainF m) = _
  unfold quietE quietF
  show ((openAttG (attPar Y p l) (chainSh m)).toOption).map (·, formsOf m.st) = _
  rw [openAtt_strong _ m t c2]
  obtain ⟨-, rfl⟩ := openAtt_lays c2
  rfl

/-- **THE FIRST PLACE OF A LAYERS' LINK BEHIND LINK 0.** -/
theorem switch_lay_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .layers) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (hp : Layer.HPlan2) (Lk : Link S ProofFile.Cl) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.G[Y.g]? = some hp ∧ cF.links[l]? = some Lk ∧ cF.blocksInOrder[14 * l + 0 + 2]? = some b ∧
      ∀ s rs gs t, b.decide s rs gs = .ok t →
        (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP (chainF s)).bind
          (quietE (openLayG (layPar Zp.p.X Y hp l))) = some (chainF t) := by
  obtain ⟨Bs, P, n, HP, Lk, b, a1, a2, a3, a4, a5, a6, hc⟩ := switch_link h l h1 h24
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain ⟨-, fs₀, hfs₀, hall⟩ := IM.frame_of h.scope h.reads O
  obtain ⟨-, f₀, -, -, -, -, -, hf₀, -⟩ := hall l (by omega)
  obtain ⟨Y, hp, hY, hG, -, eo, -⟩ :=
    row_lay h (by omega : l < 25) (by omega : l ≠ 0) hs hfs₀ hf₀
  refine ⟨Bs, P, n, HP, Y, hp, Lk, b, a1, a2, a3, a4, hY, hG, a5, a6, fun s rs gs t hd => ?_⟩
  obtain ⟨fs, f, m, hfs, hf, c1, c2⟩ := hc s rs gs t hd
  obtain rfl : fs₀ = fs := Except.ok.inj (hfs₀.symm.trans hfs)
  obtain rfl : f₀ = f := Option.some.inj (hf₀.symm.trans hf)
  rw [eo] at c2
  rw [c1]
  show quietE (openLayG (layPar Zp.p.X Y hp l)) (chainF m) = _
  unfold quietE quietF
  show ((openLayG (layPar Zp.p.X Y hp l) (chainSh m)).toOption).map (·, formsOf m.st) = _
  rw [openLay_strong _ m t c2]
  obtain ⟨-, rfl⟩ := openLay_lays c2
  rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.switch_head_at
#print axioms Johnson.AtFull.Shape.openAtt_strong
#print axioms Johnson.AtFull.Shape.openLay_strong
#print axioms Johnson.AtFull.Shape.switch_att_at
#print axioms Johnson.AtFull.Shape.switch_lay_at
#print axioms Johnson.AtFull.Shape.nameless
#print axioms Johnson.AtFull.Shape.dress_carries
#print axioms Johnson.AtFull.Shape.switch_finish_at
#print axioms Johnson.AtFull.Shape.andThen_ok
#print axioms Johnson.AtFull.Shape.switchU
#print axioms Johnson.AtFull.Shape.letters_at
#print axioms Johnson.AtFull.Shape.arms_at
#print axioms Johnson.AtFull.Shape.quietE
#print axioms Johnson.AtFull.Shape.switch_link
