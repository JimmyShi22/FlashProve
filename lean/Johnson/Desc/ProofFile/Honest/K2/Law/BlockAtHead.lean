-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/BlockAtHead.lean: the kind "the code switch" (K2): TWO FIELDS
OF THE RECORD `K2SeatedL` (Honest/K2/SeatedL.lean), shape AND decides, IN THE RECORD's OWN TEXT,
UNDER THE LIBRARY's HEAD AND THE OPENING, AT EACH SWITCH OF THE PLAN: of the block that stands in
the first chain's flat list at the number where the written list of places first bears the switch's
place. THE DECISION, BOTH WAYS, IS THE LIBRARY's OWN, SEALED: `link_seat_decides`
(Johnson/Desc/K2/Honest/Returns/SeatAtLinks.lean), `head_seat_decides`, `fin_seat_decides`
(Returns/SeatAtArms.lean): HERE THE THREE ARE JOINED INTO ONE LAW OVER THE 25 PLACES, and the
block's place, rounds and oracle messages are added, by the same steps. Two definitions: a public
test and a form; one closed fact by evaluation in Lean's kernel; lemmas.

  `link_block_shape`, `head_block_shape`, `fin_block_shape`   the block at 14 l + 2 (1 ≤ l < 24),
                    at 339, at 353: its place; its rounds and oracle messages are the kind's at the
                    plan's numbers, whatever place, name and dress the numbers are laid under; AND
                    THE WAY DOWN AT ANY ROUNDS AND GROUPS: a yes of the block holds a yes of the
                    kind's own decision at the first two rounds and the first groups, as many as
                    the place reads trees
  `switchArmNo`, `switchArmNosW`   A PUBLIC TEST: a written place is a link's first place, the
                    head's link's second or the one behind the links, and the written list of places
                    first bears it at that arm's number; BY LEAN's KERNEL at the 25 written places
  `SwitchArm`       A FORM: which terms before and after are, arm by arm: at a link: nothing;
                    `leaveOpened` f · at the head's link: nothing; `headOpenQ` HP, then the guards ·
                    behind the links: `finishFrontQ`; `finishBehindQ`, then the guards
  `k2_block_at_head`   THE END: there are the plan's numbers n, a name nm, a dress st, and the
                    place's own steps before and after, with `SwitchArm`, shape, decides and the way
                    down at q := `IM.k2P` Zp p.place nm st n

By, sealed: the three tops named · `link_dress`, `head_dress` · `k2_link_sits`, `Joined`
(Johnson/IMR/FirstSeats.lean, SameSpot.lean) · `k2_head_of`, `k2_finish_of`
(Johnson/IMR/K2Seat.lean) · `alone_place`, `alone_rounds`, `alone_oracles`
(Johnson/IMR/SeatForm.lean) · `with_iff`, `alone_iff`, `leaveOpened_iff`, `guards_iff`
(Returns/SeatIff.lean) · `andThen_ok` (Johnson/Desc/K12/FrameLaws.lean) · `tests_at_head`
(Returns/UnderHead.lean). Ours: `places_at_head` (Honest/K2/Law/PlacesWritten.lean). Kin, ours, not
imported: `link_seat_shape` (Johnson/Desc/K2/Honest/Returns/SeatYes.lean): `link_block_shape`'s end
at the links.

Limits. THE BLOCK's TEXT ALONE: its place, rounds, oracle messages and decision: no coin, input or
run occurs. THAT THE DECISION SAYS YES ANYWHERE IS NOT SAID. before and after stand under "there
are"; `SwitchArm` says which terms they are. The full size and the format's second hash function alone. The
head and the opening are premises; that they can be met is not said. All limits of the sealed files
named stand. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Returns.SeatAtArms
import Johnson.Desc.K2.Honest.Returns.UnderHead
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind decideWith rounds HeadPar headOpenQ headOpened
  finishFrontQ finishBehindQ finishPlace finishFrontQ_rest)
open VerifiableInference.Desc.K2.Honest.Returns (switchPlaceAt headPlaceAt link_dress head_dress
  link_seat_decides head_seat_decides fin_seat_decides tests_at_head with_iff alone_iff
  leaveOpened_iff guards_iff k2_openings)
open VerifiableInference.Desc.K12 (andThen_ok)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open P1K2 (Prep Nums numsAt prepOf guards leaveOpened)
open IM (k2P under k2PlaceF)
open _root_.Tw.K2 (sendByL8)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)

/-! ## 1 The block's place, rounds and oracle messages, arm by arm -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At 14 l + 2, 1 ≤ l < 24.** -/
theorem link_block_shape (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) :
    ∃ (b : Block S Cl) (Pp : Prep) (n : Nums), c.blocksInOrder[14 * l + 2]? = some b ∧
      prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some l) = some n ∧ b.place = switchPlaceAt l ∧
      (∀ (a : Place) (nm : String) (st : At), b.rounds = rounds (k2P Z a nm st n) ∧
        b.oracles = [(k2P Z a nm st n).sent, []]) ∧
      ∀ (nm : String) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        b.decide s rs gs = .ok t → ∃ fs f m, framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
          fs[l]? = some f ∧
          decideWith sendByL8 (k2P Z (switchPlaceAt l) nm .link n) s (rs.take 2)
            (gs.take n.read.length) = .ok m ∧ leaveOpened f s m = .ok t := by
  obtain ⟨Lk, b, x, e1, e2, hx, J, hi⟩ := IM.k2_link_sits hS hR O l h1 h24
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 0] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  obtain ⟨fs, f, hfs, hff, ep⟩ := J.planOk
  rw [hb] at ep
  obtain ⟨hq, hfp⟩ := Bool.and_eq_true_iff.1 ep.symm
  have hxp := (IM.retype_planOk x hq).1
  have hpc : x.place = (switchPlaceAt l) := by
    obtain ⟨_, _, -, -, arms⟩ := hi.live hxp
    rcases arms with ⟨-, e⟩ | ⟨_, _, -, -, e⟩ | ⟨_, -, e⟩ <;> rw [e] <;> rfl
  obtain ⟨Pp, n, hP, hn, ex⟩ := link_dress hS hR O hpl hcut h24 hx hxp hpc
  have hr : b.rounds = (x.retype : Block S Cl).rounds := J.rounds
  obtain ⟨fs', f', hfs', hff', e⟩ := J
  have ho : b.oracles = (x.retype : Block S Cl).oracles := by
    rw [e]
    show (x.retype : Block S Cl).oracles ++ [] = (x.retype : Block S Cl).oracles
    rw [List.append_nil]
  have hpl' : b.place = switchPlaceAt l := by
    rw [e]
    rfl
  refine ⟨b, Pp, n, by simpa using hf, hP, hn, hpl', fun a nm st => ⟨?_, ?_⟩, ?_⟩
  · rw [hr, ex]
    rfl
  · rw [ho, ex]
    rfl
  · intro nm s t rs gs hy
    have hk7 : (switchPlaceAt l).kind ≠ KindName.K7 := by
      intro h7
      cases h7
    rw [e, with_iff hk7] at hy
    obtain ⟨m, d1, d2, d3, d4, d5⟩ := hy
    obtain ⟨o1, o2⟩ := (IM.guardMark_yes _ m t _ _).1 d3
    have hr' : (x.retype : Block S Cl).rounds.length = 2 := by
      rw [ex]
      rfl
    have hg' : (x.retype : Block S Cl).openings = n.read.length := by
      rw [ex]
      exact k2_openings (C := Unit) (k2P Z (switchPlaceAt l) x.name .link n)
    rw [hr', hg'] at d1
    have d1' : decideWith sendByL8 (k2P Z (switchPlaceAt l) nm .link n) s (rs.take 2)
        (gs.take n.read.length) = .ok m := by
      rw [ex] at d1
      exact d1
    exact ⟨fs', f', m, hfs', hff', d1', (leaveOpened_iff f' s m t).2 ⟨d2, o1, o2, d4, d5⟩⟩

/-- **At 339.** -/
theorem head_block_shape (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) :
    ∃ (b : Block S Cl) (Pp : Prep) (n : Nums), c.blocksInOrder[339]? = some b ∧
      prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some 24) = some n ∧ b.place = headPlaceAt ∧
      (∀ (a : Place) (nm : String) (st : At), b.rounds = rounds (k2P Z a nm st n) ∧
        b.oracles = [(k2P Z a nm st n).sent, []]) ∧
      ∀ (nm : String) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        b.decide s rs gs = .ok t → ∃ HP u, P1K2.pureLetters Bs.G₀ 24 = some HP ∧
          decideWith sendByL8 (k2P Z headPlaceAt nm .head n) s (rs.take 2)
            (gs.take n.read.length) = .ok u ∧ (headOpenQ HP u).bind (guards s) = .ok t := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  have hpc : x.place = headPlaceAt := by
    obtain ⟨_, _, -, -, arms⟩ := hi.live hxp
    rcases arms with ⟨-, e⟩ | ⟨_, _, -, -, e⟩ | ⟨_, -, e⟩ <;> rw [e] <;> rfl
  obtain ⟨Pp, n, HP, hP, hn, hHP, ex⟩ := head_dress hS hR O hpl hcut hx hxp hpc
  refine ⟨b, Pp, n, hf, hP, hn, IM.alone_place hl, fun a nm st => ⟨?_, ?_⟩, ?_⟩
  · rw [IM.alone_rounds hl, ex]
    rfl
  · rw [IM.alone_oracles hl, ex]
    rfl
  · intro nm s t rs gs hy
    have hk7 : headPlaceAt.kind ≠ KindName.K7 := by
      intro h7
      cases h7
    obtain ⟨m, a, g⟩ := (alone_iff hl hk7 s t rs gs).1 hy
    have a' : ((codeSwitchKind (k2P Z headPlaceAt x.name .head n) : Block S Unit).andThen x.name
        (headOpened x.name headPlaceAt HP)).decide s rs gs = .ok m := by
      rw [ex] at a
      exact a
    obtain ⟨u, a1, a2⟩ := (andThen_ok _ _ _ _ _ _ _).1 a'
    rw [k2_openings] at a1
    exact ⟨HP, u, hHP, a1, (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨m, a2, g⟩⟩

/-- **At 353.** -/
theorem fin_block_shape (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) :
    ∃ (b : Block S Cl) (Pp : Prep) (n : Nums), c.blocksInOrder[353]? = some b ∧
      prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧ b.place = k2PlaceF ∧
      (∀ (a : Place) (nm : String) (st : At), b.rounds = rounds (k2P Z a nm st n) ∧
        b.oracles = [(k2P Z a nm st n).sent, []]) ∧
      ∀ (nm : String) (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
        b.decide s rs gs = .ok t → ∃ s₁ u, finishFrontQ s = .ok s₁ ∧
          decideWith sendByL8 (k2P Z k2PlaceF nm .finish n) s₁ (rs.take 2)
            (gs.take n.read.length) = .ok u ∧ (finishBehindQ u).bind (guards s₁) = .ok t := by
  obtain ⟨b, x, e1, hx, -, hl, hi⟩ := IM.k2_finish_of O
  have hb := P1K2.back_planOk O hpl (List.mem_of_getElem? e1)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  obtain ⟨Pp, n, hP, hn, ex⟩ : ∃ Pp n, prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧
      x = under x.name k2PlaceF (finishPlace (k2P Z k2PlaceF x.name .finish n)) := by
    rcases hi with ⟨h0, -⟩ | h
    · rw [h0] at hxp
      cases hxp
    · exact h
  have hf := IM.back_at_flat e1
  rw [(IM.links_flat_352 hS hR O).1, (IM.links_flat_352 hS hR O).2] at hf
  refine ⟨_, Pp, n, hf, hP, hn, ?_, fun a nm st => ⟨?_, ?_⟩, ?_⟩
  · show b.place = k2PlaceF
    exact IM.alone_place hl
  · show b.rounds = _
    rw [IM.alone_rounds hl, ex]
    rfl
  · show b.oracles = _
    rw [IM.alone_oracles hl, ex]
    rfl
  · intro nm s t rs gs hy
    have hy' : b.decide s rs gs = .ok t := hy
    have hk7 : k2PlaceF.kind ≠ KindName.K7 := by
      intro h7
      cases h7
    obtain ⟨m, a, g⟩ := (alone_iff hl hk7 s t rs gs).1 hy'
    have a' : (Block.andThen x.name (Block.andThen x.name
        (VerifiableInference.Desc.roundlessBlock (x.name ++ ": front") k2PlaceF.chain k2PlaceF.link
          k2PlaceF.piece finishFrontQ) (codeSwitchKind (k2P Z k2PlaceF x.name .finish n) : Block S Unit))
        (VerifiableInference.Desc.roundlessBlock (x.name ++ ": behind") k2PlaceF.chain k2PlaceF.link
          k2PlaceF.piece finishBehindQ)).decide s rs gs = .ok m := by
      rw [ex] at a
      exact a
    obtain ⟨u, b1, b2⟩ := (andThen_ok _ _ _ _ _ _ _).1 a'
    obtain ⟨s₁, c1, c2⟩ := (andThen_ok _ _ _ _ _ _ _).1 b1
    have c1' : finishFrontQ s = .ok s₁ := c1
    have hO : (Block.andThen x.name
        (VerifiableInference.Desc.roundlessBlock (x.name ++ ": front") k2PlaceF.chain k2PlaceF.link
          k2PlaceF.piece finishFrontQ)
        (codeSwitchKind (k2P Z k2PlaceF x.name .finish n) : Block S Unit)).openings = n.read.length :=
      k2_openings (C := Unit) (k2P Z k2PlaceF x.name .finish n)
    rw [hO] at c2
    have c2' : decideWith sendByL8 (k2P Z k2PlaceF nm .finish n) s₁ (rs.take 2)
        (gs.take n.read.length) = .ok u := c2
    have b2' : finishBehindQ u = .ok m := b2
    have g' : guards s₁ m = .ok t := by
      rw [guards_iff] at g ⊢
      have eo : ProofFile.sameReply s₁ m = ProofFile.sameReply s m := by
        show (s₁.out.reply == m.out.reply) = (s.out.reply == m.out.reply)
        rw [(finishFrontQ_rest c1').2.2.2.2.2.1]
      rw [eo]
      exact g
    exact ⟨s₁, u, c1', c2', (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨m, b2', g'⟩⟩

end

/-! ## 2 Which arm a written place is -/

/-- **A PUBLIC TEST**: 0: a link's first place, 1 ≤ l < 24, borne first at 14 l + 2 · 1: the head's
link's second place, at 339 · 2: the place behind the links, at 353 · 3: none of these. -/
def switchArmNo (p : SwitchPlace) : Nat :=
  if p.place == switchPlaceAt p.link && decide (1 ≤ p.link) && decide (p.link < 24) &&
      P5J.At.ps.findIdx (· == p.place) == 14 * p.link + 2 then 0
  else if p.place == headPlaceAt && P5J.At.ps.findIdx (· == p.place) == 339 then 1
  else if p.place == k2PlaceF && P5J.At.ps.findIdx (· == p.place) == 353 then 2
  else 3

set_option maxRecDepth 1000000 in
/-- **At the written places**: 23 links, then the head's link, then the place behind the links. -/
theorem switchArmNosW : placesW.map switchArmNo = List.replicate 23 0 ++ [1, 2] := by
  decide +kernel

/-! ## 3 Under the head -/

/-- **WHICH TERMS before AND after ARE, ARM BY ARM.** st: the dress. In each arm: the place, and the
number where the written list of places first bears it (14 l + 2 | 339 | 353). At a link's first
place: nothing in front; behind: `leaveOpened` f, f: the link's own row of `framesOf`, whose test on
the plan says yes. At the head's link's second place: nothing in front; behind: `headOpenQ` HP, HP:
the ground's own letters at link 24, then the guards. Behind the links: `finishFrontQ` in front;
behind: `finishBehindQ`, then the guards. A definition: a form for whoever must speak of the two
steps. -/
def SwitchArm (Zp : ProofFile.Pub) (G : ProofFile.Ground) (p : SwitchPlace) (st : At)
    (before : S → Except String S) (after : S → S → Except String S) : Prop :=
  (st = .link ∧ p.place = switchPlaceAt p.link ∧ 1 ≤ p.link ∧ p.link < 24 ∧
    P5J.At.ps.findIdx (· == p.place) = 14 * p.link + 2 ∧ before = (fun s => .ok s) ∧
    ∃ fs f, framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs ∧
      fs[p.link]? = some f ∧ f.plan = true ∧ after = leaveOpened f) ∨
  (st = .head ∧ p.place = headPlaceAt ∧ P5J.At.ps.findIdx (· == p.place) = 339 ∧
    before = (fun s => .ok s) ∧
    ∃ HP, P1K2.pureLetters G 24 = some HP ∧
      after = fun s u => (headOpenQ HP u).bind (guards s)) ∨
  (st = .finish ∧ p.place = k2PlaceF ∧ P5J.At.ps.findIdx (· == p.place) = 353 ∧
    before = finishFrontQ ∧
    after = fun s₁ u => (finishBehindQ u).bind (guards s₁))

variable {W : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {p : SwitchPlace} {blk : Block S ProofFile.Cl}

/-- **shape AND decides, IN THE RECORD's OWN TEXT, AT A SWITCH OF THE PLAN**, with `SwitchArm` in
front and the way down at any rounds and groups behind. member: the record's field, at the head's
letters. -/
theorem k2_block_at_head (h : P5J.AtMgA OnBytes.secondHashFunction W D r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction W.pol W.lay W.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (member : cF.blocksInOrder[P5J.At.ps.findIdx (· == p.place)]? = some blk) :
    ∃ (Pp : Prep) (n : Nums) (nm : String) (st : At) (before : S → Except String S)
      (after : S → S → Except String S),
      prepOf Zp Bs.G₀ = some Pp ∧ numsAt Pp p.place.link = some n ∧
      SwitchArm Zp Bs.G₀ p st before after ∧
      (blk.place = p.place ∧ blk.rounds = rounds (k2P Zp p.place nm st n) ∧
        blk.oracles = [(k2P Zp p.place nm st n).sent, []]) ∧
      (∀ s rs gs t, rs.length = 2 → gs.length = (k2P Zp p.place nm st n).read.length →
        (blk.decide s rs gs = .ok t ↔ ∃ s₁ m, before s = .ok s₁ ∧
          decideWith sendByL8 (k2P Zp p.place nm st n) s₁ rs gs = .ok m ∧
            after s₁ m = .ok t)) ∧
      ∀ s rs gs t, blk.decide s rs gs = .ok t → ∃ s₁ m, before s = .ok s₁ ∧
        decideWith sendByL8 (k2P Zp p.place nm st n) s₁ (rs.take 2)
          (gs.take (k2P Zp p.place nm st n).read.length) = .ok m ∧ after s₁ m = .ok t := by
  have hpW : p ∈ placesW := by
    rw [← places_at_head h.toAtMg O]
    exact hp
  have hcut := (tests_at_head h.toAtMg O).2.1
  have ha : switchArmNo p = 0 ∨ switchArmNo p = 1 ∨ switchArmNo p = 2 := by
    have hm : switchArmNo p ∈ placesW.map switchArmNo := List.mem_map.2 ⟨p, hpW, rfl⟩
    rw [switchArmNosW, List.mem_append] at hm
    rcases hm with hm | hm
    · exact Or.inl (List.eq_of_mem_replicate hm)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      exact Or.inr hm
  unfold switchArmNo at ha
  split at ha
  · rename_i c0
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
      decide_eq_true_eq] at c0
    obtain ⟨⟨⟨ep, h1⟩, h24⟩, ei⟩ := c0
    have ep' : p.place = switchPlaceAt p.link := beq_iff_eq.1 ep
    rw [beq_iff_eq.1 ei] at member
    obtain ⟨b, nm, fs, f, Pp, n, hb, hfs, hff, hfp, hP, hn, hd⟩ :=
      link_seat_decides h.scope h.reads O h.laid.planOk hcut h1 h24
    obtain ⟨b', Pp', n', hb', hP', hn', s1, s2, s3⟩ :=
      link_block_shape h.scope h.reads O h.laid.planOk hcut h1 h24
    obtain rfl : b = blk := Option.some.inj (hb.symm.trans member)
    obtain rfl : b' = b := Option.some.inj (hb'.symm.trans member)
    obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
    obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
    have hA : SwitchArm Zp Bs.G₀ p .link (fun s => .ok s) (leaveOpened f) :=
      Or.inl ⟨rfl, ep', h1, h24, beq_iff_eq.1 ei, rfl, fs, f, hfs, hff, hfp, rfl⟩
    rw [ep']
    refine ⟨Pp', n', nm, .link, fun s => .ok s, leaveOpened f, hP, hn, hA,
      ⟨s1, (s2 _ nm .link).1, (s2 _ nm .link).2⟩, fun s rs gs t hr hg => ?_,
      fun s rs gs t hy => ?_⟩
    · rw [hd s t rs gs hr hg]
      constructor
      · rintro ⟨m, a1, a2⟩
        exact ⟨s, m, rfl, a1, a2⟩
      · rintro ⟨s₁, m, e, a1, a2⟩
        obtain rfl : s = s₁ := Except.ok.inj e
        exact ⟨m, a1, a2⟩
    · obtain ⟨fs₂, f₂, m, hfs₂, hff₂, d1, d2⟩ := s3 nm s t rs gs hy
      obtain rfl : fs₂ = fs := Except.ok.inj (hfs₂.symm.trans hfs)
      obtain rfl : f₂ = f := Option.some.inj (hff₂.symm.trans hff)
      exact ⟨s, m, rfl, d1, d2⟩
  · split at ha
    · rename_i c1
      rw [Bool.and_eq_true] at c1
      have ep' : p.place = headPlaceAt := beq_iff_eq.1 c1.1
      rw [beq_iff_eq.1 c1.2] at member
      obtain ⟨b, nm, HP, Pp, n, hb, hHP, hP, hn, hd⟩ :=
        head_seat_decides h.scope h.reads O h.laid.planOk hcut
      obtain ⟨b', Pp', n', hb', hP', hn', s1, s2, s3⟩ :=
        head_block_shape h.scope h.reads O h.laid.planOk hcut
      obtain rfl : b = blk := Option.some.inj (hb.symm.trans member)
      obtain rfl : b' = b := Option.some.inj (hb'.symm.trans member)
      obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
      obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
      have hA : SwitchArm Zp Bs.G₀ p .head (fun s => .ok s)
          (fun s u => (headOpenQ HP u).bind (guards s)) :=
        Or.inr (Or.inl ⟨rfl, ep', beq_iff_eq.1 c1.2, rfl, HP, hHP, rfl⟩)
      rw [ep']
      refine ⟨Pp', n', nm, .head, fun s => .ok s, fun s u => (headOpenQ HP u).bind (guards s),
        hP, hn, hA, ⟨s1, (s2 _ nm .head).1, (s2 _ nm .head).2⟩, fun s rs gs t hr hg => ?_,
        fun s rs gs t hy => ?_⟩
      · rw [hd s t rs gs hr hg]
        constructor
        · rintro ⟨m, a1, a2⟩
          exact ⟨s, m, rfl, a1, a2⟩
        · rintro ⟨s₁, m, e, a1, a2⟩
          obtain rfl : s = s₁ := Except.ok.inj e
          exact ⟨m, a1, a2⟩
      · obtain ⟨HP₂, u, hHP₂, d1, d2⟩ := s3 nm s t rs gs hy
        obtain rfl : HP₂ = HP := Option.some.inj (hHP₂.symm.trans hHP)
        exact ⟨s, u, rfl, d1, d2⟩
    · split at ha
      · rename_i c2
        rw [Bool.and_eq_true] at c2
        have ep' : p.place = k2PlaceF := beq_iff_eq.1 c2.1
        rw [beq_iff_eq.1 c2.2] at member
        obtain ⟨b, nm, Pp, n, hb, hP, hn, hd⟩ :=
          fin_seat_decides h.scope h.reads O h.laid.planOk
        obtain ⟨b', Pp', n', hb', hP', hn', s1, s2, s3⟩ :=
          fin_block_shape h.scope h.reads O h.laid.planOk
        obtain rfl : b = blk := Option.some.inj (hb.symm.trans member)
        obtain rfl : b' = b := Option.some.inj (hb'.symm.trans member)
        obtain rfl : Pp' = Pp := Option.some.inj (hP'.symm.trans hP)
        obtain rfl : n' = n := Option.some.inj (hn'.symm.trans hn)
        have hA : SwitchArm Zp Bs.G₀ p .finish finishFrontQ
            (fun s₁ u => (finishBehindQ u).bind (guards s₁)) :=
          Or.inr (Or.inr ⟨rfl, ep', beq_iff_eq.1 c2.2, rfl, rfl⟩)
        rw [ep']
        exact ⟨Pp', n', nm, .finish, finishFrontQ,
          fun s₁ u => (finishBehindQ u).bind (guards s₁), hP, hn, hA,
          ⟨s1, (s2 _ nm .finish).1, (s2 _ nm .finish).2⟩,
          fun s rs gs t hr hg => hd s t rs gs hr hg, fun s rs gs t hy => s3 nm s t rs gs hy⟩
      · rcases ha with e | e | e <;> cases e

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.link_block_shape
#print axioms ProofFile.Honest.K2.Law.head_block_shape
#print axioms ProofFile.Honest.K2.Law.fin_block_shape
#print axioms ProofFile.Honest.K2.Law.switchArmNo
#print axioms ProofFile.Honest.K2.Law.switchArmNosW
#print axioms ProofFile.Honest.K2.Law.SwitchArm
#print axioms ProofFile.Honest.K2.Law.k2_block_at_head
