-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/SeatAtArms.lean: FROM THE CODE SWITCH's OWN SUB-PROTOCOL TO THE ONE
THAT THE PROOF FILE's DESCRIPTION SEATS, AT THE TWO ARMS: THE NUMBERS 339 (the output head's switch)
AND 353 (behind the last segment) OF THE FIRST CHAIN's FLAT LIST: THE SEATED DECISION, BOTH WAYS, AT
ALL STATES, at two rounds and as many groups of columns as the place reads trees. AT 339: nothing in
front · the kind's own in the head's dress · then "H.1.quiet" (`headOpenQ HP`) and the seat's two
guards. AT 353: "F.0.front" (`finishFrontQ`) in front · the kind's own in the finish's dress, at the
state that the front returns · then "F.0.quiet" (`finishBehindQ`) and the two guards. In the goals'
scope, at an opening, under the plan's own test; at 339 under the written cut too. Statements with
their proofs: unfolding and calls.

  `headJoined_iff`, `finishPlace_iff` the kind's own with "H.1.quiet" behind; the place "F:1": each
                    decision both ways, at all numbers p
  `head_dress` at the head's link the lot's live sub-protocol is the kind's own in the HEAD's dress
                    with "H.1.quiet" joined behind, at the plan's numbers
  `head_seat_decides` there are b, nm, HP, Pp, n: b is entry 339 · HP are the lot's letters of link
                    24 · n the plan's numbers · b.decide s rs gs = ok t ↔ ∃ u, the kind's own
                    decision at s returns u ∧ (headOpenQ HP u).bind (guards s) = ok t
  `fin_seat_decides` there are b, nm, Pp, n: b is entry 353 · n the plan's numbers · b.decide s rs
                    gs = ok t ↔ ∃ s₁ u, finishFrontQ s = ok s₁ ∧ the kind's own decision at s₁
                    returns u ∧ (finishBehindQ u).bind (guards s₁) = ok t

By, this folder's: `alone_iff`, `guards_iff` (Returns/SeatIff.lean) · `k2_openings`
(Returns/SeatAtLinks.lean). The library's: `k2_head_of`, `k2_finish_of`, `K2Is.live`, `k2P`,
`under`, `k2PlaceF` (Johnson/IMR/K2Seat.lean) · `hear_at_flat` (Johnson/IMR/FlatIx.lean),
`flatIx_scope` (Johnson/IMR/FlatScope.lean), `back_at_flat`, `links_flat_352`
(Johnson/IMR/BackSeat.lean) · `flat_planOk`, `back_planOk` (Johnson/P1K2R/SitsDoor.lean),
`laid_planOk`, `retype_planOk` (Johnson/IMR/SeatForm.lean) · `seated_is_pAt`, `dressOf`
(Johnson/Top/H0/K2Caller/PAtSeated.lean), `spots_open` (Johnson/Loose/H2K12/SpotsAtAll.lean),
`links25_open` (Johnson/Loose/H2K12/HsAtAll.lean) · `headOpenQ`, `headOpened`
(Johnson/Top/H0/Tw/K2C/Head.lean), `finishFrontQ`, `finishBehindQ`, `finishPlace`
(Johnson/Top/H0/Tw/K2C/Finish.lean), `finishFrontQ_rest` (Johnson/Top/H0/Tw/K2C/FinFront.lean) ·
`guards` (Johnson/P1K2R/SitsStep.lean) · `andThen_ok` (Johnson/Desc/K12/FrameLaws.lean): two
sub-protocols as one, the decision both ways · `Except.bind_eq_ok`
(Johnson/Top/H0/StepLaws/StepLaws.lean). NEAR RELATIVES, NOT CALLED: THE DOORS' OWN TEXTS, EACH BOTH
WAYS: `finishFrontQ_iff`, `finishBehindQ_iff`, `headOpenQ_iff` (Johnson/Top/H0/Tw/K2C/Asks.lean):
for whoever goes on to "the way out returns" · `andThen_decide` (Johnson/Desc/K13/Law/Then.lean): an
equation where the first half takes all rounds and groups · ONE WAY: `andThen_yes`
(Johnson/IMR/FoldTools.lean, Johnson/Desc/K1/Law/SitsKey.lean), two more `andThen_ok`
(Johnson/Desc/Kinds/Law/HeadPlanesFive.lean, Johnson/Desc/Reads/LiesBehind.lean) · `k02_sits_pAt`,
`sits_head_at`, `sits_finish_at` (Johnson/Top/H0/K2Caller/SitsAtP.lean): THE NEAREST: at all 25
places, in one dress, settled by the same two tests, through the same doors by name: the way down at
the step alone · `k02_sits_step`, `SitsAt` (Johnson/P1K2R/SitsStep.lean): the like with the dress
left open at a link.

Limits. THE TWO-WAY SENTENCE ALONE: THAT A WAY IN OR A WAY OUT RETURNS IS NOT SAID, AT ANY STATE. AT
339 THE WAY OUT TESTS MORE THAN SHAPES: `headOpenQ` asks that a reply lies in the seat and is an
entry of the vocabulary, and, through `S.covered`, four things of the request's words: so that it
returns behind every yes cannot be had from shapes alone. At the decision, not at the step. At 353
the entry of the flat list is the chain's back's first with its test on the plan narrowed
(`back_at_flat`): the decision is the same. The plan's own test, and at 339 the written cut, are
premises. At the format's second hash function alone. This file's imports are heavy. Nothing on any
property.



-/
import Johnson.Desc.K2.Honest.Returns.SeatAtLinks
import Johnson.IMR.BackSeat
import Johnson.Desc.K12.FrameLaws
import Johnson.Top.H0.Tw.K2C.FinFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith rounds HeadPar headOpenQ headOpened
  finishFrontQ finishBehindQ finishPlace finishFrontQ_rest)
open VerifiableInference.Desc.First.K2Caller (seated_is_pAt dressOf)
open VerifiableInference.Desc.K12 (andThen_ok)
open VerifiableInference.PlanWritten (cutOf cutFirstFull)
open P1K2 (Prep Nums numsAt prepOf guards)
open IM (k2P under k2PlaceF)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)

/-- The output head's switch's place, as the description writes it. -/
abbrev headPlaceAt : Place := { chain := 1, link := some 24, piece := 2, kind := .K2 }

/-- The kind's own with "H.1.quiet" joined behind: the decision, both ways. -/
theorem headJoined_iff {C : Type} (p : P2) (nm : String) (a : Place) (HP : HeadPar) (s m : S)
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hr : rs.length = 2)
    (hg : gs.length = p.read.length) :
    ((codeSwitchKind p : Block S C).andThen nm (headOpened nm a HP)).decide s rs gs = .ok m ↔
      ∃ u, decideWith sendByL8 p s rs gs = .ok u ∧ headOpenQ HP u = .ok m := by
  rw [andThen_ok, k2_openings]
  have hL : (codeSwitchKind p : Block S C).rounds.length = 2 := rfl
  rw [hL, List.take_of_length_le (le_of_eq hr), List.take_of_length_le (le_of_eq hg)]
  exact Iff.rfl

/-- The place "F:1": the decision, both ways. -/
theorem finishPlace_iff {C : Type} (p : P2) (s m : S) {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hr : rs.length = 2)
    (hg : gs.length = p.read.length) :
    (finishPlace p : Block S C).decide s rs gs = .ok m ↔
      ∃ s₁ u, finishFrontQ s = .ok s₁ ∧ decideWith sendByL8 p s₁ rs gs = .ok u ∧
        finishBehindQ u = .ok m := by
  have e : (finishPlace p : Block S C).decide s rs gs =
      (Block.andThen p.name (Block.andThen p.name
        (VerifiableInference.Desc.roundlessBlock (p.name ++ ": front") p.place.chain p.place.link
          p.place.piece finishFrontQ) (codeSwitchKind p))
        (VerifiableInference.Desc.roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link
          p.place.piece finishBehindQ)).decide s rs gs := rfl
  rw [e, andThen_ok]
  have hL : (Block.andThen p.name
      (VerifiableInference.Desc.roundlessBlock (p.name ++ ": front") p.place.chain p.place.link
        p.place.piece finishFrontQ) (codeSwitchKind p : Block S C)).rounds.length = 2 := rfl
  have hO : (Block.andThen p.name
      (VerifiableInference.Desc.roundlessBlock (p.name ++ ": front") p.place.chain p.place.link
        p.place.piece finishFrontQ) (codeSwitchKind p : Block S C)).openings = p.read.length :=
    k2_openings (C := C) p
  rw [hL, hO, List.take_of_length_le (le_of_eq hr), List.take_of_length_le (le_of_eq hg)]
  constructor
  · rintro ⟨u, h1, h2⟩
    obtain ⟨s₁, h3, h4⟩ := (andThen_ok _ _ _ _ _ _ _).1 h1
    exact ⟨s₁, u, h3, h4, h2⟩
  · rintro ⟨s₁, u, h3, h4, h2⟩
    exact ⟨u, (andThen_ok _ _ _ _ _ _ _).2 ⟨s₁, h3, h4⟩, h2⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **At the head's link the lot's live sub-protocol wears the head's dress.** -/
theorem head_dress (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) {x : Block S Unit}
    (hx : x ∈ P1K2.pureTable (fun _ _ => some none) Z Bs.G₀) (hxp : x.planOk = true)
    (hpc : x.place = headPlaceAt) :
    ∃ Pp n HP, prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some 24) = some n ∧
      P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      x = under x.name headPlaceAt ((codeSwitchKind (k2P Z headPlaceAt x.name .head n) : Block S Unit).andThen
        x.name (headOpened x.name headPlaceAt HP)) := by
  obtain ⟨Pp, n, hP, hn, ep, arms⟩ :=
    seated_is_pAt O.blank (H2K12.spots_open hS hR O hcut) hx hxp
  rw [H2K12.links25_open hS hR O hpl, hpc] at ep
  have hd : dressOf 25 (some 24) = .head := rfl
  rw [hd] at ep
  rw [hpc] at hn arms
  rw [ep] at arms
  rcases arms with ⟨e, -⟩ | ⟨-, l, HP, el, hHP, e⟩ | ⟨e, -⟩
  · cases e
  · obtain rfl : 24 = l := Option.some.inj el
    exact ⟨Pp, n, HP, hP, hn, hHP, e⟩
  · cases e

/-- **The seated decision at 339, both ways.** -/
theorem head_seat_decides (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true)
    (hcut : cutOf c.blocksInOrder = cutFirstFull) :
    ∃ (b : Block S Cl) (nm : String) (HP : HeadPar) (Pp : Prep) (n : Nums),
      c.blocksInOrder[339]? = some b ∧ P1K2.pureLetters Bs.G₀ 24 = some HP ∧
      prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp (some 24) = some n ∧
      ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), rs.length = 2 →
        gs.length = n.read.length →
        (b.decide s rs gs = .ok t ↔ ∃ u,
          decideWith sendByL8 (k2P Z headPlaceAt nm .head n) s rs gs = .ok u ∧
            (headOpenQ HP u).bind (guards s) = .ok t) := by
  obtain ⟨Lk, b, x, e1, e2, hx, hl, hi⟩ := IM.k2_head_of hS hR O
  have hf := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) 1] at hf
  have hb := P1K2.flat_planOk O hpl b (List.mem_of_getElem? hf)
  have hxp := (IM.retype_planOk x (IM.laid_planOk hl.laid hb)).1
  have hpc : x.place = headPlaceAt := by
    obtain ⟨_, _, -, -, arms⟩ := hi.live hxp
    rcases arms with ⟨-, e⟩ | ⟨_, _, -, -, e⟩ | ⟨_, -, e⟩ <;> rw [e] <;> rfl
  obtain ⟨Pp, n, HP, hP, hn, hHP, ex⟩ := head_dress hS hR O hpl hcut hx hxp hpc
  refine ⟨b, x.name, HP, Pp, n, hf, hHP, hP, hn, fun s t rs gs hr hg => ?_⟩
  have hk7 : headPlaceAt.kind ≠ KindName.K7 := by
    intro h7
    cases h7
  rw [alone_iff hl hk7 s t rs gs]
  have ed : ∀ m, ((x.retype : Block S Cl).decide s rs gs = .ok m ↔ ∃ u,
      decideWith sendByL8 (k2P Z headPlaceAt x.name .head n) s rs gs = .ok u ∧
        headOpenQ HP u = .ok m) := by
    intro m
    conv_lhs => rw [ex]
    exact headJoined_iff (C := Unit) (k2P Z headPlaceAt x.name .head n) x.name headPlaceAt HP s m
      hr hg
  constructor
  · rintro ⟨m, a, g⟩
    obtain ⟨u, a1, a2⟩ := (ed m).1 a
    exact ⟨u, a1, (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨m, a2, g⟩⟩
  · rintro ⟨u, a1, g⟩
    obtain ⟨m, a2, g'⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 g
    exact ⟨m, (ed m).2 ⟨u, a1, a2⟩, g'⟩

/-- **The seated decision at 353, both ways.** -/
theorem fin_seat_decides (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol P.lay P.KL F Z Bs base c A B) (hpl : F.planOk = true) :
    ∃ (b : Block S Cl) (nm : String) (Pp : Prep) (n : Nums),
      c.blocksInOrder[353]? = some b ∧ prepOf Z Bs.G₀ = some Pp ∧ numsAt Pp none = some n ∧
      ∀ (s t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), rs.length = 2 →
        gs.length = n.read.length →
        (b.decide s rs gs = .ok t ↔ ∃ s₁ u, finishFrontQ s = .ok s₁ ∧
          decideWith sendByL8 (k2P Z k2PlaceF nm .finish n) s₁ rs gs = .ok u ∧
            (finishBehindQ u).bind (guards s₁) = .ok t) := by
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
  refine ⟨_, x.name, Pp, n, hf, hP, hn, fun s t rs gs hr hg => ?_⟩
  have hk7 : k2PlaceF.kind ≠ KindName.K7 := by
    intro h7
    cases h7
  show b.decide s rs gs = .ok t ↔ _
  rw [alone_iff hl hk7 s t rs gs]
  have ed : ∀ m, ((x.retype : Block S Cl).decide s rs gs = .ok m ↔ ∃ s₁ u,
      finishFrontQ s = .ok s₁ ∧
      decideWith sendByL8 (k2P Z k2PlaceF x.name .finish n) s₁ rs gs = .ok u ∧
        finishBehindQ u = .ok m) := by
    intro m
    conv_lhs => rw [ex]
    exact finishPlace_iff (C := Unit) (k2P Z k2PlaceF x.name .finish n) s m hr hg
  have hg2 : ∀ s₁ m, finishFrontQ s = .ok s₁ → (guards s m = .ok t ↔ guards s₁ m = .ok t) := by
    intro s₁ m hq
    rw [guards_iff, guards_iff]
    have eo : ProofFile.sameReply s₁ m = ProofFile.sameReply s m := by
      show (s₁.out.reply == m.out.reply) = (s.out.reply == m.out.reply)
      rw [(finishFrontQ_rest hq).2.2.2.2.2.1]
    rw [eo]
  constructor
  · rintro ⟨m, a, g⟩
    obtain ⟨s₁, u, a1, a2, a3⟩ := (ed m).1 a
    exact ⟨s₁, u, a1, a2,
      (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).2 ⟨m, a3, (hg2 s₁ m a1).1 g⟩⟩
  · rintro ⟨s₁, u, a1, a2, g⟩
    obtain ⟨m, a3, g'⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 g
    exact ⟨m, (ed m).2 ⟨s₁, u, a1, a2, a3⟩, (hg2 s₁ m a1).2 g'⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.headJoined_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.finishPlace_iff
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_dress
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_seat_decides
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_seat_decides
