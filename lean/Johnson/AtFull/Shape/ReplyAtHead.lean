-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/ReplyAtHead.lean: THE PLACE THAT HEARS THE REPLY ("H:1", the kind K7; member
338 of the flat list: the head's link's first place) AT ITS SEAT IN THE PROOF FILE's OWN FIRST
CHAIN: the member has one step on the chain's shape, with both laws at the seated block's own
decision (behind a yes the step returns the shape behind; where the step returns, the block says
yes). Under the head P5J.AtMgA; a joining of laws; nothing is evaluated.
  1 `joined_iff_K7`: for b "the lot's sub-protocol b' with the frame's row's opened joined"
    (IM.seatedWith), at the place that hears the reply, where that "opened" hands the state on: b's
    yes is b''s yes at its own rounds and columns, with no mark behind. Both ways. (The library's
    IM.k7_sits_yes is the way from a yes.)
  `k7Block_iff`: the lot's block there (IM.k7Block, Johnson/IMR/K7Seat.lean), half by half, both
    ways: the head's front, then the kind "the next token"; the guard on the reply around the front
    is paid (headFront_keeps).
  2 `replyGS t`: the step at the seat: headFrontG t, then replyG
    (Johnson/Desc/First/Shape/HeadFront.lean). t: the shape of the plan's record of the smallness
    test at the head's link.
  **`reply_at`**: with Bs what the maker's own ProofFile.baseOf returns at the public part: the member b
    at number 338 of cF.blocksInOrder is such that, at the step replyGS (tailSh Bs.G₀.W.H.tl): behind a yes
    of b the step returns the shape behind (the strong form: no premise that the step returns), and
    the makes of the statement's rows behind are those in front with one new group without a row;
    and where the step returns, b says yes on one round that holds just one element, draws nothing,
    and whose element is a token of a vocabulary of Bs.G₀.W.hS.V entries.
By IM.k7_sits (Johnson/IMR/FirstSeats.lean: the seat holds the lot's block with the head's row's
"opened" joined, and that text hands the state on), IM.guardMark_yes (Johnson/IMR/SeatForm.lean),
guarded_yes (Johnson/Desc/Sound/SeatGuardLaws.lean), headFront_sh, headFront_forms, reply_carries,
reply_returns (HeadFront.lean), IM.hear_at_flat and IM.flatIx_scope (the number in the flat list: 14
· 24 + 0 + 2).
Limits. The two premises of "returns" are on the round; "the element is a token" is a test on a
value. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. NO STATE IS SHOWN AT WHICH THE STEP RETURNS. At
the earlier hash OnBytes.secondHashFunction. Nothing on soundness, completeness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Shape.HeadFront
import Johnson.IMR.FirstSeats
import Johnson.IMR.FlatScope
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S hearsReply)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk.Seat (LinkFrame)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)

/-! ## 1 The seated member's decision at the place that hears the reply -/

/-- For b "the lot's sub-protocol b' with the row f's opened joined", AT THE PLACE THAT HEARS THE
REPLY, where the row's "opened" hands the state on: b's yes is b''s yes at its own rounds and
columns, with no mark behind. Both ways. The driver's guard on the reply is free at this place. -/
theorem joined_iff_K7 {b b' : Block S ProofFile.Cl} {a : Place} {f : LinkFrame}
    (e : b = IM.seatedWith ProofFile.sameReply b' (ProofFile.guardMark (IM.openedOf f).retype) b.name a)
    (hk : a.kind = KindName.K7) (hid : f.opened = fun s => .ok s) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    b.decide s rs gs = .ok t ↔
      b'.decide s (rs.take b'.rounds.length) (gs.take b'.openings) = .ok t ∧ t.failed = none := by
  have hp : hearsReply a = true := by
    show (a.kind == KindName.K7) = true
    simpa using hk
  have ed : b.decide s rs gs = (IM.seatedWith ProofFile.sameReply b'
      (ProofFile.guardMark (IM.openedOf f).retype) b.name a).decide s rs gs :=
    congrArg (fun y : Block S ProofFile.Cl => y.decide s rs gs) e
  rw [ed]
  unfold IM.seatedWith
  show (if hearsReply a then
      ((ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings)).bind
        (fun s' => ((ProofFile.guardMark (IM.openedOf f).retype).guarded ProofFile.sameReply
          fun _ => false).decide s' (rs.drop b'.rounds.length) (gs.drop b'.openings))
      else _) = .ok t ↔ _
  rw [hp, if_pos rfl]
  constructor
  · intro hy
    cases hd : (ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings) with
    | error w => rw [hd] at hy; exact nomatch hy
    | ok m =>
      rw [hd] at hy
      obtain ⟨h1, h2⟩ := (IM.guardMark_yes b' s m _ _).1 hd
      obtain ⟨h3, -⟩ := (VerifiableInference.Desc.guarded_yes ProofFile.sameReply (fun _ => false)
        (ProofFile.guardMark (IM.openedOf f).retype) rfl m _ _ t).1 hy
      obtain ⟨h5, -⟩ := (IM.guardMark_yes _ m t _ _).1 h3
      have h5' : f.opened m = .ok t := h5
      rw [hid] at h5'
      obtain rfl : m = t := Except.ok.inj h5'
      exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hd : (ProofFile.guardMark b').decide s (rs.take b'.rounds.length) (gs.take b'.openings) =
        .ok t := (IM.guardMark_yes b' s t _ _).2 ⟨h1, h2⟩
    rw [hd]
    refine (VerifiableInference.Desc.guarded_yes ProofFile.sameReply (fun _ => false)
      (ProofFile.guardMark (IM.openedOf f).retype) rfl t _ _ t).2
      ⟨(IM.guardMark_yes _ t t _ _).2 ⟨?_, h2⟩, ?_⟩
    · show f.opened t = .ok t
      rw [hid]
    · unfold ProofFile.sameReply
      exact beq_self_eq_true _

/-- **The lot's block at "H:1", half by half**: the head's front, then the kind "the next token".
-/
theorem k7Block_iff (X : Verify.Public) (l : Nat) (s t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (IM.k7Block X l).decide s rs gs = .ok t ↔
      ∃ m, VerifiableInference.Desc.First.K2.headFrontQ X.H.tl s = .ok m ∧
        (VerifiableInference.Desc.Kinds.Reply.blockAt l X.hS.V).decide m rs gs = .ok t := by
  show ((((VerifiableInference.Desc.First.K2.headFrontQ X.H.tl s).bind
      (VerifiableInference.Desc.seatSame ProofFile.sameReply s))).bind fun m =>
      (VerifiableInference.Desc.Kinds.Reply.blockAt l X.hS.V).decide m rs gs) = .ok t ↔ _
  constructor
  · intro h
    obtain ⟨m, h1, h2⟩ := ex_bind h
    obtain ⟨m', h3, h4⟩ := ex_bind h1
    unfold VerifiableInference.Desc.seatSame at h4
    split at h4
    · obtain rfl := Except.ok.inj h4
      exact ⟨m', h3, h2⟩
    · cases h4
  · rintro ⟨m, h1, h2⟩
    rw [h1]
    have hs : ProofFile.sameReply s m = true := by
      unfold ProofFile.sameReply
      rw [(headFront_keeps h1).1]
      exact beq_self_eq_true _
    show ((VerifiableInference.Desc.seatSame ProofFile.sameReply s m).bind _) = _
    unfold VerifiableInference.Desc.seatSame
    rw [if_pos hs]
    exact h2

/-! ## 2 The member at the head's link's first place -/

/-- **The step at the seat**: the head's front (headFrontG: it asks that there is no mark), then
the kind's step (replyG): Johnson/Desc/First/Shape/HeadFront.lean. t: the shape of the plan's record
of the smallness test at the head's link. -/
def replyGS (t : TailSh) (a : ChainSh) : Option ChainSh := (headFrontG t a).bind replyG

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The member number 338 at its seat**: behind a yes the step returns the shape behind; where the
step returns, the member says yes on one round whose one element is a token. -/
theorem reply_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ (Bs : ProofFile.PureBase) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.blocksInOrder[338]? = some b ∧
      (∀ s rs gs t, b.decide s rs gs = .ok t →
        replyGS (tailSh Bs.G₀.W.H.tl) (chainSh s) = some (chainSh t) ∧
        formsOf t.st = { formsOf s.st with groups := (formsOf s.st).groups ++ [[]] }) ∧
      ∀ s q y gs u, replyGS (tailSh Bs.G₀.W.H.tl) (chainSh s) = some u →
        OnBytes.Desc.Reply.readReply q = some y →
        OnBytes.Desc.Reply.isToken Bs.G₀.W.hS.V y = true →
        ∃ t, b.decide s [q] gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, eL, eb, ⟨fs, f, hfs, hf, e⟩, hid⟩ := IM.k7_sits h.scope h.reads O
  have hy := joined_iff_K7 e rfl (hid fs f hfs hf)
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 24 ≤ 24) 0] at q
  refine ⟨Bs, b, O.made, q, fun s rs gs t hd => ?_, fun s q y gs u hg hr ht => ?_⟩
  · obtain ⟨m, h1, h2⟩ := (k7Block_iff Bs.G₀.W 24 s t _ _).1 ((hy s t rs gs).1 hd).1
    have e1 := headFront_sh Bs.G₀.W.H.tl s
    rw [h1] at e1
    refine ⟨?_, ?_⟩
    · unfold replyGS
      rw [← e1]
      exact reply_carries h2
    · obtain ⟨_, _, _, -, -, -, -, -, -, rfl⟩ := (reply_iff 24 _ m t _ _).1 h2
      show formsOf m.st = _
      exact headFront_forms h1
  · unfold replyGS at hg
    obtain ⟨m', hm', hu⟩ := Option.bind_eq_some_iff.1 hg
    have e1 := headFront_sh Bs.G₀.W.H.tl s
    rw [hm'] at e1
    obtain ⟨m, hm, rfl⟩ := Option.map_eq_some_iff.1 e1
    have hm2 : VerifiableInference.Desc.First.K2.headFrontQ Bs.G₀.W.H.tl s = .ok m := by
      cases hh : VerifiableInference.Desc.First.K2.headFrontQ Bs.G₀.W.H.tl s with
      | error w => rw [hh] at hm; cases hm
      | ok m₂ => rw [hh] at hm; rw [Option.some.inj hm]
    obtain ⟨t, ht', hf'⟩ := reply_returns (l := 24) (gs := gs.take (IM.k7Block Bs.G₀.W 24).openings)
      hu hr ht
    exact ⟨t, (hy s t [q] gs).2 ⟨(k7Block_iff Bs.G₀.W 24 s t _ _).2 ⟨m, hm2, ht'⟩,
      hf'.trans (headFront_keeps hm2).2⟩⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.joined_iff_K7
#print axioms Johnson.AtFull.Shape.k7Block_iff
#print axioms Johnson.AtFull.Shape.reply_at
