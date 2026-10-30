-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/SwitchReturns.lean: THE CODE SWITCH's PLACES AT THE LINKS 1 TO 23 OF THE PROOF
FILE's OWN FIRST CHAIN (kind K2), IN THE FRAME's OWN FORM: TWO OF THE PREMISES THAT THE RULE FOR
ACCEPTANCE ASKS: Carries AND Returns (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean),
at the reader shA, at SwitchFrames.lean's steps WITH A GUARD ON THE SHAPE IN FRONT, under one named
test on values. A joining of laws; nothing is evaluated.

  `linkGd p x`: THE GUARD, on the shape with the rows' makes: no mark of failure · linkB
    (Johnson/Desc/First/Shape/SwitchLinkB.lean) · linkP (SwitchLinkFits.lean).
  `switchW s`: THE TEST ON VALUES: onesV (SwitchFrontFits.lean): in the carried single rows' forms
    and in the kept members' stored sample rows each written-out variable's pair is (1, 1).
  `switchV p s rs gs`: all that the decision's law asks, as one test: two rounds · no mark · linkB ·
    onesV · linkR. A stage on the way: no frame names it.
  `stands_at`: under the head every place with numbers of the lot stands in the dress that its link
    asks (by spots_atAll, Johnson/Loose/H2K12/SpotsAtAll.lean, and links25_open, HsAtAll.lean
    there).
  `link_yes`: from a yes of the kind's own decision at a link: no new mark, the reply as it was, as
    many groups of columns as the place reads trees.
  **`seat_returns`**: GENERAL: the lot's block in the link's dress with a row's "opened" joined
    behind it, at a place that does not hear the reply, where "opened" keeps the mark and the reply:
    switchV accepts, and "opened" returns behind every yes of the decision: the seated member's
    decision returns.
  `switchV_here`, `quietE_ok`: where switchV accepts the chain stands between two links; a quiet
    step that returns on the pair returns on the shape.
  `switch_link_returns`: under the head, 1 ≤ l < 24: the member, its declared rounds, and: switchV
    accepts, and "opened" returns AT EVERY STATE WHOSE SHAPE AND MAKES ARE WHAT THE UPDATE linkU
    RETURNS (a yes of the decision or not): the member's decision returns.
  **`switchV_of`**: THE JOINT: the guard, the member's own test on rounds and columns and the test
    on values give switchV.
  **`switch_att_both`** (12) · **`switch_lay_both`** (11): under the head, 1 ≤ l < 24, at 14 l + 0 +
    2: for every table of steps G and of tests vals with G ‹number› = the guarded step and vals
    ‹number› = switchW, at the plan's numbers: Carries and Returns.

What pays what in Returns. The guard pays all that hangs on the shape and the plan. The member's own
test on rounds and columns (Block.Fits) pays linkR under the guard (linkR_of_Fits_whole,
Johnson/Desc/First/Shape/SwitchLinkFactor.lean). The test on values pays the rest. The dress
(IM.K2Is leaves "the head's | the link's" open) is paid under the head: SwitchDress.lean.

Limits. That the guard or the test accepts at any state is not shown. WITH THE GUARD IN FRONT
Carries HAS THE WEAK FORM, AND NO LAW HERE OR IN THESE LOTS SAYS THAT A YES OF THE MEMBER, OR A
STATE THAT IS REACHED THERE, PASSES linkGd: as far as these go, the run on shapes may refuse at one
of these 23 members where the verifier accepts. Neither end statement says that a member stands at
its number (SwitchAtHead.lean's do). HP is idle in the guarded step: the guard gives "here" = 0, and
switchU reads HP at 4 alone. The head's place and the place behind the links are not here. G and
vals are letters. That the head has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Loose.H2K12.HsAtAll
import Johnson.AtFull.Shape.SwitchDress
import Johnson.AtFull.Shape.SwitchFrames
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Shape.SwitchLinkFactor
import Johnson.AtFull.Shape.FrameNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 At codeSwitchKind decideWith HeadPar)
open VerifiableInference.Desc.First.K2Caller (dressOf spotsFitB)
open VerifiableInference.Desc.First.Shape
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Shape
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame)
open OnBytes.Maker (WholeD)
open IM (subAt k2P under)
open P5J (AtMgA)
open ProofFile.Honest (Carries Returns returns_seat)

/-- **THE GUARD**, on the shape with the rows' makes. -/
def linkGd (p : P2) (x : ChainF) : Bool := !x.1.marked && linkB p x && linkP p x

/-- **THE TEST ON VALUES.** -/
def switchW (s : S) : Bool := onesV s.st s.check.frame.rows

/-- All that the decision's law asks, as one test. -/
def switchV (p : P2) (s : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) : Bool :=
  match rs with
  | [r₁, r₂] =>
    s.failed.isNone && linkB p (chainF s) && onesV s.st s.check.frame.rows &&
      linkR p (chainF s) r₁ r₂ gs
  | _ => false

/-- From a yes of the kind's own decision at a link. -/
theorem link_yes {p : P2} {s m : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (h : decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok m) :
    m.failed = s.failed ∧ ProofFile.sameReply s m = true ∧ gs.length = p.read.length := by
  obtain ⟨r₁, r₂, y, w, roots, S', f, mine, -, R⟩ :=
    VerifiableInference.Desc.First.K2.link_inv hp h
  refine ⟨by rw [R.hOut], ?_, R.hTaken.2⟩
  unfold ProofFile.sameReply
  rw [R.hOut]
  exact beq_self_eq_true _

/-- **GENERAL: the seated member's decision returns.** -/
theorem seat_returns {b : Block S ProofFile.Cl} {a : Place} {nm : String} {f : LinkFrame} {p : P2}
    (e : b = IM.seatedWith ProofFile.sameReply (under nm a (codeSwitchKind p) : Block S Unit).retype
      (ProofFile.guardMark (IM.openedOf f).retype) b.name a)
    (hk : a.kind ≠ KindName.K7) (hO : Keeps f.opened) (hp : p.stands = .link) {s : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hv : switchV p s rs gs = true)
    (hopen : ∀ m, decideWith _root_.Tw.K2.sendByL8 p s rs gs = .ok m → ∃ t, f.opened m = .ok t) :
    ∃ t, b.decide s rs gs = .ok t := by
  unfold switchV at hv
  split at hv
  · rename_i r₁ r₂
    simp only [Bool.and_eq_true] at hv
    obtain ⟨⟨⟨hv0, hv1⟩, hv2⟩, hv3⟩ := hv
    obtain ⟨m, hm⟩ := link_returns_B hv1 hv2 hv3
    obtain ⟨q1, q2, q3⟩ := link_yes hp hm
    obtain ⟨t, ht⟩ := hopen m hm
    refine ⟨t, (joined_iff e hk hO s t [r₁, r₂] gs).2 ⟨m, ?_, ?_, q2, ht⟩⟩
    · show decideWith _root_.Tw.K2.sendByL8 p s ([r₁, r₂].take 2)
        (gs.take ((under nm a (codeSwitchKind p) : Block S Unit).retype : Block S ProofFile.Cl).openings) = .ok m
      have ho : ((under nm a (codeSwitchKind p) : Block S Unit).retype : Block S ProofFile.Cl).openings =
          p.read.length := by
        simp [Block.openings, Block.retype, under, codeSwitchKind, VerifiableInference.Desc.First.K2.rounds]
      rw [ho, ← q3, List.take_length]
      exact hm
    · rw [q1]
      simpa using hv0
  · cases hv

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Under the head every place with numbers of the lot stands in the dress that its link asks. -/
theorem stands_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    ∀ y ∈ P1K2.pureSpots Zp Bs.G₀, y.2.stands = dressOf 25 y.1.place.link := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl : Bs' = Bs := Except.ok.inj (O.made.symm.trans hB)
  have hfit := H2K12.spots_atAll h (P5J.pins_of_laid h.scope h.laid).2
  have hk2 : ProofFile.k2SpotsAt Zp = P1K2.pureSpots Zp Bs'.G₀ := by
    unfold ProofFile.k2SpotsAt
    rw [O.blank]
    rfl
  unfold spotsFitB at hfit
  rw [Bool.and_eq_true, hk2, H2K12.links25_open h.scope h.reads O h.laid.planOk] at hfit
  intro y hy
  exact of_decide_eq_true (List.all_eq_true.1 hfit.2 y hy)

/-- Where the test accepts the state stands between the links. -/
theorem switchV_here {p : P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hv : switchV p s rs gs = true) : (chainF s).1.here = 0 := by
  unfold switchV at hv
  split at hv
  · simp only [Bool.and_eq_true] at hv
    exact beq_iff_eq.1 (linkB_here hv.1.1.2)
  · cases hv

/-- A quiet step that returns on the pair returns on the shape. -/
theorem quietE_ok {g : ChainSh → Except String ChainSh} {y u : ChainF} (h : quietE g y = some u) :
    ∃ v, g y.1 = .ok v := by
  unfold quietE quietF at h
  obtain ⟨v, hv, -⟩ := Option.map_eq_some_iff.1 h
  have hv' : (g y.1).toOption = some v := hv
  cases e : g y.1 with
  | error w => rw [e] at hv'; cases hv'
  | ok v' => exact ⟨v', rfl⟩

/-- **What stands at the first place of a link l, 1 ≤ l < 24, for "returns"**: the letters, the
member, its declared rounds, and: where switchV accepts and the row's "opened" returns at every
state whose shape and makes are what the update linkU returns, the member's decision returns. -/
theorem switch_link_returns (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (b : Block S ProofFile.Cl)
        (fs : List LinkFrame) (f : LinkFrame),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      cF.blocksInOrder[14 * l + 0 + 2]? = some b ∧
      b.rounds = VerifiableInference.Desc.First.K2.rounds
        (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) ∧
      framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs ∧ fs[l]? = some f ∧
      ∀ s rs gs, Keeps f.opened →
        switchV (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) s rs
          gs = true →
        (∀ m, linkU (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n)
            (chainF s) = some (chainF m) → ∃ t, f.opened m = .ok t) →
        ∃ t, b.decide s rs gs = .ok t := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, hy, hj, his⟩ := IM.k2_link_sits h.scope h.reads O l h1 h24
  have hb : b.planOk = true := plans_at h b (List.mem_of_getElem? (IM.hear_at_flat e1 e2))
  have hyp : y.planOk = true := by
    obtain ⟨fs, f, -, -, e⟩ := hj.planOk
    rw [e, Bool.and_eq_true] at hb
    exact (IM.retype_planOk y hb.1).1
  have hpl : y.place = { chain := 1, link := some l, piece := 1, kind := .K2 } := by
    obtain ⟨P0, n0, _, _, harm⟩ := his.live hyp
    rcases harm with ⟨_, e⟩ | ⟨_, _, _, _, e⟩ | ⟨_, _, e⟩ <;> exact congrArg Block.place e
  obtain ⟨P, n, hP, hn, ey⟩ := link_arm hy hyp (stands_at h O.made) (l := l) (by rw [hpl])
    (by omega)
  rw [hpl] at ey
  have hro : b.rounds = VerifiableInference.Desc.First.K2.rounds
      (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) := by
    rw [hj.rounds, ey]
    rfl
  obtain ⟨fs, f, hfs, hf, e⟩ := hj
  have q := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope h.scope h.reads O (by omega : l ≤ 24) 0] at q
  refine ⟨Bs, P, n, b, fs, f, O.made, hP, hn, q, hro, hfs, hf, fun s rs gs hO hv hopen => ?_⟩
  have e' : b = IM.seatedWith ProofFile.sameReply
      (under y.name { chain := 1, link := some l, piece := 1, kind := .K2 }
        (codeSwitchKind (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } y.name .link n)) :
          Block S Unit).retype (ProofFile.guardMark (IM.openedOf f).retype) b.name
      { chain := 1, link := some l, piece := 1, kind := .K2 } := by
    rw [← ey]
    exact e
  refine seat_returns e' (by simp) hO rfl (s := s) (rs := rs) (gs := gs) hv fun m hm => ?_
  exact hopen m (link_carries rfl hm)

/-- **The guard, the member's own test on rounds and columns, and the test on values give all that
the decision's law asks.** -/
theorem switchV_of {Cl : Type} {blk : Block S Cl} {p : P2} {s : S} {ft : Nat} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hb : blk.rounds = VerifiableInference.Desc.First.K2.rounds p) (hF : blk.Fits ft rs cols)
    (hg : linkGd p (chainF s) = true) (hv : switchW s = true) :
    switchV p s (rs.map noDigest) (blk.shown ft rs cols) = true := by
  unfold linkGd at hg
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hg
  obtain ⟨⟨g1, g2⟩, g3⟩ := hg
  obtain ⟨R₁, R₂, rfl, hl⟩ := linkR_of_Fits_whole hb hF g2 g3
  unfold switchW at hv
  have hn : s.failed.isNone = true := by
    have e : (chainF s).1.marked = s.failed.isSome := rfl
    rw [e] at g1
    cases hf : s.failed with
    | none => rfl
    | some w => rw [hf] at g1; cases g1
  show (s.failed.isNone && linkB p (chainF s) && onesV s.st s.check.frame.rows &&
    linkR p (chainF s) (noDigest R₁) (noDigest R₂) (blk.shown ft [R₁, R₂] cols)) = true
  rw [hn, g2, hv, hl]
  rfl

/-- **THE FIRST PLACE OF AN ATTENTION LINK: BOTH PREMISES.** -/
theorem switch_att_both (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .attention) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (p : Attention.Plan),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.A[Y.g]? = some p ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + 0 + 2) = optE (fun y =>
          if linkGd (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openAttG (attPar Y p l)))
          else none) →
        (∀ s rs gs, vals (14 * l + 0 + 2) s rs gs = switchW s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + 0 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + 0 + 2) := by
  obtain ⟨Bs, P, n, HP, Y, p, Lk, b, a1, a2, a3, a4, a5, a6, -, a8, hc⟩ :=
    switch_att_at h l h1 h24 hs
  obtain ⟨Bs', P', n', b', fs, f, c1, c2, c3, c4, hro, c5, c6, hr⟩ :=
    switch_link_returns h l h1 h24
  obtain rfl : Bs = Bs' := Except.ok.inj (a1.symm.trans c1)
  obtain rfl : P = P' := Option.some.inj (a2.symm.trans c2)
  obtain rfl : n = n' := Option.some.inj (a3.symm.trans c3)
  obtain rfl : b = b' := Option.some.inj (a8.symm.trans c4)
  obtain ⟨Y', q', hY, hA, hplan, eo, -⟩ := row_att h (by omega : l < 25) hs c5 c6
  obtain rfl : Y = Y' := Option.some.inj (a5.symm.trans hY)
  obtain rfl : p = q' := Option.some.inj (a6.symm.trans hA)
  refine ⟨Bs, P, n, HP, Y, p, a1, a2, a3, a4, a5, a6, fun ft G vals hG hV => ⟨?_, ?_⟩⟩
  · refine carries_of_seat a8 fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    obtain ⟨-, hu'⟩ := optE_guard hu
    exact Option.some.inj ((optE_ok.1 hu').symm.trans (hc s _ gs t hd))
  · refine returns_seat a8 fun rs cols hF s u hg hv => ?_
    have hg1 : G (14 * l + 0 + 2) (shA s) = .ok u := hg
    rw [hG] at hg1
    obtain ⟨hgd, hg0⟩ := optE_guard hg1
    have hg' := optE_ok.1 hg0
    have hv1 : vals (14 * l + 0 + 2) s (rs.map noDigest) (b.shown ft rs cols) = true := hv
    rw [hV] at hv1
    have hv2 := switchV_of hro hF hgd hv1
    refine hr s _ _ (by rw [eo]; exact keeps_att _) hv2 fun m hm => ?_
    unfold switchU at hg'
    have hh : (shA s).1.here = 0 := switchV_here hv2
    rw [hh] at hg'
    have hg2 : (linkU (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n)
        (chainF s)).bind (quietE (openAttG (attPar Y p l))) = some u := hg'
    rw [hm] at hg2
    obtain ⟨v, hv'⟩ := quietE_ok (y := chainF m) hg2
    rw [eo]
    exact openAtt_returns _ hplan m v hv'

/-- **THE FIRST PLACE OF A LAYERS' LINK BEHIND LINK 0: BOTH PREMISES.** -/
theorem switch_lay_both (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (h1 : 1 ≤ l)
    (h24 : l < 24) (hs : subAt l = .layers) :
    ∃ (Bs : ProofFile.PureBase) (P : P1K2.Prep) (n : P1K2.Nums) (HP : HeadPar) (Y : Stages.LinkH)
        (hp : Layer.HPlan2),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      P1K2.prepOf Zp Bs.G₀ = some P ∧ P1K2.numsAt P (some l) = some n ∧
      P1K2.pureLetters Bs.G₀ l = some HP ∧ Zp.p.built.links[l]? = some Y ∧
      Zp.p.X.G[Y.g]? = some hp ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (14 * l + 0 + 2) = optE (fun y =>
          if linkGd (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n) y
          then (switchU Zp { chain := 1, link := some l, piece := 1, kind := .K2 } n HP y).bind
              (quietE (openLayG (layPar Zp.p.X Y hp l)))
          else none) →
        (∀ s rs gs, vals (14 * l + 0 + 2) s rs gs = switchW s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (14 * l + 0 + 2) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (14 * l + 0 + 2) := by
  obtain ⟨Bs, P, n, HP, Y, hp, Lk, b, a1, a2, a3, a4, a5, a6, -, a8, hc⟩ :=
    switch_lay_at h l h1 h24 hs
  obtain ⟨Bs', P', n', b', fs, f, c1, c2, c3, c4, hro, c5, c6, hr⟩ :=
    switch_link_returns h l h1 h24
  obtain rfl : Bs = Bs' := Except.ok.inj (a1.symm.trans c1)
  obtain rfl : P = P' := Option.some.inj (a2.symm.trans c2)
  obtain rfl : n = n' := Option.some.inj (a3.symm.trans c3)
  obtain rfl : b = b' := Option.some.inj (a8.symm.trans c4)
  obtain ⟨Y', q', hY, hA, hplan, eo, -⟩ := row_lay h (by omega : l < 25) (by omega : l ≠ 0) hs c5 c6
  obtain rfl : Y = Y' := Option.some.inj (a5.symm.trans hY)
  obtain rfl : hp = q' := Option.some.inj (a6.symm.trans hA)
  refine ⟨Bs, P, n, HP, Y, hp, a1, a2, a3, a4, a5, a6, fun ft G vals hG hV => ⟨?_, ?_⟩⟩
  · refine carries_of_seat a8 fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    obtain ⟨-, hu'⟩ := optE_guard hu
    exact Option.some.inj ((optE_ok.1 hu').symm.trans (hc s _ gs t hd))
  · refine returns_seat a8 fun rs cols hF s u hg hv => ?_
    have hg1 : G (14 * l + 0 + 2) (shA s) = .ok u := hg
    rw [hG] at hg1
    obtain ⟨hgd, hg0⟩ := optE_guard hg1
    have hg' := optE_ok.1 hg0
    have hv1 : vals (14 * l + 0 + 2) s (rs.map noDigest) (b.shown ft rs cols) = true := hv
    rw [hV] at hv1
    have hv2 := switchV_of hro hF hgd hv1
    refine hr s _ _ (by rw [eo]; exact keeps_lay _) hv2 fun m hm => ?_
    unfold switchU at hg'
    have hh : (shA s).1.here = 0 := switchV_here hv2
    rw [hh] at hg'
    have hg2 : (linkU (k2P Zp { chain := 1, link := some l, piece := 1, kind := .K2 } "" .link n)
        (chainF s)).bind (quietE (openLayG (layPar Zp.p.X Y hp l))) = some u := hg'
    rw [hm] at hg2
    obtain ⟨v, hv'⟩ := quietE_ok (y := chainF m) hg2
    rw [eo]
    exact openLay_returns _ hplan m v hv'

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.switchV_here
#print axioms Johnson.AtFull.Shape.quietE_ok
#print axioms Johnson.AtFull.Shape.switch_link_returns
#print axioms Johnson.AtFull.Shape.switchV_of
#print axioms Johnson.AtFull.Shape.switch_att_both
#print axioms Johnson.AtFull.Shape.switch_lay_both
#print axioms Johnson.AtFull.Shape.link_yes
#print axioms Johnson.AtFull.Shape.seat_returns
#print axioms Johnson.AtFull.Shape.stands_at
#print axioms Johnson.AtFull.Shape.linkGd
#print axioms Johnson.AtFull.Shape.switchW
#print axioms Johnson.AtFull.Shape.switchV
