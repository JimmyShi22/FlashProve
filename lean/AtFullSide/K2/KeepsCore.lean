-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/KeepsCore.lean: what a yes of a member of the code switch (the kind K2) keeps of the
verifier's state, under the library's head. No thread and no prover stands here.

  k2Keeps_of_link, k2Keeps_of_head, k2Keeps_of_finish   K2Keeps at each sort of place, from what the
                       place's decision says yes to
  head_yes, fin_yes    the block of the head's place and of the finish, from their steps
  k2_left_behind       what an accept leaves (Left)
  k2_pile_parts        the four things that the item on the pending claims reads stay: the rows, the
                       codes, the shape and the seat of the index masks' message
  k2_keeps_core        which sort of place the member is, and K2Keeps there. At a link's first place
                       the state between, and the frame's step behind it
  k2_reply_kept        what goes out stays
  k2_border_at, k2_riders_behind   a member of the kind stands below 339 or the next border is
                       above it; no clause of the list csHead speaks at the next border

Limits. The library's head is a premise. Nothing here says that the member accepts.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.NoMarkBehind
import Johnson.Desc.ProofFile.Honest.K2.Law.BlockAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.Thread.CsHead
import Johnson.Desc.K2.Honest.KeepsAt
import Johnson.P1K2R.MoreLeft
import Johnson.P1K2R.LastLineOfHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Term
open VerifiableInference.Desc (Block Chain KindName Place roundlessBlock)
open VerifiableInference.Desc.Book (BookFits placed_of_fits)
open VerifiableInference.Desc.First (S Item Pub bookAt pubHeld pubOfItems)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind decideWith HeadPar headOpened headOpenQ finishPlace
  finishFrontQ finishBehindQ)
open VerifiableInference.Desc.First.K2Ties (Left seat_left shape_left pinOpen_of_B)
open VerifiableInference.Desc.K2.Honest (K2Keeps k2KeepsLink_of_yes k2PlaceHead_of_yes
  k2PlaceFinish_of_yes)
open VerifiableInference.Desc.K2.Honest.Returns (k2_openings)
open VerifiableInference.Desc.K12 (andThen_ok)
open VerifiableInference.Desc.K13 (indexThereC)
open VerifiableInference.Desc.Sound (below seatBy noFirst)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw stepYes_decide)
open Johnson.Desc.First.Walk.Seat (framesOf)
open P1L20 (link_off head_off finish_off)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open _root_.Desc.K14.Law (secondAt seatZ)
open _root_.Tw.K2 (sendByL8)
open ProofFile (Cl)
open ProofFile.Honest (RiderCl ridersOf csHead csHead_span)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces)
open ProofFile.Honest.K2.Law (k2_block_at_head k2_place_at k2_sits_of_head places_at_head)

/-! ## 1 K2Keeps at each sort of place -/

section Sorts
variable {p : P2} {s t : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}

/-- At a link's first place, from a yes of the kind's decision. -/
theorem k2Keeps_of_link (hq : p.stands = .link) (e : decideWith sendByL8 p s rs gs = .ok t) :
    K2Keeps p s t := by
  refine ⟨fun o ho => link_off hq e ho, ?_⟩
  rw [hq]
  exact k2KeepsLink_of_yes hq e

/-- At the head's place, from a yes of the place's block with no mark behind. -/
theorem k2Keeps_of_head {nm : String} {pl : Place} {HP : HeadPar} (hq : p.stands = .head)
    (e : ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm pl HP)).decide s rs gs = .ok t)
    (h0 : t.failed = none) : K2Keeps p s t := by
  refine ⟨fun o ho => head_off hq e ho, ?_⟩
  rw [hq]
  exact ⟨k2PlaceHead_of_yes hq nm pl HP e, h0⟩

/-- Behind the last segment, from a yes of the place's block with no mark behind. -/
theorem k2Keeps_of_finish (hq : p.stands = .finish)
    (e : (finishPlace p : Block S Unit).decide s rs gs = .ok t) (h0 : t.failed = none) :
    K2Keeps p s t := by
  refine ⟨fun o ho => finish_off hq e ho, ?_⟩
  rw [hq]
  exact ⟨k2PlaceFinish_of_yes hq e, h0⟩

/-- The block of the head's place says yes where its two steps do. -/
theorem head_yes {nm : String} {pl : Place} {HP : HeadPar} {u : S}
    (e : decideWith sendByL8 p s (rs.take 2) (gs.take p.read.length) = .ok u)
    (h : headOpenQ HP u = .ok t) :
    ((codeSwitchKind p : Block S Unit).andThen nm (headOpened nm pl HP)).decide s rs gs = .ok t := by
  refine (andThen_ok _ _ _ _ _ _ _).2 ⟨u, ?_, h⟩
  rw [k2_openings]
  exact e

/-- The block of the finish says yes where its three steps do. -/
theorem fin_yes {s₁ u : S} (e1 : finishFrontQ s = .ok s₁)
    (e2 : decideWith sendByL8 p s₁ (rs.take 2) (gs.take p.read.length) = .ok u)
    (e3 : finishBehindQ u = .ok t) : (finishPlace p : Block S Unit).decide s rs gs = .ok t := by
  have hO : (Block.andThen p.name
      (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece finishFrontQ)
      (codeSwitchKind p : Block S Unit)).openings = p.read.length := k2_openings (C := Unit) p
  show (Block.andThen p.name (Block.andThen p.name
      (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece finishFrontQ)
      (codeSwitchKind p : Block S Unit))
      (roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece
        finishBehindQ)).decide s rs gs = .ok t
  refine (andThen_ok _ _ _ _ _ _ _).2 ⟨u, ?_, e3⟩
  rw [hO]
  exact (andThen_ok _ _ _ _ _ _ _).2 ⟨s₁, e1, e2⟩

end Sorts

/-! ## 2 What a yes leaves -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What an accept of a member of the kind leaves.** -/
theorem k2_left_behind (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) {blk : Block S Cl}
    (hblk : cF.blocksInOrder[b]? = some blk) {s s' : S} (hyes : IM.Yes 0 blk s s') : Left s s' := by
  obtain ⟨enter, leave, hSit, hLD, -⟩ := k2_sits_of_head h ha hk hblk
  exact P1K2.left_of_sits hSit hLD.1 hLD.2 hyes

/-- **What goes out stays.** -/
theorem k2_reply_kept (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) {blk : Block S Cl}
    (hblk : cF.blocksInOrder[b]? = some blk) {s s' : S} (hyes : IM.Yes 0 blk s s') : s'.out = s.out :=
  (k2_left_behind h ha hk hblk hyes).out

/-- **The four things that the item on the pending claims reads stay**, at a state that is reached
and has the six Bools. -/
theorem k2_pile_parts (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) {blk : Block S Cl}
    (hblk : cF.blocksInOrder[b]? = some blk) {z : ProofFile.InstPub} {s s' : S} (hyes : IM.Yes 0 blk s s')
    (hreach : Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) b (z, s))
    (hx : IM.XK (P5J.At.N Zp cF) P5J.At.links P5J.At.ps
      (P1K2.EQ (P5J.mgAtAll h) P5J.At.links P5J.At.ps z) b s = true) :
    s'.rows = s.rows ∧ s'.st.codes = s.st.codes ∧
      (s'.st.oracles[s.out.indexMasks]?).map (·.shape) =
        (s.st.oracles[s.out.indexMasks]?).map (·.shape) ∧
      seatBy noFirst s'.book s.out.indexMasks = seatBy noFirst s.book s.out.indexMasks := by
  have hL := k2_left_behind h ha hk hblk hyes
  obtain ⟨-, -, -, hbk, hE⟩ := IM.xk_parts hx
  unfold P1K2.EQ at hE
  rw [Bool.and_eq_true] at hE
  have hpub := hE.2
  unfold pubHeld at hpub
  have hI : Item.pinI ∈ IM.openAt P5J.At.links P5J.At.ps b :=
    pinOpen_of_B _ _ _ (P1K2.pinOpen_at ha hk)
  have hq₀ : Pub.indexThere ∈ [Pub.indexIs, Pub.indexThere] := by simp
  have hq₁ : Pub.indexThere ∈ pubOfItems (IM.openAt P5J.At.links P5J.At.ps b) :=
    List.mem_flatMap.2 ⟨.pinI, hI, hq₀⟩
  have h2 : indexThereC s = true := List.all_eq_true.1 hpub _ (List.mem_append_right _ hq₁)
  have ho : s.out.indexMasks < s.st.oracles.size := by
    by_contra hn
    unfold indexThereC at h2
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at h2
    cases h2
  unfold bookAt at hbk
  simp only [Bool.and_eq_true] at hbk
  have hsz : s.book.place.size = s.st.oracles.size := eq_of_beq hbk.1.2
  have hpo : s.out.indexMasks < s.book.place.size := by
    rw [hsz]
    exact ho
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hF : BookFits s.book :=
    (VerifiableInference.Desc.Sound.bookFitsB_iff _).1
      (Meaning.K2.atFirstFits_all O (P1K2.plan_of O h.toAtMg.laid.planOk) (reach_raw hreach))
  have hq := Array.getElem?_eq_getElem hpo
  exact ⟨hL.rows, hL.smp.1, shape_left hL _ ho,
    seat_left hL _ _ hq (placed_of_fits hF _ _ hq)⟩

/-! ## 3 Which sort of place -/

/-- **Which sort of place the member is, and K2Keeps there.** At a link's first place K2Keeps holds
up to the state between, behind which the frame's step stands. -/
theorem k2_keeps_core (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) {blk : Block S Cl}
    (hblk : cF.blocksInOrder[b]? = some blk) {s s' : S} (hyes : IM.Yes 0 blk s s') :
    (∃ l fs f m, blk.place.link = some l ∧ l ≠ 24 ∧
        framesOf Zp.p.built.links Zp.first Zp.p.X = .ok fs ∧ fs[l]? = some f ∧
        (∃ q : P2, q.stands = .link ∧ K2Keeps q s m) ∧ P1K2.leaveOpened f s m = .ok s') ∨
      (blk.place.link = some 24 ∧ ∃ q : P2, q.stands = .head ∧ K2Keeps q s s') ∨
      (blk.place.link = none ∧ ∃ q : P2, q.stands = .finish ∧ K2Keeps q s s') := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨p, hpW, rfl⟩ := k2_place_at ha hk
  have hp : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hpW
  obtain ⟨rs, gs, e⟩ := stepYes_decide (IM.yes_stepYes hyes)
  obtain ⟨Pp, n, nm, st, before, after, -, -, hA, ⟨epl, -, -⟩, -, hd⟩ :=
    k2_block_at_head h O hp hblk
  obtain ⟨s₁, m, e1, e2, e3⟩ := hd s rs gs s' e
  rcases hA with ⟨rfl, ep, -, h24, -, rfl, fs, f, hfs, hff, -, rfl⟩ |
    ⟨rfl, ep, -, rfl, HP, -, rfl⟩ | ⟨rfl, ep, -, rfl, rfl⟩
  · have es : s = s₁ := Except.ok.inj e1
    rw [← es] at e2
    rw [← es] at e3
    have el : blk.place.link = some p.link :=
      (congrArg Place.link epl).trans (congrArg Place.link ep)
    exact Or.inl ⟨p.link, fs, f, m, el, by omega, hfs, hff, ⟨_, rfl, k2Keeps_of_link rfl e2⟩, e3⟩
  · have es : s = s₁ := Except.ok.inj e1
    rw [← es] at e2
    rw [← es] at e3
    have e3' : (headOpenQ HP m).bind (P1K2.guards s) = .ok s' := e3
    obtain ⟨u, u1, u2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e3'
    have eu : s' = u := P1K2.guards_same u2
    have hn : s'.failed = none := (P1K2.guards_none u2).2
    have el : blk.place.link = some 24 :=
      (congrArg Place.link epl).trans (congrArg Place.link ep)
    have hy := head_yes (nm := nm) (pl := p.place) (rs := rs) (gs := gs) e2 (eu ▸ u1)
    exact Or.inr (Or.inl ⟨el, _, rfl, k2Keeps_of_head rfl hy hn⟩)
  · have e3' : (finishBehindQ m).bind (P1K2.guards s₁) = .ok s' := e3
    obtain ⟨u, u1, u2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e3'
    have eu : s' = u := P1K2.guards_same u2
    have hn : s'.failed = none := (P1K2.guards_none u2).2
    have el : blk.place.link = none :=
      (congrArg Place.link epl).trans (congrArg Place.link ep)
    have hy := fin_yes (rs := rs) (gs := gs) e1 e2 (eu ▸ u1)
    exact Or.inr (Or.inr ⟨el, _, rfl, k2Keeps_of_finish rfl hy hn⟩)

/-! ## 4 The riders -/

/-- A member of the kind stands at 339 or above, if the border behind it does. -/
theorem k2_border_at {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl)
    (hk : pl.kind = KindName.K2) (h : 339 ≤ b + 1) : 339 ≤ b := by
  rcases P1K2.k2_spots b pl ha hk with ⟨l, -, h24, rfl⟩ | rfl | rfl <;> omega

/-- **No clause of the list speaks at the border behind a member of the kind.** -/
theorem k2_riders_behind {W : Type} (ν : Nat) (st : Nat → S → Prop)
    (R : Nat → Option OnBytes.Model.Forest.Heard → Prop) {b : Nat} {pl : Place}
    (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K2) (v : W) (s' : S) :
    ridersOf (csHead ν st R) (b + 1) v s' := by
  unfold ridersOf
  intro c hc hlo hhi
  exfalso
  have hsp := csHead_span hc
  rcases P1K2.k2_spots b pl ha hk with ⟨l, -, h24, rfl⟩ | rfl | rfl <;>
    rcases hsp with ⟨a1, a2⟩ | ⟨l', -, a1, a2⟩ | ⟨g, hg, a1, a2⟩ | ⟨g, hg, a1, a2⟩ <;> omega

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.k2Keeps_of_link
#print axioms AtFullSide.K2.Term.k2Keeps_of_head
#print axioms AtFullSide.K2.Term.k2Keeps_of_finish
#print axioms AtFullSide.K2.Term.head_yes
#print axioms AtFullSide.K2.Term.fin_yes
#print axioms AtFullSide.K2.Term.k2_left_behind
#print axioms AtFullSide.K2.Term.k2_reply_kept
#print axioms AtFullSide.K2.Term.k2_pile_parts
#print axioms AtFullSide.K2.Term.k2_keeps_core
#print axioms AtFullSide.K2.Term.k2_border_at
#print axioms AtFullSide.K2.Term.k2_riders_behind
