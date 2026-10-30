-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K7/Accepts.lean: THE NEXT TOKEN's MEMBER OF THE FIRST CHAIN SAYS YES
TO ITS HONEST HALF's ROUND: `AcceptedS` (Honest/Thread/PaysS.lean), at every fall: the member has
none. General in the thread T and in the letter Said, at the first chain's type of states.

  `K7Ready T Said b G f`   WHAT THE YES WANTS OF THE THREAD IN FRONT: a record of named premises:
      from the pair (`ThrS`): the entry into the head's segment returns (`enters`); nothing is heard
      yet (`unheard`); no mark (`unmarked`) · from `T.valid`: the asked token is an entry of the
      vocabulary (`tok`) · the frame's half: «opened» hands on behind the lot's own sub-protocol
      (`opens`)
  `headFrontQ_here`   behind the entry the chain stands in the head's segment, not yet opened
  `h1Front_yes`, `blockAt_yes`, `h1_yes`   THE WAY FORWARD through the lot's three texts: where the
      entry returns t, nothing is heard, and the one round reads as a token: the lot's decision
      returns t with that token laid
  `h1_shape`          the lot's rounds and oracle messages
  `reply_draw`, `reply_read_at`   a challenge that fits the round draws nothing; so the round as
      played reads as the asked token
  `k7_lot_yes`        the lot's own STEP says yes at the round as played
  `k7_acceptedS`      **IT IS ACCEPTED**

By `acceptedS_joined` (Honest/Law/NoHouse/JoinDebts.lean), `step_iff_decide` (Honest/Law/Cut.lean),
`play_row_whole` (Honest/Small/PlayRow.lean), the library's `guarded_yes`
(Johnson/Desc/Sound/SeatGuardLaws.lean), `headFrontQ_iff` (Top/H0/Tw/K2C/Asks.lean),
`headFrontQ_rest`, and this folder's files.

Limits. A conditional lemma on our own definitions; none of the library's goals. NOTHING SHOWS THAT
THE THREE RECORDS' PREMISES HOLD AT A THREAD: `enters` is the heaviest: the entry's own guards.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K7.Lays
import Johnson.Desc.Sound.SeatGuardLaws
import Johnson.Top.H0.Tw.K2C.Asks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place noDigest roundlessBlock)
open VerifiableInference.Desc.First (S HeadOwn hearsReply)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_rest headFrontQ_iff enterHeadQ)
open VerifiableInference.Desc.Kinds (Reply.blockAt Reply.kind Reply.seatAt)
open OnBytes.Desc.Reply (readReply isToken)
open OnBytes.Model (HTailF2)
open Johnson.Desc.First.Walk.Seat (LinkFrame)
open ProofFile.Honest.Small (play_row_whole row_silent)
open ProofFile (Cl)

/-! ## 1 The way forward through the lot's texts -/

theorem headFrontQ_here {tl : HTailF2} {s t : S} (h : headFrontQ tl s = .ok t) :
    ∃ o : HeadOwn, t.here = .head o ∧ o.opened = false := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s t).1 h
  have e : s₁ = s.enterHead tl := enterHeadQ k.enters
  unfold S.enterHead at e
  rw [if_pos k.between] at e
  have ha := k.entered
  rw [e] at ha
  cases ha
  rw [k.out]
  exact ⟨_, rfl, rfl⟩

theorem h1Front_yes (tl : HTailF2) (name : String) (l : Nat) (a : Place) {s t : S}
    (ht : headFrontQ tl s = .ok t) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    (Block.guarded sameReply (fun _ => false)
      ({ (roundlessBlock name 1 (some l) 1 (headFrontQ tl) : Block S Unit) with place := a })).decide
        s rs gs = .ok t := by
  refine (VerifiableInference.Desc.guarded_yes sameReply (fun _ => false) _ rfl s rs gs t).2
    ⟨ht, ?_⟩
  show (s.out.reply == t.out.reply) = true
  rw [(headFrontQ_rest ht).2.2.2.2.2.1]
  exact beq_self_eq_true _

theorem blockAt_yes (l V : Nat) {t : S} {o : HeadOwn} {r : Fmt.RoundView} {v : OnBytes.E}
    (ho : t.here = .head o) (hop : o.opened = false) (hn : t.out.reply = none)
    (hr : readReply r = some v) (hv : isToken V v = true)
    (gs : List (List (Nat × List UInt64))) :
    (Reply.blockAt l V).decide t [r] gs = .ok { t with out := { t.out with reply := some v } } := by
  have hk : (Reply.kind (Cl := Unit) Reply.seatAt l 1 V).decide t [r] gs =
      .ok { t with out := { t.out with reply := some v } } := by
    show VerifiableInference.Desc.Kinds.Reply.decideE V Reply.seatAt t [r] = _
    have h0 : (Reply.seatAt.reply t).isSome = false := by
      show t.out.reply.isSome = false
      rw [hn]
      rfl
    unfold VerifiableInference.Desc.Kinds.Reply.decideE
    simp only [h0, hr, hv, Bool.false_eq_true, if_false, if_true]
    rfl
  unfold Reply.blockAt VerifiableInference.Desc.Kinds.Reply.entered
  dsimp only
  rw [ho]
  dsimp only
  rw [hop, if_neg Bool.false_ne_true, hk, ho]

theorem h1_shape {G : Ground} {x : Block S Unit} (hx : x ∈ h1Own G) :
    x.rounds = VerifiableInference.Desc.Kinds.Reply.rounds ∧ x.oracles = [[]] := by
  unfold h1Own at hx
  obtain rfl := List.mem_singleton.1 hx
  exact ⟨rfl, rfl⟩

/-- **The lot's decision says yes.** -/
theorem h1_yes {G : Ground} {x : Block S Unit} (hx : x ∈ h1Own G) {s t : S} {r : Fmt.RoundView}
    {v : OnBytes.E} (ht : headFrontQ G.W.H.tl s = .ok t) (hn : s.out.reply = none)
    (hr : readReply r = some v) (hv : isToken G.W.hS.V v = true)
    (gs : List (List (Nat × List UInt64))) :
    x.decide s [r] gs = .ok { t with out := { t.out with reply := some v } } := by
  obtain ⟨o, ho, hop⟩ := headFrontQ_here ht
  have hn' : t.out.reply = none := by rw [(headFrontQ_rest ht).2.2.2.2.2.1, hn]
  unfold h1Own at hx
  obtain rfl := List.mem_singleton.1 hx
  unfold Block.andThen
  dsimp only
  rw [h1Front_yes _ _ _ _ ht]
  exact blockAt_yes _ _ ho hop hn' hr hv _

/-! ## 2 The round as played -/

theorem reply_draw {d : Fmt.Drawn}
    (h : drawsFit VerifiableInference.Desc.Kinds.Reply.rounds [d] = true) :
    d.elems = [] ∧ d.poss = [] ∧ d.trits = [] := by
  unfold VerifiableInference.Desc.Kinds.Reply.rounds at h
  simp only [drawsFit, drawFit, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨List.length_eq_zero_iff.1 h.1.1.1.1.1.1.1.1, List.length_eq_zero_iff.1 h.1.1.1.1.1.1.1.2,
    List.length_eq_zero_iff.1 h.1.1.1.1.1.1.2⟩

theorem reply_read_at (name : String) (a : Place) (x : Inst) {d : Fmt.Drawn}
    (h : drawsFit VerifiableInference.Desc.Kinds.Reply.rounds [d] = true) :
    readReply (noDigest ⟨(replyShown name a x d).vals, d⟩) = some x.asked := by
  obtain ⟨e1, e2, e3⟩ := reply_draw h
  unfold readReply noDigest replyShown
  simp only [e1, e2, e3, List.isEmpty_nil, Option.isNone_none, Bool.and_self, if_true]
  rw [asked_code]

/-! ## 3 The record, and the debt -/

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-- **What the yes wants of the thread in front.** A hypothesis's form. -/
structure K7Ready (T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) (b : Nat) (G : Ground)
    (f : LinkFrame) : Prop where
  /-- from the pair: the entry into the head's segment returns -/
  enters : ∀ k s m E, ThrS T Said b k s m E → ∃ t, headFrontQ G.W.H.tl s = .ok t
  /-- from the pair: nothing is heard yet -/
  unheard : ∀ k s m E, ThrS T Said b k s m E → s.out.reply = none
  /-- from the pair: no mark -/
  unmarked : ∀ k s m E, ThrS T Said b k s m E → s.failed = none
  /-- from `T.valid`: the asked token is an entry of the vocabulary -/
  tok : ∀ v, T.valid v → isToken G.W.hS.V v.x.asked = true
  /-- the frame's half of the yes -/
  opens : ∀ s mid, H1Keeps G.W.H.tl G.W.hS.V s mid →
    ∃ s', f.opened mid = .ok s' ∧ s'.failed = none ∧ sameReply mid s' = true

variable {T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb} {b l V : Nat}
  {blk : Block S Cl} {G : Ground} {x : Block S Unit}

/-- **The lot's own step says yes at the round as played.** -/
theorem k7_lot_yes (K : K7Stands T b l V blk) (hx : x ∈ h1Own G) {k : Coins Bk} {s t : S}
    {m : Mid (Local W₀ Rc Inst Tr) X} {E : Env} {d : Fmt.Drawn}
    {L : List (Step (Local W₀ Rc Inst Tr) X)} (hd : drawsFit blk.rounds [d] = true)
    (hst : chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc [d] = none)
    (hl : chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs =
      .ok L)
    (ht : headFrontQ G.W.H.tl s = .ok t) (hn : s.out.reply = none)
    (hv : isToken G.W.hS.V m.st.input.x.asked = true) :
    (x.retype : Block S Cl).step T.ft s
      (roundsOf [replyShown blk.name blk.place m.st.input.x d]) [] =
        .ok ({ t with out := { t.out with reply := some m.st.input.x.asked } }, 0) := by
  have hs' := row_silent K.half hd hst
  obtain ⟨c, -, -⟩ := steps_one_half K.half hl
  obtain ⟨er, eo⟩ := h1_shape hx
  have hd' : drawsFit VerifiableInference.Desc.Kinds.Reply.rounds [d] = true := K.rounds ▸ hd
  have hy := play_row_whole (x.retype : Block S Cl).name (x.retype : Block S Cl).place
    (T.φ.sees m.st.input) (replyHalf (W₀ := W₀) (Rc := Rc) (Tr := Tr) (X := X) l 1 V).parts 0
    ((x.retype : Block S Cl).rounds.zip (x.retype : Block S Cl).oracles) c [d] [] m _ hs'
    (by
      show Small.fitsRow _ (x.rounds.zip x.oracles) c m.st m.shown [d] = true
      rw [er, eo]
      exact reply_fits c m.st m.shown d)
    (reply_played _ _ c m.st m.shown d)
  refine (step_iff_decide (g := replyHalf l 1 V) (b := (x.retype : Block S Cl))
    (chain := T.chain) (ft := T.ft) (stored := E.stored) (tree := E.tree) (cols := []) s _
    (by show _ = x.rounds.length; rw [er]; rfl)
    (by show x.oracles.length = x.rounds.length; rw [er, eo]; rfl)
    hy (by show drawsFit x.rounds [d] = true; rw [er]; exact hd')
    (by show fillCols (readsOf _ _ _ _ x.rounds [d]) [] = .ok []; rw [er]; rfl)).2 ?_
  exact h1_yes hx ht hn (reply_read_at _ _ _ hd') hv _

variable {Z : Pub} {a : Place} {fs : List LinkFrame} {f : LinkFrame}

/-- **IT IS ACCEPTED.** -/
theorem k7_acceptedS (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (K : K7Stands T b l V blk) (D : K7Made Z G l blk x a fs f) (R : K7Ready T Said b G f)
    (ha : hearsReply a = true) (fall : Nat → S → List Fmt.Drawn → Option String) :
    AcceptedS T Said fall b := by
  refine acceptedS_joined T D.joined D.frames D.frame K.member
    (fun _ s _ _ _ mid => H1Keeps G.W.H.tl G.W.hS.V s mid) ?_ ?_
  · intro k s m E ds y cols hA hd hst _ hM
    obtain ⟨t, ht⟩ := R.enters k s m E hA
    have hn := R.unheard k s m E hA
    have hv := R.tok _ hA.1.2.2.2.2.2.2
    obtain ⟨d, rfl, ey⟩ := k7_played K hd hM
    obtain ⟨⟨L, hl, -⟩, hc⟩ := hM
    have hc0 : cols = [] := by
      rw [K.rounds] at hc
      exact (Except.ok.inj hc).symm
    subst hc0
    obtain ⟨o, ho, hop⟩ := headFrontQ_here ht
    have hf : t.failed = none := by
      rw [(headFrontQ_rest ht).2.2.2.1]
      exact R.unmarked k s m E hA
    refine ⟨{ t with out := { t.out with reply := some m.st.input.x.asked } }, ?_, hf,
      fun h => absurd ha (by rw [h]; exact Bool.false_ne_true), hf, t, ht, o, _, ho, hop, ?_, hv,
      rfl⟩
    · rw [ey]
      exact k7_lot_yes (E := E) K D.lot hd hst hl ht hn hv
    · rw [(headFrontQ_rest ht).2.2.2.2.2.1, hn]
  · intro k s m E y mid _ hMid
    exact R.opens s mid hMid

end ProofFile.Honest

#print axioms ProofFile.Honest.headFrontQ_here
#print axioms ProofFile.Honest.h1Front_yes
#print axioms ProofFile.Honest.blockAt_yes
#print axioms ProofFile.Honest.h1_shape
#print axioms ProofFile.Honest.h1_yes
#print axioms ProofFile.Honest.reply_draw
#print axioms ProofFile.Honest.reply_read_at
#print axioms ProofFile.Honest.k7_lot_yes
#print axioms ProofFile.Honest.k7_acceptedS
