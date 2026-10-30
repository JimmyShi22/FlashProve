-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K7/Lays.lean: THE NEXT TOKEN's MEMBER LAYS THE REPLY's CLAUSE: behind
the member's own step, at the round that its honest half has played, the reply's seat holds the
token that the run's input asks about: `LaysAtS` (Honest/Thread/SharesS.lean) for the clause
«s.out.reply = some v.x.asked». General in the thread T and in the letter Said, at the first chain's
type of states.

  `K7Made Z G l blk x a fs f`   WHAT THE MEMBER IS MADE OF: a record of named premises: x is the
      lot's own sub-protocol (`h1Own`); blk is x, carried over, with the «opened» of segment l's own
      row of frames joined behind it (the library's `IM.Joined`)
  `blockAt_kind`    a return of the seated sub-protocol's decision is a return of the kind's
  `readReply_e`     what `readReply` yields at a round of one element
  `h1_reads`        a return of the lot's decision: it was shown just one round, and the reply's
      seat behind holds what `readReply` yields of that round
  `k7_played`       where the member's prover's side has moved: what was played is `replyShown`
  `k7_mid_reply`    at the state between: the seat holds the asked token
  `k7_laysS`        **THE CLAUSE IS LAID**, lo and hi free

By `stepped_joined` (Honest/Law/NoHouse/JoinDebts.lean), `member_played`
(Honest/Small/SaysYesOf.lean), the library's `step_ok_iff` (Johnson/Desc/Sound/RunIsDecide.lean),
`k7_ok` (Kinds/Law/Heard.lean), `IM.sameReply_eq`, and `asked_code` (Honest/K7/Played.lean).

Limits. A conditional lemma on our own definitions; none of the library's goals. Nothing shows that
the two records' premises hold at a thread. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K7.Plays
import Johnson.Desc.ProofFile.Honest.K7.Keeps
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.JoinDebts
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.Kinds.Law.Heard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headFrontQ)
open VerifiableInference.Desc.Kinds (Reply.blockAt Reply.kind Reply.seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (k7_ok)
open OnBytes.Desc.Reply (readReply)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open ProofFile.Honest.Small (member_played)
open ProofFile (Cl)

/-- **What the member is made of.** A hypothesis's form. -/
structure K7Made (Z : Pub) (G : Ground) (l : Nat) (blk : Block S Cl) (x : Block S Unit) (a : Place)
    (fs : List LinkFrame) (f : LinkFrame) : Prop where
  lot : x ∈ h1Own G
  joined : IM.Joined Z l blk x.retype a
  frames : framesOf Z.p.built.links Z.first Z.p.X = .ok fs
  frame : fs[l]? = some f

theorem blockAt_kind {l V : Nat} {t m : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (Reply.blockAt l V).decide t rs gs = .ok m) :
    (Reply.kind (Cl := Unit) Reply.seatAt l 1 V).decide t rs gs = .ok m := by
  unfold Reply.blockAt VerifiableInference.Desc.Kinds.Reply.entered at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · exact h
  · cases h

theorem readReply_e {t : Fmt.Ext3} {D : Fmt.Drawn} {v : OnBytes.E}
    (h : readReply ⟨[.e t], D⟩ = some v) : v = OnBytes.E.ofTriple t := by
  unfold readReply at h
  dsimp only at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- A return of the lot's own decision reads one round. -/
theorem h1_reads {G : Ground} {x : Block S Unit} (hx : x ∈ h1Own G) {s m : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : x.decide s rs gs = .ok m) :
    ∃ r0 v, rs = [r0] ∧ readReply r0 = some v ∧ m.out.reply = some v := by
  unfold h1Own at hx
  obtain rfl := List.mem_singleton.1 hx
  generalize hf : (Block.guarded sameReply (fun _ => false)
    ({ (VerifiableInference.Desc.roundlessBlock "H:1" 1 (some (G.built.size - 1)) 1
        (headFrontQ G.W.H.tl) : Block S Unit) with place := (P4.k7Core G).place })) = front at h
  have hr : front.rounds = [] := by
    rw [← hf]
    rfl
  have h' : ((front.decide s (rs.take front.rounds.length) (gs.take front.openings)).bind
      fun s1 => (P4.k7Core G).decide s1 (rs.drop front.rounds.length) (gs.drop front.openings)) =
        .ok m := h
  cases hp : front.decide s (rs.take front.rounds.length) (gs.take front.openings) with
  | error e =>
    rw [hp] at h'
    cases h'
  | ok t =>
    rw [hp, hr] at h'
    obtain ⟨r0, v, e1, e2, -, rfl⟩ := k7_ok (blockAt_kind h')
    exact ⟨r0, v, e1, e2, rfl⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}
  {T : Thread Bk S Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb} {b l V : Nat}
  {blk : Block S Cl}

/-- Where the challenges fit the member's rounds (`drawsFit`) and the prover's side has moved: what
was played. -/
theorem k7_played (K : K7Stands T b l V blk) {k : Coins Bk} {m : Mid (Local W₀ Rc Inst Tr) X}
    {E : Env} {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hd : drawsFit blk.rounds ds = true)
    (hM : T.Moved blk k m E ds y cols) :
    ∃ d, ds = [d] ∧ y.1 = [replyShown blk.name blk.place m.st.input.x d] := by
  obtain ⟨⟨L, hl, hy⟩, -⟩ := hM
  obtain ⟨d, rfl⟩ : ∃ d, ds = [d] := one_draw (K.rounds ▸ hd)
  obtain ⟨c, -, -, hp, -, -⟩ := member_played K.half hl hy
  have e := (reply_played blk.name blk.place c m.st m.shown d).symm.trans hp
  exact ⟨d, rfl, (Option.some.inj e).symm⟩

variable {Z : Pub} {G : Ground} {x : Block S Unit} {a : Place} {fs : List LinkFrame} {f : LinkFrame}

/-- At the state between, where the challenges fit (`drawsFit`): the seat holds the asked token. -/
theorem k7_mid_reply (K : K7Stands T b l V blk) (D : K7Made Z G l blk x a fs f) {k : Coins Bk}
    {s mid : S} {m : Mid (Local W₀ Rc Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc Inst Tr) X} {cols : List VerifiableInference.Desc.OpenedColumn}
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
    (hs : (x.retype : Block S Cl).step T.ft s (roundsOf y.1) cols = .ok (mid, cols.length)) :
    mid.out.reply = some m.st.input.x.asked := by
  obtain ⟨d, -, ey⟩ := k7_played K hd hM
  have hdec :=
    ((VerifiableInference.Desc.Sound.step_ok_iff T.ft _ s mid _ cols cols.length).1 hs).2.2.2
  obtain ⟨r0, v, e1, e2, e3⟩ := h1_reads D.lot (show x.decide s _ _ = .ok mid from hdec)
  rw [ey] at e1
  obtain rfl : noDigest ⟨(replyShown blk.name blk.place m.st.input.x d).vals, d⟩ = r0 :=
    List.head_eq_of_cons_eq e1
  rw [e3, readReply_e e2, asked_code]

/-- **THE CLAUSE IS LAID.** -/
theorem k7_laysS (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (K : K7Stands T b l V blk) (D : K7Made Z G l blk x a fs f) (lo hi : Nat) :
    LaysAtS T Said b ⟨lo, hi, fun _ v s => s.out.reply = some v.x.asked⟩ := by
  intro blk' hblk k s m E ds y cols s' _ hd hS
  obtain rfl : blk = blk' := Option.some.inj (K.member.symm.trans hblk)
  obtain ⟨hM, ⟨mid, hs, -, -, hsame⟩, -⟩ :=
    (stepped_joined T D.joined D.frames D.frame k s m E ds y cols s').1 hS
  show s'.out.reply = some m.st.input.x.asked
  rw [← IM.sameReply_eq hsame]
  exact k7_mid_reply K D hd hM hs

end ProofFile.Honest

#print axioms ProofFile.Honest.blockAt_kind
#print axioms ProofFile.Honest.readReply_e
#print axioms ProofFile.Honest.h1_reads
#print axioms ProofFile.Honest.k7_played
#print axioms ProofFile.Honest.k7_mid_reply
#print axioms ProofFile.Honest.k7_laysS
#print axioms ProofFile.Honest.K7Made
