-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Makers.lean: THE GUARD ON THE REPLY: THE MAKERS. Every maker of the proof file's
seat but K7's leaves the reply that the verifier's state has heard: the twenty fields of
`SeatBut` (Johnson/LPFGuard/Ground.lean) at the relation `ReplyR`. Theorems, proved.

Main names.
* `seatBut_reply : SeatBut ReplyR`: the twenty fields laid together.
* `reply_frames`, `reply_k1First` and so on (`reply_` and the field's name): one theorem a field.
* `whole_up`: `Whole` passes to every weaker relation. `reply_of_outer`: from `Whole Outer`.
* `reads_noRuns`: the quiet step behind the reads states no run.

What it leans on: each field is a law of the library, called. No maker's text is walked by hand here
but framesOf's rows, the reads' three arms and closeOf's list of three (to see which law applies, or
that a list of runs is empty); that a maker's lists of runs are empty is elsewhere left to Lean's
unfolding (`nomatch`).
* K3, K4, K5, K6, K8, K11: `Whole Outer` (Johnson/Goal/Meaning/OuterSeated.lean: theStated_outer,
  blockAtC_outer, k5AtN_outer, seatedClaims_outer, k8Whole_outer, headMerge11_outer).
* The frames: layFront_leaves, openAtt_leaves, openLay_leaves, openLayZero_leaves, clearWith_leaves
  (Johnson/Top/H0/Walk/FrameLaw.lean), tailHead_leaves (Johnson/Top/H0/Walk/FrameLeaves.lean).
* K1: firstAtS_ok (Johnson/Desc/K1/Law/AtRecord.lean), commitAtS_out
  (Johnson/Desc/AtSeats/ReplyLeft.lean), quietK_readsQuietAt
  (Johnson/Desc/K1/Law/PubAtLaterKeeper.lean), sendAtS_here (Johnson/Desc/K1/Law/HereAtRecord.lean).
* K2: k2LeavesReply (Johnson/Top/H0/Tw/K2C/LeavesOut.lean), headFrontOut, headOpenLays,
  finishFrontOut, finishBehindOut (Johnson/Top/H0/Tw/K2C/Reply.lean).
* K9, K10: leaves_closeOf, leaves_batch (Johnson/Desc/First/Batch/Law/LeavesClose.lean,
  Leaves.lean), at the reading S.heard, which is out.reply by definition
  (Johnson/Desc/First/StateHeard.lean).
* K12: atFinish_reply, atFinish_claims, atFinish_after (Johnson/Desc/K12/SeatReply.lean).
* K13: atM3_rec (Johnson/Desc/K13/Law/AtRecord.lean), rowsB_at (Johnson/Desc/K13/Law/AtM4.lean),
  Keeps.andThen_whole (Johnson/Desc/BlockKeeps.lean). NOT atM4_rec, which speaks of two rounds
  alone.
* Tools: Meaning.K2.mem_of_mapM_ok (Johnson/Goal/Meaning/KeepsDriver.lean), Seat.headFrame_clear
  (Johnson/Top/H0/Walk/FrameLot.lean).

Proofs carried from other files.
* `whole_up`: whole_mono, Johnson/Road/K4/K4WholeSt.lean, typed again so that this file does
  not import that road.
* `reply_frames`: the walk over framesOf's rows, with this relation's laws at the leaves; carried
  from a file that is not in this library.
* `noRuns_blockAt`, `reads_noRuns`: the walk is readsBlockAt_quiet's and readsQuietAt_quiet's,
  Johnson/IMR/SeatKeeps.lean; `noRuns_att`: readsAtO_quiet's, Johnson/Goal/Meaning/RecGrows.lean.
* `reply_closeOf`: the three cases are closeOf_rs's, Johnson/IMR/RowsSent.lean.

Limits. These are frame laws: implications from a yes; a maker that refuses all meets them emptily.
Nothing is said of K7's block, which hears the reply. Nothing is said here of a lot, of a chain or
of the guard itself: for these see the other files of this folder. Nothing on soundness.


-/
import Johnson.LPFGuard.Ground
import Johnson.Goal.Meaning.OuterSeated
import Johnson.Top.H0.Walk.FrameLaw
import Johnson.Top.H0.Walk.FrameLeaves
import Johnson.Desc.AtSeats.ReplyLeft
import Johnson.Desc.K1.Law.PubAtLaterKeeper
import Johnson.Top.H0.Tw.K2C.LeavesOut
import Johnson.Desc.First.Batch.Law.LeavesClose
import Johnson.Desc.K12.SeatReply
import Johnson.Desc.K13.Law.AtRecord
import Johnson.Desc.K13.Law.AtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)

/-! ## Three rules -/

/-- Whole passes to every weaker relation. -/
theorem whole_up {Cl : Type} {R R' : S → S → Prop} {b : Block S Cl}
    (hm : ∀ s s', R s s' → R' s s') (W : Whole R b) : Whole R' b :=
  ⟨fun s rs gs s' h => hm _ _ (W.1 s rs gs s' h), fun c hc n s y h => hm _ _ (W.2.1 c hc n s y h),
    fun c hc s s' h => hm _ _ (W.2.2 c hc s s' h)⟩

/-- Whoever keeps Outer (out, check and req as they were) leaves the reply. -/
theorem reply_of_outer {Cl : Type} {b : Block S Cl} (W : Whole Meaning.Out.Outer b) :
    Whole ReplyR b :=
  whole_up (fun _ _ h => replyR_of_out h.1) W

/-- A block that states no run: its decision is all of it. -/
theorem whole_of_decides {Cl : Type} {R : S → S → Prop} {b : Block S Cl} (hd : Decides R b)
    (hc : b.claims = []) (ha : b.after = []) : Whole R b :=
  ⟨hd, (fun c k => by rw [hc] at k; cases k), (fun c k => by rw [ha] at k; cases k)⟩

/-! ## The six kinds that send nothing inside a link -/

theorem reply_k3 (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole ReplyR b :=
  reply_of_outer (Meaning.Out.theStated_outer claim readers X codes shape a h)

theorem reply_k4 (p : OnBytes.Desc.First.K4.Par) :
    Whole ReplyR (OnBytes.Desc.First.K4.blockAtC p) :=
  reply_of_outer (Meaning.Out.blockAtC_outer p)

theorem reply_k5 (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim}
    (h : Att.P.k5AtN W l g before = some b) : Whole ReplyR b :=
  reply_of_outer (Meaning.Out.k5AtN_outer W l g before h)

theorem reply_k6 {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim}
    (h : Kinds.Head.seatedClaims W l before = some b) : Whole ReplyR b :=
  reply_of_outer (Meaning.Out.seatedClaims_outer h)

theorem reply_k8 (p : K8.ParW) : Whole ReplyR (K8.whole p) :=
  reply_of_outer (Meaning.Out.k8Whole_outer p)

theorem reply_k11 (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    Whole ReplyR (Johnson.Desc.First.ForkMerge.headClaimMergeKind P) :=
  reply_of_outer (Meaning.Out.headMerge11_outer P)

/-! ## The frames -/

section frames
open Johnson.Desc.First.Walk
open Johnson.Desc.First.Walk.Law (layFront_leaves openAtt_leaves openLay_leaves openLayZero_leaves
  clearWith_leaves)
open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame)

theorem fn_lay (l : Nat) : Fn ReplyR (layFront l) := fun _ _ k => layFront_leaves k

theorem fn_openAtt (P : AttPar) : Fn ReplyR (openAtt P) := fun _ _ k => openAtt_leaves k

theorem fn_openLay (P : LayPar) : Fn ReplyR (openLay P) := fun _ _ k => openLay_leaves k

theorem fn_openZero (P : LayPar) (fvs : List Bool) (kCol : Nat) :
    Fn ReplyR (openLayZero P fvs kCol) := fun _ _ k => openLayZero_leaves k

theorem fn_clear (X : LinkPub) (counts : S → Except String Unit) (left : S → Option WsForkOut)
    (row : RowFn) : Fn ReplyR (clearWith X counts left row) := fun _ _ k => clearWith_leaves k

/-- The head's link's end. -/
theorem fn_tailHead (X : LinkPub) (lay : WsLay) (lin : Params.LinShape) :
    Fn ReplyR (Close.tailHead X lay lin) := fun s t k => Law.tailHead_leaves X lay lin s t k

/-- **Every row of the frame**: "laid", "opened" and "cleared", at every link, the head's among
them. -/
theorem reply_frames {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn ReplyR f.lay ∧ Fn ReplyR f.opened ∧ Fn ReplyR f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := Meaning.K2.mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      refine ⟨fn_lay l, fun s t k => by cases k; exact replyR_refl s, ?_⟩
      rw [Seat.headFrame_clear]
      exact fn_tailHead _ _ _
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨fn_lay 0, fn_openZero _ _ _, fn_clear _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨fn_lay l, fn_openAtt _, fn_clear _ _ _ _⟩
      · cases e
        exact ⟨fn_lay l, fn_openLay _, fn_clear _ _ _ _⟩

end frames

/-! ## K1 -/

theorem reply_k1First (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    Whole ReplyR (K1.firstSegmentOpening (Cl := Unit) q gp) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨_, _, _, _, ho⟩ := K1.firstAtS_ok q gp s s' rs gs h
      exact replyR_of_out ho,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem reply_k1Later (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Whole ReplyR (K1.laterAt (Cl := Unit) q gp link piece moment arrays) :=
  ⟨fun s rs gs s' h => replyR_of_out (K1.commitAtS_out _ link moment arrays s s' rs gs h),
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem noRuns_att {W : Verify.Public} {l g : Nat} {b : Block S Unit}
    (h : Att.readsAtO W l g = some b) : b.claims = [] ∧ b.after = [] := by
  unfold Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, rfl⟩

theorem noRuns_blockAt {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : b.claims = [] ∧ b.after = [] := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · cases h

/-- The quiet step behind the reads states no run of claims and no run behind the batching. -/
theorem reads_noRuns {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : b.claims = [] ∧ b.after = [] := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact noRuns_att h
    | exact noRuns_blockAt h
    | cases h

theorem reply_reads {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : Whole ReplyR b :=
  whole_of_decides
    (fun s rs gs s' k => replyR_of_out (K1.quietK_readsQuietAt l X piece b h s s' rs gs k).2)
    (reads_noRuns h).1 (reads_noRuns h).2

/-! ## K2 -/

theorem reply_k2 (p : K2.P2) : Whole ReplyR (K2.codeSwitchKind p : Block S Unit) :=
  ⟨fun s rs gs s' h => K2.k2LeavesReply p s rs gs s' h,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem reply_front (tl : HTailF2) : Fn ReplyR (K2.headFrontQ tl) :=
  fun s s' h => replyR_of_out (K2.headFrontOut tl s s' h)

theorem reply_openQ (P : K2.HeadPar) : Fn ReplyR (K2.headOpenQ P) := fun s s' h => by
  obtain ⟨_, _, _, _, _, _, _, ho⟩ := K2.headOpenLays P s s' h
  exact replyR_of_out ho

theorem reply_finFront : Fn ReplyR K2.finishFrontQ :=
  fun s s' h => replyR_of_out (K2.finishFrontOut s s' h)

theorem reply_finBehind : Fn ReplyR K2.finishBehindQ :=
  fun s s' h => replyR_of_out (K2.finishBehindOut s s' h)

/-! ## K9 and K10: the batching and what closes a segment -/

theorem reply_closeOf (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Unit) p P, Whole ReplyR b := by
  intro b hb
  have hd : Decides ReplyR b := fun s rs gs s' h => K9L.leaves_closeOf p P b hb s rs gs s' h
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  all_goals exact ⟨hd, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- The batching, as a function of the gatherer: it leaves the reply wherever the gatherer does. -/
theorem reply_batch (p : K9.Where) {claims : S → Except String (List Claim × S)}
    (hcl : FnCl ReplyR claims) : Whole ReplyR (K9.batch K9.atS p claims) :=
  ⟨fun s rs gs s' h => K9L.leaves_batch p claims (fun t x hx => hcl t x hx) s rs gs s' h,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-! ## Behind the last link: K12 and K13 -/

theorem reply_k12 (p : K12.P12) : Whole ReplyR (K12.atFinish p) :=
  whole_of_decides (fun s rs gs s' h => K12.Seat.atFinish_reply p s s' rs gs h)
    (K12.Seat.atFinish_claims p) (K12.Seat.atFinish_after p)

theorem reply_k13M3 (p : K13.Where) : Whole ReplyR (K13.atM3 (Cl := Unit) p) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨_, _, _, _, rfl⟩ := K13.Law.atM3_rec h
      exact replyR_of_out rfl,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- The first half of `K13.atM4`: W's sending, at every list of rounds. -/
theorem reply_sendAtS (P : K1.Par) : Whole ReplyR (K1.sendAtS P : Block S Unit) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨_, _, _, _, _, _, ho, _⟩ := K1.sendAtS_here P s s' rs gs h
      exact replyR_of_out ho,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

/-- The second half of `K13.atM4`: the own group and (Eval), at every list of rounds. -/
theorem reply_rowsB (p : K13.Where) : Whole ReplyR (K13.rowsB (Cl := Unit) K13.atS p) :=
  ⟨fun s rs gs s' h => by
      obtain ⟨_, _, _, _, _, _, _, rfl⟩ := K13.Law.rowsB_at h
      exact replyR_of_out rfl,
    (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩

theorem reply_k13M4 (p : K13.Where) (P : K1.Par) :
    Whole ReplyR (K13.atM4 (Cl := Unit) p (K1.sendAtS P)) :=
  Keeps.andThen_whole ReplyR replyR_trans _ _ _ (reply_sendAtS P) (reply_rowsB p)

/-! ## The twenty, laid together -/

/-- **EVERY MAKER OF THE SEAT BUT K7's LEAVES THE REPLY.** -/
theorem seatBut_reply : SeatBut ReplyR where
  frames := fun h => reply_frames h
  k1First := reply_k1First
  k1Later := reply_k1Later
  reads := fun h => reply_reads h
  k3 := fun c r X cs sh a _ h => reply_k3 c r X cs sh a h
  k4 := reply_k4
  k5 := fun W l g bf _ h => reply_k5 W l g bf h
  k6 := fun h => reply_k6 h
  k8 := reply_k8
  k11 := reply_k11
  closeOf := reply_closeOf
  batch := fun p _ hf => reply_batch p hf
  k2 := reply_k2
  front := reply_front
  openQ := reply_openQ
  finFront := reply_finFront
  finBehind := reply_finBehind
  k12 := reply_k12
  k13M3 := reply_k13M3
  k13M4 := reply_k13M4

end LPFGuard

#print axioms LPFGuard.reply_frames
#print axioms LPFGuard.reply_k1First
#print axioms LPFGuard.reply_k1Later
#print axioms LPFGuard.reply_reads
#print axioms LPFGuard.reply_k3
#print axioms LPFGuard.reply_k4
#print axioms LPFGuard.reply_k5
#print axioms LPFGuard.reply_k6
#print axioms LPFGuard.reply_k8
#print axioms LPFGuard.reply_k11
#print axioms LPFGuard.reply_closeOf
#print axioms LPFGuard.reply_batch
#print axioms LPFGuard.reply_k2
#print axioms LPFGuard.reply_front
#print axioms LPFGuard.reply_openQ
#print axioms LPFGuard.reply_finFront
#print axioms LPFGuard.reply_finBehind
#print axioms LPFGuard.reply_k12
#print axioms LPFGuard.reply_k13M3
#print axioms LPFGuard.reply_k13M4
#print axioms LPFGuard.seatBut_reply
