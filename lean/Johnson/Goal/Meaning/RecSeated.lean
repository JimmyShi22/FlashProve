-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecSeated.lean: the makers whose blocks the lots lay into the first chain's
links, over the base files,
as far as the files beside this one do not pay them: each hands RecAll on
(Johnson/Goal/Meaning/RecAll.lean), most as Quiet blocks (Johnson/Goal/Meaning/RecQuiet.lean).

  theStated_quiet: K3.theStated (Johnson/Desc/First/Look/K3Stated.lean): over theWhole_quiet and
    withCallerCalls_quiet.
  atClaims_whole: A GENERAL RULE: K4.atClaims (Johnson/Desc/First/K4/AtC.lean) keeps what the block
    keeps. blockAtC_quiet: so K4.blockAtC.
  k5AtN_quiet: Att.P.k5AtN (Johnson/Desc/First/Att/SeatN.lean): over k5_whole, by the library's
    runN_ok.
  kindJoinAt_quiet, blockClaims_quiet, seatedClaims_quiet: K6's block with true claims, as a lot
    seats it (Johnson/Stored/HeadAddsAtS.lean; tested, Johnson/Stored/HeadSeatAt.lean).
  atRecord_quiet, k8Whole_quiet: K8.whole (Johnson/Desc/First/K8/Whole.lean): the hearing, the runs
    of claims and the two runs behind the batching.
  laterAt_rec: K1's laterAt (Johnson/Desc/K1/Places.lean) is commitAtS.
  headMerge11_quiet: K11's block at the head's link (Johnson/Desc/First/Fork/MergeKind.lean).
  tailHead_rec; framesOf_rec: every row of Walk.Seat.framesOf
    (Johnson/Top/H0/Walk/FrameLot.lean): its lay, opened and clear are Fn (RecRel cs sh).
OBJECT: the laid makers' blocks and steps that are named above. USERS: through whole_rec the walk
(Johnson/Goal/Meaning/RecWalk.lean: recAll_border) and the library's LinkKeeps
(Johnson/Desc/FoldKeeps.lean), at the letters cs and sh. Neither calls them. That a seated text
lays these makers at its places is not said here.
-/
import Johnson.Goal.Meaning.KeepsDriver
import Johnson.Goal.Meaning.RecK1
import Johnson.Goal.Meaning.RecK3More
import Johnson.Goal.Meaning.RecK4
import Johnson.Goal.Meaning.RecK6
import Johnson.Desc.First.Look.K3Stated
import Johnson.Desc.First.K4.AtC
import Johnson.Desc.First.Att.SeatN
import Johnson.Stored.HeadAddsAtS
import Johnson.Desc.First.K8.Whole
import Johnson.Desc.K1.Places
import Johnson.Desc.First.Fork.MergeKind
import Johnson.Top.H0.Walk.FrameLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)

variable {cs : Codes} {sh : ReqShape} {Cl : Type}

/-! ## K3 -/

theorem theStated_quiet (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : Whole Quiet b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_quiet claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact withCallerCalls_quiet claim p _ W

/-! ## K4 -/

/-- **A block whose runs list forms, at the one type of a claim, keeps what it kept.** -/
theorem atClaims_whole {T : Type} {R : T → T → Prop} {b : Block T Aff} (W : Whole R b) :
    Whole R (OnBytes.Desc.First.K4.atClaims b) := by
  refine ⟨W.1, fun c hc n s y h => ?_, W.2.2⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hc
  obtain ⟨y₀, e, rfl⟩ := Keeps.emap_ok h
  exact W.2.1 x hx n s y₀ e

theorem blockAtC_quiet (p : OnBytes.Desc.First.K4.Par) :
    Whole Quiet (OnBytes.Desc.First.K4.blockAtC p) := atClaims_whole (k4_quiet p)

/-! ## K5 -/

theorem k5AtN_quiet (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat))
    {b : Block S Claim} (h : Att.P.k5AtN W l g before = some b) : Whole Quiet b := by
  obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 h
  have H : ∀ x ∈ Att.P.runsO p, ∀ n, FnCl Quiet (x.2 n) := withJoin_keep _ _ _
  refine whole_same (k5_whole Quiet _ seatSO_lay (Att.P.runsN p) (fun c hc n s y e => ?_) _) rfl
    (fun _ hx => hx) rfl
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hc
  obtain ⟨fs, e', -⟩ := Att.P.runN_ok e
  exact H r hr n s _ e'

/-! ## K6 -/

theorem kindJoinAt_quiet (claim : Aff → Cl) (h : Model.Head.Shape) (iU3 l piece : Nat)
    (p : Kinds.Head.Par) :
    Whole Quiet
      (Kinds.Head.kindWithJoin (K3.seatCalls claim) (Kinds.Head.seatAt h iU3) l piece p) :=
  k6Join_whole Quiet quiet_refl quiet_trans _ (seatCalls_mark _) (Kinds.Head.seatAt h iU3)
    (seatAt_ledger h iU3) (seatAt_heard h iU3) (fun s _ => quiet_refl s) (fun s _ => quiet_refl s)
    l piece p

theorem blockClaims_quiet {W : Verify.Public} {l : Nat} {b : Block S Claim}
    (h : Kinds.Head.blockClaims W l = some b) : Whole Quiet b := by
  unfold Kinds.Head.blockClaims at h
  obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact kindJoinAt_quiet _ _ _ _ _ _

/-- A block whose yes is a yes of b's decision, with runs among b's, keeps what b keeps. -/
theorem whole_sub {T : Type} {R : T → T → Prop} {b c : Block T Cl} (W : Whole R b)
    (hd : ∀ s rs gs s', c.decide s rs gs = .ok s' → b.decide s rs gs = .ok s')
    (hc : ∀ x ∈ c.claims, x ∈ b.claims) (ha : c.after = b.after) : Whole R c :=
  ⟨fun s rs gs s' e => W.1 s rs gs s' (hd s rs gs s' e), fun x hx => W.2.1 x (hc x hx),
    fun x hx => W.2.2 x (ha ▸ hx)⟩

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- ONE TEXT FOR TWO FORMS OF THE SEAT (Johnson/Stored/HeadSeatAt.lean: tested): in the one the
seated block's decision IS the block's; in the other it asks a test on the record in front, and a
yes of it is a yes of the block's. (The two linters are off here alone: over either form one of
the two arms of "first" is not reached.) -/
theorem seatedClaims_quiet {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)}
    {b : Block S Claim} (h : Kinds.Head.seatedClaims W l before = some b) : Whole Quiet b := by
  unfold Kinds.Head.seatedClaims at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  refine whole_sub (blockClaims_quiet h0) (fun s rs gs s' k => ?_) (fun _ hx => hx) rfl
  first
    | exact k
    | (unfold Kinds.Head.tested at k
       dsimp only at k
       split at k
       · exact k
       · cases k)

/-! ## K8 -/

theorem k8Set_quiet (s : S) (q : TailClaims.K8Part) : Quiet s (TailClaims.k8PartP.set s q) := by
  show Quiet s ((s.putTl q.tl).putFork q.F)
  exact quiet_trans _ _ _ (quiet_putTl s _) (quiet_putFork _ _)

theorem atRecord_quiet {α : Type} (f : TailClaims.K8Part → Except String (α × TailClaims.K8Part))
    {s : S} {y : α × S} (h : K8.atRecord f s = .ok y) : Quiet s y.2 := by
  unfold K8.atRecord at h
  split at h
  · cases h
  · obtain ⟨x, -, rfl⟩ := Keeps.emap_ok h
    exact k8Set_quiet s _

theorem k8Whole_quiet (p : K8.ParW) : Whole Quiet (K8.whole p) := by
  refine ⟨(k8_quiet (Cl := Claim) p.toPar).1, fun c hc n s y h => ?_, fun c hc s s' h => ?_⟩
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    exact atRecord_quiet _ h
  · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hc
    obtain ⟨y, e, rfl⟩ := Keeps.emap_ok h
    exact atRecord_quiet _ e

/-! ## K1 -/

theorem laterAt_rec (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    Whole (RecRel cs sh) (K1.laterAt (Cl := Cl) q gp link piece moment arrays) :=
  commitAtS_rec _ link moment arrays

/-! ## K11 -/

open Johnson.Desc.First.ForkMerge in
theorem headMerge11_quiet (P : HeadMergeP) : Whole Quiet (headClaimMergeKind P) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · have h' : headMergeDecide P s rs = .ok s' := h
    unfold headMergeDecide at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨⟨wo, F, t⟩, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨_, -, h'⟩ := bindE h'
      cases h'
      refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
        by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun _ => rfl,
        fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
    · cases h'
  · obtain rfl := List.mem_singleton.1 hc
    have h' : headMergeClaim n s = .ok y := h
    unfold headMergeClaim at h'
    split at h'
    · rename_i a ha
      obtain ⟨_, -, h'⟩ := bindE h'
      obtain ⟨x, -, h'⟩ := bindE h'
      cases h'
      refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
        by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
    · cases h'

/-! ## The links' frames -/

/-- The end of the head's link is the frame's one clearing, at the head's own readings. -/
theorem tailHead_rec (X : Johnson.Desc.First.Walk.LinkPub) (lay : WsLay) (lin : Params.LinShape) :
    Fn (RecRel cs sh) (Close.tailHead X lay lin) := clearWith_rec _ _ _ _

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- **Every row of the frame, link by link.** -/
theorem framesOf_rec {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} (h : framesOf built first W = .ok fs) : ∀ f ∈ fs,
    Fn (RecRel cs sh) f.lay ∧ Fn (RecRel cs sh) f.opened ∧ Fn (RecRel cs sh) f.clear := by
  intro f hf
  unfold framesOf at h
  obtain ⟨l, -, e⟩ := mem_of_mapM_ok _ _ _ h f hf
  dsimp only at e
  split at e
  · split at e
    · cases e
    · cases e
      exact ⟨layFront_rec l, fun s t k R => by cases k; exact R, tailHead_rec _ _ _⟩
  · split at e
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_rec 0, openLayZero_rec _ _ _, clearWith_rec _ _ _ _⟩
    · split at e
      · cases e
      · cases e
        exact ⟨layFront_rec l, openAtt_rec _, clearWith_rec _ _ _ _⟩
      · cases e
        exact ⟨layFront_rec l, openLay_rec _, clearWith_rec _ _ _ _⟩

#print axioms theStated_quiet
#print axioms blockAtC_quiet
#print axioms k5AtN_quiet
#print axioms seatedClaims_quiet
#print axioms k8Whole_quiet
#print axioms laterAt_rec
#print axioms headMerge11_quiet
#print axioms framesOf_rec

end Meaning.K2
