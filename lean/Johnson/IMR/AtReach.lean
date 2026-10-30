-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/AtReach.lean: theorems along the first chain's fold, stated at «reached».


WHY. The soundness proof's chain gains, at each border between two sub-protocols, the condition «reached»: the verifier's state at the border is one that the chain's own sub-protocols hand on from the start at the statement's own public part (the inductive Reach, Johnson/Top/H0/Walk/Reach.lean). Facts on the verifier's state are to be taken from that condition, a field a fact, in the structure FoldFacts (Johnson/Desc/First/FoldFacts.lean; a form of it was held against this file by program). This file gives twelve of its fields whole, at every border, each statement ending in the field's own type (section 7). WHAT STANDS IN FRONT OF THAT END IS SHOWN NOWHERE HERE: the opening O and hRch at all twelve · hp, the tests on the plan, at eleven (not at ownIs_field) · the goals' scope hS, hR at ten (not at bookInOrder_field | bookFits_field). Without hp the same facts are given «in front» (see WORDS; sections 1, 2, 5). THE TIE TO THE STRUCTURE IS BY TEXT: FoldFacts.lean is not imported, so Lean has not checked that a _field's type is its field's; a program compared the texts, and section 7's head pins the names that both texts use to their full names.

THE FAMILY. Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s): k: the border's number, from 0, in the flat list of the first chain of the IOP as written in Lean; z : ProofFile.InstPub: the statement's own public part, a free letter; s: the verifier's state. The letters Z, c and the rest are those of IM.Open (Johnson/IMR/SeatOpen.lean), which names each part of what ProofFile.onlineDescription returns. rch_is: it is Reach 0 F.first.blocksInOrder F.start₁ at F as O.desc spells it (what rchAt_raw, Johnson/Top/H0/Walk/ReachAt.lean, concludes); rch_narrow: RchAt (that same file), which steps by the wrapped sub-protocols, gives it, at that same F written out.

WORDS. A mark: S.failed ≠ none: a deferred rejection that the state carries. The blank state: S.blank, which ProofFile.startS hands out where z's request fails its test; it bears a mark. z's request's test: (Z.s₀.withReq (Verify.words32 z.request)).reqOk …, the test on the instance that reads nothing of the reply. In front: k ≤ (frontOf c).length: at or before the border just before the first sub-protocol behind the last link (in scope the borders 0 to at least 345, of 0 to 358: ownIs_reached24's proof shows 345 ≤ (frontOf c).length). hp: ∀ b ∈ c.blocksInOrder, b.planOk = true: each entry of the flat list passes its test on the plan, a Bool that reads no state and no reply; as Chain.blocksInOrder lays the entries, at the first sub-protocol, at those behind the last link and at the seal that Bool also asks Block.hasNoClaimsAndNothingAfter. The fence: the fields' own premise «no mark at the state». A premise is spent where the proof uses it. A free letter: a variable that the statement binds with no condition.

HOW. In sections 1, 2, 4 and 6 each proof takes a fold off Reach.fold (the bridge of Johnson/Top/H0/Walk/Reach.lean) and calls one of Johnson/IMR/'s theorems along the fold. The fold's rounds and columns are bound inside «there are» and end inside the proof: no conclusion names them. Sections 3, 5 and 7 chain such steps.

THE PREMISES THAT A FIELD DOES NOT HAVE. (a) EITHER «in front» (sections 1, 2, 5; not at ownIs_* and xk_reached) OR hp, the tests on the plan (sections 6, 7). (b) RecAll and what follows from it hold where z's request has passed its test. Three forms: «_reached_of»: the test as a premise, at every o, no scope, from border 0 · «_reached»: in the goals' scope, from border 2 on, where «link 0: laid» has accepted (start_real) · «_noMark» and section 5: in scope, «no mark at the state», which is the fields' own fence · «_all_of» | «_all»: the first and the third form at every border, under hp (section 6).

  fold_cut_le             a fold over the first k returns: so does the fold over the first j ≤ k, at the same rounds and columns
  rch_is · rch_narrow  Reach over the file's own first chain and start is this file's family · the narrower family RchAt gives it
  planOk_of_run        hp follows from one accepting run of the file's decision
  recAll_reached_of | recAll_reached | recAll_noMark     RecAll: the codes, and the shape, groups and carried rows of every copy of the frame that the state holds, are the plan's
  bookInOrder_reached  Book.NumberedC 0: as many roots as commitment trees in the state's list; the tree at place j bears the number j and the source «own j»
  bookFits_reached · bookHas_reached   each oracle message's place names a tree and a part that hold it · as many places as oracle messages
  bookFitsB_of · atFirstBook_reached · atFirstFits_reached   the same two in the door's own Bools (Johnson/Desc/K12/Door/DoorBools.lean)
  rootsCount_reached   the count of roots is the declared rounds' count: UNDER the tests on the plan of the sub-protocols in front of the border, as a premise
  ownInv_reached_of · both_reached · shapeOk_reached   the invariant behind the lookups' tie · with RecAll · the public test on shapes
  rowsLayout_reached_of | _reached · liveIs_reached_of | _reached | _noMark   both copies of the rows' layout · the lookups' own Bool liveIsB at sentAt Z
  reqOk_reached · start_of_early · reqOk_of_noMark   when z's request has passed its test
  ownIs_reached | ownIs_reached24 | ownIs_k3_reached | ownIs_atK3   the lookups' tie OwnIs (sentAt Z) l, with no instance x and no test on it
  walkGives_reached | 0 | 24 · midRoots_reached | 24   section 3: several states of one fold
  xk_reached           the table's fixed Bools at border k: UNDER IM.SharesS, which is not paid
  codes_inFront · shape_inFront · layout_inFront · liveShape_inFront · liveLayout_inFront · groups_inFront · liveGroups_inFront · frameShape_inFront · frameGroups_inFront   nine fields' facts, letter for letter, in front
  recAll_all_of | recAll_all · ownInv_all_of · rowsLayout_all · atFirstBook_all · atFirstFits_all   section 6: the same at EVERY border, under hp
  bookInOrder_field · bookFits_field · codes_field · shape_field · layout_field · liveShape_field · liveLayout_field · groups_field · liveGroups_field · frameShape_field · frameGroups_field · ownIs_field   section 7: twelve fields whole, general in Rch and at_
  k3Fit · k3_numbers · k3Bent · k3_bent_fails · k3_number_at   a closed test on the written list of places, by the kernel, with a negative test

CALLED, NOT TYPED: Reach.fold · reach_of_fold · reach_raw (Johnson/Top/H0/Walk/Reach.lean) · open_fold_all (Johnson/IMR/OpenFlat.lean) · seatBack_rec · seatBack_own (Johnson/LTPileR/BackSeats.lean) · seatKeeps_sentence · seatBack_sentence · recv_ordered · ordered_same · k12_ordered · empty_ordered · recvP_fits · fits_same · k12_fits · open_fold (Johnson/IMR/OpenWalk.lean) · start_real (Johnson/IMR/ListsEnds.lean) · recAll_startS · seatKeeps_rec · k2Share · own_startS · seatKeeps_own · arrOk_at · letters_arr · own_rows · open_fits · open_has · seatKeeps_front · numberedP_iff · start_empty · ctx_at | ctx_at24 · ownIs_of_ctx · draw_in_front · flatIx_le · walkGives_at | _at0 | _at24 (these in Johnson/IMR/, own_rows in Johnson/Goal/Meaning/) · mid_roots | mid_roots24 (Johnson/IMR/MidRoots.lean) · roots_at_cut_paid (Johnson/IMR/RootsSeat.lean) · frame_of · flatIx_scope · x_reached · front_of · placesW (Johnson/IMR/: FrameSeat.lean · FlatScope.lean · GrownStart.lean · FrontSeat.lean · WrittenList.lean) · bookStep_iff (Johnson/Desc/Sound/BookInOrder.lean) · Keeps.foldBlocks_split.

What is not claimed. Behind the last link (the last sub-protocols, the proximity test's finish, the seal) nothing without hp, but for xk_reached, which goes as far as its unpaid premise. No test on the plan is shown: hp is a premise. The structure FoldFacts is not imported and no value of it is made: fourteen of its fields are not touched here. hRch at RchAt F (Johnson/Top/H0/Walk/ReachAt.lean) is stated by no theorem here: its spender replaces F through O.desc, takes at_ := Prod.fst, and calls rch_narrow. That an accepting run exists at the release's own values, and that hS, hR and O can be met there together, is not shown here. No soundness.
-/
import Johnson.IMR.WalkGivesAt
import Johnson.IMR.OwnAtHead
import Johnson.IMR.MidRoots
import Johnson.IMR.RootsSeat
import Johnson.IMR.GrownStart
import Johnson.IMR.FrontSeat
import Johnson.IMR.PlacesScope
import Johnson.IMR.OpenFlat
import Johnson.IMR.BookPaid
import Johnson.IMR.BookFitsPaid
import Johnson.LTPileR.BackSeats
import Johnson.Desc.RunLaws
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.Sound.BookInOrder
import Johnson.Top.H0.Walk.Reach
import Johnson.Desc.First.Look.K3LiveIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K1.RelCore (coreS)
open VerifiableInference.Desc.Book (BookFits)
open VerifiableInference.Desc.First.Look (liveIsB liveIsB_iff)
open ProofFile (Cl)
open VerifiableInference.Desc.First.Look (OwnIs)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold reach_raw)
open Johnson.G.OfPlan (rootsOf)
open H2K.First (declOf)

variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- Where the fold over the first k sub-protocols returns, so does the fold over the first j ≤ k, at the same rounds and columns. -/
theorem fold_cut_le {ft j k : Nat} (hjk : j ≤ k) {bs : List (Block S Cl)} {s : S} {rs : List Fmt.RoundView}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    {r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn}
    (h : foldBlocks ft (bs.take k) s rs cols = .ok r) :
    ∃ t R C, foldBlocks ft (bs.take j) s rs cols = .ok (t, R, C) := by
  have e : bs.take j ++ (bs.take k).drop j = bs.take k := by
    have q := List.take_append_drop j (bs.take k)
    rwa [List.take_take, Nat.min_eq_left hjk] at q
  rw [← e] at h
  obtain ⟨t, R, C, g, -⟩ := Keeps.foldBlocks_split ft _ _ _ _ _ _ h
  exact ⟨t, R, C, g⟩

/-- **Reach over the file's own first chain and start is this file's family**: at the file as IM.Open.desc spells it, the first chain is c and the start is ProofFile.startS Z. (The left side is what rchAt_raw, Johnson/Top/H0/Walk/ReachAt.lean, concludes.) -/
theorem rch_is (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) (k : ℕ) (a : ProofFile.InstPub × S) : Reach 0 (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).first.blocksInOrder (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).start₁ k a ↔ Reach 0 c.blocksInOrder (ProofFile.startS Z) k a :=
  Iff.rfl

/-- **And the narrower family**, which steps by the wrapped sub-protocols (Johnson/Top/H0/Walk/ReachAt.lean: RchAt F k a := Reach 0 (F.first.blocksInOrder.map below) F.start₁ k a.1), gives this file's: by reach_raw (Johnson/Top/H0/Walk/Reach.lean). So what is shown here of a reached state holds of a state reached in the narrower sense. -/
theorem rch_narrow (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S Cl) (k : ℕ) (a : ProofFile.InstPub × S) (h : Reach 0 ((ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).first.blocksInOrder.map VerifiableInference.Desc.Sound.below) (ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c).start₁ k a) : Reach 0 c.blocksInOrder (ProofFile.startS Z) k a :=
  reach_raw h

/-! ## 1 At every o, with no scope -/

/-- **The codes and every copy of the frame that the verifier's state holds are the plan's**, in front, from border 0 on, where z's request passes its test. -/
theorem recAll_reached_of (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) (hk : k ≤ (frontOf c).length) : RecAll Z.first.codes Z.first.shape s := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_fold (seatKeeps_rec (k2Share _ _)) O trivial (fun _ _ _ => trivial) hk f
    (recAll_startS O.pub hq)

/-- **The state's list of commitment trees is in order**: as many roots as trees; the tree at place j bears the number j and the source «own j». -/
theorem bookInOrder_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) : Book.NumberedC 0 (coreS s) := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have K3 : SeatKeeps (PR numberedP) := seatKeeps_front
    (fun d d' sent ids e k => Book.recvP_numbered 0 d d' sent ids e k) numbered_sameNumbers
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  refine (numberedP_iff (coreS s)).2 (open_fold K3 O trivial (fun _ _ _ => trivial) hk f ?_)
  show numberedP (ProofFile.startS Z z).book (ProofFile.startS Z z).roots
  rw [(start_empty hZ z).1, (start_empty hZ z).2]
  exact empty_numbered

/-- Each oracle message's place names a tree and a part that hold it. -/
theorem bookFits_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) : BookFits s.book := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_fits O hk f

/-- As many places in the list of commitment trees as oracle messages. -/
theorem bookHas_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) : s.book.place.size = s.st.oracles.size := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_has O hk f

/-- The test with code says what BookFits says: one way. -/
theorem bookFitsB_of {T : TreeBook} (h : BookFits T) : Sound.bookFitsB T = true := by
  unfold Sound.bookFitsB
  rw [List.all_eq_true]
  intro i _
  cases hq : T.place[i]? with
  | none => rfl
  | some q =>
    obtain ⟨t, h1, h2⟩ := h i q hq
    simp only [h1]
    exact decide_eq_true h2

/-- **The field «K12.bookInOrder», in the door's own Bool** (Johnson/Desc/K12/Door/DoorBools.lean). -/
theorem atFirstBook_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) : K12.Door.atFirstBook 0 s = true := by
  have N := bookInOrder_reached O h hk
  exact (VerifiableInference.Desc.Sound.bookStep_iff 0 s.book s.roots).2
    ⟨N.1, fun j t ht => (N.2 j t ht).1⟩

/-- **The field «K12.bookFits», in the door's own Bool.** -/
theorem atFirstFits_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) : K12.Door.atFirstFits s = true :=
  bookFitsB_of (bookFits_reached O h hk)

/-- **The count of roots is the declared rounds' count**, under the tests on the plan of the sub-protocols in front of the border. -/
theorem rootsCount_reached (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hk : k ≤ (frontOf c).length) (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) : s.roots = rootsOf (declOf (c.blocksInOrder.take k)) := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have q := Meaning.Carry.roots_at_cut_paid O k hk hp 0 _ rs cols _ f
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  rw [(start_empty hZ z).2, Nat.zero_add] at q
  exact q

/-- The invariant behind the lookups' tie, from border 0 on, where z's request passes its test. -/
theorem ownInv_reached_of (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) (hk : k ≤ (frontOf c).length) : OwnInv (arrOf Z) Z.first.layout s := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_fold (seatKeeps_own (A := arrOf Z) (lay := Z.first.layout)) O (arrOk_at Z)
    (fun l Q hQ => letters_arr (IM.base_made O.made).2.2.1 hQ) hk f (own_startS O.pub hq)

/-- **Both copies of the rows' layout that the calls can read are the plan's**, from border 0 on, where z's request passes its test. -/
theorem rowsLayout_reached_of (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) (hk : k ≤ (frontOf c).length) : s.check.rows.layout = Z.first.layout ∧ s.live.rows.layout = Z.first.layout := by
  exact own_rows (ownInv_reached_of O h hq hk)

/-- **The lookups' own Bool on the copy in use.** -/
theorem liveIs_reached_of (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) (hk : k ≤ (frontOf c).length) : liveIsB (sentAt Z) s = true :=
  (liveIsB_iff _ _).2 ⟨(recAll_reached_of O h hq hk).live.shape, (rowsLayout_reached_of O h hq hk).2⟩

/-! ## 2 In the goals' scope, from border 2 on -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- **From border 2 on z's request has passed its test**: «link 0: laid», the second sub-protocol of the flat list, rejects the blank state. -/
theorem reqOk_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (h2 : 2 ≤ k) : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  obtain ⟨t, R, C, g⟩ := fold_cut_le h2 f
  exact start_real hS hR O g

theorem recAll_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (h2 : 2 ≤ k) (hk : k ≤ (frontOf c).length) : RecAll Z.first.codes Z.first.shape s :=
  recAll_reached_of O h (reqOk_reached hS hR O h h2) hk

theorem rowsLayout_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (h2 : 2 ≤ k) (hk : k ≤ (frontOf c).length) : s.check.rows.layout = Z.first.layout ∧ s.live.rows.layout = Z.first.layout :=
  rowsLayout_reached_of O h (reqOk_reached hS hR O h h2) hk

theorem liveIs_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (h2 : 2 ≤ k) (hk : k ≤ (frontOf c).length) : liveIsB (sentAt Z) s = true :=
  liveIs_reached_of O h (reqOk_reached hS hR O h h2) hk

/-- RecAll and the invariant together. -/
theorem both_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (h2 : 2 ≤ k) (hk : k ≤ (frontOf c).length) : BothAt Z s :=
  ⟨recAll_reached hS hR O h h2 hk, ownInv_reached_of O h (reqOk_reached hS hR O h h2) hk⟩

/-- The shape of the copy of the frame in use passes the public test on shapes. -/
theorem shapeOk_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (h2 : 2 ≤ k) (hk : k ≤ (frontOf c).length) : reqShapeOk s.live.frame.shape = true := by
  have Rr := recAll_reached hS hR O h h2 hk
  rw [Rr.live.shape]
  have q := Rr.ok
  simp only [reqOk, Bool.and_eq_true] at q
  exact q.1

/-- **The lookups' tie at the place (l, i)**, l < 24, i from 1 to 6: at the border in front of link l's hearing sub-protocol number i, counted from 0 (Lk.hear[i]). No instance x and no test on it is asked: z is a free letter. -/
theorem ownIs_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l i : ℕ} (hl : l < 24) (h1 : 1 ≤ i) (h6 : i ≤ 6) {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 2 + i) (z, s)) : OwnIs (sentAt Z) l s := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
  have hk : 14 * l + 2 + (n + 1) ≤ (frontOf c).length := by
    have q := draw_in_front hS hR O (l := l) (i := n + 1) (by omega) (by omega)
    omega
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have f' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3 + n)) (ProofFile.startS Z z) rs cols = .ok (s, [], []) := by
    rwa [show 14 * l + 3 + n = 14 * l + 2 + (n + 1) by omega]
  obtain ⟨r, ar, k⟩ := ctx_at hS hR O hl n (by omega) s [] [] f'
  exact ownIs_of_ctx (both_reached hS hR O h (by omega) hk) k (by decide)

/-- **The same at the head's link**, i from 2 to 7. -/
theorem ownIs_reached24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {i : ℕ} (h2 : 2 ≤ i) (h7 : i ≤ 7) {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (338 + i) (z, s)) : OwnIs (sentAt Z) 24 s := by
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := ⟨i - 2, by omega⟩
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have f' : foldBlocks 0 (c.blocksInOrder.take (340 + n)) (ProofFile.startS Z z) rs cols = .ok (s, [], []) := by
    rwa [show 340 + n = 338 + (n + 2) by omega]
  obtain ⟨r, ar, k⟩ := ctx_at24 hS hR O n (by omega) s [] [] f'
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, -, -, -, -, eL, hlen, -⟩ := hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  obtain ⟨b, e⟩ : ∃ b, Lk.hear[n + 2]? = some b :=
    ⟨_, List.getElem?_eq_getElem (by omega : n + 2 < Lk.hear.length)⟩
  have hk : 338 + (n + 2) ≤ (frontOf c).length := by
    have q := flatIx_le (chainBy_noFront O.chain) eL e
    rw [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) (n + 2)] at q
    omega
  exact ownIs_of_ctx (both_reached hS hR O h (by omega) hk) k (by decide)

/-- **The tie at kind K3's own two places of every link.** -/
theorem ownIs_k3_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25) (digits : Bool) {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 2 + IM.k3Ix l digits) (z, s)) : OwnIs (sentAt Z) l s := by
  have ix : IM.k3Ix l digits = (if digits = true then 6 else 1) + (if l = 24 then 1 else 0) := rfl
  by_cases h24 : l = 24
  · subst h24
    rw [ix, if_pos rfl] at h
    cases digits
    · exact ownIs_reached24 hS hR O (i := 2) (by omega) (by omega) h
    · exact ownIs_reached24 hS hR O (i := 7) (by omega) (by omega) h
  · rw [ix, if_neg h24] at h
    cases digits
    · exact ownIs_reached hS hR O (i := 1) (by omega) (by omega) (by omega) h
    · exact ownIs_reached hS hR O (i := 6) (by omega) (by omega) (by omega) h

/-! ## 3 Theorems that speak of several states of one fold

Each takes «reached» at the LAST of its borders, at the spender's own state, and says: THERE ARE states t₀, t₁, reached at the earlier borders at the same z, of which the conclusion holds. HOW LITTLE THAT GIVES: a spender that holds its OWN reached state at an earlier border learns nothing of it from these alone: the witnesses need not be that state, and that they lie on one fold with the last state is a fact of the proof which no statement hands out. The witnesses enter the conclusions through their counts of roots alone: so the one road to the spender's own earlier state is a fact that fixes the count of roots by the border: here rootsCount_reached, under its premise on the plan. -/

/-- **WalkSeven's seven conjuncts at the links 1 to 23**, at the border in front of hearing sub-protocol number 4, counted from 0; t₀ and t₁ are witnesses (this section's head). -/
theorem walkGives_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h1 : 1 ≤ l) (h24 : l < 24) {z : ProofFile.InstPub} {t₄ : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 6) (z, t₄)) : ∃ t₀ t₁ : S, Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 2) (z, t₀) ∧ Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 3) (z, t₁) ∧ WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧ t₁.roots ≤ t₄.roots := by
  obtain ⟨hl, rs, cols, f₄⟩ := h.fold
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut_le (j := 14 * l + 2) (by omega) f₄
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut_le (j := 14 * l + 3) (by omega) f₄
  exact ⟨t₀, t₁, reach_of_fold _ (by omega) _ _ _ _ _ f₀, reach_of_fold _ (by omega) _ _ _ _ _ f₁,
    walkGives_at hS hR O l h1 h24 z rs cols t₀ t₁ t₄ R₀ R₁ [] C₀ C₁ [] f₀ f₁ f₄⟩

/-- **At link 0.** -/
theorem walkGives_reached0 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {t₄ : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 6 (z, t₄)) : ∃ t₀ t₁ : S, Reach 0 c.blocksInOrder (ProofFile.startS Z) 2 (z, t₀) ∧ Reach 0 c.blocksInOrder (ProofFile.startS Z) 3 (z, t₁) ∧ WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧ t₁.roots ≤ t₄.roots := by
  obtain ⟨hl, rs, cols, f₄⟩ := h.fold
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut_le (j := 2) (by omega) f₄
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut_le (j := 3) (by omega) f₄
  exact ⟨t₀, t₁, reach_of_fold _ (by omega) _ _ _ _ _ f₀, reach_of_fold _ (by omega) _ _ _ _ _ f₁,
    walkGives_at0 hS hR O z rs cols t₀ t₁ t₄ R₀ R₁ [] C₀ C₁ [] f₀ f₁ f₄⟩

/-- **At the head's link.** -/
theorem walkGives_reached24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {t₄ : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 343 (z, t₄)) : ∃ t₀ t₁ : S, Reach 0 c.blocksInOrder (ProofFile.startS Z) 339 (z, t₀) ∧ Reach 0 c.blocksInOrder (ProofFile.startS Z) 340 (z, t₁) ∧ WalkSeven t₀.roots t₁.roots t₄.roots t₄ ∧ t₀.roots ≤ t₁.roots ∧ t₁.roots ≤ t₄.roots := by
  obtain ⟨hl, rs, cols, f₄⟩ := h.fold
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_cut_le (j := 339) (by omega) f₄
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut_le (j := 340) (by omega) f₄
  exact ⟨t₀, t₁, reach_of_fold _ (by omega) _ _ _ _ _ f₀, reach_of_fold _ (by omega) _ _ _ _ _ f₁,
    walkGives_at24 hS hR O z rs cols t₀ t₁ t₄ R₀ R₁ [] C₀ C₁ [] f₀ f₁ f₄⟩

/-- **There is a state reached at border 14 l + 3 with t₃'s count of roots**, t₃ reached at border 14 l + 5, l < 24. Of another state reached at 14 l + 3 it says nothing (this section's head). -/
theorem midRoots_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h24 : l < 24) {z : ProofFile.InstPub} {t₃ : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 5) (z, t₃)) : ∃ t₁ : S, Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 2 + 1) (z, t₁) ∧ t₃.roots = t₁.roots := by
  obtain ⟨hl, rs, cols, f₃⟩ := h.fold
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut_le (j := 14 * l + 2 + 1) (by omega) f₃
  exact ⟨t₁, reach_of_fold _ (by omega) _ _ _ _ _ f₁, mid_roots hS hR O h24 f₁ f₃⟩

/-- The like at the head's link: the borders 340 and 342. -/
theorem midRoots_reached24 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {z : ProofFile.InstPub} {t₃ : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) 342 (z, t₃)) : ∃ t₁ : S, Reach 0 c.blocksInOrder (ProofFile.startS Z) (339 + 1) (z, t₁) ∧ t₃.roots = t₁.roots := by
  obtain ⟨hl, rs, cols, f₃⟩ := h.fold
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_cut_le (j := 339 + 1) (by omega) f₃
  exact ⟨t₁, reach_of_fold _ (by omega) _ _ _ _ _ f₁, mid_roots24 hS hR O f₁ f₃⟩

/-! ## 4 The table's fixed Bools at a border: under IM.SharesS, which is not paid -/

/-- **«Reached» and no mark give IM.XK at border k**: x_reached (Johnson/IMR/GrownStart.lean), at Reach. ITS PREMISE Sh : IM.SharesS … IS NOT PAID. -/
theorem xk_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {N : Numbers} {E : ℕ → S → Bool} (Sh : IM.SharesS N E 0 Z Bs.G₀ c) {z : ProofFile.InstPub} (hT : N.treesAt (some frontPlace) = 0) (hM : N.msgsAt (some frontPlace) = 0) (hE : (ProofFile.startS Z z).failed = none → E 0 (ProofFile.startS Z z) = true) {k : ℕ} (hk : k ≤ 358) {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) : IM.XK N IM.linksW IM.placesW E k s = true := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact IM.x_reached hS hR O Sh z hT hM hE hk f hu

/-! ## 5 Nine fields' facts of the structure FoldFacts, in front, fenced as the fields are: «no mark at the state»; and the field ownIs

Johnson/Desc/First/FoldFacts.lean (another form of it): each field reads «∀ k a, Rch k a → (at_
a).2.failed = none → ‹the fact›». Here: Rch := Reach 0 c.blocksInOrder (ProofFile.startS Z), the fact's text letter
for letter at d.ft := 0 and d.sent := sentAt Z, AND ONE PREMISE MORE, WHICH THE FIELD DOES NOT HAVE:
k ≤ (frontOf c).length. SO NONE OF THE NINE IS THE FIELD: each is the field's fact in front (the
fields whole: section 7). (bookInOrder and bookFits likewise: atFirstBook_reached |
atFirstFits_reached, section 1.) The structure itself is not imported. -/

/-- At the borders 0 and 1 the state is the start's: the first sub-protocol of the chain hands the state on as it is (front_of, Johnson/IMR/FrontSeat.lean). At every o. -/
theorem start_of_early (O : IM.Open o pol lay KL F Z Bs base c A B) {k : ℕ} (hk1 : k ≤ 1) {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) : s = ProofFile.startS Z z := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have fz : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z z) rs cols = .ok (ProofFile.startS Z z, rs, cols) := rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hk1 with rfl | rfl
  · have f' : foldBlocks 0 (c.blocksInOrder.take 0) (ProofFile.startS Z z) rs cols = .ok (s, [], []) := f
    rw [fz] at f'
    exact (congrArg Prod.fst (Except.ok.inj f')).symm
  · obtain ⟨b, hb, -, -, -, -, hd⟩ := IM.front_of O
    have f' : foldBlocks 0 (c.blocksInOrder.take (0 + 1)) (ProofFile.startS Z z) rs cols = .ok (s, [], []) := f
    obtain ⟨rs', gs', d⟩ := fold_next hb fz f'
    exact (hd _ _ _ _).1 d

/-- **The fence shuts the blank start out**: at a reached state without a mark z's request has passed the test that reads no reply. At the borders 0 and 1 because the blank state bears a mark by its make; from border 2 on by reqOk_reached, where the fence is not spent. -/
theorem reqOk_of_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true := by
  by_cases h2 : 2 ≤ k
  · exact reqOk_reached hS hR O h h2
  · have es := start_of_early O (by omega) h
    by_contra hq
    have eb : ProofFile.startS Z z = S.blank := by
      unfold ProofFile.startS
      dsimp only
      rw [if_neg hq]
    rw [es, eb] at hu
    exact absurd hu (by decide)

/-- RecAll at every reached state without a mark, in front, from border 0 on. -/
theorem recAll_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : RecAll Z.first.codes Z.first.shape s :=
  recAll_reached_of O h (reqOk_of_noMark hS hR O h hu) hk

/-- The lookups' own Bool at every reached state without a mark, in front. -/
theorem liveIs_noMark (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : liveIsB (sentAt Z) s = true :=
  liveIs_reached_of O h (reqOk_of_noMark hS hR O h hu) hk

/-- **Field codes's fact, in front.** -/
theorem codes_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.st.codes = (sentAt Z).codes :=
  (recAll_noMark hS hR O h hu hk).codes

/-- **Field shape's fact, in front.** -/
theorem shape_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.check.frame.shape = (sentAt Z).shape :=
  (recAll_noMark hS hR O h hu hk).walk.shape

/-- **Field layout's fact, in front.** -/
theorem layout_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.check.rows.layout = (sentAt Z).layout :=
  (rowsLayout_reached_of O h (reqOk_of_noMark hS hR O h hu) hk).1

/-- **Field liveShape's fact, in front.** -/
theorem liveShape_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.live.frame.shape = (sentAt Z).shape :=
  (recAll_noMark hS hR O h hu hk).live.shape

/-- **Field liveLayout's fact, in front.** -/
theorem liveLayout_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.live.rows.layout = (sentAt Z).layout :=
  (rowsLayout_reached_of O h (reqOk_of_noMark hS hR O h hu) hk).2

/-- **Field groups's fact, in front.** -/
theorem groups_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.check.frame.groups = reqGroups s.check.frame.shape :=
  by rw [(recAll_noMark hS hR O h hu hk).walk.shape]; exact (recAll_noMark hS hR O h hu hk).walk.groups

/-- **Field liveGroups's fact, in front.** -/
theorem liveGroups_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.live.frame.groups = reqGroups s.live.frame.shape :=
  by rw [(recAll_noMark hS hR O h hu hk).live.shape]; exact (recAll_noMark hS hR O h hu hk).live.groups

/-- **Field frameShape's fact, in front**: the frame that the calls turn, S.frame: in the output head's front a third copy, which RecAll holds too (RecAll.turn). THE FINISH, where S.frame is a third copy as well, LIES BEHIND THE LAST LINK: NOT COVERED HERE (frameShape_field covers it, under hp). -/
theorem frameShape_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.frame.shape = (sentAt Z).shape :=
  (recAll_noMark hS hR O h hu hk).turn.shape

/-- **Field frameGroups's fact, in front.** -/
theorem frameGroups_inFront (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) (hk : k ≤ (frontOf c).length) : s.frame.groups = reqGroups s.frame.shape :=
  by rw [(recAll_noMark hS hR O h hu hk).turn.shape]; exact (recAll_noMark hS hR O h hu hk).turn.groups

/-- On the written list of the 358 places: a place of kind K3 in link l stands at one of the two numbers at which ownIs_k3_reached speaks. A test with code. -/
def k3Fit (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | some p =>
      (p.kind != KindName.K3) ||
        (match p.link with
         | some l => decide (l < 25) &&
            (k == 14 * l + 2 + IM.k3Ix l false || k == 14 * l + 2 + IM.k3Ix l true)
         | none => true)
    | none => true

set_option maxRecDepth 1000000 in
theorem k3_numbers : k3Fit IM.placesW = true := by decide +kernel

/-- A negative test: the written list with its first place replaced by a place of kind K3 in link 0: number 0 is neither of link 0's two numbers. (It tries neither the clause l < 25 nor a place of kind K3 with no link, which k3Fit lets pass: the field asks p.link = some l.) -/
def k3Bent : List Place := { chain := 1, link := some 0, piece := 1, kind := .K3 } :: IM.placesW.drop 1

set_option maxRecDepth 1000000 in
theorem k3_bent_fails : k3Fit k3Bent = false := by decide +kernel

theorem k3_number_at {k l : ℕ} {p : Place} (hpl : IM.placesW[k]? = some p) (hK : p.kind = .K3) (hl : p.link = some l) : l < 25 ∧ ∃ d : Bool, k = 14 * l + 2 + IM.k3Ix l d := by
  have q := k3_numbers
  unfold k3Fit at q
  rw [List.all_eq_true] at q
  have q' := q k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hpl).1)
  simp only [hpl, hK, hl, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, beq_iff_eq] at q'
  exact ⟨q'.1, q'.2.elim (fun e => ⟨false, e⟩) fun e => ⟨true, e⟩⟩

/-- **Field ownIs, at every border**, at ps := the written list of places IM.placesW, which in scope is the flat list's own (places_scope, Johnson/IMR/PlacesScope.lean; whoever makes a value of FoldFacts must take the same list for groupIs and room). No bound on k and no fence is asked: kind K3's places all stand in front. -/
theorem ownIs_atK3 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {z : ProofFile.InstPub} {s : S} {p : Place} {l : ℕ} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hpl : IM.placesW[k]? = some p) (hK : p.kind = .K3) (hl : p.link = some l) : OwnIs (sentAt Z) l s := by
  obtain ⟨h25, d, rfl⟩ := k3_number_at hpl hK hl
  exact ownIs_k3_reached hS hR O h25 d h

end

/-! ## 6 At EVERY border, under the tests on the plan

hp : ∀ b ∈ c.blocksInOrder, b.planOk = true (see WORDS in the head). With hp the bound k ≤ (frontOf c).length is not needed. The walk behind the last link: Johnson/IMR/OpenFlat.lean (open_fold_all), over SeatBack at each relation: at RecRel and OwnRel Johnson/LTPileR/BackSeats.lean (seatBack_rec | seatBack_own); at the two sentences on the list of commitment trees seatBack_sentence (Johnson/IMR/BookSeat.lean). hp IS A PREMISE. planOk_of_run turns it into another: the file's decision accepts once. -/

/-- **hp follows from one accepting run of the file's decision**, at whatever instance and views: the tests on the plan read nothing of the run (the library's FileDescription.planOk_parts_of_run). THAT SUCH A RUN EXISTS at the release's own values is not shown here. -/
theorem planOk_of_run (O : IM.Open o pol lay KL F Z Bs base c A B) {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
  have PP := FileDescription.planOk_parts_of_run hr
  have eF := O.desc
  subst eF
  exact fun b hb => (PP.blocks₁ b hb).1

/-- RecAll at every border, where z's request passes its test. At every o. -/
theorem recAll_all_of (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) : RecAll Z.first.codes Z.first.shape s := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_fold_all (seatKeeps_rec (k2Share _ _)) (seatBack_rec _ _) O trivial
    (fun _ _ _ => trivial) hp k f (recAll_startS O.pub hq)

/-- The invariant behind the lookups' tie at every border, where z's request passes its test. At every o. -/
theorem ownInv_all_of (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hq : (Z.s₀.withReq (Verify.words32 z.request)).reqOk Z.p.X.T Z.p.X.P.h.V = true) : OwnInv (arrOf Z) Z.first.layout s := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  exact open_fold_all (seatKeeps_own (A := arrOf Z) (lay := Z.first.layout)) (seatBack_own _ _) O
    (arrOk_at Z) (fun l Q hQ => letters_arr (IM.base_made O.made).2.2.1 hQ) hp k f
    (own_startS O.pub hq)

/-- **«K12.bookInOrder» in the door's own Bool, at every border.** At every o. -/
theorem atFirstBook_all (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) : K12.Door.atFirstBook 0 s = true := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have H : BookLaw orderedP :=
    ⟨recv_ordered, fun A B r hs k => K2.ordered_same 0 A B r hs k, k12_ordered⟩
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  have q : orderedP s.book s.roots :=
    open_fold_all (seatKeeps_sentence H) (seatBack_sentence H) O trivial (fun _ _ _ => trivial) hp k f
      (by
        show orderedP (ProofFile.startS Z z).book (ProofFile.startS Z z).roots
        rw [(start_empty hZ z).1, (start_empty hZ z).2]
        exact empty_ordered)
  exact (VerifiableInference.Desc.Sound.bookStep_iff 0 s.book s.roots).2 q

/-- **«K12.bookFits» in the door's own Bool, at every border.** At every o. -/
theorem atFirstFits_all (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) : K12.Door.atFirstFits s = true := by
  obtain ⟨-, rs, cols, f⟩ := h.fold
  have H : BookLaw fun T _ => BookFits T :=
    ⟨fun d d' sent ids e k => Book.recvP_fits 0 d d' sent ids e k,
      fun _ _ _ hs k => K2.fits_same hs k, k12_fits⟩
  have hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z := O.pub
  have q : BookFits s.book :=
    open_fold_all (seatKeeps_sentence H) (seatBack_sentence H) O trivial (fun _ _ _ => trivial) hp k f
      (by
        show BookFits (ProofFile.startS Z z).book
        rw [(start_empty hZ z).1]
        exact Book.bookFits_empty)
  exact bookFitsB_of q

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy}

/-- RecAll at every reached state without a mark, at every border, in scope. -/
theorem recAll_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) : RecAll Z.first.codes Z.first.shape s :=
  recAll_all_of O hp h (reqOk_of_noMark hS hR O h hu)

/-- Both copies of the rows' layout at every reached state without a mark, at every border, in scope. -/
theorem rowsLayout_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {k : ℕ} {z : ProofFile.InstPub} {s : S} (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) k (z, s)) (hu : s.failed = none) : s.check.rows.layout = Z.first.layout ∧ s.live.rows.layout = Z.first.layout :=
  own_rows (ownInv_all_of O hp h (reqOk_of_noMark hS hR O h hu))

/-! ## 7 Twelve fields of FoldFacts, WHOLE, in the structure's own letters

Each statement's end is the field's own type (Johnson/Desc/First/FoldFacts.lean), letter for letter, at d.ft := 0 · d.sent := sentAt Z · ps := IM.placesW; general in Rch and at_, with ONE premise on Rch: hRch: what is reached in Rch's sense is reached in this file's (how it is met at RchAt, Johnson/Top/H0/Walk/ReachAt.lean: the head, «What is not claimed»). IN FRONT: O and hRch at all twelve · hp at eleven (ownIs_field has none) · hS, hR at ten (bookInOrder_field | bookFits_field have none). «LETTER FOR LETTER» IS A COMPARISON OF TEXTS BY PROGRAM: the structure is not imported. The five names that both texts write short are pinned here to their full names: -/

example : @reqGroups = @OnBytes.reqGroups := rfl
example : @K12.Door.atFirstBook = @VerifiableInference.Desc.K12.Door.atFirstBook := rfl
example : @K12.Door.atFirstFits = @VerifiableInference.Desc.K12.Door.atFirstFits := rfl
example : @Look.OwnIs = @VerifiableInference.Desc.First.Look.OwnIs := rfl
example : S = VerifiableInference.Desc.First.S := rfl

/-- **Field bookInOrder, whole.** At every o; neither the scope nor the fence is spent. -/
theorem bookInOrder_field (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → K12.Door.atFirstBook 0 (at_ a).2 = true :=
  fun k a hr _ => atFirstBook_all O hp (hRch k a hr)

/-- **Field bookFits, whole.** At every o; neither the scope nor the fence is spent. -/
theorem bookFits_field (O : IM.Open o pol lay KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → K12.Door.atFirstFits (at_ a).2 = true :=
  fun k a hr _ => atFirstFits_all O hp (hRch k a hr)

/-- **Field codes, whole.** -/
theorem codes_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.st.codes = (sentAt Z).codes :=
  fun k a hr hu => (recAll_all hS hR O hp (hRch k a hr) hu).codes

/-- **Field shape, whole.** -/
theorem shape_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.check.frame.shape = (sentAt Z).shape :=
  fun k a hr hu => (recAll_all hS hR O hp (hRch k a hr) hu).walk.shape

/-- **Field layout, whole.** -/
theorem layout_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.check.rows.layout = (sentAt Z).layout :=
  fun k a hr hu => (rowsLayout_all hS hR O hp (hRch k a hr) hu).1

/-- **Field liveShape, whole.** -/
theorem liveShape_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.live.frame.shape = (sentAt Z).shape :=
  fun k a hr hu => (recAll_all hS hR O hp (hRch k a hr) hu).live.shape

/-- **Field liveLayout, whole.** -/
theorem liveLayout_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.live.rows.layout = (sentAt Z).layout :=
  fun k a hr hu => (rowsLayout_all hS hR O hp (hRch k a hr) hu).2

/-- **Field groups, whole.** -/
theorem groups_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.check.frame.groups = reqGroups (at_ a).2.check.frame.shape :=
  fun k a hr hu => by rw [(recAll_all hS hR O hp (hRch k a hr) hu).walk.shape]; exact (recAll_all hS hR O hp (hRch k a hr) hu).walk.groups

/-- **Field liveGroups, whole.** -/
theorem liveGroups_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.live.frame.groups = reqGroups (at_ a).2.live.frame.shape :=
  fun k a hr hu => by rw [(recAll_all hS hR O hp (hRch k a hr) hu).live.shape]; exact (recAll_all hS hR O hp (hRch k a hr) hu).live.groups

/-- **Field frameShape, whole.** -/
theorem frameShape_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.frame.shape = (sentAt Z).shape :=
  fun k a hr hu => (recAll_all hS hR O hp (hRch k a hr) hu).turn.shape

/-- **Field frameGroups, whole.** -/
theorem frameGroups_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hp : ∀ b ∈ c.blocksInOrder, b.planOk = true) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a, Rch k a → (at_ a).2.failed = none → (at_ a).2.frame.groups = reqGroups (at_ a).2.frame.shape :=
  fun k a hr hu => by rw [(recAll_all hS hR O hp (hRch k a hr) hu).turn.shape]; exact (recAll_all hS hR O hp (hRch k a hr) hu).turn.groups

/-- **Field ownIs, whole.** It has no premise hp, and the fence is not spent. -/
theorem ownIs_field (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp) (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop) (at_ : X → ProofFile.InstPub × S) (hRch : ∀ k a, Rch k a → Reach 0 c.blocksInOrder (ProofFile.startS Z) k (at_ a)) : ∀ k a p l, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.kind = .K3 → p.link = some l → Look.OwnIs (sentAt Z) l (at_ a).2 :=
  fun k a _ _ hr _ h1 h2 h3 => ownIs_atK3 hS hR O (hRch k a hr) h1 h2 h3

end

end Meaning.K2

#print axioms Meaning.K2.fold_cut_le
#print axioms Meaning.K2.recAll_reached_of
#print axioms Meaning.K2.bookInOrder_reached
#print axioms Meaning.K2.bookFits_reached
#print axioms Meaning.K2.bookHas_reached
#print axioms Meaning.K2.rowsLayout_reached_of
#print axioms Meaning.K2.liveIs_reached_of
#print axioms Meaning.K2.reqOk_reached
#print axioms Meaning.K2.recAll_reached
#print axioms Meaning.K2.rowsLayout_reached
#print axioms Meaning.K2.liveIs_reached
#print axioms Meaning.K2.bookFitsB_of
#print axioms Meaning.K2.atFirstBook_reached
#print axioms Meaning.K2.atFirstFits_reached
#print axioms Meaning.K2.rootsCount_reached
#print axioms Meaning.K2.ownInv_reached_of
#print axioms Meaning.K2.both_reached
#print axioms Meaning.K2.shapeOk_reached
#print axioms Meaning.K2.ownIs_reached
#print axioms Meaning.K2.ownIs_reached24
#print axioms Meaning.K2.ownIs_k3_reached
#print axioms Meaning.K2.walkGives_reached
#print axioms Meaning.K2.walkGives_reached0
#print axioms Meaning.K2.walkGives_reached24
#print axioms Meaning.K2.midRoots_reached
#print axioms Meaning.K2.midRoots_reached24
#print axioms Meaning.K2.xk_reached
#print axioms Meaning.K2.start_of_early
#print axioms Meaning.K2.reqOk_of_noMark
#print axioms Meaning.K2.recAll_noMark
#print axioms Meaning.K2.codes_inFront
#print axioms Meaning.K2.shape_inFront
#print axioms Meaning.K2.layout_inFront
#print axioms Meaning.K2.liveShape_inFront
#print axioms Meaning.K2.liveLayout_inFront
#print axioms Meaning.K2.groups_inFront
#print axioms Meaning.K2.liveGroups_inFront
#print axioms Meaning.K2.frameShape_inFront
#print axioms Meaning.K2.frameGroups_inFront
#print axioms Meaning.K2.k3_numbers
#print axioms Meaning.K2.k3_bent_fails
#print axioms Meaning.K2.k3_number_at
#print axioms Meaning.K2.ownIs_atK3
#print axioms Meaning.K2.rch_is
#print axioms Meaning.K2.liveIs_noMark
#print axioms Meaning.K2.rch_narrow
#print axioms Meaning.K2.recAll_all_of
#print axioms Meaning.K2.ownInv_all_of
#print axioms Meaning.K2.atFirstBook_all
#print axioms Meaning.K2.atFirstFits_all
#print axioms Meaning.K2.recAll_all
#print axioms Meaning.K2.rowsLayout_all
#print axioms Meaning.K2.bookInOrder_field
#print axioms Meaning.K2.bookFits_field
#print axioms Meaning.K2.codes_field
#print axioms Meaning.K2.shape_field
#print axioms Meaning.K2.layout_field
#print axioms Meaning.K2.liveShape_field
#print axioms Meaning.K2.liveLayout_field
#print axioms Meaning.K2.groups_field
#print axioms Meaning.K2.liveGroups_field
#print axioms Meaning.K2.frameShape_field
#print axioms Meaning.K2.frameGroups_field
#print axioms Meaning.K2.ownIs_field
#print axioms Meaning.K2.planOk_of_run
