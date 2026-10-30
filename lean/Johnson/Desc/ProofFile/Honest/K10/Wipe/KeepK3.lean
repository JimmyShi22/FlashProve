-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepK3.lean: the closing of a segment (K10): the lookups' blocks (kind K3,
Johnson/Desc/ProofFile/Lot/K3.lean: hear) do alike at two states of the first chain that are one once wiped. Two
structures of type Prop; the rest are theorems.

Words. wipeS sets to zero the targets of the rows that a state of the first chain holds (Honest/K10/WipeS.lean says
which). Two states are one under w where w s = w s'. A reader does not see w where it returns at w s what it returns
at s. A writer goes through w where it returns at w s the image under w of what it returns at s. Two outcomes are
alike where both refuse with the same word, or both return and the values are one under w (AlikeE, Wipe/Alike.lean). A
block does alike (Whole2 w) where its decide, each of its runs of claims and each of its runs behind the batching have
like outcomes at two states that are one under w; the claims of a run are then equal.

What is proved.
  K3Blind w L     what is asked of a seat L of the lookup: its three readers do not see w; its two layings go through
                  w
  K3Blind.mark2, decideVia2, blockVia_whole2, joinRun2, planesRun2, withCaller_whole2   K3Blind w L ⊢ at any type of
                  state these do alike: the seat's mark, the kind's decide, its block without guests, the runs "join"
                  and "planes" (at keys and at readers that do not see w), the block with "planes" stated
  seatCalls_blind, seatDigits_blind   K3Blind wipeS of the lookup's two seats at the first chain's state
  quietLook2, quietDigits2, quietHead2, quietAt2   Fn2 wipeS of each step without a round that stands behind a lookup
  theOwn_whole2, theWhole_whole2, theStated_whole2   Whole2 wipeS of the block at an address, as each of the three
                  makers gives it; the last at readers that do not see the wiping
  SeatCBlind w L, inOf_blind, keysOfK_blind, readersOfK_blind, seatCO_blind, keysOfO_blind, readersOfO_blind   the
                  keys and the readers that kind K5 hands the lookup do not see w, or the wiping
  planesAt_blind, callerReaders_blind   the same of the readers that kind K6 hands the lookup
  readersAt_blind   the readers that the lot itself hands the lookup do not see the wiping
  **k3_keeps**      ∀ b ∈ K3Lot.hear Z, Whole2 wipeS b: the field k3 of SeatKeeps2 (Wipe/Lots2.lean)

By what. At any type of state: what the seat's readers return at s is rewritten to what they return at s'; then the
two texts make the same calls, one after the other (AlikeE.head'); the last line is the seat's laying. The hearing
(hearVia) and the runs' formulas are handed a ledger, rounds and what was heard, never the state: they are not opened.
At the first chain's state: Wipe/WipeLaws.lean, or the state is taken apart by the kind of place. The three makers of a
block at an address are followed case for case, as Johnson/Goal/Meaning/RecK3More.lean and RecSeated.lean follow them,
over Wipe/Wrap2.lean.

Limits. blockVia_whole2 is shown at the empty list of guests alone, which is the list that theOwn hands it. K5's and
K6's readers stand here, not in Wipe/KeepK5.lean and KeepK6K7.lean, because these two files import this one. Nothing is
said of what the hearing or the formulas compute. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.KeepBase
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Wrap2
import Johnson.Desc.ProofFile.Lot.K3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First

/-! ## 1 The kind at any type of state -/

section letter
variable {T Cl : Type} {w : T → T} {L : K3.Seat T Cl}

/-- What is asked of a seat of the lookup: the readers do not see w; the layings go through w. -/
structure K3Blind (w : T → T) (L : K3.Seat T Cl) : Prop where
  fork : ∀ s, L.fork (w s) = L.fork s
  owed : ∀ s, L.owed (w s) = L.owed s
  heard : ∀ s, L.heard (w s) = L.heard s
  put : ∀ s g G, L.put (w s) g G = w (L.put s g G)
  mark : ∀ s G, L.mark (w s) G = w (L.mark s G)

/-- The seat's mark in the ledger returns, at two states that are one under w, states that are one under w. -/
theorem K3Blind.mark2 (h : K3Blind w L) {s s' : T} (hs : w s = w s') (G : Fork) :
    w (L.mark s G) = w (L.mark s' G) := by
  rw [← h.mark s, ← h.mark s', hs]

/-- The lookup's decide has like outcomes at two states that are one under w. -/
theorem decideVia2 (h : K3Blind w L) (p : First.Look.P) {s s' : T} (hs : w s = w s') (rs : List Fmt.RoundView) :
    AlikeE w (K3.Law.decideVia L p s rs) (K3.Law.decideVia L p s' rs) := by
  unfold K3.Law.decideVia
  rw [blind2 (f := L.fork) h.fork hs, blind2 (f := L.heard) h.heard hs, blind2 (f := L.owed) h.owed hs]
  refine AlikeE.head' fun F => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun x => ?_
  refine AlikeE.ok ?_
  rw [← h.put s, ← h.put s', hs]

/-- **The lookup's block, at the empty list of guests, does alike.** -/
theorem blockVia_whole2 (h : K3Blind w L) (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (p : First.Look.P) : Whole2 w (K3.Law.blockVia L piece laid before p []) := by
  refine ⟨fun s s' rs _ _ hs _ => decideVia2 h p hs rs, fun c hc n s s' hs => ?_, (fun _ hc => nomatch hc)⟩
  rcases List.mem_cons.1 hc with rfl | hc
  · dsimp only
    rw [blind2 (f := L.fork) h.fork hs, blind2 (f := L.heard) h.heard hs]
    refine AlikeE.head' fun F => ?_
    refine AlikeE.head' fun g => ?_
    exact AlikeE.ok (wCl_eq (h.mark2 hs _))
  · rcases List.mem_cons.1 hc with rfl | hc
    · show AlikeE (wCl w) (Except.ok (([] : List Cl), s)) (Except.ok (([] : List Cl), s'))
      exact AlikeE.ok (wCl_eq hs)
    · cases hc

/-- **The run "join"**, at keys that do not see w, returns equal claims and like states. -/
theorem joinRun2 (h : K3Blind w L) {keys : T → Option (Array Aff)} (hk : ∀ s, keys (w s) = keys s) (n : Nat) :
    FnCl2 w (K3.joinRun L keys n) := by
  intro s s' hs
  unfold K3.joinRun
  rw [blind2 (f := L.fork) h.fork hs, blind2 (f := L.heard) h.heard hs, blind2 (f := keys) hk hs]
  refine AlikeE.head' fun F => ?_
  refine AlikeE.head' fun g => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun KF => ?_
  refine AlikeE.head' fun x => ?_
  exact AlikeE.ok (wCl_eq (h.mark2 hs _))

/-- **The run "planes"**, at readers that do not see w, returns equal claims and like states. -/
theorem planesRun2 (h : K3Blind w L) (lm : Nat) {readers : K3.Readers T} (hr : ∀ s, readers (w s) = readers s)
    (n : Nat) : FnCl2 w (K3.planesRun L lm readers n) := by
  intro s s' hs
  unfold K3.planesRun
  rw [blind2 (f := L.fork) h.fork hs, blind2 (f := L.heard) h.heard hs, blind2 (f := readers) hr hs]
  refine AlikeE.head' fun F => ?_
  refine AlikeE.head' fun g => ?_
  refine AlikeE.head' fun _ => ?_
  refine AlikeE.head' fun r => ?_
  refine AlikeE.head' fun x => ?_
  exact AlikeE.ok (wCl_eq (h.mark2 hs _))

/-- A block that does alike still does with "planes" stated behind its own runs. -/
theorem withCaller_whole2 (h : K3Blind w L) (p : First.Look.P) {readers : K3.Readers T}
    (hr : ∀ s, readers (w s) = readers s) {b : Block T Cl} (W : Whole2 w b) :
    Whole2 w (K3.withCaller L p readers b) := by
  refine ⟨W.1, fun c hc n => ?_, W.2.2⟩
  rcases List.mem_append.1 hc with hc | hc
  · exact W.2.1 c hc n
  · rcases List.mem_cons.1 hc with rfl | hc
    · exact planesRun2 h _ hr n
    · cases hc

end letter

/-! ## 2 The two seats at the first chain's state -/

section atS
variable {Cl : Type}

/-- The seat at the lookup on a link's calls: its readers do not see the wiping; its layings go through it. -/
theorem seatCalls_blind (claim : Aff → Cl) : K3Blind wipeS (K3.seatCalls claim) where
  fork s := fork?_wipe s
  owed _ := rfl
  heard s := lookHeard?_wipe s
  put s g G := by
    show ((wipeS s).putFork G).hearLook g = wipeS ((s.putFork G).hearLook g)
    rw [hearLook_wipe, putFork_wipe]
  mark s G := (putFork_wipe s G).symm

/-- The seat at the lookup on the smallness test's digits: its readers do not see the wiping; its layings go through
it. -/
theorem seatDigits_blind (claim : Aff → Cl) : K3Blind wipeS (K3.seatDigits claim) where
  fork s := fork?_wipe s
  owed _ := rfl
  heard s := by
    show (wipeS s).tl?.bind (·.heard) = s.tl?.bind (·.heard)
    rw [tl?_wipe]
  put s g G := by
    rcases s with ⟨_, _, _, _, _ | _, _, _, _ | _ | _ |
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl
  mark s G := (putFork_wipe s G).symm

/-! ## 3 The steps without a round behind a lookup -/

/-- The step behind the lookup on a layers' link's calls has like outcomes at two states that are one once wiped. -/
theorem quietLook2 (fs : Forest.Shape) : Fn2 wipeS (K3.quietLook fs) := by
  refine Fn2.of_wiped fun s => ?_
  unfold K3.quietLook
  rw [lookHeard?_wipe]
  refine AlikeE.head' fun g => ?_
  refine AlikeE.head' fun _ => ?_
  exact AlikeE.ok (alike_of_wiped rfl)

/-- So has the step behind the lookup on the digits, at a layers' or an attention link. -/
theorem quietDigits2 (used claims : Nat) : Fn2 wipeS (K3.quietDigits used claims) := by
  refine Fn2.of_wiped fun s => ?_
  unfold K3.quietDigits
  rw [fork?_wipe]
  refine AlikeE.head' fun F => ?_
  refine AlikeE.head' fun G => ?_
  exact AlikeE.ok (alike_of_wiped (putFork_wipe s G).symm)

/-- So has the step behind the lookup on the digits, at the head's link. -/
theorem quietHead2 (X : Verify.Public) : Fn2 wipeS (K3.quietHead X) := by
  refine Fn2.of_wiped fun s => ?_
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | between => exact AlikeE.error _
  | lay a => exact AlikeE.error _
  | att a => exact AlikeE.error _
  | fin a => exact AlikeE.error _
  | mem a => exact AlikeE.error _
  | head a =>
    unfold K3.quietHead wipeS wipeHere
    dsimp only
    refine AlikeE.head' fun _ => ?_
    refine AlikeE.head_eq' (covered_wipe _ _ ⟨st, book, roots, owed, failed, check, out, .head a, req⟩) fun cov => ?_
    refine AlikeE.head' fun x => ?_
    refine AlikeE.head' fun t => ?_
    refine AlikeE.head' fun claim => ?_
    refine AlikeE.head' fun _ => ?_
    exact AlikeE.ok (alike_of_wiped rfl)

/-- So has whatever quietAt lays behind a link's lookup. -/
theorem quietAt2 (X : Verify.Public) (i : Nat) (digits : Bool) {f : S → Except String S}
    (h : K3.quietAt X i digits = some f) : Fn2 wipeS f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead2 X)
    | (cases h; exact quietLook2 _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits2 _ _)
    | cases h

/-! ## 4 The block at an address -/

/-- Every block that theOwn gives does alike. -/
theorem theOwn_whole2 (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes) (shape : ReqShape)
    (a : Place) {b : Block S Cl} (h : K3.theOwn claim runs X codes shape a = some b) : Whole2 wipeS b := by
  unfold K3.theOwn at h
  split at h
  · cases h
  · obtain ⟨i, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨digits, _, h⟩ := List.exists_of_findSome?_eq_some h
    split at h
    · cases h
    · obtain ⟨p, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨sent, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨laid, _, h⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨key, _, h⟩ := Option.map_eq_some_iff.1 h
      have W : Whole2 wipeS (K3.Law.blockVia (if digits = true then K3.seatDigits claim
          else K3.seatCalls claim) a.piece laid sent p []) := by
        cases digits
        · exact blockVia_whole2 (seatCalls_blind claim) _ _ _ _
        · exact blockVia_whole2 (seatDigits_blind claim) _ _ _ _
      rw [← h]
      cases runs
      · exact whole_same2 W rfl (fun _ hx => nomatch hx) rfl
      · exact whole_same2 W rfl (fun _ hx => hx) rfl

/-- Every block that theWhole gives does alike. -/
theorem theWhole_whole2 (claim : Aff → Cl) (runs : Bool) (X : Verify.Public) (codes : Codes) (shape : ReqShape)
    (a : Place) {b : Block S Cl} (h : K3.theWhole claim runs X codes shape a = some b) : Whole2 wipeS b := by
  unfold K3.theWhole at h
  obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  have W := theOwn_whole2 claim runs X codes shape a h0
  split
  · rename_i f hf
    obtain ⟨i, _, hq⟩ := Option.bind_eq_some_iff.1 hf
    exact andThen_whole2 _ _ _ W (quietBlock_whole2 _ _ _ _ (quietAt2 X i _ hq))
  · exact W

/-- **Every block that theStated gives does alike**, at readers that do not see the wiping. -/
theorem theStated_whole2 (claim : Aff → Cl) (readers : Nat → Option (K3.Readers S))
    (hr : ∀ i r, readers i = some r → ∀ s, r (wipeS s) = r s) (X : Verify.Public) (codes : Codes)
    (shape : ReqShape) (a : Place) {b : Block S Cl} (h : K3.theStated claim readers X codes shape a = some b) :
    Whole2 wipeS b := by
  unfold K3.theStated at h
  obtain ⟨b₀, h0, h⟩ := Option.bind_eq_some_iff.1 h
  have W := theWhole_whole2 claim true X codes shape a h0
  split at h
  · cases h
    exact W
  · split at h
    · cases h
      exact W
    · split at h
      · cases h
        exact W
      · rename_i r hri
        obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
        exact withCaller_whole2 (seatCalls_blind claim) p (hr _ r hri) W

end atS

/-! ## 5 The readers that kind K5 hands the lookup -/

section k5
variable {T : Type} {w : T → T} {L : Att.P.SeatC T}

/-- What is asked of a seat of K5's claims: its five readers do not see w. -/
structure SeatCBlind (w : T → T) (L : Att.P.SeatC T) : Prop where
  pts : ∀ s, L.pts (w s) = L.pts s
  cols : ∀ s, L.cols (w s) = L.cols s
  look : ∀ s, L.look (w s) = L.look s
  pad : ∀ s, L.pad (w s) = L.pad s
  zk : ∀ s, L.zk (w s) = L.zk s

/-- What K5's runs read does not see w. -/
theorem inOf_blind (h : SeatCBlind w L) (c : Att.P.ParC) (s : T) : Att.P.inOf L c (w s) = Att.P.inOf L c s := by
  unfold Att.P.inOf
  rw [h.pts s, h.look s, h.zk s, h.cols s]

/-- The calls' key forms do not see w. -/
theorem keysOfK_blind (h : SeatCBlind w L) (c : Att.P.ParC) (s : T) :
    Att.P.keysOfK L c (w s) = Att.P.keysOfK L c s := by
  unfold Att.P.keysOfK
  rw [inOf_blind h c s, h.pad s]

/-- The readers for "planes" do not see w. -/
theorem readersOfK_blind (h : SeatCBlind w L) (c : Att.P.ParC) (s : T) :
    Att.P.readersOfK L c (w s) = Att.P.readersOfK L c s := by
  unfold Att.P.readersOfK
  rw [inOf_blind h c s]

end k5

/-- The seat of K5's claims at the first chain's state does not see the wiping. -/
theorem seatCO_blind (c : Att.P.ParC) : SeatCBlind wipeS (Att.P.seatCO c) where
  pts s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl
  cols s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl
  look s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl
  pad s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl
  zk s := by
    rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ | _ | _ | _, _⟩ <;> rfl

/-- K5's keys for "join" do not see the wiping. -/
theorem keysOfO_blind (A : Attention.Plan) (s : S) : Att.P.keysOfO A (wipeS s) = Att.P.keysOfO A s :=
  keysOfK_blind (seatCO_blind _) _ s

/-- K5's readers for "planes" do not see the wiping. -/
theorem readersOfO_blind (A : Attention.Plan) (s : S) : Att.P.readersOfO A (wipeS s) = Att.P.readersOfO A s :=
  readersOfK_blind (seatCO_blind _) _ s

/-! ## 6 The readers that kind K6 hands the lookup -/

/-- The three further reads at the first chain's state do not see the wiping. -/
theorem planesAt_blind (iU3 : Nat) (s : S) : Kinds.Head.planesAt iU3 (wipeS s) = Kinds.Head.planesAt iU3 s := by
  rcases s with ⟨_, _, _, _, _, _, _, _ | _ | _ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _ | _, _, _⟩ | _ | _, _⟩ <;> rfl

/-- K6's readers for "planes" do not see w where the seat of the reads that they are made of does not. -/
theorem callerReaders_blind {T : Type} {w : T → T} {X : Kinds.Head.PlaneSeat T} (h : ∀ s, X (w s) = X s) (s : T) :
    Kinds.Head.callerReaders X (w s) = Kinds.Head.callerReaders X s := by
  unfold Kinds.Head.callerReaders
  rw [h s]

/-! ## 7 The lot -/

/-- The readers that the lot itself hands the lookup do not see the wiping. -/
theorem readersAt_blind (X : Verify.Public) (i : Nat) (r : K3.Readers S) (h : K3Lot.readersAt X i = some r) (s : S) :
    r (wipeS s) = r s := by
  unfold K3Lot.readersAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (obtain ⟨iU3, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact callerReaders_blind (planesAt_blind iU3) s)
    | (obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h; exact readersOfO_blind A s)
    | cases h

/-- **Each of kind K3's blocks does alike at two states that are one once wiped.** -/
theorem k3_keeps (Z : ProofFile.Pub) : ∀ b ∈ K3Lot.hear Z, Whole2 wipeS b := by
  intro b hb
  obtain ⟨x, -, h⟩ := List.mem_filterMap.1 hb
  exact theStated_whole2 _ _ (readersAt_blind Z.p.X) _ _ _ _ h

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.K3Blind
#print axioms ProofFile.Honest.K10.K3Blind.mark2
#print axioms ProofFile.Honest.K10.decideVia2
#print axioms ProofFile.Honest.K10.blockVia_whole2
#print axioms ProofFile.Honest.K10.joinRun2
#print axioms ProofFile.Honest.K10.planesRun2
#print axioms ProofFile.Honest.K10.withCaller_whole2
#print axioms ProofFile.Honest.K10.seatCalls_blind
#print axioms ProofFile.Honest.K10.seatDigits_blind
#print axioms ProofFile.Honest.K10.quietLook2
#print axioms ProofFile.Honest.K10.quietDigits2
#print axioms ProofFile.Honest.K10.quietHead2
#print axioms ProofFile.Honest.K10.quietAt2
#print axioms ProofFile.Honest.K10.theOwn_whole2
#print axioms ProofFile.Honest.K10.theWhole_whole2
#print axioms ProofFile.Honest.K10.theStated_whole2
#print axioms ProofFile.Honest.K10.SeatCBlind
#print axioms ProofFile.Honest.K10.inOf_blind
#print axioms ProofFile.Honest.K10.keysOfK_blind
#print axioms ProofFile.Honest.K10.readersOfK_blind
#print axioms ProofFile.Honest.K10.seatCO_blind
#print axioms ProofFile.Honest.K10.keysOfO_blind
#print axioms ProofFile.Honest.K10.readersOfO_blind
#print axioms ProofFile.Honest.K10.planesAt_blind
#print axioms ProofFile.Honest.K10.callerReaders_blind
#print axioms ProofFile.Honest.K10.readersAt_blind
#print axioms ProofFile.Honest.K10.k3_keeps
