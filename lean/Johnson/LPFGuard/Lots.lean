-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Lots.lean: THE GUARD ON THE REPLY: the walk from the makers to the seat's lots.

What the file is. The proof file's seat (ProofFile.onlineFirstChainBlockTables Z, Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean) has
fifteen lots of blocks. For a relation R on the first chain's state that every maker of the seat but
K7's keeps (SeatBut R, Ground.lean), if R is reflexive and transitive, fourteen lots keep R at every
block, with no side premise. The fifteenth lot has one block, at "H:1", the place where the reply is
heard: that block stands at a place of the kind K7, and it has no runs.

Main names.
* One theorem a lot, each LotAll R L G (Meaning.K2.LotAll: every block of the lot, its decision and
  its runs, and the lot's batching): framesLot_all, k1Pure_all, k2Pure_all, k3Lot_all, k4Lot_all,
  k5LotN_all, k8Lot_all, k9Ninth_all, k11Lot_all, k12Lot_all, k13Lot_all, k13Lot4_all, k6Lot_all.
  The fourteenth, the last block's lot, has the library's Meaning.K2.k13LotEnd_keeps, called.
* h1_facts: the block at "H:1": its place's kind is K7; it has no run of claims and no run behind
  the batching.
* LotBut R L G: what LotsBut (Ground.lean) asks, of one lot. LotBut.ofAll; h1Lot_but.
* thePure_but: LotsBut R (ProofFile.onlineFirstChainBlockTables Z) G.

What it leans on. Ground.lean. Called from the library, in the namespace Meaning.K2: LotAll,
lotAll_of, quiet_whole, refuses, orLoud_whole, k13LotEnd_keeps (Johnson/IMR/SeatKeeps.lean),
whole_same (Johnson/Goal/Meaning/RecK3.lean); and Keeps.andThen_whole
(Johnson/Desc/BlockKeeps.lean).

Carried proofs. The proofs of twelve of the thirteen theorems on lots, of k1Blocks_all and of
finishPlace_all follow those of the like theorems of Johnson/IMR/SeatKeeps.lean (there mostly named
_keeps or _whole), which are stated for H : SeatKeeps R okB okP or Hb : SeatBack R. Those cannot be
called: SeatKeeps cannot be had at the relation "the reply is as it was", for its field k7 asks that
K7's block leave the reply, which that block is there to write (not proved here). SeatBack's fields
are taken into SeatBut so that one structure is enough. The differences: H : SeatBut R; transitivity
is a premise of its own; no side premise (on the links built, the first tree's number, the head's
letters). k12Lot_all follows none: that file's k12Lot_if asks the block's test on the plan. The
cases of thePure_but follow twelve_all there, and IM.lot_K7 (Johnson/IMR/K7Seat.lean).

Limits. Nothing is shown here of any maker: that SeatBut holds at a given R is Makers.lean's.
THE BLOCK AT "H:1" IS A JOINT: its first half is K2's step that enters the head's segment, its
second K7's block. It goes free here whole, under K7's label: nothing is said of what either half
decides, and SeatBut's field front is not spent here. The first half is proved in Strike.lean
(h1_same). The lots are not the chain: the walk from the lots to the chain's parts is
Seat.lean's. Nothing on soundness.


-/
import Johnson.LPFGuard.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)
open Meaning.K2 (LotAll lotAll_of quiet_whole refuses orLoud_whole whole_same k13LotEnd_keeps)

variable {R : S → S → Prop}

/-! ## The frames -/

theorem framesLot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (ProofFile.framesLot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1L20.blocksOf Z := hb
  unfold P1L20.blocksOf at hb'
  split at hb'
  · rename_i fs hfs
    obtain ⟨f, hf, hb'⟩ := List.mem_flatMap.1 hb'
    obtain ⟨k1, k2, k3⟩ := H.frames hfs f hf
    unfold ProofFile.frameBlocks at hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact quiet_whole k1 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k2 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k3 (fun _ _ _ => rfl) rfl rfl
  · obtain rfl := List.mem_singleton.1 hb'
    exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl

/-! ## K1 -/

theorem k1Blocks_all (ht : ∀ a b c, R a b → R b c → R a c) (H : SeatBut R)
    (gp : _root_.Desc.Plain.GPar) (quiet : K1.Quiet)
    (hq : ∀ G l X z, quiet G l X = some z → Whole R z) (G : Ground) :
    ∀ b ∈ K1.blocks gp quiet G, Whole R b := by
  intro b hb
  unfold K1.blocks at hb
  dsimp only at hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain rfl := List.mem_singleton.1 hb
    exact H.k1First _ _
  · obtain ⟨⟨X, l⟩, -, hb⟩ := List.mem_flatMap.1 hb
    dsimp only at hb
    split at hb
    · cases hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · split
        · rename_i z hz
          exact Keeps.andThen_whole _ ht _ _ _ (H.k1Later _ _ _ _ _ _) (hq _ _ _ z hz)
        · exact H.k1Later _ _ _ _ _ _
      · exact H.k1Later _ _ _ _ _ _

theorem k1Pure_all (ht : ∀ a b c, R a b → R b c → R a c) (H : SeatBut R) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.k1Pure Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  unfold ProofFile.k1Pure K1.lotWith at hb
  dsimp only at hb
  refine k1Blocks_all ht H _ _ (fun G l X z hz => ?_) G b hb
  cases hz
  exact orLoud_whole fun b hb => H.reads hb

/-! ## K2 -/

theorem finishPlace_all (ht : ∀ a b c, R a b → R b c → R a c) (H : SeatBut R) (p : K2.P2) :
    Whole R (K2.finishPlace p : Block S Unit) :=
  whole_same (Keeps.andThen_whole _ ht p.name _ _
    (Keeps.andThen_whole _ ht p.name
      (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece K2.finishFrontQ) _
      (quiet_whole H.finFront (fun _ _ _ => rfl) rfl rfl) (H.k2 p))
    (quiet_whole (b := roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece
      K2.finishBehindQ) H.finBehind (fun _ _ _ => rfl) rfl rfl)) rfl (fun _ hx => hx) rfl

theorem k2Pure_all (ht : ∀ a b c, R a b → R b c → R a c) (H : SeatBut R) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.k2Pure Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hb'
  split
  · exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
  · rename_i x _
    cases hx : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
    | some b₀ =>
      show Whole R b₀
      unfold P1K2.pureAt at hx
      dsimp only at hx
      split at hx
      · cases hx
        exact whole_same (finishPlace_all ht H x.2) rfl (fun _ hx => hx) rfl
      · obtain ⟨P, -, rfl⟩ := Option.map_eq_some_iff.1 hx
        exact whole_same (Keeps.andThen_whole _ ht x.1.name (K2.codeSwitchKind x.2)
          (K2.headOpened x.1.name x.1.place P) (H.k2 _)
          (quiet_whole (H.openQ P) (fun _ _ _ => rfl) rfl rfl)) rfl (fun _ hx => hx) rfl
      · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 ho
        cases e
        exact whole_same (H.k2 x.2) rfl (fun _ hx => hx) rfl

/-! ## The lots of blocks with runs -/

theorem k3Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (K3Lot.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ K3Lot.hear Z from hb)
  exact H.k3 _ _ _ _ _ _ e

theorem k4Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (ProofFile.k4Lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
  exact whole_same (H.k4 _) rfl (fun _ hx => hx) rfl

theorem k5LotN_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (H2K5.lotN Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ H2K5.k5OwnN Z G from hb)
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 e
  exact whole_same (H.k5 _ _ _ _ e₀) rfl (fun _ hx => hx) rfl

theorem k8Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (ProofFile.P1K8.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show b ∈ ProofFile.k8Whole Z G from hb)
  exact H.k8 _

theorem k11Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (K11.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact H.k11 _

theorem k6Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (P4.k6Lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  have hb' : b ∈ P4.k6Hear Z G := hb
  unfold P4.k6Hear at hb'
  obtain ⟨ms, -, e⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 hb')
  exact H.k6 e

/-! ## K9 with K10's closing -/

theorem k9Ninth_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (ProofFile.k9Ninth Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun a mk h f hf => ?_)
  · unfold ProofFile.k9Ninth at hb
    dsimp only at hb
    obtain ⟨w, -, hb⟩ := List.mem_flatMap.1 hb
    split at hb
    · exact H.closeOf _ _ b hb
    · obtain rfl := List.mem_singleton.1 hb
      exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
  · unfold ProofFile.k9Ninth at h
    dsimp only at h
    split at h
    · obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · cases h
        exact H.batch p hf
      · cases h
    · cases h

/-! ## Behind the last link -/

/-- Kind K12's lot: its one block, whatever its test on the plan says. -/
theorem k12Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (K12.lot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact H.k12 _

theorem k13Lot_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (K13.lot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact H.k13M3 _

theorem k13Lot4_all (H : SeatBut R) (Z : Pub) (G : Ground) : LotAll R (K13.lot4 Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
  have hw' : K13.wBlock Z = some w := Option.mem_toList.1 hw
  unfold K13.wBlock K1.wAt at hw'
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
  exact H.k13M4 _ _

/-! ## "H:1" -/

/-- **The block at "H:1"**: its place's kind is K7, and it has no runs. -/
theorem h1_facts (G : Ground) :
    ∀ b ∈ ProofFile.h1Own G, b.place.kind = KindName.K7 ∧ b.claims = [] ∧ b.after = [] := by
  intro b hb
  obtain rfl := List.mem_singleton.1 hb
  exact ⟨rfl, rfl, rfl⟩

/-- What `LotsBut` asks, of one lot. -/
def LotBut (R : S → S → Prop) (L : Lot) (G : Ground) : Prop :=
  (∀ b ∈ L.blocks G, b.place.kind = KindName.K7 ∨ Decides R b) ∧ (∀ b ∈ L.blocks G, Runs R b) ∧
    ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)

theorem LotBut.ofAll {L : Lot} {G : Ground} (K : LotAll R L G) : LotBut R L G :=
  ⟨fun b hb => Or.inr (K.1 b hb).1, fun b hb => (K.1 b hb).2, K.2⟩

/-- **The fifteenth lot**, under whatever name: `own` is `ProofFile.h1Own`, and the rest is the
structure's default. It holds at every R. -/
theorem h1Lot_but (n : String) (l : Bool) (G : Ground) :
    LotBut R { name := n, letters := l, own := ProofFile.h1Own } G := by
  have key : ∀ b ∈ Lot.blocks { name := n, letters := l, own := ProofFile.h1Own } G,
      ∃ x ∈ ProofFile.h1Own G, b = x.retype := by
    intro b hb
    rcases List.mem_append.1 hb with hb | hb
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      exact ⟨x, hx, rfl⟩
    · exact nomatch hb
  refine ⟨fun b hb => Or.inl ?_, fun b hb => ?_, fun _ _ h => nomatch h⟩
  · obtain ⟨x, hx, rfl⟩ := key b hb
    exact (h1_facts G x hx).1
  · obtain ⟨x, hx, rfl⟩ := key b hb
    refine ⟨fun _ hc => (nomatch hc), fun c hc => ?_⟩
    have hc' : c ∈ x.after := hc
    rw [(h1_facts G x hx).2.2] at hc'
    cases hc'

/-! ## The seat -/

/-- **THE SEAT's LOTS**: every block stands at a place of the kind K7 or its decision keeps R; every
block's runs keep R; every batching keeps R at a gatherer that does. -/
theorem thePure_but (hr : ∀ s, R s s) (ht : ∀ a b c, R a b → R b c → R a c) (H : SeatBut R)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotsBut R (ProofFile.onlineFirstChainBlockTables Z) G := by
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotBut R L G := by
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      (rfl | rfl)
    · exact .ofAll (framesLot_all H Z G)
    · exact .ofAll (k1Pure_all ht H Z G)
    · exact .ofAll (k2Pure_all ht H Z G)
    · exact .ofAll (k3Lot_all H Z G)
    · exact .ofAll (k4Lot_all H Z G)
    · exact .ofAll (k5LotN_all H Z G)
    · exact .ofAll (k8Lot_all H Z G)
    · exact .ofAll (k9Ninth_all H Z G)
    · exact .ofAll (k11Lot_all H Z G)
    · exact .ofAll (k12Lot_all H Z G)
    · exact .ofAll (k13Lot_all H Z G)
    · exact .ofAll (k13Lot4_all H Z G)
    · exact .ofAll (k13LotEnd_keeps hr Z G)
    · exact .ofAll (k6Lot_all H Z G)
    · exact h1Lot_but _ _ G
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2.1, fun L hL => (key L hL).2.2⟩

#print axioms h1_facts
#print axioms h1Lot_but
#print axioms thePure_but

end LPFGuard
