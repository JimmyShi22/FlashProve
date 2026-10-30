-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/Fit/SeatFits.lean: AT THE PROOF FILE's SEAT (ProofFile.onlineDescription):
SeatKeepsF | SeatBackF: SeatKeeps | SeatBack WITH WholeF IN Whole's PLACE AT THE FOUR MAKERS THAT
ADMIT A SAMPLE AT ROUNDS: K1's firstSegmentOpening and laterAt · K2's codeSwitchKind · K13's atM4 over W's sending. Every
other field is the original's, to the letter.
  descPure_flatF   **every sub-protocol of c.blocksInOrder that passes its own test on the list of rounds:
  Fits R b**
  ‹lot›_keepsW (eleven): the original's proof, word for word, at H : SeatKeepsF: they conclude the
  ORIGINAL LotAll · k1Blocks_wholeF · k1Pure_keepsF · finishPlace_wholeF · k2Pure_keepsF ·
  k13Lot4_allF: at WholeF · twelve_allF · thePure_keepsF | _allF: joined by hand; that K1's and K2's
  lots lay no sub-protocol of the kind "frame": IM.kind_K1 | kind_K2 (Johnson/IMR/LotKinds.lean),
  called.
CARRIED BY PROGRAM out of Johnson/IMR/SeatKeeps.lean:
each declaration that is needed for the top and names Decides | Whole is copied under
its own name with a letter behind it (F | W), with Fits | WholeF in that word's place; its
docstrings are struck (they are that file's); where a proof opens the word itself it is turned by
hand. THE ORIGINAL IS IMPORTED AND NOT TURNED: what names neither word is called from it. IF THE
ORIGINAL ITSELF IS WIDENED INSTEAD, THIS FILE FALLS.
What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.IMR.SeatKeeps
import Johnson.Desc.Tidy.Fits
import Johnson.IMR.LotKinds
import Johnson.Desc.AtSeats.Fit.FoldFits
import Johnson.Desc.AtSeats.Fit.DriverFits
import Johnson.Desc.AtSeats.Fit.SeatCoreFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Keeps (WholeF Fits LinkKeepsF wholeF_of_whole fits_of_decides
    andThen_wholeF whole_sameF fits_planOk)
open ProofFile (Lot Ground Pub)

variable {R : S → S → Prop} {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}

open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame) in
structure SeatKeepsF (R : S → S → Prop)
    (okB : Array Stages.LinkH → Prop := fun _ => True)
    (okP : K2.HeadPar → Prop := fun _ => True) : Prop where
  refl : ∀ s, R s s
  trans : ∀ a b c, R a b → R b c → R a c
  frames : ∀ {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame}, okB built → framesOf built first W = .ok fs → ∀ f ∈ fs,
    Fn R f.lay ∧ Fn R f.opened ∧ Fn R f.clear
  k1First : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar), gp.firstTree = 0 →
    WholeF R (K1.firstSegmentOpening (Cl := Unit) q gp)
  k1Later : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)), gp.firstTree = 0 →
    WholeF R (K1.laterAt (Cl := Unit) q gp link piece moment arrays)
  reads : ∀ {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit},
    ProofFile.readsQuietAt G l X piece = some b → Whole R b
  k3 : ∀ (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl},
    K3.theStated claim readers X codes shape a = some b → Whole R b
  k4 : ∀ p : OnBytes.Desc.First.K4.Par, Whole R (OnBytes.Desc.First.K4.blockAtC p)
  k5 : ∀ (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim},
    Att.P.k5AtN W l g before = some b → Whole R b
  k6 : ∀ {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim},
    Kinds.Head.seatedClaims W l before = some b → Whole R b
  k7 : ∀ (W : Verify.Public) (l : Nat), Whole R (Kinds.Reply.blockOf W l)
  k8 : ∀ p : K8.ParW, Whole R (K8.whole p)
  k11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP,
    Whole R (Johnson.Desc.First.ForkMerge.headClaimMergeKind P)
  closeOf : ∀ (p : K9.Where) (P : Close.Par), ∀ b ∈ K9.closeOf (Cl := Unit) p P, Whole R b
  batch : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl R claims →
    Whole R (K9.batch K9.atS p claims)
  k2 : ∀ p : K2.P2, p.firstTree = 0 → WholeF R (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn R (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, okP P → Fn R (K2.headOpenQ P)
  finFront : Fn R K2.finishFrontQ
  finBehind : Fn R K2.finishBehindQ

structure SeatBackF (R : S → S → Prop) : Prop where
  k12 : ∀ m : Johnson.G.OfPlan.Made, (K12.atFinish (H2U.p12OfMade m)).planOk = true →
    Whole R (K12.atFinish (H2U.p12OfMade m))
  k13M3 : ∀ p : K13.Where, Whole R (K13.atM3 (Cl := Unit) p)
  k13M4 : ∀ (p : K13.Where) (P : K1.Par), P.gp.firstTree = 0 →
    WholeF R (K13.atM4 (Cl := Unit) p (K1.sendAtS P))

def LotAllF (R : S → S → Prop) (L : Lot) (G : Ground) : Prop :=
  (∀ b ∈ L.blocks G, WholeF R b) ∧
    ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f)

theorem lotAll_ofF {L : Lot} {G : Ground} (h1 : ∀ b ∈ L.own G, WholeF R b)
    (h2 : ∀ b ∈ L.hearC G, WholeF R b)
    (h3 : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f)) : LotAllF R L G := by
  refine ⟨fun b hb => ?_, h3⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact retype_wholeF (h1 b₀ h₀)
  · exact h2 b hb

theorem lotAllF_of {L : Lot} {G : Ground} (K : LotAll R L G) : LotAllF R L G :=
  ⟨fun b hb => wholeF_of_whole (K.1 b hb), fun a mk h f hf => wholeF_of_whole (K.2 a mk h f hf)⟩
theorem framesLot_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (hB : okB Z.p.built.links)
    (G : Ground) : LotAll R (ProofFile.framesLot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1L20.blocksOf Z := hb
  unfold P1L20.blocksOf at hb'
  split at hb'
  · rename_i fs hfs
    obtain ⟨f, hf, hb'⟩ := List.mem_flatMap.1 hb'
    obtain ⟨k1, k2, k3⟩ := H.frames hB hfs f hf
    unfold ProofFile.frameBlocks at hb'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
    rcases hb' with rfl | rfl | rfl
    · exact quiet_whole k1 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k2 (fun _ _ _ => rfl) rfl rfl
    · exact quiet_whole k3 (fun _ _ _ => rfl) rfl rfl
  · obtain rfl := List.mem_singleton.1 hb'
    exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl

theorem k1Blocks_wholeF (H : SeatKeepsF R okB okP) (gp : _root_.Desc.Plain.GPar)
    (h0 : gp.firstTree = 0) (quiet : K1.Quiet)
    (hq : ∀ G l X z, quiet G l X = some z → Whole R z) (G : Ground) :
    ∀ b ∈ K1.blocks gp quiet G, WholeF R b := by
  intro b hb
  unfold K1.blocks at hb
  dsimp only at hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain rfl := List.mem_singleton.1 hb
    exact H.k1First _ _ h0
  · obtain ⟨⟨X, l⟩, -, hb⟩ := List.mem_flatMap.1 hb
    dsimp only at hb
    split at hb
    · cases hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · split
        · rename_i z hz
          exact andThen_wholeF _ H.trans _ _ _ (H.k1Later _ _ _ _ _ _ h0)
            (wholeF_of_whole (hq _ _ _ z hz))
        · exact H.k1Later _ _ _ _ _ _ h0
      · exact H.k1Later _ _ _ _ _ _ h0

theorem k1Pure_keepsF (H : SeatKeepsF R okB okP) (Z : Pub) (h0 : Z.P.firstTree = 0) (G : Ground) :
    LotAllF R (ProofFile.k1Pure Z) G := by
  refine lotAll_ofF (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  unfold ProofFile.k1Pure K1.lotWith at hb
  dsimp only at hb
  refine k1Blocks_wholeF H _ h0 _ (fun G l X z hz => ?_) G b hb
  cases hz
  exact orLoud_whole fun b hb => H.reads hb

theorem finishPlace_wholeF (H : SeatKeepsF R okB okP) (p : K2.P2) (h0 : p.firstTree = 0) :
    WholeF R (K2.finishPlace p : Block S Unit) :=
  whole_sameF (andThen_wholeF _ H.trans p.name _ _
    (andThen_wholeF _ H.trans p.name
      (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece K2.finishFrontQ) _
      (wholeF_of_whole (quiet_whole H.finFront (fun _ _ _ => rfl) rfl rfl)) (H.k2 p h0))
    (wholeF_of_whole (quiet_whole (b := roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link
      p.place.piece K2.finishBehindQ) H.finBehind (fun _ _ _ => rfl) rfl rfl))) rfl
    (fun _ hx => hx) rfl (fun h => h) rfl
theorem k2Pure_keepsF (H : SeatKeepsF R okB okP) (Z : Pub) (h0 : Z.P.firstTree = 0) (G : Ground)
    (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) : LotAllF R (ProofFile.k2Pure Z) G := by
  refine lotAll_ofF (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hb'
  split
  · exact wholeF_of_whole (quiet_whole refuses (fun _ _ _ => rfl) rfl rfl)
  · rename_i x hfind
    have hx0 : x.2.firstTree = 0 :=
      (pureSpots_firstTree (List.mem_of_find?_eq_some hfind)).trans h0
    cases hx : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact wholeF_of_whole (quiet_whole refuses (fun _ _ _ => rfl) rfl rfl)
    | some b₀ =>
      show WholeF R b₀
      unfold P1K2.pureAt at hx
      dsimp only at hx
      split at hx
      · cases hx
        exact whole_sameF (finishPlace_wholeF H x.2 hx0) rfl (fun _ hx => hx) rfl (fun h => h) rfl
      · obtain ⟨P, hPe, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, eP⟩ := Option.bind_eq_some_iff.1 hPe
        exact whole_sameF (andThen_wholeF _ H.trans x.1.name (K2.codeSwitchKind x.2)
          (K2.headOpened x.1.name x.1.place P) (H.k2 _ hx0)
          (wholeF_of_whole (quiet_whole (H.openQ P (hP l P eP)) (fun _ _ _ => rfl) rfl rfl))) rfl
          (fun _ hx => hx) rfl (fun h => h) rfl
      · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 ho
        cases e
        exact whole_sameF (H.k2 x.2 hx0) rfl (fun _ hx => hx) rfl (fun h => h) rfl

theorem k3Lot_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (K3Lot.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ K3Lot.hear Z from hb)
  exact H.k3 _ _ _ _ _ _ e

theorem k4Lot_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.k4Lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
  exact whole_same (H.k4 _) rfl (fun _ hx => hx) rfl

theorem k5LotN_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (H2K5.lotN Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ H2K5.k5OwnN Z G from hb)
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 e
  exact whole_same (H.k5 _ _ _ _ e₀) rfl (fun _ hx => hx) rfl

theorem k8Lot_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.P1K8.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show b ∈ ProofFile.k8Whole Z G from hb)
  exact H.k8 _

theorem k11Lot_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (K11.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact H.k11 _

theorem k6Lot_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (P4.k6Lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  have hb' : b ∈ P4.k6Hear Z G := hb
  unfold P4.k6Hear at hb'
  obtain ⟨ms, -, e⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 hb')
  exact H.k6 e

theorem k9Ninth_keepsW (H : SeatKeepsF R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.k9Ninth Z) G := by
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

theorem h1_wholeW (H : SeatKeepsF R okB okP) (G : Ground) : ∀ b ∈ ProofFile.h1Own G, Whole R b := by
  intro b hb
  unfold ProofFile.h1Own at hb
  obtain rfl := List.mem_singleton.1 hb
  exact Keeps.andThen_whole _ H.trans _ _ _
    (guarded_whole _ _ (quiet_whole (H.front _) (fun _ _ _ => rfl) rfl rfl)) (H.k7 _ _)

theorem k12Lot_ifW (Hb : SeatBackF R) (Z : Pub) (G : Ground) :
    (∀ b ∈ (K12.lot Z).blocks G, b.planOk = true → Whole R b) ∧
      ∀ a mk, (K12.lot Z).batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f) := by
  refine ⟨fun b hb hp => ?_, fun _ _ h => nomatch h⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    obtain rfl := List.mem_singleton.1 h₀
    exact retype_whole (Hb.k12 _ (Bool.and_eq_true _ _ ▸ hp).1)
  · exact nomatch hb

theorem k13Lot_allW (Hb : SeatBackF R) (Z : Pub) (G : Ground) : LotAll R (K13.lot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact Hb.k13M3 _

theorem k13Lot4_allF (Hb : SeatBackF R) (Z : Pub) (h0 : Z.P.firstTree = 0) (G : Ground) :
    LotAllF R (K13.lot4 Z) G := by
  refine lotAll_ofF (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
  have hw' : K13.wBlock Z = some w := Option.mem_toList.1 hw
  unfold K13.wBlock K1.wAt at hw'
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
  exact Hb.k13M4 _ _ h0

theorem twelve_allF (H : SeatKeepsF R okB okP) (Z : Pub) (hB : okB Z.p.built.links)
    (h0 : Z.P.firstTree = 0) (G : Ground) (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) :
    ∀ L ∈ [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
      ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, K13.lotEnd Z] ++ ProofFile.p4Pure Z,
      LotAllF R L G ∧ ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b := by
  have up : ∀ {L : Lot}, LotAll R L G →
      LotAllF R L G ∧ ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b :=
    fun K => ⟨lotAllF_of K, fun b hb _ => K.1 b hb⟩
  intro L hL
  unfold ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact up (framesLot_keepsW H Z hB G)
  · exact ⟨k1Pure_keepsF H Z h0 G, fun b hb hk => absurd hk (by rw [IM.kind_K1 Z G b hb]; decide)⟩
  · exact ⟨k2Pure_keepsF H Z h0 G hP,
      fun b hb hk => absurd hk (by rw [IM.kind_K2 Z G b hb]; decide)⟩
  · exact up (k3Lot_keepsW H Z G)
  · exact up (k4Lot_keepsW H Z G)
  · exact up (k5LotN_keepsW H Z G)
  · exact up (k8Lot_keepsW H Z G)
  · exact up (k9Ninth_keepsW H Z G)
  · exact up (k11Lot_keepsW H Z G)
  · exact up (k13LotEnd_keeps H.refl Z G)
  · exact up (k6Lot_keepsW H Z G)
  · exact up (lotAll_of (fun b hb => h1_wholeW H G b hb) (fun _ hb => nomatch hb)
      (fun _ _ h => nomatch h))
theorem thePure_keepsF (H : SeatKeepsF R okB okP) (Z : Pub) (hB : okB Z.p.built.links)
    (h0 : Z.P.firstTree = 0) (G : Ground) (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) :
    LotsKeepF R (ProofFile.onlineFirstChainBlockTables Z) G := by
  have T := twelve_allF H Z hB h0 G hP
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, (∀ b ∈ L.blocks G, b.place.link ≠ none → WholeF R b) ∧
      (∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b) ∧
      ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f) := by
    have t : ∀ {L : Lot}, (LotAllF R L G ∧
        ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b) →
        (∀ b ∈ L.blocks G, b.place.link ≠ none → WholeF R b) ∧
        (∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b) ∧
        ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f) :=
      fun K => ⟨fun b hb _ => K.1.1 b hb, K.2, K.1.2⟩
    have u : ∀ {L : Lot}, LotKeeps R L G →
        (∀ b ∈ L.blocks G, b.place.link ≠ none → WholeF R b) ∧
        (∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true → Whole R b) ∧
        ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f) :=
      fun K => ⟨fun b hb hl => wholeF_of_whole (K.1 b hb (Or.inl hl)),
        fun b hb hk => K.1 b hb (Or.inr hk), fun a mk h f hf => wholeF_of_whole (K.2 a mk h f hf)⟩
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact t (T L (Or.inl (Or.inl h)))
    · exact t (T L (Or.inl (Or.inr (Or.inl h))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inl h)))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h))))))))))
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h)))))))))))
    · exact u (k12Lot_keeps Z G)
    · exact u (k13Lot_keeps Z G)
    · exact u (k13Lot4_keeps Z G)
    · exact t (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h)))))))))))
    · exact t (T L (Or.inr h))
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2.1, fun L hL => (key L hL).2.2⟩

theorem thePure_allF (H : SeatKeepsF R okB okP) (Hb : SeatBackF R) (Z : Pub)
    (hB : okB Z.p.built.links) (h0 : Z.P.firstTree = 0)
    (G : Ground) (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) :
    LotsAllF R (ProofFile.onlineFirstChainBlockTables Z) G := by
  have T := twelve_allF H Z hB h0 G hP
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, (∀ b ∈ L.blocks G, b.planOk = true → WholeF R b) ∧
      ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f) := by
    have up : ∀ {L : Lot}, LotAllF R L G → (∀ b ∈ L.blocks G, b.planOk = true → WholeF R b) ∧
        ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → WholeF R (mk f) :=
      fun K => ⟨fun b hb _ => K.1 b hb, K.2⟩
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact up (T L (Or.inl (Or.inl h))).1
    · exact up (T L (Or.inl (Or.inr (Or.inl h)))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inl h))))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))).1
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))))))).1
    · exact ⟨fun b hb hp => wholeF_of_whole ((k12Lot_ifW Hb Z G).1 b hb hp),
        fun a mk h f hf => wholeF_of_whole ((k12Lot_ifW Hb Z G).2 a mk h f hf)⟩
    · exact up (lotAllF_of (k13Lot_allW Hb Z G))
    · exact up (k13Lot4_allF Hb Z h0 G)
    · exact up (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h))))))))))).1
    · exact up (T L (Or.inr h)).1
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2⟩

theorem descPure_flatF (H : SeatKeepsF R okB) (Hb : SeatBackF R) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Fits R b := by
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, e, k⟩ := pureZ_flatF H.refl H.trans (T := ProofFile.pureSeat o Z)
    (fun G => thePure_keepsF H Z (hB Z hZ) (pub_firstTree hZ) G fun _ _ _ => trivial)
    (fun G => thePure_allF H Hb Z (hB Z hZ) (pub_firstTree hZ) G fun _ _ _ => trivial) h
  exact ⟨Z, A, B, c, hZ, e, k⟩

section And
variable {R₁ R₂ : S → S → Prop} {ok₁ ok₂ : Array Stages.LinkH → Prop}
  {op₁ op₂ : K2.HeadPar → Prop} {Cl : Type}

end And

end Meaning.K2
