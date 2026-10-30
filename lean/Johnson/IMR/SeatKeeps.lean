-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/SeatKeeps.lean: AT THE PROOF FILE's SEAT (Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean: onlineFirstChainBlockTables;
Johnson/Desc/ProofFile/OnlineDescription.lean: onlineDescription): every block that the description lays in front of
the blocks behind the last link keeps a relation R on the first chain's record, FOR EVERY R THAT THE
SEAT's MAKERS KEEP (SeatKeeps R).
  SeatKeeps R okB okP: okB: A PREMISE ON THE LINKS BUILT, under which alone the frames' rows are
    asked; okP: A PREMISE ON THE HEAD's LINK's LETTERS, under which alone headOpenQ is asked (by
    default none): for a relation that names the seat's own links. WHAT IS ASKED OF R: it is
    reflexive and transitive, and EVERY MAKER OF THE SEAT in front of the blocks behind the last
    link keeps it, ONE FIELD A MAKER: the rows of the links'
    frames (Walk.Seat.framesOf), K1's firstSegmentOpening and laterAt (at a chain whose first tree bears the
    number 0), the quiet step behind the reads, K3's theStated, K4's blockAtC, K5's k5AtN, K6's
    seatedClaims, K7's blockOf, K8's whole, K9's three blocks of a closing and its batching, K11's
    headClaimMergeKind, and five texts of kind K2 (codeSwitchKind p at p.firstTree = 0, headFrontQ, headOpenQ,
    finishFrontQ, finishBehindQ).
  SeatBack R: the makers behind the last link: K12's atFinish AT THE SEAT's OWN NUMBERS AND UNDER
    ITS OWN TEST ON THE PLAN, K13's atM3, and atM4 over W's sending.
  LotKeeps R L G, lot_of: what is asked of one lot; from its own blocks and its blocks with runs.
  One theorem a lot: framesLot_keeps, k1Pure_keeps, k2Pure_keeps, k3Lot_keeps, k4Lot_keeps,
    k5LotN_keeps, k8Lot_keeps, k9Ninth_keeps, k11Lot_keeps, k6Lot_keeps, h1_whole; k12Lot_keeps,
    k13Lot_keeps, k13Lot4_keeps: their blocks stand behind the last link, so nothing is asked of
    them; k13LotEnd_keeps: the seal hands the record back.
  LotAll, lotAll_of, k12Lot_if, k13Lot_all, k13Lot4_all, twelve_all: the same for every block.
  thePure_keeps: LotsKeep R (onlineFirstChainBlockTables Z) G; thePure_all: LotsAll R (onlineFirstChainBlockTables Z) G
    (Johnson/IMR/KeepsSeat.lean).
  pub_firstTree: on the plain road Z.P.firstTree = 0.
  descPure_keeps: onlineDescription o pol lay KL = .ok F → F is fileDescBy … c, c.front = [], and every block
    of frontOf c (Johnson/Goal/Meaning/KeepsDriver.lean) is Decides R.
  descPure_flat: under SeatBack R too: every block of c.blocksInOrder THAT PASSES ITS OWN TEST ON THE PLAN is
    Decides R. descPure_end: so a yes of F.run, which holds the tests on the plan
    (FileDescription.planOk_parts_of_run), relates the first chain's first record to its last (the
    library's FileDescription.run_ok and chainAt_keeps). descPure_passes: and every record that the fold
    passes through (Keeps.Passes, chainAt_passes: Johnson/Desc/StatementGrows.lean).
  atFinish_planOk: a tool. SeatKeeps.mono: SeatKeeps goes up along an implication, but for refl,
    trans and the batching. whole_and, SeatKeeps.and: what the makers keep one by one they keep
    together (the batching too: a run of claims that keeps both keeps each).
THE SEAT: Johnson/Desc/ProofFile/Lots/PureLots.lean:
these tops stand on those lots.
OBJECT: ProofFile.onlineDescription's value. USERS: Johnson/IMR/RecSeat.lean (R := RecRel cs sh),
Johnson/IMR/GrowsSeat.lean (R := the statement grows).
-/
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.IMR.KeepsSeat
import Johnson.Goal.Meaning.RecK7
import Johnson.Goal.Meaning.RecGrows
import Johnson.Goal.Meaning.RecSeated
import Johnson.Desc.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)

variable {R : S → S → Prop} {okB : Array Stages.LinkH → Prop} {okP : K2.HeadPar → Prop}

open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame) in
/-- **WHAT IS ASKED OF A RELATION ON THE FIRST CHAIN's RECORD.** -/
structure SeatKeeps (R : S → S → Prop)
    (okB : Array Stages.LinkH → Prop := fun _ => True)
    (okP : K2.HeadPar → Prop := fun _ => True) : Prop where
  refl : ∀ s, R s s
  trans : ∀ a b c, R a b → R b c → R a c
  frames : ∀ {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame}, okB built → framesOf built first W = .ok fs → ∀ f ∈ fs,
    Fn R f.lay ∧ Fn R f.opened ∧ Fn R f.clear
  k1First : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar), gp.firstTree = 0 →
    Whole R (K1.firstSegmentOpening (Cl := Unit) q gp)
  k1Later : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)), gp.firstTree = 0 →
    Whole R (K1.laterAt (Cl := Unit) q gp link piece moment arrays)
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
  k2 : ∀ p : K2.P2, p.firstTree = 0 → Whole R (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn R (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, okP P → Fn R (K2.headOpenQ P)
  finFront : Fn R K2.finishFrontQ
  finBehind : Fn R K2.finishBehindQ

/-- **WHAT IS ASKED BESIDE, FOR THE WHOLE CHAIN**: the makers behind the last link. (Kind K2's place
there is paid by SeatKeeps' five; the seal hands the record back.) -/
structure SeatBack (R : S → S → Prop) : Prop where
  /-- AT THE SEAT's OWN NUMBERS ALONE: what the maker lays at the first chain's last test -/
  k12 : ∀ m : Johnson.G.OfPlan.Made, (K12.atFinish (H2U.p12OfMade m)).planOk = true →
    Whole R (K12.atFinish (H2U.p12OfMade m))
  k13M3 : ∀ p : K13.Where, Whole R (K13.atM3 (Cl := Unit) p)
  k13M4 : ∀ (p : K13.Where) (P : K1.Par), P.gp.firstTree = 0 →
    Whole R (K13.atM4 (Cl := Unit) p (K1.sendAtS P))

/-- Inside a link, or of no kind. -/
def Asked {Cl : Type} (b : Block S Cl) : Prop :=
  b.place.link ≠ none ∨ (b.place.kind == KindName.frame) = true

/-- What is asked of one lot. -/
def LotKeeps (R : S → S → Prop) (L : Lot) (G : Ground) : Prop :=
  (∀ b ∈ L.blocks G, Asked b → Whole R b) ∧
    ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)

theorem lot_of {L : Lot} {G : Ground} (h1 : ∀ b ∈ L.own G, Asked b → Whole R b)
    (h2 : ∀ b ∈ L.hearC G, Asked b → Whole R b)
    (h3 : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)) : LotKeeps R L G := by
  refine ⟨fun b hb ha => ?_, h3⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact retype_whole (h1 b₀ h₀ ha)
  · exact h2 b hb ha

/-- What is asked of one lot for the whole chain: every block. -/
def LotAll (R : S → S → Prop) (L : Lot) (G : Ground) : Prop :=
  (∀ b ∈ L.blocks G, Whole R b) ∧
    ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)

theorem LotAll.keep {L : Lot} {G : Ground} (K : LotAll R L G) : LotKeeps R L G :=
  ⟨fun b hb _ => K.1 b hb, K.2⟩

theorem lotAll_of {L : Lot} {G : Ground} (h1 : ∀ b ∈ L.own G, Whole R b)
    (h2 : ∀ b ∈ L.hearC G, Whole R b)
    (h3 : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f)) : LotAll R L G := by
  refine ⟨fun b hb => ?_, h3⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact retype_whole (h1 b₀ h₀)
  · exact h2 b hb

/-- A block whose decision is a step of the record alone, and which states no run, keeps what the
step keeps. -/
theorem quiet_whole {Cl : Type} {b : Block S Cl} {f : S → Except String S} (hf : Fn R f)
    (hd : ∀ s rs gs, b.decide s rs gs = f s) (hc : b.claims = []) (ha : b.after = []) :
    Whole R b :=
  ⟨fun s rs gs s' h => hf s s' (hd s rs gs ▸ h), (fun c k => by rw [hc] at k; cases k),
    (fun c k => by rw [ha] at k; cases k)⟩

theorem refuses {e : String} : Fn R fun _ => (Except.error e : Except String S) :=
  fun _ _ k => nomatch k

/-! ## The frames -/

theorem framesLot_keeps (H : SeatKeeps R okB okP) (Z : Pub) (hB : okB Z.p.built.links)
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

/-! ## K1 -/

theorem orLoud_whole {n : String} {a : Place} {w : String} {o : Option (Block S Unit)}
    (h : ∀ b, o = some b → Whole R b) : Whole R (ProofFile.orLoud n a w o) := by
  cases o with
  | some b => exact h b rfl
  | none => exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl

theorem readsBlockAt_quiet {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL}
    {Hp : Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit}
    (h : K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) : Whole Quiet b := by
  unfold K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact layers_quiet _
  · split at h
    · cases h
      exact headReads_quiet _
    · cases h

theorem readsQuietAt_quiet {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat}
    {b : Block S Unit} (h : ProofFile.readsQuietAt G l X piece = some b) : Whole Quiet b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtO_quiet h
    | exact readsBlockAt_quiet h
    | cases h

theorem k1Blocks_whole (H : SeatKeeps R okB okP) (gp : _root_.Desc.Plain.GPar)
    (h0 : gp.firstTree = 0) (quiet : K1.Quiet)
    (hq : ∀ G l X z, quiet G l X = some z → Whole R z) (G : Ground) :
    ∀ b ∈ K1.blocks gp quiet G, Whole R b := by
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
          exact Keeps.andThen_whole _ H.trans _ _ _ (H.k1Later _ _ _ _ _ _ h0)
            (hq _ _ _ z hz)
        · exact H.k1Later _ _ _ _ _ _ h0
      · exact H.k1Later _ _ _ _ _ _ h0

theorem k1Pure_keeps (H : SeatKeeps R okB okP) (Z : Pub) (h0 : Z.P.firstTree = 0) (G : Ground) :
    LotAll R (ProofFile.k1Pure Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  unfold ProofFile.k1Pure K1.lotWith at hb
  dsimp only at hb
  refine k1Blocks_whole H _ h0 _ (fun G l X z hz => ?_) G b hb
  cases hz
  exact orLoud_whole fun b hb => H.reads hb

/-! ## K2 -/

theorem finishPlace_whole (H : SeatKeeps R okB okP) (p : K2.P2) (h0 : p.firstTree = 0) :
    Whole R (K2.finishPlace p : Block S Unit) :=
  whole_same (Keeps.andThen_whole _ H.trans p.name _ _
    (Keeps.andThen_whole _ H.trans p.name
      (roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece K2.finishFrontQ) _
      (quiet_whole H.finFront (fun _ _ _ => rfl) rfl rfl) (H.k2 p h0))
    (quiet_whole (b := roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece
      K2.finishBehindQ) H.finBehind (fun _ _ _ => rfl) rfl rfl)) rfl (fun _ hx => hx) rfl

/-- Every place of kind K2 that the lot makes counts its trees from the chain's first. -/
theorem pureSpots_firstTree {Z : Pub} {G : Ground} {x : ProofFile.Spot × K2.P2}
    (h : x ∈ P1K2.pureSpots Z G) : x.2.firstTree = Z.P.firstTree := by
  unfold P1K2.pureSpots at h
  cases hs : ProofFile.spotsOf Z.cuts with
  | none =>
    rw [hs] at h
    cases h
  | some sps =>
    rw [hs] at h
    have h' : x ∈ P1K2.p2All Z G sps := h
    unfold P1K2.p2All at h'
    split at h'
    · cases h'
    · obtain ⟨sp, -, e⟩ := List.mem_filterMap.1 h'
      obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.1 e
      unfold P1K2.p2With at hp
      obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hp
      rfl

theorem k2Pure_keeps (H : SeatKeeps R okB okP) (Z : Pub) (h0 : Z.P.firstTree = 0) (G : Ground)
    (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) : LotAll R (ProofFile.k2Pure Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hb'
  split
  · exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
  · rename_i x hfind
    have hx0 : x.2.firstTree = 0 :=
      (pureSpots_firstTree (List.mem_of_find?_eq_some hfind)).trans h0
    cases hx : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact quiet_whole refuses (fun _ _ _ => rfl) rfl rfl
    | some b₀ =>
      show Whole R b₀
      unfold P1K2.pureAt at hx
      dsimp only at hx
      split at hx
      · cases hx
        exact whole_same (finishPlace_whole H x.2 hx0) rfl (fun _ hx => hx) rfl
      · obtain ⟨P, hPe, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, eP⟩ := Option.bind_eq_some_iff.1 hPe
        exact whole_same (Keeps.andThen_whole _ H.trans x.1.name (K2.codeSwitchKind x.2)
          (K2.headOpened x.1.name x.1.place P) (H.k2 _ hx0)
          (quiet_whole (H.openQ P (hP l P eP)) (fun _ _ _ => rfl) rfl rfl)) rfl (fun _ hx => hx) rfl
      · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 ho
        cases e
        exact whole_same (H.k2 x.2 hx0) rfl (fun _ hx => hx) rfl

/-! ## The lots of blocks with runs -/

theorem k3Lot_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (K3Lot.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ K3Lot.hear Z from hb)
  exact H.k3 _ _ _ _ _ _ e

theorem k4Lot_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.k4Lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
  exact whole_same (H.k4 _) rfl (fun _ hx => hx) rfl

theorem k5LotN_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (H2K5.lotN Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ H2K5.k5OwnN Z G from hb)
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 e
  exact whole_same (H.k5 _ _ _ _ e₀) rfl (fun _ hx => hx) rfl

theorem k8Lot_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (ProofFile.P1K8.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show b ∈ ProofFile.k8Whole Z G from hb)
  exact H.k8 _

theorem k11Lot_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (K11.lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact H.k11 _

theorem k6Lot_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
    LotAll R (P4.k6Lot Z) G := by
  refine lotAll_of (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  have hb' : b ∈ P4.k6Hear Z G := hb
  unfold P4.k6Hear at hb'
  obtain ⟨ms, -, e⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 hb')
  exact H.k6 e

/-! ## K9 with K10's closing -/

theorem k9Ninth_keeps (H : SeatKeeps R okB okP) (Z : Pub) (G : Ground) :
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

/-! ## «H:1» -/

theorem h1_whole (H : SeatKeeps R okB okP) (G : Ground) : ∀ b ∈ ProofFile.h1Own G, Whole R b := by
  intro b hb
  unfold ProofFile.h1Own at hb
  obtain rfl := List.mem_singleton.1 hb
  exact Keeps.andThen_whole _ H.trans _ _ _
    (guarded_whole _ _ (quiet_whole (H.front _) (fun _ _ _ => rfl) rfl rfl)) (H.k7 _ _)

/-! ## Behind the last link -/

theorem atFinish_place (m : Johnson.G.OfPlan.Made) :
    (K12.atFinish (H2U.p12OfMade m)).place = ⟨1, none, 2, .K12⟩ := by
  have e : ∀ p : K12.P12, (K12.proximityTestKind (Cl := Unit) K12.guardedProximityTestParts p).place = p.place := by
    intro p
    unfold K12.proximityTestKind
    split <;> rfl
  show (K12.proximityTestKind (Cl := Unit) K12.guardedProximityTestParts (H2U.p12OfMade m)).place = _
  rw [e]
  have e2 : ∀ (a : Place) (x : H2U.PlaceNums), (H2U.proximityTestParametersAt a x).place = a := by
    intro a x
    unfold H2U.proximityTestParametersAt
    split
    · rfl
    · split <;> rfl
  unfold H2U.p12OfMade
  dsimp only
  split
  · exact e2 _ _
  · rfl

/-- A TOOL: IT HOLDS AT EVERY R, EMPTY BY DESIGN: the lot's one block stands behind the last link
and is of a kind, so nothing is asked of it. -/
theorem k12Lot_keeps (Z : Pub) (G : Ground) : LotKeeps R (K12.lot Z) G := by
  refine lot_of (fun b hb ha => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  unfold Asked at ha
  rw [atFinish_place] at ha
  rcases ha with h | h
  · exact absurd rfl h
  · exact absurd h (by decide)

/-- A tool: it holds at every R, empty by design, as k12Lot_keeps. -/
theorem k13Lot_keeps (Z : Pub) (G : Ground) : LotKeeps R (K13.lot Z) G := by
  refine lot_of (fun b hb ha => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  rcases ha with h | h
  · exact absurd rfl h
  · cases h

/-- A tool: it holds at every R, empty by design, as k12Lot_keeps. -/
theorem k13Lot4_keeps (Z : Pub) (G : Ground) : LotKeeps R (K13.lot4 Z) G := by
  refine lot_of (fun b hb ha => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
  have hw' : K13.wBlock Z = some w := Option.mem_toList.1 hw
  unfold K13.wBlock K1.wAt at hw'
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
  rcases ha with h | h
  · exact absurd rfl h
  · cases h

theorem k13LotEnd_keeps (hr : ∀ s, R s s) (Z : Pub) (G : Ground) :
    LotAll R (K13.lotEnd Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  refine quiet_whole (f := fun s => (ChainEnd.refuse (endAsks s)).map fun _ => s)
    (fun s s' k => ?_) (fun _ _ _ => rfl) rfl rfl
  obtain ⟨_, -, rfl⟩ := Keeps.emap_ok k
  exact hr s

/-! ### the same three lots, paid -/

/-- Kind K12's lot: its one block, UNDER ITS OWN TEST ON THE PLAN. -/
theorem k12Lot_if (Hb : SeatBack R) (Z : Pub) (G : Ground) :
    (∀ b ∈ (K12.lot Z).blocks G, b.planOk = true → Whole R b) ∧
      ∀ a mk, (K12.lot Z).batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f) := by
  refine ⟨fun b hb hp => ?_, fun _ _ h => nomatch h⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    obtain rfl := List.mem_singleton.1 h₀
    exact retype_whole (Hb.k12 _ (Bool.and_eq_true _ _ ▸ hp).1)
  · exact nomatch hb

theorem k13Lot_all (Hb : SeatBack R) (Z : Pub) (G : Ground) : LotAll R (K13.lot Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact Hb.k13M3 _

theorem k13Lot4_all (Hb : SeatBack R) (Z : Pub) (h0 : Z.P.firstTree = 0) (G : Ground) :
    LotAll R (K13.lot4 Z) G := by
  refine lotAll_of (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hb
  have hw' : K13.wBlock Z = some w := Option.mem_toList.1 hw
  unfold K13.wBlock K1.wAt at hw'
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
  exact Hb.k13M4 _ _ h0

/-! ## The seat -/

/-- The twelve lots that are paid alike for both forms. -/
theorem twelve_all (H : SeatKeeps R okB okP) (Z : Pub) (hB : okB Z.p.built.links)
    (h0 : Z.P.firstTree = 0) (G : Ground) (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) :
    ∀ L ∈ [ProofFile.framesLot Z, ProofFile.k1Pure Z, ProofFile.k2Pure Z, K3Lot.lot Z, ProofFile.k4Lot Z, H2K5.lotN Z,
      ProofFile.P1K8.lot Z, ProofFile.k9Ninth Z, K11.lot Z, K13.lotEnd Z] ++ ProofFile.p4Pure Z, LotAll R L G := by
  intro L hL
  unfold ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl)
  · exact framesLot_keeps H Z hB G
  · exact k1Pure_keeps H Z h0 G
  · exact k2Pure_keeps H Z h0 G hP
  · exact k3Lot_keeps H Z G
  · exact k4Lot_keeps H Z G
  · exact k5LotN_keeps H Z G
  · exact k8Lot_keeps H Z G
  · exact k9Ninth_keeps H Z G
  · exact k11Lot_keeps H Z G
  · exact k13LotEnd_keeps H.refl Z G
  · exact k6Lot_keeps H Z G
  · exact lotAll_of (fun b hb => h1_whole H G b hb) (fun _ hb => nomatch hb)
      (fun _ _ h => nomatch h)

theorem thePure_keeps (H : SeatKeeps R okB okP) (Z : Pub) (hB : okB Z.p.built.links)
    (h0 : Z.P.firstTree = 0) (G : Ground) (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) :
    LotsKeep R (ProofFile.onlineFirstChainBlockTables Z) G := by
  have T := twelve_all H Z hB h0 G hP
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotKeeps R L G := by
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact (T L (Or.inl (Or.inl h))).keep
    · exact (T L (Or.inl (Or.inr (Or.inl h)))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inl h))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))).keep
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))))))).keep
    · exact k12Lot_keeps Z G
    · exact k13Lot_keeps Z G
    · exact k13Lot4_keeps Z G
    · exact (T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h))))))))))).keep
    · exact (T L (Or.inr h)).keep
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2⟩

theorem thePure_all (H : SeatKeeps R okB okP) (Hb : SeatBack R) (Z : Pub)
    (hB : okB Z.p.built.links) (h0 : Z.P.firstTree = 0)
    (G : Ground) (hP : ∀ l P, P1K2.pureLetters G l = some P → okP P) :
    LotsAll R (ProofFile.onlineFirstChainBlockTables Z) G := by
  have T := twelve_all H Z hB h0 G hP
  have key : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, (∀ b ∈ L.blocks G, b.planOk = true → Whole R b) ∧
      ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f) := by
    have up : ∀ {L : Lot}, LotAll R L G → (∀ b ∈ L.blocks G, b.planOk = true → Whole R b) ∧
        ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R f → Whole R (mk f) :=
      fun K => ⟨fun b hb _ => K.1 b hb, K.2⟩
    intro L hL
    unfold ProofFile.onlineFirstChainBlockTables at hL
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL T
    rcases hL with (h | h | h | h | h | h | h | h | h | rfl | rfl | rfl | h) | h
    · exact up <| T L (Or.inl (Or.inl h))
    · exact up <| T L (Or.inl (Or.inr (Or.inl h)))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl h)))))))))
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl h))))))))))
    · exact k12Lot_if Hb Z G
    · exact up (k13Lot_all Hb Z G)
    · exact up (k13Lot4_all Hb Z h0 G)
    · exact up <| T L (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr h))))))))))
    · exact up <| T L (Or.inr h)
  exact ⟨fun L hL => (key L hL).1, fun L hL => (key L hL).2⟩

/-- On the plain road a first chain takes over no tree: the number of its first tree is 0. -/
theorem pub_firstTree {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {Z : Pub} (h : ProofFile.pubPlain o pol lay KL = .ok Z) :
    Z.P.firstTree = 0 := by
  unfold ProofFile.pubPlain ProofFile.pubBy at h
  obtain ⟨m, -, h⟩ := bindE h
  dsimp only at h
  split at h
  · cases h
  · obtain ⟨_, -, h⟩ := bindE h
    obtain ⟨D, -, h⟩ := bindE h
    obtain ⟨told, -, h⟩ := bindE h
    obtain ⟨depth, -, h⟩ := bindE h
    obtain ⟨cuts, -, h⟩ := bindE h
    obtain ⟨s₀, -, h⟩ := bindE h
    cases h
    rfl

/-- **AT THE PROOF FILE's SEAT**, with a premise on the head's link's letters: AT THE BLANK LETTERS
ALONE, of which the seat's blocks are made. -/
theorem descPure_keepsP (H : SeatKeeps R okB okP) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (hP : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → ∀ G,
      ProofFile.blankBy ProofFile.pureRoad.links Z = some G → ∀ l P, P1K2.pureLetters G l = some P → okP P)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides R b := by
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, e, k0, k⟩ := pureZ_front H.refl H.trans (T := ProofFile.pureSeat o Z)
    (fun G hG => thePure_keeps H Z (hB Z hZ) (pub_firstTree hZ) G (hP Z hZ G hG)) h
  exact ⟨Z, A, B, c, hZ, e, k0, k⟩

/-- **AT THE PROOF FILE's SEAT.** -/
theorem descPure_keeps (H : SeatKeeps R okB) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Decides R b :=
  descPure_keepsP H hB (fun _ _ _ _ _ _ _ => trivial) h

/-- **AT THE PROOF FILE's SEAT, THE WHOLE FIRST CHAIN.** -/
theorem descPure_flat (H : SeatKeeps R okB) (Hb : SeatBack R) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
        ∀ b ∈ c.blocksInOrder, b.planOk = true → Decides R b := by
  obtain ⟨Z, hZ, h⟩ := ProofFile.Law.descPure_made h
  obtain ⟨A, B, c, e, k⟩ := pureZ_flat H.refl H.trans (T := ProofFile.pureSeat o Z)
    (fun G => thePure_keeps H Z (hB Z hZ) (pub_firstTree hZ) G fun _ _ _ => trivial)
    (fun G => thePure_all H Hb Z (hB Z hZ) (pub_firstTree hZ) G fun _ _ _ => trivial) h
  exact ⟨Z, A, B, c, hZ, e, k⟩

/-- **A yes of the file's decision: the first chain's last record is related to its first.** -/
theorem descPure_end (H : SeatKeeps R okB) (Hb : SeatBack R) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray}
    {F : FileDescription ProofFile.Inst} (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F) {x : ProofFile.Inst}
    {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      R (ProofFile.startS Z x.pub) e₁ := by
  obtain ⟨Z, A, B, c, hZ, rfl, k⟩ := descPure_flat H Hb hB h
  obtain ⟨e₁, -, -, -, -, -, -, -, j₁, -⟩ := (FileDescription.run_ok _ x v₁ v₂ v₃).1 hr
  have j : chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ := j₁
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := fun b hb =>
    ((FileDescription.planOk_parts_of_run hr).blocks₁ b hb).1
  exact ⟨Z, A, B, c, e₁, hZ, rfl, j,
    Keeps.chainAt_keeps R H.refl H.trans _ _ _ (fun b hb => k b hb (hp b hb)) _ _ _ j⟩

/-- **A yes of the file's decision: every record that the first chain's fold passes through is
related to the first, and the last to it** (Keeps.Passes, Johnson/Desc/StatementGrows.lean). -/
theorem descPure_passes (H : SeatKeeps R okB) (Hb : SeatBack R) {o : ProofFile.SecondHashFunctionArgument}
    {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    (hB : ∀ Z, ProofFile.pureRoad.pub o pol lay KL = .ok Z → okB Z.p.built.links)
    (h : ProofFile.onlineDescription o pol lay KL = .ok F)
    {x : ProofFile.Inst} {v₁ v₂ v₃ : Fmt.View} (hr : F.run x v₁ v₂ v₃ = true) :
    ∃ (Z : Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl) (e₁ : S),
      ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      F = ProofFile.fileDescBy o ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c ∧
      chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ ∧
      ∀ t, Keeps.Passes 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) t →
        R (ProofFile.startS Z x.pub) t ∧ R t e₁ := by
  obtain ⟨Z, A, B, c, hZ, rfl, k⟩ := descPure_flat H Hb hB h
  obtain ⟨e₁, -, -, -, -, -, -, -, j₁, -⟩ := (FileDescription.run_ok _ x v₁ v₂ v₃).1 hr
  have j : chainAt "the first chain" 0 c.blocksInOrder (ProofFile.startS Z x.pub) (withEmptySealRound v₁) = .ok e₁ := j₁
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := fun b hb =>
    ((FileDescription.planOk_parts_of_run hr).blocks₁ b hb).1
  exact ⟨Z, A, B, c, e₁, hZ, rfl, j, fun t ht =>
    Keeps.chainAt_passes R H.refl H.trans _ _ _ (fun b hb => k b hb (hp b hb)) _ _ _ j t ht⟩

/-- The door's block passes its test on the plan only where the kind's own block does. -/
theorem atFinish_planOk {p : K12.P12} (hp : (K12.atFinish p).planOk = true) :
    (K12.proximityTestKind K12.guardedProximityTestParts p : Block K12.T12 Unit).planOk = true := by
  have e : ((K12.proximityTestKind K12.guardedProximityTestParts p : Block K12.T12 Unit).planOk &&
      (K12.proximityTestKind K12.guardedProximityTestParts p : Block K12.T12 Unit).claims.isEmpty &&
      (K12.proximityTestKind K12.guardedProximityTestParts p : Block K12.T12 Unit).after.isEmpty) = true := hp
  simp only [Bool.and_eq_true] at e
  exact e.1.1

/-- **SeatKeeps goes up along an implication of relations**, but for three clauses, which are asked
anew: reflexive, transitive, and the batching (whose premise on the claims' function goes the other
way). -/
theorem SeatKeeps.mono {R' : S → S → Prop} (H : SeatKeeps R okB okP) (up : ∀ s t, R s t → R' s t)
    (hr : ∀ s, R' s s) (ht : ∀ a b c, R' a b → R' b c → R' a c)
    (hb : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl R' claims →
      Whole R' (K9.batch K9.atS p claims)) : SeatKeeps R' okB okP where
  refl := hr
  trans := ht
  frames := fun hB h f hf => ⟨fun s t k => up _ _ ((H.frames hB h f hf).1 s t k),
    fun s t k => up _ _ ((H.frames hB h f hf).2.1 s t k),
    fun s t k => up _ _ ((H.frames hB h f hf).2.2 s t k)⟩
  k1First := fun q gp h0 => whole_mono up (H.k1First q gp h0)
  k1Later := fun q gp l p m a h0 => whole_mono up (H.k1Later q gp l p m a h0)
  reads := fun h => whole_mono up (H.reads h)
  k3 := fun c r X cs sh a _ h => whole_mono up (H.k3 c r X cs sh a h)
  k4 := fun p => whole_mono up (H.k4 p)
  k5 := fun W l g bf _ h => whole_mono up (H.k5 W l g bf h)
  k6 := fun h => whole_mono up (H.k6 h)
  k7 := fun W l => whole_mono up (H.k7 W l)
  k8 := fun p => whole_mono up (H.k8 p)
  closeOf := fun p P b hb' => whole_mono up (H.closeOf p P b hb')
  batch := hb
  k11 := fun P => whole_mono up (H.k11 P)
  k2 := fun p h0 => whole_mono up (H.k2 p h0)
  front := fun tl s t k => up _ _ (H.front tl s t k)
  openQ := fun P hP s t k => up _ _ (H.openQ P hP s t k)
  finFront := fun s t k => up _ _ (H.finFront s t k)
  finBehind := fun s t k => up _ _ (H.finBehind s t k)

/-! ## Two relations at once -/

section And
variable {R₁ R₂ : S → S → Prop} {ok₁ ok₂ : Array Stages.LinkH → Prop}
  {op₁ op₂ : K2.HeadPar → Prop} {Cl : Type}

theorem whole_and {b : Block S Cl} (W₁ : Whole R₁ b) (W₂ : Whole R₂ b) :
    Whole (fun s t => R₁ s t ∧ R₂ s t) b :=
  ⟨fun s rs gs s' e => ⟨W₁.1 s rs gs s' e, W₂.1 s rs gs s' e⟩,
    fun c hc n s y e => ⟨W₁.2.1 c hc n s y e, W₂.2.1 c hc n s y e⟩,
    fun c hc s s' e => ⟨W₁.2.2 c hc s s' e, W₂.2.2 c hc s s' e⟩⟩

/-- **What the seat's makers keep one by one they keep together.** -/
theorem SeatKeeps.and (H₁ : SeatKeeps R₁ ok₁ op₁) (H₂ : SeatKeeps R₂ ok₂ op₂) :
    SeatKeeps (fun s t => R₁ s t ∧ R₂ s t) (fun b => ok₁ b ∧ ok₂ b) (fun P => op₁ P ∧ op₂ P) where
  refl := fun s => ⟨H₁.refl s, H₂.refl s⟩
  trans := fun a b c h k => ⟨H₁.trans a b c h.1 k.1, H₂.trans a b c h.2 k.2⟩
  frames := fun hB h f hf =>
    ⟨fun s t k => ⟨(H₁.frames hB.1 h f hf).1 s t k, (H₂.frames hB.2 h f hf).1 s t k⟩,
      fun s t k => ⟨(H₁.frames hB.1 h f hf).2.1 s t k, (H₂.frames hB.2 h f hf).2.1 s t k⟩,
      fun s t k => ⟨(H₁.frames hB.1 h f hf).2.2 s t k, (H₂.frames hB.2 h f hf).2.2 s t k⟩⟩
  k1First := fun q gp h0 => whole_and (H₁.k1First q gp h0) (H₂.k1First q gp h0)
  k1Later := fun q gp l p m a h0 =>
    whole_and (H₁.k1Later q gp l p m a h0) (H₂.k1Later q gp l p m a h0)
  reads := fun h => whole_and (H₁.reads h) (H₂.reads h)
  k3 := fun c r X cs sh a _ h => whole_and (H₁.k3 c r X cs sh a h) (H₂.k3 c r X cs sh a h)
  k4 := fun p => whole_and (H₁.k4 p) (H₂.k4 p)
  k5 := fun W l g bf _ h => whole_and (H₁.k5 W l g bf h) (H₂.k5 W l g bf h)
  k6 := fun h => whole_and (H₁.k6 h) (H₂.k6 h)
  k7 := fun W l => whole_and (H₁.k7 W l) (H₂.k7 W l)
  k8 := fun p => whole_and (H₁.k8 p) (H₂.k8 p)
  closeOf := fun p P b hb => whole_and (H₁.closeOf p P b hb) (H₂.closeOf p P b hb)
  batch := fun p _ hcl => whole_and (H₁.batch p fun s y e => (hcl s y e).1)
    (H₂.batch p fun s y e => (hcl s y e).2)
  k11 := fun P => whole_and (H₁.k11 P) (H₂.k11 P)
  k2 := fun p h0 => whole_and (H₁.k2 p h0) (H₂.k2 p h0)
  front := fun tl s t k => ⟨H₁.front tl s t k, H₂.front tl s t k⟩
  openQ := fun P hP s t k => ⟨H₁.openQ P hP.1 s t k, H₂.openQ P hP.2 s t k⟩
  finFront := fun s t k => ⟨H₁.finFront s t k, H₂.finFront s t k⟩
  finBehind := fun s t k => ⟨H₁.finBehind s t k, H₂.finBehind s t k⟩

end And

#print axioms thePure_keeps
#print axioms thePure_all
#print axioms descPure_keeps
#print axioms descPure_flat
#print axioms descPure_end
#print axioms descPure_passes
#print axioms SeatKeeps.mono
#print axioms SeatKeeps.and

end Meaning.K2
