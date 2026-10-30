-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/CarryLots.lean: THE
FIFTEEN LOTS OF onlineDescription's SEAT (ProofFile.onlineFirstChainBlockTables Z), WALKED ONCE, GENERAL IN A PROPERTY OF BLOCKS: what
the seat's MAKERS' blocks have, every lot's blocks have as Johnson/IMR/RootsCut.lean's LotCarry asks
it. The
like of SeatKeeps.lean ("one theorem a lot"), which is no corollary of this file:
THE WALK STANDS TWICE.

  CarriedAll Pr R₀: the property at every type of a claim (the lots' own blocks are typed at Unit
      and carried over): Carried (Johnson/Goal/Meaning/CarryDriver.lean) at each, and Block.retype
      carries it. WP: WholeP at such a property.
  retype_wp, same_wp (a block with another's rounds, decision and runs whose test on the plan holds
      the other's: a lot's conjunct more in planOk; a name; a place), quiet_qw, quiet_wp, refuses,
      retype_qw.
  SeatCarry Pr R₀: **WHAT IS ASKED: ONE FIELD A MAKER, NINETEEN FIELDS**: the rows of the links'
      frames (R₀ of lay, opened, clear) · K1's firstSegmentOpening and laterAt · the quiet step behind the
      reads · K3's theStated · K4's blockAtC · K5's k5AtN · K6's seatedClaims · K7's blockOf · K8's
      whole · K11's headClaimMergeKind · K9's three blocks of a closing and its batching (at every gatherer
      that keeps R₀) · K2's codeSwitchKind and its four quiet steps (R₀) · the seal (Pr).
  LotAllP, lotAllP_of, LotAllP.carry, kind_ne: a lot none of whose blocks is of the kind "frame": by
      AllKind (LotKinds.lean).
  One theorem a lot: framesLot_quiet, framesLot_carry · k1Pure_all (orLoud_wp, k1Blocks_wp) ·
      k2Pure_all (finishPlace_wp) · k3Lot_all · k4Lot_all · k5LotN_all · k8Lot_all · k9Ninth_all ·
      k11Lot_all · k6Lot_all · h1_all · outside_carry, k12Lot_carry, k13Lot_carry, k13Lot4_carry
      (behind the last link, of a kind: nothing is asked) · k13LotEnd_carry (the seal).
  thePure_carry: **CarriedAll Pr R₀ → SeatCarry Pr R₀ → ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotCarry Pr R₀ L G.**
      seat_frontP: so, at an opening of onlineDescription, every block of frontOf c has Pr.
AGAINST Johnson/IMR/SeatKeeps.lean's FIELDS: its side conditions (okB · "firstTree = 0" at K1 and at
K2 ·
okP) are ONE LETTER here, ok : Oks, by default "at all numbers"; OksAt ok Z
G: the seat's own numbers are among them (oksAt_all at the default);
the seal is one field more.
OBJECT: ProofFile.onlineFirstChainBlockTables Z's lots.
USER: RootsSeat.lean.
LETTERS: Pr, R₀, Z, G: free.
Compiled with the whole library.
Limits. Nothing on what any maker does. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.OnlineDescription
import Johnson.IMR.RootsCut
import Johnson.IMR.LotKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)
open ProofFile (Lot Ground Pub)

/-! ## 1 A property at every type of a claim -/

/-- **A property of blocks at every type of a claim**, which Block.retype carries too. -/
structure CarriedAll (Pr : ∀ {Cl : Type}, Block S Cl → Prop) (R₀ : S → S → Prop) : Prop where
  each : ∀ Cl : Type, Carried (T := S) (Cl := Cl) (fun b => Pr b) R₀
  retype : ∀ {Cl Cl' : Type} {b : Block S Cl}, Pr b → Pr (b.retype : Block S Cl')

/-- WholeP at such a property. -/
abbrev WP (Pr : ∀ {Cl : Type}, Block S Cl → Prop) (R₀ : S → S → Prop) {Cl : Type}
    (b : Block S Cl) : Prop := WholeP (fun b => Pr b) R₀ b

variable {Pr : ∀ {Cl : Type}, Block S Cl → Prop} {R₀ : S → S → Prop}

theorem retype_wp (C : CarriedAll Pr R₀) {Cl Cl' : Type} {b : Block S Cl} (W : WP Pr R₀ b) :
    WP Pr R₀ (b.retype : Block S Cl') := ⟨C.retype W.1, (fun _ hc => nomatch hc), W.2.2⟩

/-- A block with the rounds, the decision and the runs of another, whose test on the plan holds the
other's. -/
theorem same_wp (C : CarriedAll Pr R₀) {Cl : Type} {b c : Block S Cl} (W : WP Pr R₀ b)
    (e0 : c.rounds = b.rounds) (e1 : c.decide = b.decide)
    (ep : c.planOk = true → b.planOk = true) (e2 : ∀ x ∈ c.claims, x ∈ b.claims)
    (e3 : c.after = b.after) (e4 : c.oracles = b.oracles := by rfl) : WP Pr R₀ c :=
  ⟨(C.each Cl).under ⟨⟨e0, fun _ _ _ _ h => e1 ▸ h⟩, ep, e4⟩ W.1, fun x hx => W.2.1 x (e2 x hx),
    fun x hx => W.2.2 x (e3 ▸ hx)⟩

/-- A block without a round whose decision is a step of the record alone, and which states no
run. -/
theorem quiet_qw {Cl : Type} {b : Block S Cl} {f : S → Except String S} (hf : Fn R₀ f)
    (h0 : b.rounds = []) (hd : ∀ s rs gs, b.decide s rs gs = f s) (hc : b.claims = [])
    (ha : b.after = []) (ho : b.oracles.flatten = [] := by rfl) : QuietW R₀ b :=
  ⟨h0, ho, fun s rs gs s' h => hf s s' (hd s rs gs ▸ h), (fun c k => by rw [hc] at k; cases k),
    (fun c k => by rw [ha] at k; cases k)⟩

theorem quiet_wp (C : CarriedAll Pr R₀) {Cl : Type} {b : Block S Cl} {f : S → Except String S}
    (hf : Fn R₀ f) (h0 : b.rounds = []) (hd : ∀ s rs gs, b.decide s rs gs = f s)
    (hc : b.claims = []) (ha : b.after = []) (ho : b.oracles.flatten = [] := by rfl) :
    WP Pr R₀ b :=
  (quiet_qw hf h0 hd hc ha ho).wholeP (C.each Cl)

theorem refuses {e : String} : Fn R₀ fun _ => (Except.error e : Except String S) :=
  fun _ _ k => nomatch k

theorem retype_qw {Cl Cl' : Type} {b : Block S Cl} (W : QuietW R₀ b) :
    QuietW R₀ (b.retype : Block S Cl') :=
  ⟨W.1, W.2.1, W.2.2.1, (fun _ hc => nomatch hc), W.2.2.2.2⟩

/-! ## 2 What is asked: one field a maker -/

/-- At which numbers four of the fields are asked; by default at all. -/
structure Oks where
  /-- the links as built, at the rows of the links' frames -/
  B : Array Stages.LinkH → Prop := fun _ => True
  /-- K1's two numbers of the plan -/
  g : _root_.Desc.Plain.GPar → Prop := fun _ => True
  /-- the head's link's letters, at the step that opens it -/
  P : K2.HeadPar → Prop := fun _ => True
  /-- a code switch's numbers -/
  p2 : K2.P2 → Prop := fun _ => True

/-- The seat's own numbers, at the public part Z and the letters G, are among them. -/
structure OksAt (ok : Oks) (Z : Pub) (G : Ground) : Prop where
  B : ok.B Z.p.built.links
  g : ok.g (K1.gpOf Z)
  P : ∀ l P, P1K2.pureLetters G l = some P → ok.P P
  p2 : ∀ x ∈ P1K2.pureSpots Z G, ok.p2 x.2

theorem oksAt_all (Z : Pub) (G : Ground) : OksAt {} Z G :=
  ⟨trivial, trivial, fun _ _ _ => trivial, fun _ _ => trivial⟩

open Johnson.Desc.First.Walk.Seat (framesOf LinkFrame) in
/-- **WHAT IS ASKED OF THE SEAT's MAKERS** in front of the blocks behind the last link. -/
structure SeatCarry (Pr : ∀ {Cl : Type}, Block S Cl → Prop) (R₀ : S → S → Prop)
    (ok : Oks := {}) : Prop where
  frames : ∀ {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame}, ok.B built → framesOf built first W = .ok fs → ∀ f ∈ fs,
    Fn R₀ f.lay ∧ Fn R₀ f.opened ∧ Fn R₀ f.clear
  k1First : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar), ok.g gp →
    WP Pr R₀ (K1.firstSegmentOpening (Cl := Unit) q gp)
  k1Later : ∀ (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)), ok.g gp →
    WP Pr R₀ (K1.laterAt (Cl := Unit) q gp link piece moment arrays)
  reads : ∀ {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit},
    ProofFile.readsQuietAt G l X piece = some b → WP Pr R₀ b
  k3 : ∀ (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S)) (X : Verify.Public)
    (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl},
    K3.theStated claim readers X codes shape a = some b → WP Pr R₀ b
  k4 : ∀ p : OnBytes.Desc.First.K4.Par, WP Pr R₀ (OnBytes.Desc.First.K4.blockAtC p)
  k5 : ∀ (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim},
    Att.P.k5AtN W l g before = some b → WP Pr R₀ b
  k6 : ∀ {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim},
    Kinds.Head.seatedClaims W l before = some b → WP Pr R₀ b
  k7 : ∀ (W : Verify.Public) (l : Nat), WP Pr R₀ (Kinds.Reply.blockOf W l)
  k8 : ∀ p : K8.ParW, WP Pr R₀ (K8.whole p)
  k11 : ∀ P : Johnson.Desc.First.ForkMerge.HeadMergeP,
    WP Pr R₀ (Johnson.Desc.First.ForkMerge.headClaimMergeKind P)
  closeOf : ∀ (p : K9.Where) (P : Close.Par), ∀ b ∈ K9.closeOf (Cl := Unit) p P, WP Pr R₀ b
  batch : ∀ (p : K9.Where) {claims : S → Except String (List Claim × S)}, FnCl R₀ claims →
    WP Pr R₀ (K9.batch K9.atS p claims)
  k2 : ∀ p : K2.P2, ok.p2 p → WP Pr R₀ (K2.codeSwitchKind p : Block S Unit)
  front : ∀ tl : HTailF2, Fn R₀ (K2.headFrontQ tl)
  openQ : ∀ P : K2.HeadPar, ok.P P → Fn R₀ (K2.headOpenQ P)
  finFront : Fn R₀ K2.finishFrontQ
  finBehind : Fn R₀ K2.finishBehindQ
  /-- the seal: of the kind "frame", outside the links, with a round -/
  theSeal : ∀ (inFront : List Fmt.DeclaredRound),
    Pr (ChainEnd.chainEnd 1 5 true inFront endAsks : Block S Unit)

/-! ## 3 One lot -/

/-- Every block of the lot, wherever it stands. -/
def LotAllP (Pr : ∀ {Cl : Type}, Block S Cl → Prop) (R₀ : S → S → Prop) (L : Lot) (G : Ground) :
    Prop :=
  (∀ b ∈ L.blocks G, WP Pr R₀ b) ∧
    ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R₀ f → WP Pr R₀ (mk f)

theorem lotAllP_of (C : CarriedAll Pr R₀) {L : Lot} {G : Ground}
    (h1 : ∀ b ∈ L.own G, WP Pr R₀ b) (h2 : ∀ b ∈ L.hearC G, WP Pr R₀ b)
    (h3 : ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R₀ f → WP Pr R₀ (mk f)) :
    LotAllP Pr R₀ L G := by
  refine ⟨fun b hb => ?_, h3⟩
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 hb
    exact retype_wp C (h1 b₀ h₀)
  · exact h2 b hb

/-- A lot none of whose blocks is of the kind "frame". -/
theorem LotAllP.carry {L : Lot} {G : Ground} (K : LotAllP Pr R₀ L G)
    (hk : ∀ b ∈ L.blocks G, b.place.kind ≠ KindName.frame) :
    LotCarry (fun b => Pr b) R₀ L G where
  blocks b hb _ := K.1 b hb
  framesIn b hb h _ := absurd (eq_of_beq h) (hk b hb)
  framesOut b hb h _ := absurd (eq_of_beq h) (hk b hb)
  batch := K.2

theorem kind_ne {L : Lot} {G : Ground} {k : KindName} (h : IM.AllKind L G k)
    (hne : k ≠ KindName.frame) : ∀ b ∈ L.blocks G, b.place.kind ≠ KindName.frame :=
  fun b hb e => hne ((h b hb).symm.trans e)

/-! ## 4 The lots -/

section
variable {ok : Oks} (C : CarriedAll Pr R₀) (H : SeatCarry Pr R₀ ok)
include C H

omit C in
/-- The frames' lot: no round; R₀. -/
theorem framesLot_quiet (Z : Pub) (hB : ok.B Z.p.built.links) (G : Ground) :
    ∀ b ∈ (ProofFile.framesLot Z).blocks G, QuietW R₀ b := by
  intro b hb
  rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · refine retype_qw ?_
    have hb' : x ∈ P1L20.blocksOf Z := hx
    unfold P1L20.blocksOf at hb'
    split at hb'
    · rename_i fs hfs
      obtain ⟨f, hf, hb'⟩ := List.mem_flatMap.1 hb'
      obtain ⟨k1, k2, k3⟩ := H.frames hB hfs f hf
      unfold ProofFile.frameBlocks at hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      rcases hb' with rfl | rfl | rfl
      · exact quiet_qw k1 rfl (fun _ _ _ => rfl) rfl rfl
      · exact quiet_qw k2 rfl (fun _ _ _ => rfl) rfl rfl
      · exact quiet_qw k3 rfl (fun _ _ _ => rfl) rfl rfl
    · obtain rfl := List.mem_singleton.1 hb'
      exact quiet_qw refuses rfl (fun _ _ _ => rfl) rfl rfl
  · exact nomatch hb

theorem framesLot_carry (Z : Pub) (hB : ok.B Z.p.built.links) (G : Ground) :
    LotCarry (fun b => Pr b) R₀ (ProofFile.framesLot Z) G where
  blocks b hb _ := (framesLot_quiet H Z hB G b hb).wholeP (C.each _)
  framesIn b hb _ _ := framesLot_quiet H Z hB G b hb
  framesOut b hb _ _ := ((framesLot_quiet H Z hB G b hb).wholeP (C.each _)).1
  batch _ _ h := nomatch h

theorem k3Lot_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (K3Lot.lot Z) G := by
  refine lotAllP_of C (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ K3Lot.hear Z from hb)
  exact H.k3 _ _ _ _ _ _ e

theorem k8Lot_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (ProofFile.P1K8.lot Z) G := by
  refine lotAllP_of C (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show b ∈ ProofFile.k8Whole Z G from hb)
  exact H.k8 _

theorem k6Lot_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (P4.k6Lot Z) G := by
  refine lotAllP_of C (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  have hb' : b ∈ P4.k6Hear Z G := hb
  unfold P4.k6Hear at hb'
  obtain ⟨ms, -, e⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 hb')
  exact H.k6 e

theorem k9Ninth_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (ProofFile.k9Ninth Z) G := by
  refine lotAllP_of C (fun b hb => ?_) (fun _ hb => nomatch hb) (fun a mk h f hf => ?_)
  · unfold ProofFile.k9Ninth at hb
    dsimp only at hb
    obtain ⟨w, -, hb⟩ := List.mem_flatMap.1 hb
    split at hb
    · exact H.closeOf _ _ b hb
    · obtain rfl := List.mem_singleton.1 hb
      exact quiet_wp C refuses rfl (fun _ _ _ => rfl) rfl rfl
  · unfold ProofFile.k9Ninth at h
    dsimp only at h
    split at h
    · obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
      split at h
      · cases h
        exact H.batch p hf
      · cases h
    · cases h

theorem k4Lot_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (ProofFile.k4Lot Z) G := by
  refine lotAllP_of C (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
  exact same_wp C (H.k4 { x.2 with k3Runs := true }) rfl rfl
    (fun h => ((Bool.and_eq_true _ _).mp h).1) (fun _ hx => hx) rfl

theorem k5LotN_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (H2K5.lotN Z) G := by
  refine lotAllP_of C (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain ⟨x, -, e⟩ := List.mem_filterMap.1 (show b ∈ H2K5.k5OwnN Z G from hb)
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 e
  exact same_wp C (H.k5 _ _ _ _ e₀) rfl rfl (fun h => (Bool.and_eq_true _ _ ▸ h).1)
    (fun _ hx => hx) rfl

theorem k11Lot_all (Z : Pub) (G : Ground) : LotAllP Pr R₀ (K11.lot Z) G := by
  refine lotAllP_of C (fun _ hb => nomatch hb) (fun b hb => ?_) (fun _ _ h => nomatch h)
  obtain rfl := List.mem_singleton.1 hb
  exact same_wp C (H.k11 _) rfl rfl (fun h => (Bool.and_eq_true _ _ ▸ h).1) (fun _ hx => hx) rfl

/-! ### K1 -/

omit H in
theorem orLoud_wp {n : String} {a : Place} {w : String} {o : Option (Block S Unit)}
    (h : ∀ b, o = some b → WP Pr R₀ b) : WP Pr R₀ (ProofFile.orLoud n a w o) := by
  cases o with
  | some b => exact h b rfl
  | none => exact quiet_wp C refuses rfl (fun _ _ _ => rfl) rfl rfl

theorem k1Blocks_wp (gp : _root_.Desc.Plain.GPar) (hg : ok.g gp) (quiet : K1.Quiet)
    (hq : ∀ G l X z, quiet G l X = some z → WP Pr R₀ z) (G : Ground) :
    ∀ b ∈ K1.blocks gp quiet G, WP Pr R₀ b := by
  intro b hb
  unfold K1.blocks at hb
  dsimp only at hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain rfl := List.mem_singleton.1 hb
    exact H.k1First _ _ hg
  · obtain ⟨⟨X, l⟩, -, hb⟩ := List.mem_flatMap.1 hb
    dsimp only at hb
    split at hb
    · cases hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl
      · split
        · rename_i z hz
          exact andThen_wholeP (C.each _) _ (H.k1Later _ _ _ _ _ _ hg) (hq _ _ _ z hz)
        · exact H.k1Later _ _ _ _ _ _ hg
      · exact H.k1Later _ _ _ _ _ _ hg

theorem k1Pure_all (Z : Pub) (hg : ok.g (K1.gpOf Z)) (G : Ground) :
    LotAllP Pr R₀ (ProofFile.k1Pure Z) G := by
  refine lotAllP_of C (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  unfold ProofFile.k1Pure K1.lotWith at hb
  dsimp only at hb
  refine k1Blocks_wp C H _ hg _ (fun G l X z hz => ?_) G b hb
  cases hz
  exact orLoud_wp C fun b hb => H.reads hb

/-! ### K2 -/

theorem finishPlace_wp (p : K2.P2) (hp : ok.p2 p) :
    WP Pr R₀ (K2.finishPlace p : Block S Unit) :=
  same_wp C (andThen_wholeP (C.each _) p.name
    (andThen_wholeP (C.each _) p.name
      (p := roundlessBlock (p.name ++ ": front") p.place.chain p.place.link p.place.piece
        K2.finishFrontQ)
      (quiet_wp C H.finFront rfl (fun _ _ _ => rfl) rfl rfl) (H.k2 p hp))
    (quiet_wp C (b := roundlessBlock (p.name ++ ": behind") p.place.chain p.place.link p.place.piece
      K2.finishBehindQ) H.finBehind rfl (fun _ _ _ => rfl) rfl rfl)) rfl rfl (fun h => h)
    (fun _ hx => hx) rfl

theorem k2Pure_all (Z : Pub) (G : Ground) (hok : ∀ x ∈ P1K2.pureSpots Z G, ok.p2 x.2)
    (hP : ∀ l P, P1K2.pureLetters G l = some P → ok.P P) :
    LotAllP Pr R₀ (ProofFile.k2Pure Z) G := by
  refine lotAllP_of C (fun b hb => ?_) (fun _ hb => nomatch hb) (fun _ _ h => nomatch h)
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, -, rfl⟩ := List.mem_map.1 hb'
  split
  · exact quiet_wp C refuses rfl (fun _ _ _ => rfl) rfl rfl
  · rename_i x hfind
    have hx2 : ok.p2 x.2 := hok x (List.mem_of_find?_eq_some hfind)
    cases hx : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact quiet_wp C refuses rfl (fun _ _ _ => rfl) rfl rfl
    | some b₀ =>
      show WP Pr R₀ b₀
      unfold P1K2.pureAt at hx
      dsimp only at hx
      split at hx
      · cases hx
        exact same_wp C (finishPlace_wp C H x.2 hx2) rfl rfl (fun h => h) (fun _ hx => hx) rfl
      · obtain ⟨P, hPe, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, eP⟩ := Option.bind_eq_some_iff.1 hPe
        exact same_wp C (andThen_wholeP (C.each _) x.1.name (p := K2.codeSwitchKind x.2)
          (q := K2.headOpened x.1.name x.1.place P) (H.k2 _ hx2)
          (quiet_wp C (H.openQ P (hP l P eP)) rfl (fun _ _ _ => rfl) rfl rfl)) rfl rfl (fun h => h)
          (fun _ hx => hx) rfl
      · obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hx
        obtain ⟨l, -, e⟩ := Option.bind_eq_some_iff.1 ho
        cases e
        exact same_wp C (H.k2 x.2 hx2) rfl rfl (fun h => h) (fun _ hx => hx) rfl

theorem h1_all (G : Ground) : ∀ b ∈ ProofFile.h1Own G, WP Pr R₀ b := by
  intro b hb
  unfold ProofFile.h1Own at hb
  obtain rfl := List.mem_singleton.1 hb
  exact andThen_wholeP (C.each _) _
    (guarded_wholeP (C.each _) _ _ (quiet_wp C (H.front _) rfl (fun _ _ _ => rfl) rfl rfl))
    (H.k7 _ _)

/-! ### Behind the last link: nothing is asked inside a link -/

omit C H in
/-- A lot all of whose blocks stand outside the links and are of a kind other than "frame", and
which gives no batching. -/
theorem outside_carry {L : Lot} {G : Ground} (hl : ∀ b ∈ L.blocks G, b.place.link = none)
    (hk : ∀ b ∈ L.blocks G, b.place.kind ≠ KindName.frame) (hb : ∀ a, L.batch G a = none) :
    LotCarry (fun b => Pr b) R₀ L G where
  blocks b hb' h := absurd (hl b hb') h
  framesIn b hb' h _ := absurd (eq_of_beq h) (hk b hb')
  framesOut b hb' h _ := absurd (eq_of_beq h) (hk b hb')
  batch a mk h := by rw [hb a] at h; cases h

omit C H in
theorem k12Lot_carry (Z : Pub) (G : Ground) : LotCarry (fun b => Pr b) R₀ (K12.lot Z) G := by
  refine outside_carry (fun b hb => ?_) (kind_ne (IM.kind_K12 Z G) (by decide)) (fun _ => rfl)
  rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · obtain rfl := List.mem_singleton.1 hx
    show (K12.proximityTestKind K12.guardedProximityTestParts (H2U.p12OfMade Z.made) : Block K12.T12 Unit).place.link = none
    rw [IM.k12_place, IM.p12_place]
  · exact nomatch hb

omit C H in
theorem k13Lot_carry (Z : Pub) (G : Ground) : LotCarry (fun b => Pr b) R₀ (K13.lot Z) G := by
  refine outside_carry (fun b hb => ?_) (kind_ne (IM.kind_K13 Z G) (by decide)) (fun _ => rfl)
  rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · obtain rfl := List.mem_singleton.1 hx
    rfl
  · exact nomatch hb

omit C H in
theorem k13Lot4_carry (Z : Pub) (G : Ground) : LotCarry (fun b => Pr b) R₀ (K13.lot4 Z) G := by
  refine outside_carry (fun b hb => ?_) (kind_ne (IM.kind_K13_4 Z G) (by decide)) (fun _ => rfl)
  rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    have hw' : K13.wBlock Z = some w := Option.mem_toList.1 hw
    unfold K13.wBlock K1.wAt at hw'
    obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
    rfl
  · exact nomatch hb

/-- The seal: of the kind "frame", outside the links. -/
theorem k13LotEnd_carry (Z : Pub) (G : Ground) :
    LotCarry (fun b => Pr b) R₀ (K13.lotEnd Z) G := by
  have key : ∀ b ∈ (K13.lotEnd Z).blocks G, b.place.link = none ∧ Pr b := by
    intro b hb
    rcases IM.blocks_mem hb with ⟨x, hx, rfl⟩ | hb
    · obtain rfl := List.mem_singleton.1 hx
      exact ⟨rfl, C.retype (H.theSeal _)⟩
    · exact nomatch hb
  exact ⟨fun b hb h => absurd (key b hb).1 h, fun b hb _ h => absurd (key b hb).1 h,
    fun b hb _ _ => (key b hb).2, fun _ _ h => nomatch h⟩

/-! ## 5 The seat -/

/-- **Every lot of onlineDescription's seat.** -/
theorem thePure_carry (Z : Pub) (G : Ground) (hok : OksAt ok Z G) :
    ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, LotCarry (fun b => Pr b) R₀ L G := by
  intro L hL
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    rfl | rfl
  · exact framesLot_carry C H Z hok.B G
  · exact (k1Pure_all C H Z hok.g G).carry (kind_ne (IM.kind_K1 Z G) (by decide))
  · exact (k2Pure_all C H Z G hok.p2 hok.P).carry (kind_ne (IM.kind_K2 Z G) (by decide))
  · exact (k3Lot_all C H Z G).carry (kind_ne (IM.kind_K3 Z G) (by decide))
  · exact (k4Lot_all C H Z G).carry (kind_ne (IM.kind_K4 Z G) (by decide))
  · exact (k5LotN_all C H Z G).carry (kind_ne (IM.kind_K5 Z G) (by decide))
  · exact (k8Lot_all C H Z G).carry (kind_ne (IM.kind_K8 Z G) (by decide))
  · exact (k9Ninth_all C H Z G).carry fun b hb e => by
      rcases IM.kind_K9 Z G b hb with h | h <;> rw [h] at e <;> cases e
  · exact (k11Lot_all C H Z G).carry (kind_ne (IM.kind_K11 Z G) (by decide))
  · exact k12Lot_carry Z G
  · exact k13Lot_carry Z G
  · exact k13Lot4_carry Z G
  · exact k13LotEnd_carry C H Z G
  · exact (k6Lot_all C H Z G).carry (kind_ne (IM.kind_K6 Z G) (by decide))
  · exact (lotAllP_of C (h1_all C H G) (fun _ hb => absurd hb List.not_mem_nil)
      (fun _ mk h => nomatch (show none = some mk from h))).carry
      (kind_ne (IM.kind_K7_lot rfl rfl) (by decide))

/-- **At an opening of onlineDescription: every block in front of the blocks behind the last link has the
property that the seat's makers' blocks have.** -/
theorem seat_frontP {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
    {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
    {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B)
    (hok : OksAt ok Z Bs.G₀) :
    c.blocksInOrder = Meaning.K2.frontOf c ++ Meaning.K2.backOf c ∧ ∀ b ∈ Meaning.K2.frontOf c, Pr b :=
  open_frontP (C.each _) O (thePure_carry C H Z Bs.G₀ hok)

end

#print axioms thePure_carry
#print axioms seat_frontP

end Meaning.Carry
