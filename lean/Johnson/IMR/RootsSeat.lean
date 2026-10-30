-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/RootsSeat.lean:
EVERY MAKER OF onlineDescription's SEAT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, AND THE SEAL: a yes of
its block's decision adds to the record's count of roots JUST WHAT THE BLOCK's DECLARED ROUNDS SEND
(K12's RootsStep), and every run leaves the count. SO THE COUNT OF ROOTS AT EVERY CUT OF THE FIRST
CHAIN's FLAT LIST IN FRONT OF THE BLOCKS BEHIND THE LAST LINK IS WHAT THE DECLARED ROUNDS IN FRONT
SEND: NONE OF SeatCarry's NINETEEN FIELDS IS LEFT AS A HYPOTHESIS.

Main theorems (namespace Meaning.Carry).
  seatCarry_roots: SeatCarry RootsStep "the count stays" (Johnson/IMR/CarryLots.lean): all nineteen
    fields.
  roots_at_cut_paid: **O : Open o pol lay KL F Z Bs base c A B · k ≤ (frontOf c).length · every
      block of c.blocksInOrder.take k passes its test on the plan · foldBlocks ft (c.blocksInOrder.take k) s rs cols =
      .ok r ⇒ r.1.roots = s.roots + rootsOf (declOf (c.blocksInOrder.take k)).** AT EVERY o, ANY FIRST RECORD
      s, ANY ft; from the fold's return alone. No "there is" stands in it.
HOW EACH FIELD IS PROVED.
  THE RECORD's SIDE OF WHOEVER SENDS NOTHING: CALLS of framesOf_core, closeOf_core,
      batch_core (Johnson/Goal/Meaning/CoreSeated.lean) at RcRoots, and of the Whole Quiet lemmas
      through whole_core: readsQuietAt_quiet, theStated_quiet, blockAtC_quiet, k5AtN_quiet,
      seatedClaims_quiet, k7Of_quiet, k8Whole_quiet, headMerge11_quiet. K2's four quiet steps:
      headFrontQ_book, headOpenQ_book, finishFrontQ_book, finishBehindQ_book
      (Johnson/Top/H0/Tw/K2C/BookKept.lean).
  THE PLAN's SIDE (rootsOf ‹maker›.rounds = 0), TYPED HERE: k7_rounds, k8_rounds, batch_rounds0: rfl
      · k4_rounds, k5_rounds (maskedSum_roots, k5Entries_roots), k6_rounds, k11_rounds,
      closeOf_rounds, reads_rounds: by the entries' texts · k3Own_rounds, k3_rounds: UNDER THE
      BLOCK's OWN TEST ON THE PLAN: fitsVia asks staticT of every entry, which holds "roots == 0":
      the planner's text (lookEntries) is not opened.
  THE SENDERS. K1: firstAtS_step, commitAtS_step: K1's firstAtS_seated, commitAtS_seated
      (field roots) with trees_eq_lay; send_two (a yes is a yes on two rounds) and k1_rounds are
      typed here. K2: k2_roots, k2_step: by the guard in the switch's own text (K2C/Closed.lean:
      SwitchIs.hTrees, hRoots); the walk through the three arms is yes_book's.
  THE SEAL: chainEnd_roots (Johnson/Desc/K13/Law/RootsBehind.lean).
OBJECT · LETTERS. Object: c := F.first, F := ProofFile.onlineDescription o's value; not verify().
Letters: none.
WHAT CAN PROVE THE ONE PREMISE: the tests on the plan: F.planOk (a yes of F.run holds it).
OVER WHICH FILES: this folder's seats · CoreSeated, RecSeated, SeatKeeps
and what lies beneath · RootsFold.lean · RootsBehind.lean, SeatedM4.lean, K13/Law/AtRecord.lean,
K1/Law/SeatedAtRecord.lean, BookAtRecord.lean · Book/BookFits.lean, BookFitsGround.lean,
Seated.lean.



Compiled with the whole library.
Limits. Nothing behind the last link (there: Johnson/IMR/RootsEnd.lean). No member. Book-keeping: no
draw, no
error. Nothing on soundness.
-/
import Johnson.IMR.CarryLots
import Johnson.Goal.Meaning.CoreSeated
import Johnson.Goal.Meaning.RecSeated
import Johnson.IMR.SeatKeeps
import Johnson.Top.H0.Tw.K2C.BookKept
import Johnson.Desc.Kinds.Law.SeatedBridge
import Johnson.Desc.K13.Law.RootsBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open VerifiableInference.Desc.Ground (Core ByC)
open VerifiableInference.Desc.K1.RelCore (coreS)
open H2K.First (RootsStep rootsStep_quiet)
open Johnson.G.OfPlan (rootsOf)
open ProofFile (Lot Ground Pub)

/-- The count of roots is as it was. -/
abbrev SameR : S → S → Prop := Same fun s : S => s.roots

/-- The same on the three that the plain ground writes. -/
def RcRoots : Core → Core → Prop := fun a b => b.roots = a.roots

theorem rc_same : ∀ a b : Core, b.book = a.book → b.roots = a.roots → RcRoots a b :=
  fun _ _ _ h => h

theorem whole_of_core {Cl : Type} {b : Block S Cl} (W : Whole (ByC RcRoots coreS) b) :
    Whole SameR b := W

theorem whole_of_quiet {Cl : Type} {b : Block S Cl} (W : Whole Meaning.K2.Quiet b) :
    Whole SameR b := whole_of_core (Meaning.K2.whole_core rc_same W)

/-! ## The plan's side -/

theorem rootsOf_zero {l : List Fmt.DeclaredRound} (h : ∀ r ∈ l, r.entry.roots = 0) : rootsOf l = 0 := by
  unfold rootsOf
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx
    exact h r hr

theorem k8_rounds (p : K8.ParW) : rootsOf (K8.whole p).rounds = 0 := rfl

theorem k4_rounds (p : OnBytes.Desc.First.K4.Par) :
    rootsOf (OnBytes.Desc.First.K4.blockAtC p).rounds = 0 := by
  refine rootsOf_zero fun r hr => ?_
  have hr' : r ∈ (OnBytes.Desc.First.K4.entries p.P p.hp p.g).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
  obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
  rfl

theorem k7_rounds (W : Verify.Public) (l : Nat) :
    rootsOf (Kinds.Reply.blockOf W l).rounds = 0 := by
  rfl

theorem k11_rounds (P : Johnson.Desc.First.ForkMerge.HeadMergeP) :
    rootsOf (Johnson.Desc.First.ForkMerge.headClaimMergeKind P).rounds = 0 := by
  refine rootsOf_zero fun r hr => ?_
  have hr' : r ∈ (Johnson.Desc.First.ForkMerge.mergeEntries P.lay.lk 1 P.work).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
  unfold Johnson.Desc.First.ForkMerge.mergeEntries at he
  simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | ⟨-, rfl⟩ | rfl | rfl <;> rfl

theorem batch_rounds0 (p : K9.Where) (claims : S → Except String (List Claim × S)) :
    rootsOf (K9.batch K9.atS p claims).rounds = 0 := by
  rfl

theorem closeOf_rounds (p : K9.Where) (P : Close.Par) :
    ∀ b ∈ K9.closeOf (Cl := Unit) p P, rootsOf b.rounds = 0 := by
  intro b hb
  unfold K9.closeOf at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl
  · rfl
  · refine rootsOf_zero fun r hr => ?_
    have hr' : r ∈ (Close.entries P).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
    unfold Close.entries at he
    simp only [List.mem_cons, List.mem_replicate] at he
    rcases he with rfl | rfl | ⟨-, rfl⟩ <;> rfl
  · rfl

theorem reads_rounds {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : rootsOf b.rounds = 0 := by
  have hA : ∀ {W : Verify.Public} {l g : Nat} {b : Block S Unit}, Att.readsAtO W l g = some b →
      rootsOf b.rounds = 0 := by
    intro W l g b h
    unfold Att.readsAtO at h
    obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  have hB : ∀ {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL} {Hp : Head.HPlanH2}
      {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit},
      K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b → rootsOf b.rounds = 0 := by
    intro G hS HLy Hp kinds l b h
    unfold K8.ReadsQuiet.blockAt at h
    obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
    split at h
    · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
      rfl
    · split at h
      · cases h
        rfl
      · cases h
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact hA h
    | exact hB h
    | cases h

/-- K3's own block: UNDER ITS OWN TEST ON THE PLAN, which asks of every entry the tests of the
strict reading that read the entry alone (staticT: no root among them). -/
theorem k3Own_rounds {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) (hp : b.planOk = true) :
    rootsOf b.rounds = 0 := by
  unfold K3.theOwn at h
  split at h
  · cases h
  obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨digits, -, h⟩ := List.exists_of_findSome?_eq_some h
  split at h
  · cases h
  obtain ⟨p, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨sent, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨laid, -, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨key, -, h⟩ := Option.map_eq_some_iff.1 h
  have e : b.rounds = p.rounds ∧ (b.planOk = true → K3.Law.fitsVia p = true) := by
    dsimp only at h
    split at h
    · subst h
      refine ⟨rfl, fun k => ?_⟩
      have k' : ((K3.planOk p laid [] && K3.Law.fitsVia p) && key) = true := k
      simp only [Bool.and_eq_true] at k'
      exact k'.1.2
    · subst h
      refine ⟨rfl, fun k => ?_⟩
      have k' : ((K3.planOk p laid [] && K3.Law.fitsVia p) && key) = true := k
      simp only [Bool.and_eq_true] at k'
      exact k'.1.2
  rw [e.1]
  have hf := e.2 hp
  unfold K3.Law.fitsVia at hf
  split at hf
  · simp only [Bool.and_eq_true, List.all_eq_true] at hf
    refine rootsOf_zero fun r hr => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    have hs := hf.2 x hx
    unfold K3.staticT at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    exact hs.2.1.1
  · cases hf

theorem k3_rounds (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl}
    (h : K3.theStated claim readers X codes shape a = some b) (hp : b.planOk = true) :
    rootsOf b.rounds = 0 := by
  unfold K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have e : b.rounds = w.rounds ∧ b.planOk = w.planOk := by
    split at h
    · cases h
      exact ⟨rfl, rfl⟩
    · split at h
      · cases h
        exact ⟨rfl, rfl⟩
      · split at h
        · cases h
          exact ⟨rfl, rfl⟩
        · obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
          exact ⟨rfl, rfl⟩
  rw [e.1]
  rw [e.2] at hp
  unfold K3.theWhole at hw
  obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hw
  cases hq : (a.link.bind fun i => K3.quietAt X i (a.piece == K3.pieceAt X i true)) with
  | some f =>
    simp only [hq] at hp ⊢
    have hp' : (o.planOk && true) = true := hp
    rw [Bool.and_true] at hp'
    show rootsOf (o.rounds ++ []) = 0
    rw [List.append_nil]
    exact k3Own_rounds claim true X codes shape a ho hp'
  | none =>
    simp only [hq] at hp ⊢
    exact k3Own_rounds claim true X codes shape a ho hp

theorem maskedSum_roots (k : Part.MaskedSum.Call) :
    ∀ e ∈ Part.MaskedSum.entries k, e.roots = 0 := by
  intro e he
  unfold Part.MaskedSum.entries at he
  rcases List.mem_append.1 he with he | he
  · rcases List.mem_append.1 he with he | he
    · obtain rfl := List.mem_singleton.1 he
      rfl
    · obtain ⟨v, -, rfl⟩ := List.mem_map.1 he
      rfl
  · split at he
    · cases he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl <;> rfl

theorem k5Entries_roots : ∀ (l : List Att.P.Stage) (lead : Nat),
    ∀ e ∈ Att.P.entriesOf lead l, e.roots = 0
  | [], _, e, he => by cases he
  | .scalars n :: l, lead, e, he => k5Entries_roots l (lead + n) e he
  | .sum vs x :: l, lead, e, he => by
    rcases List.mem_append.1 (show e ∈ Part.MaskedSum.entries ⟨lead, vs, some x⟩ ++
      Att.P.entriesOf 0 l from he) with he | he
    · exact maskedSum_roots _ e he
    · exact k5Entries_roots l 0 e he
  | .batch rows :: l, lead, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact k5Entries_roots l 0 e he
  | .point n :: l, lead, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact k5Entries_roots l 0 e he

theorem k5_rounds (W : Verify.Public) (l g : Nat) (before : List (Nat × Nat)) {b : Block S Claim}
    (h : Att.P.k5AtN W l g before = some b) : rootsOf b.rounds = 0 := by
  unfold Att.P.k5AtN at h
  obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
  refine rootsOf_zero fun r hr => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (show r ∈ (Att.P.entriesOf 0 (Att.P.script p.own)).map _
    from hr)
  have h0 := k5Entries_roots _ _ e he
  dsimp only
  split
  · exact h0
  · exact h0

theorem k6_rounds {W : Verify.Public} {l : Nat} {before : List (Nat × Nat)} {b : Block S Claim}
    (h : Kinds.Head.seatedClaims W l before = some b) : rootsOf b.rounds = 0 := by
  obtain ⟨b0, h0, rfl⟩ := Kinds.Head.Law.seatedClaims_some h
  unfold Kinds.Head.blockClaims at h0
  obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
  refine rootsOf_zero fun r hr => ?_
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show r ∈ List.map _ _ from hr)
  rfl

/-! ## The senders -/

open _root_.Tw.K2 (switchBehind sendByL8) in
/-- **K2: a yes of the switch adds to the count just what its declared rounds send**: by the guard
that stands in the switch's own text (K2C/Closed.lean: SwitchIs.hTrees, hRoots). The walk through
the three arms is K2C/BookKept.lean's yes_book's. -/
theorem k2_roots {p : K2.P2} {s : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {s' : S} (h : K2.decideWith sendByL8 p s rs gs = .ok s') : s'.roots = s.roots + p.roots := by
  have key : ∀ {f : ReqFrame} {x : _root_.Tw.K2.Front} {r₁ r₂ : Fmt.RoundView} {w : _root_.Tw.K2.SwOut}
      {roots : Nat},
      _root_.Tw.K2.switchE switchBehind (K2.par9 p) sendByL8 ⟨s.st, s.book, s.roots, f, [],
          s.noneWaits⟩
        x r₁ r₂ (K2.flat p gs) = .ok (w, roots) → roots = s.roots + p.roots := by
    intro f x r₁ r₂ w roots hw
    obtain ⟨y, k⟩ := K2.switchE_inv hw
    exact k.hRoots.trans k.hTrees
  rcases (K2.stands _ _ _ _ _ _ h) with ⟨hp, _⟩ | ⟨hp, _⟩ | ⟨hp, _⟩
  · obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ := K2.link_inv hp h
    rw [k.hOut]
    exact key k.hSwitch
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := K2.head_inv hp h
    rw [k.hOut]
    exact key k.hSwitch
  · obtain ⟨r₁, r₂, a, G, w, roots, rfl, k⟩ := K2.finish_inv hp h
    rw [k.hOut]
    exact key k.hSwitch

theorem k2_step (p : K2.P2) : RootsStep (fun s : S => s.roots) (K2.codeSwitchKind p : Block S Unit) :=
  fun _ s s' rs gs h => by
    have e : rootsOf (K2.codeSwitchKind p : Block S Unit).rounds = p.roots := by
      show (p.roots + (0 + 0)) = p.roots
      rfl
    rw [e]
    exact k2_roots h

/-- A yes of K1's sending is a yes on two rounds. -/
theorem send_two {L : Type} {P : K1.Par} {owed : Option Nat} {d : _root_.Desc.Plain.DState L}
    {rs : List Fmt.RoundView} {x : Array Nat × _root_.Desc.Plain.DState L}
    (h : K1.decideSend P owed d rs = .ok x) : ∃ a b, rs = [a, b] := by
  match rs, h with
  | [a, b], _ => exact ⟨a, b, rfl⟩

theorem k1_rounds (P : K1.Par) : rootsOf (K1.rounds P) = (K1.layOf P).shapes.size := by
  rw [← K13.Law.trees_eq_lay]
  simp [rootsOf, K1.rounds, K1.seedEntry, K1.answerEntry]

/-- **K1, a segment's later moment.** By commitAtS_seated. -/
theorem commitAtS_step (P : K1.Par) (link moment : Nat) (arrays : Option (List Nat)) :
    RootsStep (fun s : S => s.roots) (K1.commitAtS (Cl := Unit) P link moment arrays) :=
  fun _ s s' rs gs h => by
    have h2 : ∃ a b, rs = [a, b] := by
      have h' := h
      unfold K1.commitAtS at h'
      dsimp only at h'
      split at h'
      · obtain ⟨y, hy, -⟩ := (K1.map_ok _ _ _).1 h'
        obtain ⟨ids, d₁, f', k, -⟩ := K1.commitOwn_ok P link moment arrays _ y _ gs hy
        exact send_two k
      · cases h'
    obtain ⟨a, b, rfl⟩ := h2
    show s'.roots = s.roots + rootsOf (K1.rounds P)
    rw [k1_rounds]
    exact (K1.commitAtS_seated P link moment arrays s s' a b gs h).roots

/-- **K1, the first segment's opening.** By firstAtS_seated. -/
theorem firstAtS_step (q : Params.First) (gp : _root_.Desc.Plain.GPar) :
    RootsStep (fun s : S => s.roots) (K1.firstSegmentOpening (Cl := Unit) q gp) :=
  fun _ s s' rs gs h => by
    have h2 : ∃ a b, rs = [a, b] := by
      obtain ⟨c, d', k, -, -⟩ := K1.firstAtS_ok q gp s s' rs gs h
      obtain ⟨g, d₁, ids, d₂, -, h4, -⟩ := K1.firstOwn_ok _ _ _ _ _ _ _ k
      exact send_two h4
    obtain ⟨a, b, rfl⟩ := h2
    show s'.roots = s.roots + rootsOf (K1.rounds (K1.firstPar q gp))
    rw [k1_rounds]
    exact (K1.firstAtS_seated q gp s s' a b gs h).roots

/-! ## The seat's makers, all -/

/-- RootsStep (RootsFold.lean) at the count of roots, at every type of a claim. -/
abbrev PrR {Cl : Type} (b : Block S Cl) : Prop := RootsStep (fun s : S => s.roots) b

theorem carriedAll_roots : CarriedAll (fun {_} b => PrR b) SameR where
  each _ := carried_roots fun s : S => s.roots
  retype {_ _ b} W := fun hp s s' rs gs h =>
    W ((Bool.and_eq_true _ _ ▸ (show (b.planOk && b.claims.isEmpty) = true from hp)).1) s s' rs gs h

/-- A maker that sends nothing. -/
theorem wp_quiet {Cl : Type} {b : Block S Cl} (h0 : rootsOf b.rounds = 0) (W : Whole SameR b) :
    WP (fun {_} b => PrR b) SameR b := wholeP_of_quiet (fun s : S => s.roots) h0 W

/-- A maker that states no run. -/
theorem wp_bare {Cl : Type} {b : Block S Cl} (W : PrR b) (hc : b.claims = []) (ha : b.after = []) :
    WP (fun {_} b => PrR b) SameR b :=
  ⟨W, (fun c k => by rw [hc] at k; cases k), (fun c k => by rw [ha] at k; cases k)⟩

theorem fn_book {f : S → Except String S}
    (h : ∀ s s', f s = .ok s' → s'.book = s.book ∧ s'.roots = s.roots) : Fn SameR f :=
  fun s s' k => (h s s' k).2

/-- **EVERY MAKER OF THE SEAT IN FRONT OF THE BLOCKS BEHIND THE LAST LINK, AND THE SEAL: a yes adds
to the count of roots just what the block's declared rounds send; every run leaves the count.** -/
theorem seatCarry_roots : SeatCarry (fun {_} b => PrR b) SameR where
  frames := fun _ h => Meaning.K2.framesOf_core rc_same h
  k1First := fun q gp _ => wp_bare (firstAtS_step q gp) rfl rfl
  k1Later := fun q gp l p m a _ => wp_bare (commitAtS_step _ l m a) rfl rfl
  reads := fun h => wp_quiet (reads_rounds h) (whole_of_quiet (Meaning.K2.readsQuietAt_quiet h))
  k3 := fun c r X cs sh a _ h =>
    have W := whole_of_quiet (Meaning.K2.theStated_quiet c r X cs sh a h)
    ⟨fun hp s s' rs gs k => by
      rw [k3_rounds c r X cs sh a h hp]
      exact W.1 s rs gs s' k, W.2.1, W.2.2⟩
  k4 := fun p => wp_quiet (k4_rounds p) (whole_of_quiet (Meaning.K2.blockAtC_quiet p))
  k5 := fun W l g bf _ h =>
    wp_quiet (k5_rounds W l g bf h) (whole_of_quiet (Meaning.K2.k5AtN_quiet W l g bf h))
  k6 := fun h => wp_quiet (k6_rounds h) (whole_of_quiet (Meaning.K2.seatedClaims_quiet h))
  k7 := fun W l => wp_quiet (k7_rounds W l) (whole_of_quiet (Meaning.K2.k7Of_quiet W l))
  k8 := fun p => wp_quiet (k8_rounds p) (whole_of_quiet (Meaning.K2.k8Whole_quiet p))
  k11 := fun Q => wp_quiet (k11_rounds Q) (whole_of_quiet (Meaning.K2.headMerge11_quiet Q))
  closeOf := fun p P b hb =>
    wp_quiet (closeOf_rounds p P b hb) (whole_of_core (Meaning.K2.closeOf_core rc_same p P b hb))
  batch := fun p claims hcl => wp_quiet (batch_rounds0 p claims)
    (whole_of_core (Meaning.K2.batch_core rc_same (fun h k => Eq.trans k h) p hcl))
  k2 := fun p _ => wp_bare (k2_step p) rfl rfl
  front := fun _ => fn_book fun _ _ h => K2.headFrontQ_book h
  openQ := fun _ _ => fn_book fun _ _ h => K2.headOpenQ_book h
  finFront := fn_book fun _ _ h => K2.finishFrontQ_book h
  finBehind := fn_book fun _ _ h => K2.finishBehindQ_book h
  theSeal := fun inFront _ _ _ _ _ h => K13.Law.chainEnd_roots 1 5 true inFront endAsks h

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **THE COUNT OF ROOTS AT EVERY CUT OF THE FIRST CHAIN's FLAT LIST IN FRONT OF THE BLOCKS BEHIND
THE LAST LINK: NO FIELD OF SeatCarry IS LEFT AS A HYPOTHESIS.** -/
theorem roots_at_cut_paid (O : IM.Open o pol lay KL F Z Bs base c A B) (k : Nat)
    (hk : k ≤ (Meaning.K2.frontOf c).length) (hp : ∀ b ∈ c.blocksInOrder.take k, b.planOk = true) (ft : Nat)
    (s : S) (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn)
    (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn)
    (h : foldBlocks ft (c.blocksInOrder.take k) s rs cols = .ok r) :
    r.1.roots = s.roots + rootsOf (H2K.First.declOf (c.blocksInOrder.take k)) :=
  roots_at_cut O (thePure_carry carriedAll_roots seatCarry_roots Z Bs.G₀ (oksAt_all _ _)) k hk hp
    ft s rs cols r h

end

#print axioms seatCarry_roots
#print axioms roots_at_cut_paid

end Meaning.Carry
