-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/NoPosSeat.lean: THE
FIFTH INSTANCE of the walk (Johnson/Goal/Meaning/CarryDriver.lean, Johnson/IMR/CarryLots.lean): OF
onlineDescription's
SEAT's MAKERS THE CODE SWITCH ALONE DECLARES A ROUND THAT DRAWS POSITIONS. So the mark by which
Johnson/IMR/MsgsCut.lean's msgs_at_cut_but sets blocks apart singles out the switches.

  NoPos b: b.planOk = true → ∀ r ∈ b.rounds, r.entry.poss = 0. carried_noPos, carriedAll_noPos:
      Carried NoPos (every two states).
  seatCarry_noPos: **SeatCarry NoPos … oksNo**: every maker but K2's (oksNo asks K2's field at no
      number): by rfl at K1, K7, K8, K9's batching and the seal; by the entries' texts at K4, K5
      (maskedSum_poss, k5Entries_poss), K6, K10's closing, K11; no round at the reads
      (reads_noRound) and the frames; K3 UNDER ITS OWN TEST ON THE PLAN (k3Own_noPos, k3_noPos:
      fitsVia asks staticT of every entry, which holds "poss == 0").
  noMark_of_carry. marked_kind: **L ∈ ProofFile.onlineFirstChainBlockTables Z · b ∈ L.blocks G · b.planOk = true · b declares
      a round that draws positions ⇒ b.place.kind = .K2 ∨ b.place.link = none.** At every Z, G.
TWINS IN FORM, KNOWN: reads_noRound, Johnson/IMR/RootsSeat.lean's reads_rounds and
Johnson/IMR/MsgsSeat.lean's
reads_told open the same text three times; k3Own_noPos and k3Own_rounds likewise: to be drawn
together when the files are next opened for more than words.
OBJECT: the seat's lots. USER: the payers of msgs_at_cut_but's hM. LETTERS: none.




Limits. Nothing on what any block does. Nothing on soundness.
-/
import Johnson.IMR.MsgsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Lot Ground Pub)

/-- Where the block passes its test on the plan, none of its declared rounds draws a position. -/
def NoPos {T Cl : Type} (b : Block T Cl) : Prop :=
  b.planOk = true → ∀ r ∈ b.rounds, r.entry.poss = 0

/-- Every two states. -/
abbrev AnyR {T : Type} : T → T → Prop := fun _ _ => True

/-- **The fifth instance.** -/
theorem carried_noPos {T Cl : Type} : Carried (T := T) (Cl := Cl) NoPos AnyR where
  refl _ := trivial
  trans _ _ _ _ _ := trivial
  under u W := fun hp r hr => W (u.2.1 hp) r (u.1.1 ▸ hr)
  quiet h0 _ _ := fun _ r hr => by rw [h0] at hr; cases hr
  andThen {n p q} W₁ W₂ := fun hp r hr => by
    have hp' : (p.planOk && q.planOk) = true := hp
    rw [Bool.and_eq_true] at hp'
    rcases List.mem_append.1 (show r ∈ p.rounds ++ q.rounds from hr) with h | h
    · exact W₁ hp'.1 r h
    · exact W₂ hp'.2 r h

theorem carriedAll_noPos : CarriedAll (fun {_} b => NoPos b) (AnyR (T := S)) where
  each _ := carried_noPos
  retype {_ _ b} W := fun hp r hr =>
    W ((Bool.and_eq_true _ _ ▸ (show (b.planOk && b.claims.isEmpty) = true from hp)).1) r hr

theorem wp_noPos {Cl : Type} {b : Block S Cl} (h : ∀ r ∈ b.rounds, r.entry.poss = 0) :
    WP (fun {_} b => NoPos b) AnyR b :=
  ⟨fun _ => h, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩

theorem wp_noRound {Cl : Type} {b : Block S Cl} (h : b.rounds = []) :
    WP (fun {_} b => NoPos b) AnyR b := wp_noPos fun r hr => by rw [h] at hr; cases hr

theorem wp_allPos {Cl : Type} {b : Block S Cl}
    (h : (b.rounds.all fun r => r.entry.poss == 0) = true) : WP (fun {_} b => NoPos b) AnyR b :=
  wp_noPos fun r hr => beq_iff_eq.1 (List.all_eq_true.1 h r hr)

theorem fn_any (f : S → Except String S) : Fn AnyR f := fun _ _ _ => trivial

/-! ## The makers -/

theorem reads_noRound {G : Ground} {l : Nat} {X : Stages.LinkH} {piece : Nat} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : b.rounds = [] := by
  have hA : ∀ {W : Verify.Public} {l g : Nat} {b : Block S Unit}, Att.readsAtO W l g = some b →
      b.rounds = [] := by
    intro W l g b h
    unfold Att.readsAtO at h
    obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rfl
  have hB : ∀ {G : Array Layer.HPlan2} {hS : Head.Shape} {HLy : Head.HL} {Hp : Head.HPlanH2}
      {kinds : List (Nat × Nat)} {l : Nat} {b : Block S Unit},
      K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b → b.rounds = [] := by
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

theorem k3Own_noPos {Cl : Type} (claim : Aff → Cl) (runs : Bool) (X : Verify.Public)
    (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S Cl}
    (h : K3.theOwn claim runs X codes shape a = some b) : NoPos b := by
  intro hp
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
    intro r hr
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
    have hs := hf.2 x hx
    unfold K3.staticT at hs
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    exact hs.1.1.1.1
  · cases hf

theorem k3_noPos (claim : Aff → ProofFile.Cl) (readers : Nat → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : ReqShape) (a : Place) {b : Block S ProofFile.Cl}
    (h : K3.theStated claim readers X codes shape a = some b) : NoPos b := by
  intro hp
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
    show ∀ r ∈ o.rounds ++ [], r.entry.poss = 0
    rw [List.append_nil]
    exact k3Own_noPos claim true X codes shape a ho hp'
  | none =>
    simp only [hq] at hp ⊢
    exact k3Own_noPos claim true X codes shape a ho hp

theorem maskedSum_poss (k : Part.MaskedSum.Call) :
    ∀ e ∈ Part.MaskedSum.entries k, e.poss = 0 := by
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

theorem k5Entries_poss : ∀ (l : List Att.P.Stage) (lead : Nat),
    ∀ e ∈ Att.P.entriesOf lead l, e.poss = 0
  | [], _, e, he => by cases he
  | .scalars n :: l, lead, e, he => k5Entries_poss l (lead + n) e he
  | .sum vs x :: l, lead, e, he => by
    rcases List.mem_append.1 (show e ∈ Part.MaskedSum.entries ⟨lead, vs, some x⟩ ++
      Att.P.entriesOf 0 l from he) with he | he
    · exact maskedSum_poss _ e he
    · exact k5Entries_poss l 0 e he
  | .batch rows :: l, lead, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact k5Entries_poss l 0 e he
  | .point n :: l, lead, e, he => by
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact k5Entries_poss l 0 e he

/-- At which numbers: at no code switch's. -/
def oksNo : Oks := { p2 := fun _ => False }

/-- **EVERY MAKER OF THE SEAT BUT THE CODE SWITCH: none of its declared rounds draws a position**
(K3's under its own test on the plan). -/
theorem seatCarry_noPos : SeatCarry (fun {_} b => NoPos b) (AnyR (T := S)) oksNo where
  frames := fun _ _ _ _ => ⟨fn_any _, fn_any _, fn_any _⟩
  k1First := fun _ _ _ => wp_allPos rfl
  k1Later := fun _ _ _ _ _ _ _ => wp_allPos rfl
  reads := fun h => wp_noRound (reads_noRound h)
  k3 := fun c r X cs sh a _ h =>
    ⟨k3_noPos c r X cs sh a h, fun _ _ _ _ _ _ => trivial, fun _ _ _ _ _ => trivial⟩
  k4 := fun p => wp_noPos fun r hr => by
    have hr' : r ∈ (OnBytes.Desc.First.K4.entries p.P p.hp p.g).map
        (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
    obtain ⟨d, -, rfl⟩ := List.mem_map.1 he
    rfl
  k5 := fun W l g bf _ h => wp_noPos fun r hr => by
    unfold Att.P.k5AtN at h
    obtain ⟨p, -, rfl⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨e, he, rfl⟩ := List.mem_map.1
      (show r ∈ (Att.P.entriesOf 0 (Att.P.script p.own)).map _ from hr)
    have h0 := k5Entries_poss _ _ e he
    dsimp only
    split
    · exact h0
    · exact h0
  k6 := fun h => wp_noPos fun r hr => by
    obtain ⟨b0, h0, rfl⟩ := Kinds.Head.Law.seatedClaims_some h
    unfold Kinds.Head.blockClaims at h0
    obtain ⟨iU3, _, rfl⟩ := Option.map_eq_some_iff.mp h0
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 (show r ∈ List.map _ _ from hr)
    rfl
  k7 := fun _ _ => wp_allPos rfl
  k8 := fun _ => wp_allPos rfl
  k11 := fun P => wp_noPos fun r hr => by
    have hr' : r ∈ (Johnson.Desc.First.ForkMerge.mergeEntries P.lay.lk 1 P.work).map
        (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
    unfold Johnson.Desc.First.ForkMerge.mergeEntries at he
    simp only [List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl | ⟨-, rfl⟩ | rfl | rfl <;> rfl
  closeOf := fun p P b hb => by
    unfold K9.closeOf at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl
    · exact wp_noRound rfl
    · refine wp_noPos fun r hr => ?_
      have hr' : r ∈ (Close.entries P).map (fun e => ({ entry := e } : Fmt.DeclaredRound)) := hr
      obtain ⟨e, he, rfl⟩ := List.mem_map.1 hr'
      unfold Close.entries at he
      simp only [List.mem_cons, List.mem_replicate] at he
      rcases he with rfl | rfl | ⟨-, rfl⟩ <;> rfl
    · exact wp_noRound rfl
  batch := fun _ _ _ => wp_allPos rfl
  k2 := fun _ h => h.elim
  front := fun _ => fn_any _
  openQ := fun _ _ => fn_any _
  finFront := fn_any _
  finBehind := fn_any _
  theSeal := fun _ _ r hr => beq_iff_eq.1 (List.all_eq_true.1
    (show ((ChainEnd.chainEnd 1 5 true _ endAsks : Block S Unit).rounds.all
      fun r => r.entry.poss == 0) = true from rfl) r hr)

/-! ## A lot's block that draws positions is a code switch's, or stands outside the links -/

theorem noMark_of_carry {L : Lot} {G : Ground}
    (K : LotCarry (fun b => NoPos b) (AnyR (T := S)) L G) {b : Block S ProofFile.Cl}
    (hb : b ∈ L.blocks G) (hp : b.planOk = true) (hm : Marked drawsPos b) :
    b.place.link = none := by
  by_contra h
  obtain ⟨r, hr, k⟩ := hm
  exact k ((K.blocks b hb h).1 hp r hr)

/-- **Of the seat's fifteen lots.** -/
theorem marked_kind (Z : Pub) (G : Ground) {L : Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S ProofFile.Cl} (hb : b ∈ L.blocks G) (hp : b.planOk = true)
    (hm : Marked drawsPos b) : b.place.kind = KindName.K2 ∨ b.place.link = none := by
  have C := carriedAll_noPos
  have H := seatCarry_noPos
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    rfl | rfl
  · exact Or.inr (noMark_of_carry (framesLot_carry C H Z trivial G) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((k1Pure_all C H Z trivial G).carry (kind_ne (IM.kind_K1 Z G) (by decide))) hb hp hm)
  · exact Or.inl (IM.kind_K2 Z G b hb)
  · exact Or.inr (noMark_of_carry
      ((k3Lot_all C H Z G).carry (kind_ne (IM.kind_K3 Z G) (by decide))) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((k4Lot_all C H Z G).carry (kind_ne (IM.kind_K4 Z G) (by decide))) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((k5LotN_all C H Z G).carry (kind_ne (IM.kind_K5 Z G) (by decide))) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((k8Lot_all C H Z G).carry (kind_ne (IM.kind_K8 Z G) (by decide))) hb hp hm)
  · exact Or.inr (noMark_of_carry ((k9Ninth_all C H Z G).carry fun b hb e => by
      rcases IM.kind_K9 Z G b hb with h | h <;> rw [h] at e <;> cases e) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((k11Lot_all C H Z G).carry (kind_ne (IM.kind_K11 Z G) (by decide))) hb hp hm)
  · exact Or.inr (noMark_of_carry (k12Lot_carry Z G) hb hp hm)
  · exact Or.inr (noMark_of_carry (k13Lot_carry Z G) hb hp hm)
  · exact Or.inr (noMark_of_carry (k13Lot4_carry Z G) hb hp hm)
  · exact Or.inr (noMark_of_carry (k13LotEnd_carry C H Z G) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((k6Lot_all C H Z G).carry (kind_ne (IM.kind_K6 Z G) (by decide))) hb hp hm)
  · exact Or.inr (noMark_of_carry
      ((lotAllP_of C (h1_all C H G) (fun _ hb => absurd hb List.not_mem_nil)
        (fun _ mk h => nomatch (show none = some mk from h))).carry
        (kind_ne (IM.kind_K7_lot rfl rfl) (by decide))) hb hp hm)

#print axioms seatCarry_noPos
#print axioms marked_kind

end Meaning.Carry
