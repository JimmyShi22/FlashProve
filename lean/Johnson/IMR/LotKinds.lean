-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/LotKinds.lean.
Where the rest of this head and the Lean text differ, the Lean text holds.
 A LAW ABOUT ProofFile.pureSeat, NO PART OF IT: each lot of onlineDescription's seat lays
blocks of one kind (K9's lot: of two), and its one maker of a batching makes blocks of the kind K9.
OBJECT. ProofFile.onlineFirstChainBlockTables Z (Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean): its fifteen lots, each through Lot.blocks (own, carried over by Block.retype, then hearC).
USER. The seats: «a block of the seat that bears the kind k comes from k's own lot».
LETTERS. Z: the public part · G: the letters at which the lots' tables are made.


THE LETTER o : ProofFile.SecondHashFunctionArgument (the second hash function, as a letter): what needs no scope stands at every o; what stands on a law of the library over «publicOf … = .ok X» stands at OnBytes.secondHashFunction, where publicOfO_older makes
publicOfO publicOf (the goals stated with VerifierAndGoals.atSecondHashFunction (Ladder.lean) hand the description secondHashFunction; G7′ | G7′bits hand every o: for these the in-scope halves are still owed, at PublicCut).

  blocks_mem        a block of Lot.blocks is a block of own carried over, or a block of hearC.
  AllKind L G k     every block of the lot L, at the letters G, has the kind k.
  kind_frames … kind_K13_end   frames: frame · K1's: K1 · K2's: K2 · K3's: K3 · K4's: K4 · K5's: K5 · K6's: K6 · K7's place's: K7 · K8's: K8 ·
                    K9's lot's closing: K9 or K10 · K11's: K11 · K12's: K12 · K13's three: K13 · K1 · frame.
  lot_of_kind       so a block of a lot of the seat, of kind K2 | K3 | K4 | K5 | K6 | K8 | K11 | K12, comes from that kind's own lot and no other.
  makers_K9         MakersK9 (Johnson/IMR/PureChain.lean) at onlineDescription's seat, OUTRIGHT: K9's lot alone gives a maker; its blocks bear the kind K9.

What is not claimed. Nothing on what the blocks do. The kinds K1 and frame (two lots each), K13 and K7 (one lot each; K7's is a record without a name
of its own), K9 and K10 (one lot for both) are not in lotOf's table. No soundness.
-/
import Johnson.IMR.PureChain

set_option autoImplicit false

namespace IM

variable {o : ProofFile.SecondHashFunctionArgument}
open VerifiableInference.Desc (Block KindName roundlessBlock)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

theorem blocks_mem {L : ProofFile.Lot} {G : ProofFile.Ground} {b : Block S Cl} (h : b ∈ L.blocks G) :
    (∃ x ∈ L.own G, b = x.retype) ∨ b ∈ L.hearC G := by
  unfold ProofFile.Lot.blocks ProofFile.asCl at h
  rcases List.mem_append.1 h with h | h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
    exact Or.inl ⟨x, hx, rfl⟩
  · exact Or.inr h

/-- Every block of the lot, at the letters G, has the kind k. -/
def AllKind (L : ProofFile.Lot) (G : ProofFile.Ground) (k : KindName) : Prop := ∀ b ∈ L.blocks G, b.place.kind = k

theorem allKind_of {L : ProofFile.Lot} {G : ProofFile.Ground} {k : KindName}
    (h1 : ∀ x ∈ L.own G, x.place.kind = k) (h2 : ∀ b ∈ L.hearC G, b.place.kind = k) :
    AllKind L G k := by
  intro b hb
  rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · exact h1 x hx
  · exact h2 b hb

theorem none_in {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := fun _ h => nomatch h

theorem kind_frames (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (ProofFile.framesLot Z) G .frame := by
  refine allKind_of (fun b hb => ?_) none_in
  have hb' : b ∈ P1L20.blocksOf Z := hb
  unfold P1L20.blocksOf at hb'
  split at hb'
  · obtain ⟨f, _, h⟩ := List.mem_flatMap.1 hb'
    unfold ProofFile.frameBlocks at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> rfl
  · obtain rfl := List.mem_singleton.1 hb'
    rfl

theorem kind_K1 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (ProofFile.k1Pure Z) G .K1 := by
  refine allKind_of (fun b hb => ?_) none_in
  unfold ProofFile.k1Pure VerifiableInference.Desc.K1.lotWith at hb
  dsimp only at hb
  unfold VerifiableInference.Desc.K1.blocks at hb
  dsimp only at hb
  rcases List.mem_append.1 hb with h | h
  · obtain rfl := List.mem_singleton.1 h
    rfl
  · obtain ⟨x, _, h⟩ := List.mem_flatMap.1 h
    split at h
    · cases h
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl
      · rfl
      · rfl

theorem kind_K2 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (ProofFile.k2Pure Z) G .K2 := by
  refine allKind_of (fun b hb => ?_) none_in
  have hb' : b ∈ P1K2.pureTable (fun _ _ => some none) Z G := hb
  unfold P1K2.pureTable at hb'
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hb'
  have hk : sp.place.kind = KindName.K2 := by simpa using (List.mem_filter.1 hsp).2
  split
  · exact hk
  · rename_i x hx
    have hx2 : x.1.place.kind = KindName.K2 := by
      have hm := List.mem_of_find?_eq_some hx
      unfold P1K2.pureSpots at hm
      cases hs : ProofFile.spotsOf Z.cuts with
      | none => rw [hs] at hm; cases hm
      | some sps =>
        rw [hs] at hm
        have hm' : x ∈ P1K2.p2All Z G sps := hm
        unfold P1K2.p2All at hm'
        split at hm'
        · cases hm'
        · obtain ⟨s, hs', e⟩ := List.mem_filterMap.1 hm'
          obtain ⟨p, _, rfl⟩ := Option.map_eq_some_iff.1 e
          simpa using (List.mem_filter.1 hs').2
    cases hp : P1K2.pureAt (fun _ _ => some none) G x with
    | none => exact hk
    | some c =>
      show c.place.kind = _
      unfold P1K2.pureAt at hp
      dsimp only at hp
      split at hp
      · obtain rfl := Option.some.inj hp
        exact hx2
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hp
        exact hx2
      · obtain ⟨o, _, rfl⟩ := Option.map_eq_some_iff.1 hp
        cases o <;> exact hx2

theorem theOwn_kind {C : Type} {claim : OnBytes.Model.Aff → C} {runs : Bool} {X : OnBytes.Model.Verify.Public}
    {codes : OnBytes.Codes} {shape : OnBytes.Params.ReqShape} {a : VerifiableInference.Desc.Place}
    {c : Block S C} (hc : VerifiableInference.Desc.K3.theOwn claim runs X codes shape a = some c) :
    c.place.kind = KindName.K3 := by
  unfold VerifiableInference.Desc.K3.theOwn at hc
  split at hc
  · cases hc
  · obtain ⟨i, _, hc⟩ := Option.bind_eq_some_iff.1 hc
    obtain ⟨dg, _, hc⟩ := List.exists_of_findSome?_eq_some hc
    split at hc
    · cases hc
    · obtain ⟨_, _, hc⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨_, _, hc⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨_, _, hc⟩ := Option.bind_eq_some_iff.1 hc
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hc
      dsimp only
      split <;> rfl

theorem kind_K3 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (K3Lot.lot Z) G .K3 := by
  refine allKind_of none_in (fun b hb => ?_)
  have hb' : b ∈ K3Lot.hear Z := hb
  unfold K3Lot.hear at hb'
  obtain ⟨x, _, h⟩ := List.mem_filterMap.1 hb'
  unfold VerifiableInference.Desc.K3.theStated at h
  obtain ⟨w, hw, h⟩ := Option.bind_eq_some_iff.1 h
  have hk : w.place.kind = KindName.K3 := by
    unfold VerifiableInference.Desc.K3.theWhole at hw
    obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 hw
    have := theOwn_kind hc
    split <;> exact this
  split at h
  · obtain rfl := Option.some.inj h
    exact hk
  · split at h
    · obtain rfl := Option.some.inj h
      exact hk
    · split at h
      · obtain rfl := Option.some.inj h
        exact hk
      · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
        exact hk

theorem kind_K4 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (ProofFile.k4Lot Z) G .K4 := by
  refine allKind_of none_in (fun b hb => ?_)
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hb
  rfl

theorem kind_K5 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (H2K5.lotN Z) G .K5 := by
  refine allKind_of none_in (fun b hb => ?_)
  obtain ⟨x, _, h⟩ := List.mem_filterMap.1 hb
  obtain ⟨b0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  show b0.place.kind = _
  rw [(VerifiableInference.Desc.First.Att.P.k5AtN_states h0).2.2]

theorem kind_K6 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (P4.k6Lot Z) G .K6 := by
  refine allKind_of none_in (fun b hb => ?_)
  have hb' : b ∈ ((P4.headBefore Z G).bind fun ms =>
      VerifiableInference.Desc.Kinds.Head.seatedClaims G.W (G.built.size - 1) ms).toList := hb
  rw [Option.mem_toList] at hb'
  obtain ⟨ms, _, h⟩ := Option.bind_eq_some_iff.1 hb'
  unfold VerifiableInference.Desc.Kinds.Head.seatedClaims at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold VerifiableInference.Desc.Kinds.Head.blockClaims at hc
  obtain ⟨u, _, rfl⟩ := Option.map_eq_some_iff.1 hc
  rfl

theorem kind_K7 (G : ProofFile.Ground) : ∀ b ∈ ProofFile.h1Own G, b.place.kind = KindName.K7 := by
  intro b hb
  obtain rfl := List.mem_singleton.1 hb
  rfl

theorem kind_K8 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (ProofFile.P1K8.lot Z) G .K8 := by
  refine allKind_of none_in (fun b hb => ?_)
  obtain ⟨x, _, rfl⟩ := List.mem_map.1 hb
  rfl

/-- K9's lot's blocks (the closing's three, or a refuser): K9 or K10. -/
theorem kind_K9 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ b ∈ (ProofFile.k9Ninth Z).blocks G, b.place.kind = KindName.K9 ∨ b.place.kind = KindName.K10 := by
  intro b hb
  rcases blocks_mem hb with ⟨x, hx, rfl⟩ | hb
  · unfold ProofFile.k9Ninth at hx
    dsimp only at hx
    obtain ⟨w, _, hx⟩ := List.mem_flatMap.1 hx
    split at hx
    · unfold VerifiableInference.Desc.K9.closeOf at hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · obtain rfl := List.mem_singleton.1 hx
      exact Or.inr rfl
  · exact nomatch hb

theorem kind_K11 (Z : ProofFile.Pub) (G : ProofFile.Ground) : AllKind (K11.lot Z) G .K11 := by
  refine allKind_of none_in (fun b hb => ?_)
  obtain rfl := List.mem_singleton.1 hb
  rfl

theorem p12_place (m : Johnson.G.OfPlan.Made) :
    (H2U.p12OfMade m).place = ⟨1, none, 2, KindName.K12⟩ := by
  unfold H2U.p12OfMade
  dsimp only
  split
  · unfold H2U.proximityTestParametersAt
    split
    · rfl
    · split <;> rfl
  · rfl

theorem k12_place {T C : Type} (X : VerifiableInference.Desc.K12.Parts T)
    (p : VerifiableInference.Desc.K12.P12) :
    (VerifiableInference.Desc.K12.proximityTestKind (Cl := C) X p).place = p.place := by
  unfold VerifiableInference.Desc.K12.proximityTestKind
  split <;> rfl

theorem kind_K12 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    AllKind (VerifiableInference.Desc.K12.lot Z) G .K12 := by
  refine allKind_of (fun b hb => ?_) none_in
  obtain rfl := List.mem_singleton.1 hb
  show (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
    (H2U.p12OfMade Z.made)).place.kind = _
  rw [k12_place, p12_place]

theorem kind_K13 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    AllKind (VerifiableInference.Desc.K13.lot Z) G .K13 := by
  refine allKind_of (fun b hb => ?_) none_in
  obtain rfl := List.mem_singleton.1 hb
  rfl

theorem kind_K13_4 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    AllKind (VerifiableInference.Desc.K13.lot4 Z) G .K1 := by
  refine allKind_of (fun b hb => ?_) none_in
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
  rw [Option.mem_toList] at hx
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hx
  obtain ⟨msg, _, rfl⟩ := Option.map_eq_some_iff.1 hx
  rfl

theorem kind_K13_end (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    AllKind (VerifiableInference.Desc.K13.lotEnd Z) G .frame := by
  refine allKind_of (fun b hb => ?_) none_in
  obtain rfl := List.mem_singleton.1 hb
  rfl

/-- K7's place's lot, as Johnson/Desc/ProofFile/Lots/PureLots.lean: p4Pure writes it. -/
theorem kind_K7_lot {L : ProofFile.Lot} {G : ProofFile.Ground} (ho : L.own = ProofFile.h1Own)
    (hh : L.hearC = fun _ => []) : AllKind L G .K7 := by
  refine allKind_of (fun b hb => ?_) (fun b hb => ?_)
  · rw [ho] at hb
    exact kind_K7 G b hb
  · rw [hh] at hb
    exact nomatch hb

/-- The kind's own lot, for the kinds that one lot of the seat lays, and it no other kind. -/
def lotOf (Z : ProofFile.Pub) : KindName → Option ProofFile.Lot
  | .K2 => some (ProofFile.k2Pure Z)
  | .K3 => some (K3Lot.lot Z)
  | .K4 => some (ProofFile.k4Lot Z)
  | .K5 => some (H2K5.lotN Z)
  | .K6 => some (P4.k6Lot Z)
  | .K8 => some (ProofFile.P1K8.lot Z)
  | .K11 => some (K11.lot Z)
  | .K12 => some (VerifiableInference.Desc.K12.lot Z)
  | _ => none

/-- **A block of one of these kinds comes from that kind's own lot and no other.** -/
theorem lot_of_kind {Z : ProofFile.Pub} {G : ProofFile.Ground} {L : ProofFile.Lot} (hL : L ∈ ProofFile.onlineFirstChainBlockTables Z)
    {b : Block S Cl} (hb : b ∈ L.blocks G) {L' : ProofFile.Lot} (hk : lotOf Z b.place.kind = some L') :
    L = L' := by
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  · rw [kind_frames Z G b hb] at hk; cases hk
  · rw [kind_K1 Z G b hb] at hk; cases hk
  · rw [kind_K2 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K3 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K4 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K5 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K8 Z G b hb] at hk; exact Option.some.inj hk
  · rcases kind_K9 Z G b hb with e | e <;> rw [e] at hk <;> cases hk
  · rw [kind_K11 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K12 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K13 Z G b hb] at hk; cases hk
  · rw [kind_K13_4 Z G b hb] at hk; cases hk
  · rw [kind_K13_end Z G b hb] at hk; cases hk
  · rw [kind_K6 Z G b hb] at hk; exact Option.some.inj hk
  · rw [kind_K7_lot rfl rfl b hb] at hk; cases hk

/-- **MakersK9 at onlineDescription's seat, outright.** -/
theorem makers_K9 (Z : ProofFile.Pub) (G : ProofFile.Ground) : MakersK9 (ProofFile.pureSeat o Z) G := by
  intro L hL a mk hmk g
  have hL' : L ∈ ProofFile.onlineFirstChainBlockTables Z := hL
  unfold ProofFile.onlineFirstChainBlockTables ProofFile.p4Pure at hL'
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL'
  rcases hL' with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
    (rfl | rfl)
  iterate 7 exact nomatch hmk
  · unfold ProofFile.k9Ninth at hmk
    dsimp only at hmk
    split at hmk
    · obtain ⟨p, _, hmk⟩ := Option.bind_eq_some_iff.1 hmk
      split at hmk
      · obtain rfl := Option.some.inj hmk
        rfl
      · cases hmk
    · cases hmk
  iterate 7 exact nomatch hmk

end IM

#print axioms IM.lot_of_kind
#print axioms IM.makers_K9
