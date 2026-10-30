-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/LotsMore.lean: LotsKeep.lean, continued: eight more lots of the proof file's
IOP as written in Lean (Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean: `onlineFirstChainBlockTables`) in PureKeeps.lean's one
form for a lot. A law file; no running text imports it.

Five lots give SameRows because the statement stays: by the laws `Whole Quiet b` at the lots' own
makers (Johnson/Goal/Meaning/RecSeated.lean, RecK7.lean; `Quiet`: RecQuiet.lean, whose first clause
is s'.st = s.st). These laws stand in those files; here they are called.
Three lots owe nothing: each of their sub-protocols stands behind the last segment and is not of the
kind `frame`.

  `rides_same`, `rowsD_of_keeps`, `rowsD_andThen`, `rowsD_guarded`   SameRows through the ways in
                   which a supplied sub-protocol is made, by ChainKeeps.lean's rules.
  `rows_of_quiet`  `Whole Quiet b` gives `RowsD b` and `RowsRuns b`.
  `lotRows_k3`, `lotRows_k4`, `lotRows_k5`, `lotRows_k6`   both lookups; the feed-forward layers';
                   the attention layers'; the output head's own rounds.
  `lotRows_k7`     the next token's place, with the step that enters the head's segment in front.
  `lotKeeps_free`  a lot of which nothing is asked.
  `free_k12`, `free_k13`, `free_k13At4`   the proximity test; the members' batching; W's commitment.
Limits. K1's lot and K9's (with K10's closing) are not treated here. Nothing on soundness or on
hiding.

-/
import Johnson.Top.H0.K2Hands.LotsKeep
import Johnson.Goal.Meaning.RecSeated
import Johnson.Goal.Meaning.RecK7

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block KindName Place roundlessBlock)
open VerifiableInference.Desc.Keeps (Whole)
open VerifiableInference.Desc.Keeps1
open Meaning.K2 (Quiet)

variable {Cl : Type}

/-! ## SameRows through the ways in which a supplied sub-protocol is made -/

theorem rides_same (A : Statement) : Rides fun s : S => SameRows A s.st :=
  fun _ _ h hs => hs.trans h

theorem rowsD_of_keeps {b : Block S Cl}
    (h : ∀ A : Statement, KeepsD (fun _ => True) (fun s : S => SameRows A s.st) b) : RowsD b :=
  fun s s' rs gs hy => h s.st s s' rs gs (fun _ _ => trivial) hy (SameRows.refl _)

theorem rowsD_andThen (name : String) {p q : Block S Cl} (hp : RowsD p) (hq : RowsD q) :
    RowsD (p.andThen name q) :=
  rowsD_of_keeps fun A => keepsD_andThen name (hp.keeps (rides_same A)) (hq.keeps (rides_same A))

theorem rowsD_guarded (same : S → S → Bool) (but : Place → Bool) {b : Block S Cl} (hb : RowsD b) :
    RowsD (b.guarded same but) :=
  rowsD_of_keeps fun A => keepsD_guarded same but (hb.keeps (rides_same A))

theorem rows_of_quiet {b : Block S Cl} (W : Whole Quiet b) : RowsD b ∧ RowsRuns b :=
  ⟨fun s s' rs gs hy => sameRows_of_eq (W.1 s rs gs s' hy).1.1,
    fun c hc n s y hy => sameRows_of_eq (W.2.1 c hc n s y hy).1.1,
    fun c hc s s' hy => sameRows_of_eq (W.2.2 c hc s s' hy).1.1⟩

/-- A lot without `own` and without a batching, whose sub-protocols all have `Whole Quiet`. -/
theorem lotRows_hear {L : ProofFile.Lot} {G : ProofFile.Ground} (h0 : L.own G = [])
    (hb : ∀ a, L.batch G a = none) (h : ∀ b ∈ L.hearC G, RowsD b ∧ RowsRuns b) : LotRows L G where
  decide := fun b hm _ => by
    rcases mem_blocks hm with ⟨b₀, hm0, rfl⟩ | hm
    · rw [h0] at hm0
      cases hm0
    · exact (h b hm).1
  runs := fun b hm _ _ _ => by
    rcases mem_blocks hm with ⟨b₀, hm0, rfl⟩ | hm
    · rw [h0] at hm0
      cases hm0
    · exact (h b hm).2
  batch := hb

/-! ## Five lots at which the statement stays -/

theorem lotRows_k3 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (K3Lot.lot Z) G :=
  lotRows_hear rfl (fun _ => rfl) fun b hb => by
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hb
    exact rows_of_quiet (Meaning.K2.theStated_quiet _ _ _ _ _ _ hx)

theorem lotRows_k4 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (ProofFile.k4Lot Z) G :=
  lotRows_hear rfl (fun _ => rfl) fun b hb => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hb
    exact rows_of_quiet (Meaning.K2.blockAtC_quiet { x.2 with k3Runs := true })

theorem lotRows_k5 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (H2K5.lotN Z) G :=
  lotRows_hear rfl (fun _ => rfl) fun b hb => by
    obtain ⟨x, -, hx⟩ := List.mem_filterMap.1 hb
    obtain ⟨b₀, h0, rfl⟩ := Option.map_eq_some_iff.1 hx
    have W := rows_of_quiet (Meaning.K2.k5AtN_quiet _ _ _ _ h0)
    exact W

theorem lotRows_k6 (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotRows (P4.k6Lot Z) G :=
  lotRows_hear rfl (fun _ => rfl) fun b hb => by
    obtain ⟨ms, -, h0⟩ := Option.bind_eq_some_iff.1 (Option.mem_toList.1 hb)
    exact rows_of_quiet (Meaning.K2.seatedClaims_quiet h0)

/-- The lot of the next token's place, as `p4Pure` writes it. -/
theorem lotRows_k7 (name : String) (G : ProofFile.Ground) :
    LotRows { name := name, letters := false, own := ProofFile.h1Own } G := by
  have W := rows_of_quiet (Meaning.K2.k7Of_quiet G.W (G.built.size - 1))
  refine ⟨fun b hb _ => ?_, fun b hb _ _ _ => ?_, fun _ => rfl⟩
  · rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain rfl := List.mem_singleton.1 h0
      exact rowsD_andThen "H:1"
        (rowsD_guarded _ _ fun s s' _ _ hy => headFrontQ_smp hy) W.1
    · cases h
  · rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain rfl := List.mem_singleton.1 h0
      refine ⟨fun c hc => (by cases hc), fun c hc s s' hy => ?_⟩
      rcases List.mem_append.1 hc with hc | hc
      · cases hc
      · exact W.2.2 c hc s s' hy
    · cases h

/-! ## Three lots of which nothing is asked -/

variable {R : Fmt.RoundView → Prop} {P : S → Prop}

theorem lotKeeps_free {L : ProofFile.Lot} {G : ProofFile.Ground}
    (h : ∀ b ∈ L.blocks G, b.place.link = none ∧ b.place.kind ≠ KindName.frame)
    (hb : ∀ a, L.batch G a = none) : LotKeeps R P L G where
  decide := fun b hm hl => (hl (h b hm).1).elim
  frame := fun b hm hk => ((h b hm).2 hk).elim
  runs := fun b hm ho => (ho.elim (fun k => k (h b hm).1) fun k => (h b hm).2 k).elim
  batch := fun a mk hm => by rw [hb a] at hm; cases hm
  batchRuns := fun a mk hm => by rw [hb a] at hm; cases hm

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

theorem k12_place {T : Type} (X : VerifiableInference.Desc.K12.Parts T)
    (p : VerifiableInference.Desc.K12.P12) :
    (VerifiableInference.Desc.K12.proximityTestKind (Cl := Cl) X p).place = p.place := by
  unfold VerifiableInference.Desc.K12.proximityTestKind
  split <;> rfl

theorem free_k12 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps R P (VerifiableInference.Desc.K12.lot Z) G :=
  lotKeeps_free (fun b hb => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain rfl := List.mem_singleton.1 h0
      have e : (VerifiableInference.Desc.K12.atFinish (H2U.p12OfMade Z.made)).place =
          ⟨1, none, 2, KindName.K12⟩ :=
        (k12_place (Cl := Unit) VerifiableInference.Desc.K12.guardedProximityTestParts _).trans (p12_place Z.made)
      have e' : ((VerifiableInference.Desc.K12.atFinish (H2U.p12OfMade Z.made)).retype :
          Block S ProofFile.Cl).place = ⟨1, none, 2, KindName.K12⟩ := e
      rw [e']
      exact ⟨rfl, by decide⟩
    · cases h) fun _ => rfl

theorem free_k13 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps R P (VerifiableInference.Desc.K13.lot Z) G :=
  lotKeeps_free (fun b hb => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain rfl := List.mem_singleton.1 h0
      exact ⟨rfl, fun k => by cases k⟩
    · cases h) fun _ => rfl

theorem free_k13At4 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    LotKeeps R P (VerifiableInference.Desc.K13.lot4 Z) G :=
  lotKeeps_free (fun b hb => by
    rcases mem_blocks hb with ⟨b₀, h0, rfl⟩ | h
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h0
      have hw' := Option.mem_toList.1 hw
      unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw'
      obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw'
      exact ⟨rfl, fun k => by cases k⟩
    · cases h) fun _ => rfl

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.lotRows_k3
#print axioms VerifiableInference.Desc.First.K2.lotRows_k4
#print axioms VerifiableInference.Desc.First.K2.lotRows_k5
#print axioms VerifiableInference.Desc.First.K2.lotRows_k6
#print axioms VerifiableInference.Desc.First.K2.lotRows_k7
#print axioms VerifiableInference.Desc.First.K2.free_k12
#print axioms VerifiableInference.Desc.First.K2.free_k13
#print axioms VerifiableInference.Desc.First.K2.free_k13At4
