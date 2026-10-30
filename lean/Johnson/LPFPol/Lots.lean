-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/Lots.lean: the fifteen lots of the first chain of the proof file's description
(`ProofFile.onlineFirstChainBlockTables`, Johnson/Desc/ProofFile/OnlineDescriptionBlocks.lean) have one skeleton at two acceptance policies.
Statements and proofs.
The skeleton is that of Johnson/LPFPol/SkR/: a block less its functions, with its rounds and oracles
whole.
  `sk0` … `sk12`, `sk14`: fourteen lots: by unfolding: none of them reads one of the three numbers
      in what a skeleton holds.
  `HeadSame W C theta cap`: the two tests on the plan of the output head's own block (`Par.ok`,
      `laidOk`) give at the other policy what they give at W's own.
  `sk13`: the lot of the output head's own rounds, under `HeadSame`.
  `lots_same`: so the list of the lots' skeletons is one.
  `steady_pure`: `Steady` at every lot: fourteen supply no batching, by their texts; the batching's
      lot makes blocks with one skeleton at any two gatherers.
Limits. `HeadSame` is a premise. A skeleton is blind to what a block decides. Nothing on soundness.

-/
import Johnson.LPFPol.WithPol
import Johnson.LPFPol.SkR.SkelEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace LPFPol
open LPFPol.SkR
open VerifiableInference.Desc.Kinds.Head (parOf laidOk seatedClaims blockClaims tested startOk)

section
variable (Z : ProofFile.Pub) (G : ProofFile.Ground) (pol' : ByteArray) (C theta cap : Nat)

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk0 : lotSk (wpG G C theta cap) (ProofFile.framesLot (wpZ Z pol' C theta cap)) =
    lotSk G (ProofFile.framesLot Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk1 : lotSk (wpG G C theta cap) (ProofFile.k1Pure (wpZ Z pol' C theta cap)) =
    lotSk G (ProofFile.k1Pure Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk2 : lotSk (wpG G C theta cap) (ProofFile.k2Pure (wpZ Z pol' C theta cap)) =
    lotSk G (ProofFile.k2Pure Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk3 : lotSk (wpG G C theta cap) (K3Lot.lot (wpZ Z pol' C theta cap)) =
    lotSk G (K3Lot.lot Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk4 : lotSk (wpG G C theta cap) (ProofFile.k4Lot (wpZ Z pol' C theta cap)) =
    lotSk G (ProofFile.k4Lot Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk5 : lotSk (wpG G C theta cap) (H2K5.lotN (wpZ Z pol' C theta cap)) =
    lotSk G (H2K5.lotN Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk6 : lotSk (wpG G C theta cap) (ProofFile.P1K8.lot (wpZ Z pol' C theta cap)) =
    lotSk G (ProofFile.P1K8.lot Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk7 : lotSk (wpG G C theta cap) (ProofFile.k9Ninth (wpZ Z pol' C theta cap)) =
    lotSk G (ProofFile.k9Ninth Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk8 : lotSk (wpG G C theta cap) (K11.lot (wpZ Z pol' C theta cap)) = lotSk G (K11.lot Z) :=
    rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk9 : lotSk (wpG G C theta cap) (VerifiableInference.Desc.K12.lot
    (wpZ Z pol' C theta cap)) = lotSk G (VerifiableInference.Desc.K12.lot Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk10 : lotSk (wpG G C theta cap) (VerifiableInference.Desc.K13.lot
    (wpZ Z pol' C theta cap)) = lotSk G (VerifiableInference.Desc.K13.lot Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk11 : lotSk (wpG G C theta cap) (VerifiableInference.Desc.K13.lot4
    (wpZ Z pol' C theta cap)) = lotSk G (VerifiableInference.Desc.K13.lot4 Z) := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk12 : lotSk (wpG G C theta cap) (VerifiableInference.Desc.K13.lotEnd
    (wpZ Z pol' C theta cap)) = lotSk G (VerifiableInference.Desc.K13.lotEnd Z) := rfl

/-- The second of the head's two lots, as `ProofFile.p4Pure` writes it. -/
def k7Lot' : ProofFile.Lot :=
  { name := "the next token (K7), with the step that enters the head's link"
    letters := false
    own := ProofFile.h1Own }

theorem p4_is : ProofFile.p4Pure Z = [P4.k6Lot Z, k7Lot'] := rfl

set_option maxHeartbeats 400000 in
set_option smartUnfolding false in
theorem sk14 : lotSk (wpG G C theta cap) k7Lot' = lotSk G k7Lot' := rfl

end

/-- The head's own block's two tests on the plan do not move. -/
structure HeadSame (W : OnBytes.Model.Verify.Public) (C theta cap : Nat) : Prop where
  par : ∀ w, (parOf (W.hS.withPol C theta cap) w).ok = (parOf W.hS w).ok
  laid : laidOk (W.withPol C theta cap) = laidOk W

/-- The place's parameters at the other policy: the policy's field alone turns. -/
theorem parOf_withPol (h : OnBytes.Model.Head.Shape) (C theta cap w : Nat) :
    parOf (h.withPol C theta cap) w = { parOf h w with policy :=
        { C := C, theta := theta, cap := cap } } := rfl

/-- The seated block's skeleton, written out. b: its test on the plan. -/
def k6Form (p : VerifiableInference.Desc.Kinds.Head.Par) (l : Nat) (ms : List (Nat × Nat))
    (b : Bool) : Skel :=
  let rs := p.declare (let _ := p.sizes; VerifiableInference.Desc.Kinds.Head.rounds)
  { name := "the output head's own rounds", place := ⟨1, some l, 4, .K6⟩
    nRounds := rs.length, nOracles := (rs.map fun _ =>
        ([] : List VerifiableInference.Desc.Oracle)).length
    rounds := rs, oracles := rs.map fun _ => []
    told := toldFrom 0 (rs.map fun _ => []), before := ms, planOk := b
    claims := ["norm", "join", "policy", "logits"], after := [] }

theorem skel_k6Form {Cl : Type} (look : VerifiableInference.Desc.K3.Seat
    VerifiableInference.Desc.First.S Cl)
    (L : VerifiableInference.Desc.Kinds.Head.Seat VerifiableInference.Desc.First.S) (l : Nat)
    (p : VerifiableInference.Desc.Kinds.Head.Par) (ok : Bool)
    (st : VerifiableInference.Desc.First.S → Bool) (ms : List (Nat × Nat)) :
    skel (tested ok st ms (VerifiableInference.Desc.Kinds.Head.kindWithJoin look L l 4 p)) =
      k6Form p l ms (p.ok && ok) := rfl

theorem k6Form_pol (p : VerifiableInference.Desc.Kinds.Head.Par)
    (P' : VerifiableInference.Desc.Kinds.Head.Policy) (l : Nat) (ms : List (Nat × Nat)) (b : Bool) :
    k6Form { p with policy := P' } l ms b = k6Form p l ms b := rfl

/-- The seated block's skeleton at a public record: no function of a block is left in it. -/
theorem seated_skel (W : OnBytes.Model.Verify.Public) (l : Nat) (ms : List (Nat × Nat)) :
    (seatedClaims W l ms).map skel =
      (W.H.tl.ix.U.getD 2 none).map fun _ =>
        k6Form (parOf W.hS ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)) l ms
          ((parOf W.hS ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)).ok &&
              laidOk W) := by
  cases h : W.H.tl.ix.U.getD 2 none with
  | none => simp only [seatedClaims, blockClaims, h, Option.map_none]
  | some i =>
    simp only [seatedClaims, blockClaims, h, Option.map_some]
    exact congrArg some (skel_k6Form _ _ _ _ _ _ _)

theorem seated_same (W : OnBytes.Model.Verify.Public) (C theta cap : Nat)
    (h : HeadSame W C theta cap)
    (l : Nat) (ms : List (Nat × Nat)) :
    (seatedClaims (W.withPol C theta cap) l ms).map skel = (seatedClaims W l ms).map skel := by
  rw [seated_skel, seated_skel]
  show (W.H.tl.ix.U.getD 2 none).map (fun _ =>
      k6Form (parOf (W.hS.withPol C theta cap)
          ((OnBytes.Params.settingOf W.P.frame).workOf .field .request)) l ms
        ((parOf (W.hS.withPol C theta cap) ((OnBytes.Params.settingOf W.P.frame).workOf .field
            .request)).ok &&
          laidOk (W.withPol C theta cap))) = _
  rw [h.par, h.laid, parOf_withPol, k6Form_pol]

/-- The head's lot's blocks' skeletons: no function of a block is left. -/
theorem k6_blocks (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ((P4.k6Lot Z).blocks G).map skel =
      ((P4.headBefore Z G).bind fun ms => (seatedClaims G.W (G.built.size - 1) ms).map
          skel).toList := by
  show (P4.k6Hear Z G).map skel = _
  unfold P4.k6Hear
  cases P4.headBefore Z G with
  | none => rfl
  | some ms =>
    show ((seatedClaims G.W (G.built.size - 1) ms).toList).map skel =
      ((seatedClaims G.W (G.built.size - 1) ms).map skel).toList
    cases seatedClaims G.W (G.built.size - 1) ms <;> rfl

theorem headBefore_wp (Z : ProofFile.Pub) (G : ProofFile.Ground) (pol' : ByteArray) (C theta cap : Nat) :
    P4.headBefore (wpZ Z pol' C theta cap) (wpG G C theta cap) = P4.headBefore Z G := rfl

theorem sk13 (Z : ProofFile.Pub) (G : ProofFile.Ground) (pol' : ByteArray) (C theta cap : Nat)
    (h : HeadSame G.W C theta cap) :
    lotSk (wpG G C theta cap) (P4.k6Lot (wpZ Z pol' C theta cap)) = lotSk G (P4.k6Lot Z) := by
  have hb : ((P4.k6Lot (wpZ Z pol' C theta cap)).blocks (wpG G C theta cap)).map skel =
      ((P4.k6Lot Z).blocks G).map skel := by
    rw [k6_blocks, k6_blocks, headBefore_wp]
    show ((P4.headBefore Z G).bind fun ms =>
      (seatedClaims (G.W.withPol C theta cap) (G.built.size - 1) ms).map skel).toList = _
    simp only [seated_same G.W C theta cap h]
  show LotSk.mk _ _ _ (((P4.k6Lot (wpZ Z pol' C theta cap)).blocks (wpG G C theta cap)).map skel) _
      _ _ =
    LotSk.mk _ _ _ (((P4.k6Lot Z).blocks G).map skel) _ _ _
  rw [hb]
  rfl

/-- **The lots' skeletons are one.** -/
theorem lots_same (Z : ProofFile.Pub) (G : ProofFile.Ground) (pol' : ByteArray) (C theta cap : Nat)
    (h : HeadSame G.W C theta cap) :
    (ProofFile.onlineFirstChainBlockTables (wpZ Z pol' C theta cap)).map (lotSk (wpG G C theta cap)) =
      (ProofFile.onlineFirstChainBlockTables Z).map (lotSk G) := by
  unfold ProofFile.onlineFirstChainBlockTables
  rw [p4_is, p4_is]
  simp only [List.map_cons, List.map_nil, List.map_append]
  rw [sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12,
      sk13 Z G pol' C theta cap h, sk14]

/-- The batching's lot is steady. -/
theorem steady_k9 (Z : ProofFile.Pub) (G : ProofFile.Ground) : Steady G (ProofFile.k9Ninth Z) := by
  intro a mk e g g'
  have hp : ∃ p, mk = fun g => VerifiableInference.Desc.K9.batch VerifiableInference.Desc.K9.atS p
      g := by
    unfold ProofFile.k9Ninth at e
    dsimp only at e
    split at e
    · obtain ⟨p, _, hp⟩ := Option.bind_eq_some_iff.1 e
      split at hp
      · exact ⟨p, (Option.some.inj hp).symm⟩
      · cases hp
    · cases e
  obtain ⟨p, rfl⟩ := hp
  rfl

/-- **Every lot is steady.** -/
theorem steady_pure (Z : ProofFile.Pub) (G : ProofFile.Ground) : ∀ L ∈ ProofFile.onlineFirstChainBlockTables Z, Steady G L := by
  intro L hL
  unfold ProofFile.onlineFirstChainBlockTables at hL
  rw [p4_is] at hL
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) |
      rfl | rfl
  all_goals first
    | exact steady_k9 Z G
    | exact steady_none G _ fun _ => rfl

end LPFPol

#print axioms LPFPol.lots_same
#print axioms LPFPol.steady_pure
