-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/WeightClaimsTests.lean: the test on the plan claimsB
(Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean) follows from four lighter tests: the count of the
weight claims, the merge's tests on the first k of them, the same tests on the rest, and the tests
on the embedding's claim in a second text. General; nothing is evaluated.

Why. claimsB runs the merge's tests on all the weight claims at once, and its embedding's claim
makes the factor on the vocabulary as V zeros with one change for each of the T tokens. Cut in four,
each test can stand alone as a closed Bool that Lean's kernel evaluates. The second
text embeddingClaimZeros writes that factor as V zeros and leaves out the T changes; the merge's
tests read only the factor's sizes.

  embeddingClaimZeros     claimE's text (OnBytes/Model/LayerPanels.lean) with V zeros for the factor
                          on the vocabulary.
  embeddingClaim_alikeZeros   the two texts return together, claims of one unit with factors of the
                          same sizes.
  claimPassesMerge        the merge's two tests on one claim.
  atWeightClaims          the weight claims at the blank environment, handed to a test.
  embeddingClaimTest, weightClaimsCountTest   two of the four tests.
  **claimsTest_ofFourTests**   the four tests give claimsB.

Limits. One way: nothing is said of the four tests where claimsB accepts. No test is shown to accept
here. What a test costs is not said. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.First.K4.Returns.Pub.ClaimsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel FacAlike ClaimAlike optRel_bind optRel_bind_same mapM_opt_rel
  all_alike shape_alike size_foldl_modify)

/-- claimE's text (OnBytes/Model/LayerPanels.lean) with V zeros for the factor on the vocabulary. -/
def embeddingClaimZeros (c : ClaimEnv) (ZE tkh : Array E) (V : Nat) (tokv : Array Nat) : Option
    WsClaim := do
  let y := c.v.y
  if tokv.size != y.T || tokv.any (· ≥ V) then none
  let ui ← c.wsLay.unitOf 12 y.h.L
  let u ← c.wsLay.U[ui]?
  let (low, _tok) ← (cutLast ZE y.h.lt).toOption
  let pnt := tkh ++ low
  let f ← u.g.mapM fun (G : WsGrp) =>
    if G.name == "v" then some ({ AV := Array.replicate V zeroE } : WsFac)
    else if G.z > y.lPd then none
    else do
      let e := eqTab (pnt.extract 0 (y.lPd - G.z))
      let HV ← (Array.range G.o).mapM fun hi => e[hi]?
      pure { pt := (Array.range G.z).map fun i => pnt.getD (y.lPd - G.z + i) zeroE, HV }
  pure { ui := ui, f := f }

/-- **The two texts return together, claims of one unit with factors of the same sizes.** -/
theorem embeddingClaim_alikeZeros (c : ClaimEnv) (ZE tkh : Array E) (V : Nat) (tokv : Array Nat) :
    OptRel ClaimAlike (c.claimE ZE tkh V tokv) (embeddingClaimZeros c ZE tkh V tokv) := by
  unfold ClaimEnv.claimE embeddingClaimZeros
  dsimp only
  refine optRel_ite trivial (optRel_bind_same fun _ => ?_)
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind_same fun _ => ?_
  refine optRel_bind_same fun a => ?_
  obtain ⟨low, tok⟩ := a
  dsimp only
  refine optRel_bind (S := All2 FacAlike) (mapM_opt_rel (fun G => ?_) _)
    fun _ _ hf => ⟨rfl, hf⟩
  refine optRel_ite ?_ (optRel_ite trivial ?_)
  · refine ⟨rfl, rfl, ?_⟩
    show Array.size _ = Array.size _
    rw [size_foldl_modify]
  · exact optRel_bind_same fun _ => ⟨rfl, rfl, rfl⟩

/-- The merge's two tests on one claim. -/
def claimPassesMerge (lay : WsLay) (c : WsClaim) : Bool :=
  decide (c.ui < lay.U.size) && (wsClaimShape lay c).isOk

/-- The weight claims at the blank environment, handed to a test. -/
def atWeightClaims (P : Pub) (hp : HPlan2) (g : Nat) (f : List WsClaim → Bool) : Bool :=
  (callsTS P).any fun TS => ((blankClaims P hp g).weightClaims TS).any f

/-- The embedding's claim in its second text passes; true after the first group. -/
def embeddingClaimTest (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  if (g == 0) = true then
    (embeddingClaimZeros (blankClaims P hp g) (Array.replicate (P.y.ls + P.y.h.lt) zeroE)
      (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0)).any
        (claimPassesMerge P.wsLay)
  else true

/-- The count: the weight claims, with the embedding's claim in the first group, are as many as the
plan counts, at least one, at most 4096. -/
def weightClaimsCountTest (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  atWeightClaims P hp g fun cp =>
    cp.length + (if (g == 0) = true then 1 else 0) == hp.NCL && decide (0 < hp.NCL) &&
      decide (hp.NCL ≤ 4096)

/-- A list of the right length that passes claimPassesMerge member by member passes the library's
claimTests. -/
theorem claimTests_ofEach {lay : WsLay} {n : Nat} {l : List WsClaim} (h1 : l.length =
    n) (h2 : 0 < n)
    (h3 : n ≤ 4096) (h4 : l.all (claimPassesMerge lay) = true) : claimTests lay n l.toArray =
        true := by
  unfold claimTests
  have a1 : (l.toArray.all fun c => decide (c.ui < lay.U.size)) = true := by
    simp only [List.all_toArray]
    rw [List.all_eq_true] at h4 ⊢
    intro c hc
    have := h4 c hc
    unfold claimPassesMerge at this
    rw [Bool.and_eq_true] at this
    exact this.1
  have a2 : (l.toArray.all fun c => (wsClaimShape lay c).isOk) = true := by
    simp only [List.all_toArray]
    rw [List.all_eq_true] at h4 ⊢
    intro c hc
    have := h4 c hc
    unfold claimPassesMerge at this
    rw [Bool.and_eq_true] at this
    exact this.2
  rw [a1, a2]
  simp only [Array.isEmpty, List.size_toArray, h1]
  simp only [beq_self_eq_true, Bool.and_true, Bool.true_and, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_false_iff_not, decide_eq_true_eq]
  omega

/-- **claimsB follows from four lighter tests.** k: where the list of the weight claims is cut. -/
theorem claimsTest_ofFourTests (P : Pub) (hp : HPlan2) (g k : Nat) (hN : weightClaimsCountTest P hp
    g = true)
    (hA : (atWeightClaims P hp g fun cp => (cp.take k).all (claimPassesMerge P.wsLay)) = true)
    (hB : (atWeightClaims P hp g fun cp => (cp.drop k).all (claimPassesMerge P.wsLay)) = true)
    (hE : embeddingClaimTest P hp g = true) : claimsB P hp g = true := by
  unfold weightClaimsCountTest atWeightClaims at hN
  unfold atWeightClaims at hA hB
  unfold claimsB
  cases hT : callsTS P with
  | none =>
    rw [hT] at hN
    cases hN
  | some TS =>
    rw [hT] at hN hA hB
    cases hW : (blankClaims P hp g).weightClaims TS with
    | none =>
      have hN' : ((blankClaims P hp g).weightClaims TS).any _ = true := hN
      rw [hW] at hN'
      cases hN'
    | some cp =>
      have hN' : ((blankClaims P hp g).weightClaims TS).any _ = true := hN
      have hA' : ((blankClaims P hp g).weightClaims TS).any _ = true := hA
      have hB' : ((blankClaims P hp g).weightClaims TS).any _ = true := hB
      rw [hW] at hN' hA' hB'
      have n0 : (cp.length + (if (g == 0) = true then 1 else 0) == hp.NCL && decide (0 < hp.NCL) &&
          decide (hp.NCL ≤ 4096)) = true := hN'
      have a0 : (cp.take k).all (claimPassesMerge P.wsLay) = true := hA'
      have b0 : (cp.drop k).all (claimPassesMerge P.wsLay) = true := hB'
      rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, decide_eq_true_eq]
        at n0
      have hall : cp.all (claimPassesMerge P.wsLay) = true := by
        rw [← List.take_append_drop k cp, List.all_append, a0, b0]
        rfl
      show Option.any _ ((blankClaims P hp g).weightClaims TS) = true
      rw [hW]
      unfold embeddingClaimTest at hE
      by_cases hg : (g == 0) = true
      · rw [if_pos hg] at hE n0
        have rel := embeddingClaim_alikeZeros (blankClaims P hp g) (Array.replicate (P.y.ls +
            P.y.h.lt) zeroE)
          (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0)
        cases hz : embeddingClaimZeros (blankClaims P hp g) (Array.replicate (P.y.ls + P.y.h.lt)
            zeroE)
          (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0) with
        | none =>
          rw [hz] at hE
          cases hE
        | some cz =>
          rw [hz] at hE rel
          cases he : (blankClaims P hp g).claimE (Array.replicate (P.y.ls + P.y.h.lt) zeroE)
            (Array.replicate (P.y.lPd - P.y.ls) zeroE) P.V (Array.replicate P.y.T 0) with
          | none =>
            rw [he] at rel
            exact rel.elim
          | some ce =>
            rw [he] at rel
            have rel' : ClaimAlike ce cz := rel
            have hE' : claimPassesMerge P.wsLay cz = true := hE
            rw [if_pos hg]
            show claimTests P.wsLay hp.NCL (cp ++ [ce]).toArray = true
            rw [claimTests_alike P.wsLay hp.NCL
              ((All2.refl (fun c => (⟨rfl, All2.refl (fun _ => ⟨rfl, rfl, rfl⟩) _⟩ :
                ClaimAlike c c)) cp).append (All2.cons rel' All2.nil))]
            refine claimTests_ofEach (by rw [List.length_append]; exact n0.1.1) n0.1.2 n0.2 ?_
            rw [List.all_append, hall]
            show (claimPassesMerge P.wsLay cz && true) = true
            rw [hE']
            rfl
      · rw [if_neg hg] at n0
        rw [if_neg hg]
        show claimTests P.wsLay hp.NCL (cp ++ []).toArray = true
        rw [List.append_nil]
        exact claimTests_ofEach n0.1.1 n0.1.2 n0.2 hall

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.embeddingClaimZeros
#print axioms OnBytes.Desc.First.K4.RtPub.embeddingClaim_alikeZeros
#print axioms OnBytes.Desc.First.K4.RtPub.claimPassesMerge
#print axioms OnBytes.Desc.First.K4.RtPub.atWeightClaims
#print axioms OnBytes.Desc.First.K4.RtPub.embeddingClaimTest
#print axioms OnBytes.Desc.First.K4.RtPub.weightClaimsCountTest
#print axioms OnBytes.Desc.First.K4.RtPub.claimTests_ofEach
#print axioms OnBytes.Desc.First.K4.RtPub.claimsTest_ofFourTests
