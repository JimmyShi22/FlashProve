-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/OfflineWidthsOfTreesSentBeforeTestAt.lean: `hwide` of `last_done` at the last thread's letters, and the three tables'
widths at the first chain's `tbH` and the shared chain's `tbKey`.

  `hwide_own`     the premise `hwide`, from three widths of the letters tb₁, tb₂
  `dueR_same`, `trees_same`   a sending's count and trees read its codes and notices alone
  `covers_full`, `omega_tree_full`   the written book has the parts' coins (the kernel)
  `idx_words`, `w_words`, `omega_words`   the three widths

Conditional on `KeySourced` and scope, and on the public numbers of the two first-chain jobs. Widths
alone: nothing on what a table holds. Nothing on any property.
-/
import E2E.OfflineWidthsOfTreesSentBeforeTest
import E2E.KeyLastDone

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (WitLens jobOmega sendPlace)
open OnBytes (TableKey)
open OnBytes.Means (Words)
open VerifiableInference.Desc (Block Place Wit)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces descriptionFromSource)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeyThread (KeyFill)
open AtPublicFiles.KeyLay (jobKWAt parIK parWK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull of_atFull idxPlace wPlace rideW)
open AtPublicFiles.KeyLastChain (threadOwn mlKey val₁Key seat_own place_own)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK)

section Letters
variable {W₀ Rc X₀ X Wk Cells M Smp Rec P₂ Wt₂ Wd : Type} {Z : VerifierAndGoals.PublicFiles}
  (K₀ : KeyPub)
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec)
  (ℓ₂ : WitLens Wt₂) (Nm : NumbersS)
  (Mg₂ : Common W₀ Rc TableKey → MeaningS St P₂ Wt₂)
  (tb₂ : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest₂ : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt₂)
  (Kp₂ : Nat → St → St → Prop) (Vd₂ : Common W₀ Rc TableKey → Prop)
  (w₂ : Common W₀ Rc TableKey) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs₁ : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X))
  (tb₁ : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Said₁ : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
  (Said₂ : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (d : (Xi × FirstState) × St)
  (Dt : Local W₀ Rc Xi Unit → MeaningS St (Xi × FirstState) (Wit Cells Unit M × Words Cb.Gl.E))
  (n₁ n₂ : Nat) (Vd : Local W₀ Rc Xi Unit → Prop) (w : Local W₀ Rc Xi Unit)
  (dfltT : Place × Table) (dfltM : Mid (Local W₀ Rc Xi Unit) X)
  (JI JW : K1.SendJob Wd X) (A : K14.SendPub)
  (lift : Local W₀ Rc Xi Unit → Wd) (ask : Local W₀ Rc Xi Unit → K14.Ask)

/-- **`hwide`**, from the three widths. At every state: the premises of the stand are not spent. -/
theorem hwide_own (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (h0 : ∀ k v h, (tb₁ (.own 0) k v h).2.words = widthIdx)
    (h5 : ∀ k v h, (tb₁ (.own 5) k v h).2.words = widthW)
    (h1 : ∀ k v h, (tb₂ (.own 1) k v h).2.words = widthOmega)
    (k : Coins (keyBook K₀)) (m : Mid (Local W₀ Rc Xi Unit) X) :
    ∀ d' ∈ (proximityTestKind guardedProximityTestParts (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p : Block T12 Unit).rounds,
      ∀ o ∈ d'.opens, oldSrc 0 o.2 = true →
        o.2 ∈ (threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt
            (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).hand 2 ∧
          ((threadOwn Xs Nr Pl K L ℓ₂ Nm Mg₂ tb₂ rest₂ Kp₂ Vd₂ w₂ w₀ rc x hs₁ tb₁ Said₁ Said₂ d Dt
            (mlKey (val₁Key Xs L)) n₁ n₂ Vd w dfltT dfltM).tableAt o.2 k m).2.words = o.1.W := by
  have hp : (jobKWAt Xs Nr Pl JI JW A lift ask).toRun.toTest.p = H2K.Member.piKWFull := place_own hs scope
  obtain ⟨blk, hb, hseat⟩ := seat_own Xs Nr Pl JI JW A lift ask
  rw [hp]
  exact hand_widths (descriptionFromSource Xs Nr Pl) _ blk hb (by rw [hseat.rounds, hp]) rfl k m
    (h0 k _ _) (h5 k _ _) (h1 k _ _)

end Letters

/-- A sending's count reads its codes and notices alone. -/
theorem dueR_same {P P' : VerifiableInference.Desc.K1.Par} (ride : Nat → Option K1.Ride) (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : K1.dueR P ride = K1.dueR P' ride := by
  simp only [K1.dueR, K1.startR, Johnson.Prover.Send.shapeAt, hc, hs]

/-- So do its trees. -/
theorem trees_same {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes) (hs : P.sent = P'.sent) :
    P.trees = P'.trees := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [hc, hs]

/-- **The written book has the coins of the three sendings.** By evaluation. -/
theorem covers_full : atFull (fun B =>
    K1.bookCovers (keyBook B) 0 ⟨idxPlace, 0⟩ (K1.dueR parIK fun _ => none) &&
      K1.bookCovers (keyBook B) 0 ⟨wPlace, 0⟩ (K1.dueR parWK rideW) &&
      K1.bookCovers (keyBook B) 1 ⟨sendPlace 5, 0⟩
        (K14.sendingPart (jobOmega ⟨QK, 0⟩)).takes) = true := by decide +kernel

/-- **The three trees are there; the first shared sending has one tree, the second more.** By
evaluation. -/
theorem omega_tree_full : (parIK.trees[0]?).isSome = true ∧ (parWK.trees[0]?).isSome = true ∧
    ((((VerifiableInference.Desc.Own.treesMade (jobOmega ⟨QK, 0⟩).Q.codes
      (jobOmega ⟨QK, 0⟩).Q.sent).getD {}).shapes.toList)[0]?).isSome = true ∧
    K14.treesU QK = 1 ∧ 0 < AtPublicFiles.KeyTreesKey.treesOf5 QK := by decide +kernel

/-- **The shared chain's tree 1 is Omega's tree 0**, where U has one tree and Omega has some. -/
theorem tbKey_one {Bk : ProverCoinCounts} {W₀ Rc : Type} (Q : _root_.Desc.K14.P14) (hU : K14.treesU Q = 1)
    (hO : 0 < AtPublicFiles.KeyTreesKey.treesOf5 Q) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (tk : Nat → Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (tt : Nat → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (k : Coins Bk) (v : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    AtPublicFiles.KeyTreesKey.tbKey Q weights rand tk tt (.own 1) k v h =
      K14.sendTable (jobOmega ⟨Q, 0⟩) (K14.witOf Q weights rand) (sendPlace 5) 1 0 k v h := by
  have h1 : ¬ 1 < K14.treesU Q := by omega
  have h2 : 1 < K14.treesU Q + AtPublicFiles.KeyTreesKey.treesOf5 Q := by omega
  simp only [AtPublicFiles.KeyTreesKey.tbKey]
  rw [if_neg h1, if_pos h2, hU]
  try rfl

section Widths
variable {W₀ Rc X' Wa : Type} {K₀ : KeyPub}

/-- **The table of the index masks has its width.** -/
theorem idx_words (hK : fullPub = some K₀) (J : K1.SendJob Wa X') (own₀ : X')
    (hp : J.P.place = idxPlace) (hc : J.P.codes = parIK.codes) (hs : J.P.sent = parIK.sent)
    (hr : J.ride = fun _ => none) (k : Coins (keyBook K₀)) (v : Wa) (h : List Fmt.Drawn) :
    (K1.treeTbl 0 id J own₀ 0 k v h).2.words = widthIdx := by
  have hb : K1.bookCovers (keyBook K₀) 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true := by
    have e := of_atFull covers_full hK
    simp only [Bool.and_eq_true] at e
    rw [hp, hr, dueR_same _ hc hs]
    exact e.1.1
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 omega_tree_full.1
  rw [tree_words 0 (by omega) id J own₀ 0 t hb (by rw [trees_same hc hs]; exact ht) k v h]
  unfold widthIdx
  rw [ht]
  rfl

/-- **W's table has its width.** -/
theorem w_words (hK : fullPub = some K₀) (J : K1.SendJob Wa X') (own₀ : X')
    (hp : J.P.place = wPlace) (hc : J.P.codes = parWK.codes) (hs : J.P.sent = parWK.sent)
    (hr : J.ride = rideW) (k : Coins (keyBook K₀)) (v : Wa) (h : List Fmt.Drawn) :
    (K1.treeTbl 0 id J own₀ 0 k v h).2.words = widthW := by
  have hb : K1.bookCovers (keyBook K₀) 0 ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = true := by
    have e := of_atFull covers_full hK
    simp only [Bool.and_eq_true] at e
    rw [hp, hr, dueR_same _ hc hs]
    exact e.1.2
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 omega_tree_full.2.1
  rw [tree_words 0 (by omega) id J own₀ 0 t hb (by rw [trees_same hc hs]; exact ht) k v h]
  unfold widthW
  rw [ht]
  rfl

/-- **The tree that the last chain takes from the shared sending of Omega has its width.** -/
theorem omega_words (hK : fullPub = some K₀) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
    (k : Coins (keyBook K₀)) (v : Common W₀ Rc TableKey) (h : List Fmt.Drawn) :
    (AtPublicFiles.KeyTreesKey.tbKey QK weights rand tk tt (.own 1) k v h).2.words = widthOmega := by
  obtain ⟨-, -, h3, hU, hO⟩ := omega_tree_full
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 h3
  have hb := (K1.lentCut_isSome k 1 (by omega) ⟨sendPlace 5, 0⟩
    (K14.sendingPart (jobOmega ⟨QK, 0⟩)).takes).trans (by
      have e := of_atFull covers_full hK
      simp only [Bool.and_eq_true] at e
      exact e.2)
  rw [tbKey_one QK hU hO]
  rw [send_words (jobOmega ⟨QK, 0⟩) _ (sendPlace 5) 1 0 t k v h hb ht]
  unfold widthOmega
  rw [ht]
  rfl

end Widths

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.hwide_own
#print axioms AtPublicFiles.OfflineRows.dueR_same
#print axioms AtPublicFiles.OfflineRows.trees_same
#print axioms AtPublicFiles.OfflineRows.covers_full
#print axioms AtPublicFiles.OfflineRows.omega_tree_full
#print axioms AtPublicFiles.OfflineRows.tbKey_one
#print axioms AtPublicFiles.OfflineRows.idx_words
#print axioms AtPublicFiles.OfflineRows.w_words
#print axioms AtPublicFiles.OfflineRows.omega_words
