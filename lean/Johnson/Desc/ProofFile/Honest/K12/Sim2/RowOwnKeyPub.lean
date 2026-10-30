-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the public numbers of the key file's own test, and where its senders stand.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowOwnKeyPub.lean: what trees_at_plain_job (RowOwnKeyAtRun.lean) asks of public numbers, at the written sendings of the index masks (parIK)
and of W (parWK, rideW), at Omega's written plan, at the key's own test piKWFull, and at the key's written rounds, by Lean's kernel. The book's tests are not here. Numbers alone:
nothing on a run, on completeness, soundness or hiding.

  ownStage, shI, shW, msI, msW, msO   the test's first stage; the two sendings' trees; the three members' shapes
  own_numbers, own_I_full, own_W_full, own_O_full, own_shapes_full   closed facts
  own_splitAt                 a list of blocks with written rows, cut at a row
  own_cut                 where the three senders stand, and how many trees are in front
  own_I_at, own_W_at      the two sendings' numbers at every plan at the written codes and messages
  own_trees_stand         the clause trees at a stand, with what stays named
  idx_plan, w_plan        the key's two jobs have the written codes and messages
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowOwnKeyAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFoldedPub
import E2E.KeyJobW
import E2E.KeyThreadBase
import Johnson.Desc.ProofFile.Honest.K12.Sim2.OwnKeyBook
import Johnson.M1.KeyNumbersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Place FileDescription blocksOk)
open Johnson.Prover.Send (shapeAt)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyLay (parIK parWK shapeOK)
open AtPublicFiles.KeyBook (rideW fullFirst fullShared wPlace idxPlace omegaPlace places_named)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K14 (jobOmega sendingsFit)
open Johnson.KB8 (declKeyFull)
open OnBytes.Slice (codeOf)

/-- The test's first stage. -/
abbrev ownStage : Fmt.M1.Stage := piKWFull.nums.stages.headD default
/-- The two sendings' trees. -/
abbrev shI : OnBytes.TreeShape := parIK.trees.getD 0 {}
abbrev shW : OnBytes.TreeShape := parWK.trees.getD 0 {}

/-- Omega's plan at the written codes and shape. -/
abbrev planAK : ProofFile.Honest.K14.SendPub := ProofFile.Honest.K12.Light.planOf AtPublicFiles.KeyLay.AK.P.codes AtPublicFiles.KeyLay.AK.P.S

/-- The depths and sources of the test's first trees. -/
theorem own_numbers : ownStage.h ≤ ownStage.k ∧ 2 * ownStage.k + 1 ≤ ownStage.h + ownStage.Z.l ∧
    [13, 22, 22] = piKWFull.nums.first.map (·.1.a) ∧
    piKWFull.nums.first.map (fun o => ProofFile.Honest.srcOf 2 o.2) = [(0, 0), (0, 5), (1, 1)] ∧
    (treesW piKWFull).map (·.1) = [13, 22, 22] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- The index masks' sending. -/
theorem own_I_full : parIK.trees[0]? = some shI ∧
    columnWidth parIK 0 = shI.mainWidth + shI.maskWidth ∧ parIK.sent.size = 1 ∧
    (shapeAt parIK 0).mainRows = 0 ∧ (shapeAt parIK 0).maskRows = 1 ∧
    codeOf (parIK.codes.mask.getD (shapeAt parIK 0).maskCode default) = ownStage.Z ∧
    (List.range parIK.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade parIK.codes parIK.sent).getD {}).tree[k]? == some 0) = [0] ∧
    0 < (K1.dueR parIK (fun _ => none)).f + (K1.dueR parIK (fun _ => none)).e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- W's sending. -/
theorem own_W_full : parWK.trees[0]? = some shW ∧
    columnWidth parWK 0 = shW.mainWidth + shW.maskWidth ∧ parWK.sent.size = 2 ∧
    rideW 1 = some ⟨ownStage.k, ownStage.h⟩ ∧ ((shapeAt parWK 1).mainDeg == 3) = false ∧
    2 * ownStage.k + 1 + 2 ^ ownStage.h * ownStage.Z.r ≤
      (K1.dueMsg parWK.codes (shapeAt parWK 1) (rideW 1)).e ∧
    (shapeAt parWK 0).mainDeg = 3 ∧
    codeOf (parWK.codes.base.getD (shapeAt parWK 0).code default) = ownStage.C ∧
    codeOf (parWK.codes.mask.getD (shapeAt parWK 0).maskCode default) = ownStage.Z ∧
    codeOf (parWK.codes.mask.getD (shapeAt parWK 1).maskCode default) = ownStage.Z ∧
    (shapeAt parWK 1).maskRows = 2 ^ ownStage.h ∧ (shapeAt parWK 1).mainRows = 0 ∧
    (List.range parWK.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade parWK.codes parWK.sent).getD {}).tree[k]? == some 0) = [0, 1] ∧
    0 < (K1.dueR parWK rideW).f + (K1.dueR parWK rideW).e := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- Omega's sending. -/
theorem own_O_full : sendingsFit planAK.P = true ∧ widthFits (jobOmega planAK) 0 = true ∧
    sameCode ((jobOmega planAK).Q.codes.base.getD (Light.shapeAt (jobOmega planAK) 0).code default)
      ownStage.C = true ∧
    mineOf (jobOmega planAK) 0 = [0] ∧ (Light.shapeAt (jobOmega planAK) 0).maskRows = 0 ∧
    0 < (ProofFile.Honest.K14.takesOf (jobOmega planAK).Q.codes (jobOmega planAK).Q.sent
        (jobOmega planAK).sort).f +
      (ProofFile.Honest.K14.takesOf (jobOmega planAK).Q.codes (jobOmega planAK).Q.sent
        (jobOmega planAK).sort).e ∧
    ((jobOmega planAK).Q.sent.getD 0 default).shape = shapeOK := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

/-- The three members' shapes. -/
theorem own_shapes_full : ((shapesW parIK parWK shapeOK).zipIdx.map fun x =>
    memShape x.1 ((firstsOf (shapesW parIK parWK shapeOK)).getD x.2 (none, none))) =
    [⟨0, 0, 0, 1, true⟩, ⟨16, 1, 1, 1, false⟩, ⟨0, 12, 0, 0, false⟩] := by
  decide +kernel

/-- A list of blocks with written rows, cut at a row. -/
theorem own_splitAt {S Cl : Type} (bs : List (Block S Cl)) (rows : List (Place × ℕ))
    (h : (bs.map fun b => (b.place, b.rounds.length)) = rows) (i : ℕ) (hi : i < rows.length) :
    ∃ (pre : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl)),
      bs = pre ++ b :: t ∧ pre.length = i ∧ (b.place, b.rounds.length) = rows[i] := by
  subst h
  rw [List.length_map] at hi
  refine ⟨bs.take i, bs[i], bs.drop (i + 1), ?_, ?_, ?_⟩
  · rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  · rw [List.length_take]
    omega
  · simp

/-- Rounds in front of a cut, off the written rows. -/
theorem own_front_rounds {S Cl : Type} {pre t : List (Block S Cl)} {b : Block S Cl} {D : List Fmt.DeclaredRound}
    (hD : (pre ++ b :: t).flatMap (·.rounds) = D) :
    pre.flatMap (·.rounds) = D.take (pre.flatMap (·.rounds)).length := by
  subst hD
  rw [List.flatMap_append, List.take_left']
  rfl

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : VerifiableInference.Desc.Key.Source} {N : H2U.PlaceNums}
  {Pl : VerifiableInference.Desc.Key.LaterPlaces}

set_option maxRecDepth 1000000 in
theorem own_rows_written : fullFirst.length = 19 ∧ fullFirst[0]? = some (idxPlace, 2) ∧
    fullFirst[17]? = some (wPlace, 2) ∧ fullShared[5]? = some (omegaPlace, 2) ∧
    ((fullFirst.take 17).map (·.2)).sum = 18848 ∧ ((fullShared.take 5).map (·.2)).sum = 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | decide +kernel | rfl

set_option maxRecDepth 1000000 in
theorem own_roots_written : Johnson.G.OfPlan.rootsOf (declKeyFull.1.take 18848) = 5 ∧
    Johnson.G.OfPlan.rootsOf (declKeyFull.2.1.take 4) = 1 := by
  decide +kernel

theorem own_shaped_first {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    ∀ b ∈ F.first.blocksInOrder, b.shaped = true := by
  have hb : blocksOk F.first.blocksInOrder = true := by
    cases hb : blocksOk F.first.blocksInOrder with
    | true => rfl
    | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h
  intro b hm
  have := List.all_eq_true.1 hb b hm
  rw [Bool.and_eq_true] at this
  exact this.2

/-- How many rounds stand in front of a cut, off the written rows. -/
theorem own_rows_front {S Cl : Type} {pre t : List (Block S Cl)} {b : Block S Cl}
    {rows : List (Place × ℕ)}
    (h : ((pre ++ b :: t).map fun b => (b.place, b.rounds.length)) = rows) :
    (pre.flatMap (·.rounds)).length = ((rows.take pre.length).map (·.2)).sum := by
  subst h
  rw [List.map_append, List.take_left' (List.length_map _), List.map_map, List.length_flatMap]
  rfl

/-- **Where the three senders stand**, and how many trees stand in front of W's sender and of Omega's. -/
theorem own_cut (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z Xs N Pl) :
    (∃ (bI : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)
        (tI : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)),
      (keyFileDescription Xs N Pl).first.blocksInOrder = [] ++ bI :: tI ∧ bI.place = idxPlace ∧ bI.rounds ≠ []) ∧
    (∃ (pW : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl))
        (bW : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)
        (tW : List (Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl)),
      (keyFileDescription Xs N Pl).first.blocksInOrder = pW ++ bW :: tW ∧ bW.place = wPlace ∧ bW.rounds ≠ [] ∧
        treesTo (keyFileDescription Xs N Pl).first.blocksInOrder pW.length + 0 = 5 ∧
        (pW.flatMap (·.rounds)).length = 18848) ∧
    (∃ (pO : List (Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl))
        (bO : Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl)
        (tO : List (Block (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl)),
      (keyFileDescription Xs N Pl).shared.blocksInOrder = pO ++ bO :: tO ∧ bO.place = omegaPlace ∧ bO.rounds ≠ [] ∧
        Johnson.G.OfPlan.rootsOf (pO.flatMap (·.rounds)) + 0 = 1 ∧
        (pO.flatMap (·.rounds)).length = 4) := by
  obtain ⟨r1, r2, -⟩ := places_named scope h
  have e1 : ((keyFileDescription Xs N Pl).first.blocksInOrder.map fun b => (b.place, b.rounds.length)) = fullFirst := r1
  have e2 : ((keyFileDescription Xs N Pl).shared.blocksInOrder.map fun b => (b.place, b.rounds.length)) = fullShared := r2
  have hd := OnBytes.M1.keyDecl_of_named scope h
  have d1 : (keyFileDescription Xs N Pl).first.blocksInOrder.flatMap (·.rounds) = declKeyFull.1 := congrArg Prod.fst hd
  have d2 : (keyFileDescription Xs N Pl).shared.blocksInOrder.flatMap (·.rounds) = declKeyFull.2.1 :=
    congrArg (fun D => D.2.1) hd
  obtain ⟨w1, w2, w3, w4, w5, w6⟩ := own_rows_written
  obtain ⟨o1, o2⟩ := own_roots_written
  have hsl : 5 < fullShared.length := (List.getElem?_eq_some_iff.1 w4).1
  have h0 : 0 < fullFirst.length := (List.getElem?_eq_some_iff.1 w2).1
  have h17 : 17 < fullFirst.length := (List.getElem?_eq_some_iff.1 w3).1
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨p, b, t, c, l, r⟩ := own_splitAt _ _ e1 0 h0
    have rr := r.trans (List.getElem?_eq_some_iff.1 w2).2
    obtain rfl : p = [] := List.length_eq_zero_iff.1 l
    refine ⟨b, t, c, congrArg Prod.fst rr, fun hn => ?_⟩
    have := congrArg Prod.snd rr
    simp only [hn] at this
    cases this
  · obtain ⟨p, b, t, c, l, r⟩ := own_splitAt _ _ e1 17 h17
    have rr := r.trans (List.getElem?_eq_some_iff.1 w3).2
    have f1 : (p.flatMap (·.rounds)).length = 18848 := by
      have := own_rows_front (c ▸ e1)
      rw [this, l]
      exact w5
    refine ⟨p, b, t, c, congrArg Prod.fst rr, fun hn => ?_, ?_, f1⟩
    · have := congrArg Prod.snd rr
      simp only [hn] at this
      cases this
    · have f2 := own_front_rounds (c ▸ d1)
      rw [f1] at f2
      have f3 : declsTo (keyFileDescription Xs N Pl).first.blocksInOrder p.length = p.flatMap (·.rounds) := by
        unfold declsTo
        rw [c, List.take_left' rfl]
      rw [Nat.add_zero, AtPublicFiles.KeyThread.treesTo_roots _ (fun x hx =>
                  AtPublicFiles.KeyThread.lists_of_shaped (own_shaped_first h.plan x hx)), f3, f2]
      exact o1
  · obtain ⟨p, b, t, c, l, r⟩ := own_splitAt _ _ e2 5 hsl
    have rr := r.trans (List.getElem?_eq_some_iff.1 w4).2
    have f1 : (p.flatMap (·.rounds)).length = 4 := by
      have := own_rows_front (c ▸ e2)
      rw [this, l]
      exact w6
    refine ⟨p, b, t, c, congrArg Prod.fst rr, fun hn => ?_, ?_, f1⟩
    · have := congrArg Prod.snd rr
      simp only [hn] at this
      cases this
    · have f2 := own_front_rounds (c ▸ d2)
      rw [f1] at f2
      rw [f2]
      exact o2

end

/-- A shape off a plan's messages. -/
theorem own_shapeAt_congr {P P' : VerifiableInference.Desc.K1.Par} (hs : P.sent = P'.sent) (k : ℕ) :
    shapeAt P k = shapeAt P' k := by
  simp only [Johnson.Prover.Send.shapeAt, hs]

/-- dueR reads a plan's codes and messages alone. -/
theorem own_dueR_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) (ride : ℕ → Option K1.Ride) : K1.dueR P ride = K1.dueR P' ride := by
  have e1 : ∀ j, K1.dueMsg P.codes (shapeAt P j) (ride j) = K1.dueMsg P'.codes (shapeAt P' j) (ride j) :=
    fun j => by simp only [Johnson.Prover.Send.shapeAt, hc, hs]
  have e2 : ∀ j, K1.startR P ride j = K1.startR P' ride j := fun j => by
    unfold K1.startR
    simp only [e1]
  unfold K1.dueR
  rw [e2, hs]

theorem own_trees_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) : P.trees = P'.trees := by
  unfold VerifiableInference.Desc.K1.Par.trees
  rw [hc, hs]

theorem own_width_congr {P P' : VerifiableInference.Desc.K1.Par} (hc : P.codes = P'.codes)
    (hs : P.sent = P'.sent) (t : ℕ) : columnWidth P t = columnWidth P' t := by
  show widthOf P.codes P.sent t = widthOf P'.codes P'.sent t
  rw [hc, hs]

/-- **The index masks' sending, at every plan at the written codes and messages.** -/
theorem own_I_at {P : VerifiableInference.Desc.K1.Par} (hc : P.codes = parIK.codes)
    (hs : P.sent = parIK.sent) : P.trees[0]? = some shI ∧
    columnWidth P 0 = shI.mainWidth + shI.maskWidth ∧ P.sent.size = 1 ∧
    (shapeAt P 0).mainRows = 0 ∧ (shapeAt P 0).maskRows = 1 ∧
    codeOf (P.codes.mask.getD (shapeAt P 0).maskCode default) = ownStage.Z ∧
    (List.range P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some 0) = [0] ∧
    0 < (K1.dueR P (fun _ => none)).f + (K1.dueR P (fun _ => none)).e := by
  rw [own_trees_congr hc hs, own_width_congr hc hs, own_dueR_congr hc hs, own_shapeAt_congr hs, hc, hs]
  exact own_I_full

/-- **W's sending, at every plan at the written codes and messages.** -/
theorem own_W_at {P : VerifiableInference.Desc.K1.Par} (hc : P.codes = parWK.codes)
    (hs : P.sent = parWK.sent) : P.trees[0]? = some shW ∧
    columnWidth P 0 = shW.mainWidth + shW.maskWidth ∧ P.sent.size = 2 ∧
    rideW 1 = some ⟨ownStage.k, ownStage.h⟩ ∧ ((shapeAt P 1).mainDeg == 3) = false ∧
    2 * ownStage.k + 1 + 2 ^ ownStage.h * ownStage.Z.r ≤
      (K1.dueMsg P.codes (shapeAt P 1) (rideW 1)).e ∧
    (shapeAt P 0).mainDeg = 3 ∧
    codeOf (P.codes.base.getD (shapeAt P 0).code default) = ownStage.C ∧
    codeOf (P.codes.mask.getD (shapeAt P 0).maskCode default) = ownStage.Z ∧
    codeOf (P.codes.mask.getD (shapeAt P 1).maskCode default) = ownStage.Z ∧
    (shapeAt P 1).maskRows = 2 ^ ownStage.h ∧ (shapeAt P 1).mainRows = 0 ∧
    (List.range P.sent.size).filter (fun k =>
      ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree[k]? == some 0) = [0, 1] ∧
    0 < (K1.dueR P rideW).f + (K1.dueR P rideW).e := by
  rw [own_trees_congr hc hs, own_width_congr hc hs, own_dueR_congr hc hs, own_shapeAt_congr hs, own_shapeAt_congr hs, hc, hs]
  exact own_W_full

theorem own_treesW : treesW piKWFull =
    [(13, [.mask 0]), (22, [.main 1, .mask 1, .fresh]), (22, [.main 2])] := by
  have e0 : ProofFile.Honest.K12.Light.depthOf piKWFull 0 = 13 := by decide +kernel
  have e1 : ProofFile.Honest.K12.Light.depthOf piKWFull 1 = 22 := by decide +kernel
  have e2 : ProofFile.Honest.K12.Light.depthOf piKWFull 2 = 22 := by decide +kernel
  unfold treesW
  rw [e0, e1, e2]

/-- The three members' shapes, one by one. -/
theorem own_mem₀ : memShape (shapeAt parIK 0) ((firstsOf (shapesW parIK parWK shapeOK)).getD 0 (none, none)) =
    ⟨0, 0, 0, 1, true⟩ := by decide +kernel
theorem own_mem₁ : memShape (shapeAt parWK 0) ((firstsOf (shapesW parIK parWK shapeOK)).getD 1 (none, none)) =
    ⟨16, 1, 1, 1, false⟩ := by decide +kernel
theorem own_mem₂ : memShape shapeOK ((firstsOf (shapesW parIK parWK shapeOK)).getD 2 (none, none)) =
    ⟨0, 12, 0, 0, false⟩ := by decide +kernel

section Run
open VerifiableInference.Desc.Key (Xi LaterPlaces Source)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyLay (jobKWAt)
open AtPublicFiles.KeyTest (sIdx sW)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub ownTestPlace)
open ProofFile.Honest.K14 (SendPub Ask)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc Ky X₀ Y V Pb : Type}

/-- **The clause trees of the key's own test at a stand**: trees_at_plain_job with the public numbers, the book's tests and where the senders stand paid. What stays are the
filling's three finds (hgI, hgW, hgO), the data's read of a front (hdata), that Omega's input is the test's (haskO), and the plans' equations. -/
theorem own_trees_stand {K : KeyPub} (hK : fullPub = some K) (scope : VerifierAndGoals.InScope Z = true)
    (hS : KeySourced Z Xs N Pl) {P : Prover W₀ Rc Xi Ky Unit X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi}
    {k : Coins (keyBook K)} {ρ : Draws} {R : Ready W₀ Rc Xi Ky Unit X₀ Y} {r : RunC (keyFileDescription Xs N Pl)}
    (hR : ready (keyFileDescription Xs N Pl) (keyBook K) P w₀ rc x k = .ok R)
    (hrun : runC (keyFileDescription Xs N Pl) (keyBook K) P w₀ rc x k ρ = .ok r)
    (σ : Side (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl V (Local W₀ Rc Xi Unit) Y Pb)
    (u : Member V (Local W₀ Rc Xi Unit) Y Pb) (pre' t' : List (Block (keyFileDescription Xs N Pl).S₃ (keyFileDescription Xs N Pl).Cl))
    (i : ℕ) (S : StandsAt (keyFileDescription Xs N Pl).second.blocksInOrder R.second σ u pre' t' i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    (hσ : σ.block.place = ownTestPlace) (hu : u.number = 1)
    (JI JW : K1.SendJob (Local W₀ Rc Xi Unit) Y) (A : SendPub) (ask : Local W₀ Rc Xi Unit → Ask)
    (hIc : JI.P.codes = parIK.codes) (hIs : JI.P.sent = parIK.sent) (hIr : JI.ride = fun _ => none)
    (hWc : JW.P.codes = parWK.codes) (hWs : JW.P.sent = parWK.sent) (hWr : JW.ride = rideW)
    (hAc : A.P.codes = AtPublicFiles.KeyLay.AK.P.codes) (hAS : A.P.S = AtPublicFiles.KeyLay.AK.P.S) (hAt : A.atPoint < 4)
    (m : ProofFile.Honest.Mid (Local W₀ Rc Xi Unit) Y)
    (hmid : midAtW (keyFileDescription Xs N Pl) (keyBook K) P w₀ rc x k ρ ⟨σ.block.place, u.number⟩ = .ok (some m))
    (hi : i = firstLen piKWFull.nums.stages)
    (Vc Wc Xc : Type) (pc : Part Vc Wc Xc) (cc : pc.Coins)
    (hlp : lendPart (keyBook K) ((keyBook K).rowsOf 2) (k.look 2) ⟨σ.block.place, u.number⟩ pc = .ok cc)
    (hgI : (P.first.find? fun g => g.place == idxPlace) = some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit) JI))
    (hgW : (P.first.find? fun g => g.place == wPlace) = some (K1.proverSideOfSending (V := Local W₀ Rc Xi Unit) JW))
    (witO : Common W₀ Rc Ky → Ask)
    (hgO : (P.shared.find? fun g => g.place == omegaPlace) =
      some ⟨omegaPlace, [(ProofFile.Honest.K14.liftSend witO (ProofFile.Honest.K14.sendingPart (jobOmega ⟨A.P, A.atPoint⟩)) :
        Part Empty (Common W₀ Rc Ky) X₀)]⟩)
    (hdata : ∀ (w : Local W₀ Rc Xi Unit) (fr fr' : Front Y),
      fr.heard.take 18848 = fr'.heard.take 18848 → JW.data w fr = JW.data w fr')
    (haskO : witO R.common = ask m.st.input) :
    TreesAt (jobKWAt Xs N Pl JI JW A id ask).toRun.toTest 2 piKWFull.nums.first
      (stretches pc.carries cc.2.2) m (r.run.beforeAt st ⟨σ.block.place, u.number⟩) := by
  have hρ₁ : ρ.first.length = ((keyFileDescription Xs N Pl).first.blocksInOrder.flatMap (·.rounds)).length := by
    have Q := ((keyFileDescription Xs N Pl).planOk_ok).1 hS.named.plan
    obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
    have o₁ := steps_shaped s1 Q.blocks₁
    have o₂ := steps_shaped s2 Q.blocks₂
    have o₃ := steps_shaped s3 Q.blocks₃
    obtain ⟨lS₁, -, -⟩ := runC_laidAs hrun hR o₁ o₂ o₃
    rw [lS₁.1, chainSteps_length _ _ s1, ← List.length_flatMap]
  have hp : AtPublicFiles.KeyLay.pWK Pl = piKWFull := own_sourced hS scope
  have hs0 : (jobKWAt Xs N Pl JI JW A id ask).s₀ = ownStage := by
    show (AtPublicFiles.KeyLay.pWK Pl).nums.stages.headD default = _
    rw [hp]
  obtain ⟨⟨bI, tI, cI, pI, nI⟩, ⟨pW, bW, tW, cW, plW, nW, jW, lW⟩, ⟨pO, bO, tO, cO, plO, nO, jO, lO⟩⟩ :=
    own_cut scope hS.named
  obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := own_I_at hIc hIs
  obtain ⟨v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14⟩ := own_W_at hWc hWs
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := own_O_full
  obtain ⟨b1, b2, b3, b4, b5⟩ := own_book_at hK hIc hIs hWc hWs ⟨A.P, A.atPoint⟩ hAc hAS
  obtain ⟨n1, n2, n3, n4, -⟩ := own_numbers
  have hk0 : JI.P.sent.size - 1 = 0 := by rw [i3]
  have hsO : ∀ a, ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape = shapeOK := fun a => by
    have e : (jobOmega ⟨A.P, a⟩).Q.sent =
        (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.sent := rfl
    rw [e, hAc, hAS]
    exact o7
  have hfs : ∀ a, firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape) =
      firstsOf (shapesW parIK parWK shapeOK) := fun a => by
    unfold shapesW
    rw [hsO, own_shapeAt_congr hIs, own_shapeAt_congr hWs, hIs]
  have hz1 : ∀ a, (memK1 (W := Local W₀ Rc Xi Unit) JI id sIdx (JI.P.sent.size - 1) ((firstsOf (shapesW JI.P JW.P
      ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape)).getD 0 (none, none))).shape = ⟨0, 0, 0, 1, true⟩ :=
    fun a => by
      show memShape (shapeAt JI.P (JI.P.sent.size - 1)) _ = _
      rw [hfs, hk0, own_shapeAt_congr hIs]
      exact own_mem₀
  have hz2 : ∀ a, (memK1 (W := Local W₀ Rc Xi Unit) JW id sW 0 ((firstsOf (shapesW JI.P JW.P
      ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape)).getD 1 (none, none))).shape = ⟨16, 1, 1, 1, false⟩ :=
    fun a => by
      show memShape (shapeAt JW.P 0) _ = _
      rw [hfs, own_shapeAt_congr hWs]
      exact own_mem₁
  have hz3 : ∀ a b, (memOfSending (X := Y) (jobOmega ⟨A.P, b⟩) senderO 0
      ((firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape)).getD 2 (none, none))
      ask none).shape = ⟨0, 12, 0, 0, false⟩ := fun a b => by
    have e : (memOfSending (X := Y) (jobOmega ⟨A.P, b⟩) senderO 0
        ((firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape)).getD 2 (none, none))
        ask none).shape = memShape ((jobOmega ⟨A.P, b⟩).Q.sent.getD 0 default).shape
        ((firstsOf (shapesW JI.P JW.P ((jobOmega ⟨A.P, a⟩).Q.sent.getD 0 default).shape)).getD 2 (none, none)) := rfl
    rw [e, hfs, hsO]
    exact own_mem₂
  have hO : ∀ a, (widthFits (jobOmega ⟨A.P, a⟩) 0 = true ∧
      sameCode ((jobOmega ⟨A.P, a⟩).Q.codes.base.getD (Light.shapeAt (jobOmega ⟨A.P, a⟩) 0).code default)
        ownStage.C = true ∧
      mineOf (jobOmega ⟨A.P, a⟩) 0 = [0] ∧ (Light.shapeAt (jobOmega ⟨A.P, a⟩) 0).maskRows = 0 ∧
      0 < (ProofFile.Honest.K14.takesOf (jobOmega ⟨A.P, a⟩).Q.codes (jobOmega ⟨A.P, a⟩).Q.sent
          (jobOmega ⟨A.P, a⟩).sort).f +
        (ProofFile.Honest.K14.takesOf (jobOmega ⟨A.P, a⟩).Q.codes (jobOmega ⟨A.P, a⟩).Q.sent
          (jobOmega ⟨A.P, a⟩).sort).e) := fun a => by
    show (widthFits (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)) 0 = true ∧
      sameCode ((jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.codes.base.getD
        (Light.shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)) 0).code default)
        ownStage.C = true ∧
      mineOf (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)) 0 = [0] ∧
      (Light.shapeAt (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)) 0).maskRows = 0 ∧
      0 < (ProofFile.Honest.K14.takesOf (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.codes
          (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.sent
          (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).sort).f +
        (ProofFile.Honest.K14.takesOf (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.codes
          (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).Q.sent
          (jobOmega (ProofFile.Honest.K12.Light.planOf A.P.codes A.P.S)).sort).e)
    rw [hAc, hAS]
    exact ⟨o2, o3, o4, o5, o6⟩
  have hBs : ∀ a, (jobOmega ⟨A.P, a⟩).sort = (jobOmega ⟨A.P, 0⟩).sort := fun _ => rfl
  obtain ⟨q1, q2, q3, q4, q5⟩ := hO A.atPoint
  refine trees_at_plain_job hS.named.plan hR hrun σ u pre' t' i S hc st
    (jobKWAt Xs N Pl JI JW A id ask) (by rw [hs0]; exact n1) A.P
    (by rw [sendingsFit_plan, hAc, hAS]; exact o1) A.atPoint _ _ _ _ _ ask rfl 13 22 22
    (by show treesW (AtPublicFiles.KeyLay.pWK Pl) = _; rw [hp]; exact own_treesW)
    piKWFull.nums.first n3 0 5 1 n4 m hmid
    (by rw [hi]; show _ = firstLen (AtPublicFiles.KeyLay.pWK Pl).nums.stages; rw [hp]) Vc Wc Xc pc cc hlp
    [] pW bI bW tI tW cI cW nI nW JI JW (by rw [pI]; exact hgI) (by rw [plW]; exact hgW) 0 0
    (JI.P.sent.size - 1) shI shW i1 v1 i2 v2 rfl jW sIdx sW _ _ rfl
    (by rw [hk0, i3]; decide) (by rw [hIr]; exact i8)
    (by rw [hσ, hu, pI, hIr, hk0]; rw [← hIs, hk0] at b1; exact b1)
    rfl (fun w fr fr' e => hdata w fr fr' (by rw [lW] at e; exact e))
    (by rw [v3]; decide) (by rw [hWr]; exact v14)
    (by rw [hσ, hu, plW, hWr]; exact b2) (by rw [hσ, hu, plW, hWr]; exact b3)
    (by rw [hs0, hWr]; exact v4) (by rw [hs0]; exact n2) v5 (by rw [hs0, hWr]; exact v6)
    (by rw [hz1, hs0]; decide +kernel) rfl (by rw [hk0, hs0]; exact i6)
    (by rw [hk0]; exact i7) (by rw [hk0]; exact i4)
    (by rw [hz2])
    (by rw [hz2, hz1]; intro b h1 h2 h3; simp only at h1 h2 h3; omega)
    (by rw [hz2, hz1]; intro b h1 h2 h3; simp only at h1 h2 h3; omega)
    (by rw [hz2, hs0]; decide +kernel) (by rw [hz2, hs0]; decide +kernel)
    rfl rfl v7 (by rw [hs0]; exact v8) (by rw [hs0]; exact v9) (by rw [hs0]; exact v10)
    (by rw [hs0]; exact v11) v12 v13
    pO bO tO cO nO witO (by rw [plO]; exact hgO) q1 jO
    (by rw [plO]; exact b5) q5 (by rw [hσ, hu, plO]; exact b4)
    (by rw [lO]; exact hAt) (by rw [hρ₁]) haskO
    (by rw [hz3])
    (fun y hy b h1 h2 h3 => ?_)
    (by rw [hz3, hs0]; decide +kernel) (by rw [hs0] ; exact q2) q3 q4
  rw [hz3] at h1 h2
  simp only at h1 h2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl
  · rw [hz1] at h3
    simp only at h3
    omega
  · rw [hz2] at h3
    simp only at h3
    omega

end Run

section Plans
open AtPublicFiles.Key (idxJob wJob BattAt)
open AtPublicFiles.KeyBook (OneFull)
open OnBytes.Params (OneTime)
open VerifiableInference.Desc.Key (Pieces)

variable {Wd Yd : Type}

/-- **The index masks' job at every chain's parameters with the written fields.** -/
theorem idx_plan {one : OneTime} (h : OneFull one) (Np : Pieces) (groups : List (List ℕ)) (first : ℕ) :
    (idxJob (W := Wd) (X := Yd) one Np groups first).P.codes = parIK.codes ∧
      (idxJob (W := Wd) (X := Yd) one Np groups first).P.sent = parIK.sent ∧
      (idxJob (W := Wd) (X := Yd) one Np groups first).ride = fun _ => none := by
  refine ⟨h.codes, ?_, rfl⟩
  show (VerifiableInference.Desc.Key.sendingPar one Np.idx "the index masks" #[one.indexMasks] groups).sent = _
  unfold VerifiableInference.Desc.Key.sendingPar VerifiableInference.Desc.K1.Par.sent
  rw [h.idx]
  rfl

/-- **W's job at every chain's parameters with the written fields.** -/
theorem w_plan {one : OneTime} (h : OneFull one) {entry : Wd → ℕ → ℕ → OnBytes.Slice.GF} {Np : Pieces}
    {groups : List (List ℕ)} {first : ℕ} {ride : ℕ → Option K1.Ride}
    {points : List Fmt.Drawn → ℕ → ℕ → List OnBytes.E} {a : BattAt} {J : K1.SendJob Wd Yd}
    (hJ : wJob entry one Np groups first ride points a = some J) :
    J.P.codes = parWK.codes ∧ J.P.sent = parWK.sent ∧ J.ride = ride := by
  unfold wJob at hJ
  obtain ⟨msg, hm, rfl⟩ := Option.map_eq_some_iff.1 hJ
  refine ⟨h.codes, ?_, rfl⟩
  rw [h.lin] at hm
  show (VerifiableInference.Desc.Key.sendingPar one Np.w "W and what rides with it" msg groups).sent = _
  unfold VerifiableInference.Desc.Key.sendingPar VerifiableInference.Desc.K1.Par.sent parWK
  rw [hm]
  rfl

end Plans

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.idx_plan
#print axioms ProofFile.Honest.K12.Sim2.w_plan

#print axioms ProofFile.Honest.K12.Sim2.own_trees_stand
#print axioms ProofFile.Honest.K12.Sim2.own_cut
#print axioms ProofFile.Honest.K12.Sim2.own_I_at
#print axioms ProofFile.Honest.K12.Sim2.own_W_at
#print axioms ProofFile.Honest.K12.Sim2.own_numbers
#print axioms ProofFile.Honest.K12.Sim2.own_I_full
#print axioms ProofFile.Honest.K12.Sim2.own_W_full
#print axioms ProofFile.Honest.K12.Sim2.own_O_full
#print axioms ProofFile.Honest.K12.Sim2.own_shapes_full
#print axioms ProofFile.Honest.K12.Sim2.own_splitAt
#print axioms ProofFile.Honest.K12.Sim2.own_rows_written
#print axioms ProofFile.Honest.K12.Sim2.own_roots_written
