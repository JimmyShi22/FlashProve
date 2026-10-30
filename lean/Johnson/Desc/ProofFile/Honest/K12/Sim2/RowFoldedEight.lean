-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the plan's eight sub-protocols at the key file, in scope.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowFoldedEight.lean: in scope the key file's shared plan returns its
eight sub-protocols, and the rounds in front of the two sendings declare the roots that the written
rounds declare: hb8, hr0, hr1 of onAtRun_folded_key.

  eight_of_some, eight_sourced, written_sourced, dry_roots, roots_sourced
  dry_first_roots, first_trees_sourced   hj of onAtRun_ranges_book

Limits. Public numbers alone. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFoldedPub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Key (LaterPlaces Source Claim sharedPar beforeSharedPoint)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open Johnson.G.OfPlan (rootsOf)
open Johnson.G (dryKeyFull)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

theorem len_cut {α : Type} (a : List α) (g : α) (o : List α) (e : α) (h1 : a.length = 2)
    (ho : o.length ≤ 1) (h : (a ++ g :: (o ++ [e])).length = 12) : False := by
  simp only [List.length_append, List.length_cons, List.length_nil] at h
  omega

/-- Where the plan returns, it returns eight. -/
theorem eight_of_some (Q : Desc.K14.P14) (l : List (Block Desc.K14.St Unit))
    (hb : Desc.K14.blocks Q = some l) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, l = [b1, b2, b3, b4, b5, b6, b7, b8] := by
  unfold Desc.K14.blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hb
  obtain ⟨sentU, hU, rfl⟩ := hb
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- **In scope the plan returns its eight.** -/
theorem eight_sourced (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, Desc.K14.blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  have hl := (AtPublicFiles.KeyThread.lengths scope hS.named).2.1
  have hcut := H2K.JointK.keyShared_cut Xs.chains Pl
  cases hb : Desc.K14.blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) with
  | none =>
    exfalso
    have e : (keyFileDescription Xs N Pl).shared.blocksInOrder.length = _ := congrArg List.length hcut
    rw [hl] at e
    have hpre : (H2K.JointK.keySharedPre Xs.chains Pl).length = 2 := by
      unfold H2K.JointK.keySharedPre Desc.K14.blocksOr
      rw [hb]
      rfl
    have ho : ((Pl.O.toList.map H2K.JointK.keyOmega)).length ≤ 1 := by
      rw [List.length_map]
      cases Pl.O <;> simp
    exact len_cut _ _ _ _ hpre ho e.symm
  | some l =>
    obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight_of_some _ _ hb
    exact ⟨_, _, _, _, _, _, _, _, rfl⟩

/-- In scope the key file's rounds are the written ones. -/
theorem written_sourced (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) :
    Johnson.G.OfPlan.writtenOf "key file" (keyFileDescription Xs N Pl).roundsDeclaredByBlocks = .ok dryKeyFull := by
  obtain ⟨X₀, m, h0, hm, hX, -, hP⟩ := hS.source
  obtain ⟨X₁, m₁, h0', hm', -, hl⟩ := hS.named.named
  obtain rfl : X₀ = X₁ := Except.ok.inj (h0.symm.trans h0')
  obtain rfl : m = m₁ := Except.ok.inj (hm.symm.trans hm')
  have hpinAt : VerifiableInference.PlanWritten.pinnedKeyAt m (keyFileDescription Xs N Pl) = true :=
    hl ("its rounds are not the written ones", _)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have hpin : VerifiableInference.PlanWritten.seatPinnedKey Z.pol (keyFileDescription Xs N Pl) = true :=
    (VerifiableInference.Desc.Key.pinned_is_seat _
      (VerifiableInference.PlanWritten.publicOfO_scan h0) hm).symm.trans hpinAt
  exact (VerifiableInference.PlanWritten.seat_in_scope_key _ _ Z scope hpin).1

theorem dry_roots : (((dryKeyFull.2.1.map (·.1)).take 1).map (·.entry.roots)).sum = 0 ∧
    (((dryKeyFull.2.1.map (·.1)).take 4).map (·.entry.roots)).sum = 1 := by decide +kernel

/-- **The roots in front of the two sendings.** -/
theorem roots_sourced (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hb8 : Desc.K14.blocks (sharedPar Xs.chains (beforeSharedPoint Pl)) =
      some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    rootsOf b1.rounds = 0 ∧ rootsOf ([b1, b2, b3, b4].flatMap (·.rounds)) = 1 := by
  obtain ⟨hc, hSh⟩ := plan_sourced scope hS (beforeSharedPoint Pl)
  have hU : Desc.K14.withU (sharedPar Xs.chains (beforeSharedPoint Pl)).S =
      some (ProofFile.Honest.K12.Light.sentOf (sharedPar Xs.chains (beforeSharedPoint Pl)).S) := by
    rw [hSh]
    exact ProofFile.Honest.K12.Light.withU_sentOf (by decide +kernel)
  have hSN : (sharedPar Xs.chains (beforeSharedPoint Pl)).S.sharedSplitNeeded = true := by
    rw [hSh]
    decide +kernel
  obtain ⟨n1, n2, n3, n4, -⟩ := ProofFile.Honest.K12.Light.lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb8 hU hSN
  have hx := (H2K.Pub.chains_of_written (written_sourced scope hS)).2.1
  have hP : H2K.JointK.keySharedPre Xs.chains Pl =
      ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype (Cl' := Claim)).first.asBare ::
        [b1, b2, b3, b4, b5, b6, b7, b8].map fun b => (b.retype (Cl' := Claim)).asBare := by
    unfold H2K.JointK.keySharedPre Desc.K14.blocksOr
    rw [hb8]
    rfl
  have hcutK := H2K.JointK.keyShared_cut Xs.chains Pl
  rw [hP] at hcutK
  have hD : (keyFileDescription Xs N Pl).roundsDeclaredByBlocks.2.1 = [b1, b2, b3, b4].flatMap (·.rounds) ++
      ([b5, b6, b7, b8].flatMap (·.rounds) ++
        (H2K.JointK.keyGu Pl :: ((Pl.O.toList.map H2K.JointK.keyOmega) ++
          [H2K.JointK.keySharedEnd Xs.chains Pl])).flatMap (·.rounds)) := by
    show ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype (Cl' := Claim)).blocksInOrder.flatMap
      (·.rounds) = _
    rw [hcutK]
    simp only [List.cons_append, List.map_cons, List.map_nil, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc]
    rfl
  have hD1 : (keyFileDescription Xs N Pl).roundsDeclaredByBlocks.2.1 = b1.rounds ++ ((b2.rounds ++ (b3.rounds ++ b4.rounds)) ++
                                   ([b5, b6, b7, b8].flatMap (·.rounds) ++
                                     (H2K.JointK.keyGu Pl :: ((Pl.O.toList.map H2K.JointK.keyOmega) ++
                                       [H2K.JointK.keySharedEnd Xs.chains Pl])).flatMap (·.rounds))) := by
    rw [hD]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc]
  have r1 := H2K.JointK.roots_closed (pre := b1.rounds) (by rw [← hD1]; exact hx)
  have r2 := H2K.JointK.roots_closed (pre := [b1, b2, b3, b4].flatMap (·.rounds)) (by rw [← hD]; exact hx)
  have L4 : ([b1, b2, b3, b4].flatMap (·.rounds)).length = 4 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, n1, n2, n3, n4]
  rw [n1] at r1
  rw [L4] at r2
  exact ⟨r1.trans dry_roots.1, r2.trans dry_roots.2⟩

theorem dry_first_roots : (((dryKeyFull.1.map (·.1)).take 2).map (·.entry.roots)).sum = 1 := by
  decide +kernel

/-- **hj at row 5**: one tree stands in front of the multiplicities' sender. -/
theorem first_trees_sourced (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) :
    ProofFile.Honest.treesTo (keyFileDescription Xs N Pl).first.blocksInOrder 1 = 1 := by
  obtain ⟨b₀, bS, tS, hcut, -, -, hb0⟩ := msg_cut scope hS.named
  have hx := (H2K.Pub.chains_of_written (written_sourced scope hS)).1
  have hall : ∀ b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder, ProofFile.Honest.Small.Listed b := fun b hb =>
    ProofFile.Honest.Small.lists_of_shaped (((ProofFile.Honest.planOk_all hS.named.plan).1 b hb).2)
  rw [AtPublicFiles.KeyThread.treesTo_roots _ hall 1]
  have hD : ProofFile.Honest.declsTo (keyFileDescription Xs N Pl).first.blocksInOrder 1 = b₀.rounds := by
    unfold ProofFile.Honest.declsTo
    rw [hcut]
    simp
  rw [hD]
  have hsplit : (keyFileDescription Xs N Pl).roundsDeclaredByBlocks.1 = b₀.rounds ++ (bS :: tS).flatMap (·.rounds) := by
    show (keyFileDescription Xs N Pl).first.blocksInOrder.flatMap (·.rounds) = _
    rw [hcut]
    simp
  have r1 := H2K.JointK.roots_closed (pre := b₀.rounds) (by rw [← hsplit]; exact hx)
  rw [hb0] at r1
  exact r1.trans dry_first_roots

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.eight_of_some
#print axioms ProofFile.Honest.K12.Sim2.eight_sourced
#print axioms ProofFile.Honest.K12.Sim2.written_sourced
#print axioms ProofFile.Honest.K12.Sim2.dry_roots
#print axioms ProofFile.Honest.K12.Sim2.roots_sourced
#print axioms ProofFile.Honest.K12.Sim2.first_trees_sourced
