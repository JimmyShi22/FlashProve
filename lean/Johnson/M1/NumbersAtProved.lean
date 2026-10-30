-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the statements of Johnson/M1/NumbersAt.lean, proved.
/-
Johnson/M1/NumbersAtProved.lean: the count at the shared chain and the last chain by evaluation in Lean's kernel at the written
values, with the tests that can fail; the law that the test on a table of openings is the test on a description. No property of
the protocol is claimed here.
-/
import Johnson.M1.NumbersAt

set_option autoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open Johnson.Prover.Send (shapeAt)

/-! ## The drawn line -/

set_option maxRecDepth 1000000 in
/-- The positions drawn for each tree of the shared chain, and for the number behind the last. -/
theorem drawnLine1 : (List.range 12).map (drawnTabAt tabM 1) =
    [101, 106, 152, 54, 54, 54, 51, 51, 51, 51, 41, 0] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The positions drawn for each tree of the last chain, and for the number behind the last. -/
theorem drawnLine2 : (List.range 5).map (drawnTabAt tabM 2) = [55, 55, 46, 44, 0] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The table names no tree outside the three chains' own numbers: 83, 11 and 4 trees. -/
theorem tab_within : (tabM.all fun x =>
    (x.1.1 == 0 && decide (x.1.2 < 83)) || (x.1.1 == 1 && decide (x.1.2 < 11)) ||
      (x.1.1 == 2 && decide (x.1.2 < 4))) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The number of openings by source chain: 83, 13 and 4: 100 in all, as tabW_length has it. -/
theorem tab_parts : ((tabM.filter fun x => x.1.1 == 0).length, (tabM.filter fun x => x.1.1 == 1).length,
    (tabM.filter fun x => x.1.1 == 2).length, tabM.length) = (83, 13, 4, 100) := by decide +kernel

/-! ## The fold's own sending -/

set_option maxRecDepth 1000000 in
/-- The fold's fresh mask, by its numbers: one mask row under mask code 6, no sample, leaf class 0. -/
theorem foldSent_is : foldSentW =
    #[⟨{ code := noId, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 6, answers := 0 }, 0⟩] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Mask code 6: length 2^13, tail 152. -/
theorem mask6 : (codesW.mask.getD 6 default).logN = 13 ∧ (codesW.mask.getD 6 default).r = 152 := by decide +kernel

/-! ## The count -/

set_option maxRecDepth 1000000 in
theorem countAt : Spec.countAt := by
  unfold Spec.countAt
  decide +kernel

set_option maxRecDepth 1000000 in
theorem treesTieAt : Spec.treesTieAt := by
  unfold Spec.treesTieAt
  decide +kernel

set_option maxRecDepth 1000000 in
theorem rootsTieAt : Spec.rootsTieAt := by
  unfold Spec.rootsTieAt
  decide +kernel

set_option maxRecDepth 1000000 in
theorem countAtEdges : Spec.countAtEdges := by
  unfold Spec.countAtEdges
  decide +kernel

set_option maxRecDepth 1000000 in
/-- THE NINE ALONE ARE REFUSED: over the entries "SEND seed" without the fold's sending, the numbers slip by one from number 6
on: the last sending stands at tree 9, for which 51 positions are drawn, and its tail is 41. -/
theorem nine_refused : ((List.range 9).all fun i =>
    readsWithinTAt tabM 1 (ProofFile.Honest.K2.sendingPar codesW ((listedAt 1).getD i #[]))
      (((List.range i).map fun j =>
        ((Own.treesMade codesW ((listedAt 1).getD j #[])).getD {}).shapes.size).sum)) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- No other first number saves the nine: at every first number below 12 the test or the clause against an idle yes refuses. -/
theorem nine_no_offset : ((List.range 12).all fun f => !((List.range 9).all fun i =>
    let n₀ := f + ((List.range i).map fun j =>
        ((Own.treesMade codesW ((listedAt 1).getD j #[])).getD {}).shapes.size).sum
    readsWithinTAt tabM 1 (ProofFile.Honest.K2.sendingPar codesW ((listedAt 1).getD i #[])) n₀ &&
      drawnTabAt tabM 1 n₀ != 0)) = true := by
  decide +kernel

/-! ## Omega, and the other tree that two lots open -/

set_option maxRecDepth 1000000 in
/-- OMEGA BY NAME. The first message of sending 1 of the shared chain has 12 main rows under base code 11 and lies in the tree
number 1. Rounds of the shared chain draw 51 positions for that tree, rounds of the last chain 55 and rounds of the first chain
none. Their sum, 106, is what the table has, and it is within the tail 3571. -/
theorem omega_counted :
    (shapeAt (parAtC 1 1) 0).mainRows = 12 ∧ (shapeAt (parAtC 1 1) 0).code = 11 ∧
    treesBeforeC 1 1 = 1 ∧ ((Own.treesMade codesW (sentAtC 1 1)).getD {}).tree[0]? = some 0 ∧
    drawnTabAt (opensTab 0 declW.1) 1 1 = 0 ∧ drawnTabAt (opensTab 1 declW.2.1) 1 1 = 51 ∧
    drawnTabAt (opensTab 2 declW.2.2) 1 1 = 55 ∧ drawnTabAt tabM 1 1 = 51 + 55 ∧
    (codesW.base.getD 11 default).r = 3571 ∧ drawnTabAt tabM 1 1 ≤ (codesW.base.getD 11 default).r := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- THE MASK THAT GOES WITH OMEGA. The second message of sending 1 has one mask row under mask code 6 and lies in the tree number
2. Two rounds of the shared chain open it, for 101 and 51 positions: 152, its tail exactly. -/
theorem omegaMask_counted :
    (shapeAt (parAtC 1 1) 1).mainRows = 0 ∧ (shapeAt (parAtC 1 1) 1).maskRows = 1 ∧
    (shapeAt (parAtC 1 1) 1).maskCode = 6 ∧ ((Own.treesMade codesW (sentAtC 1 1)).getD {}).tree[1]? = some 1 ∧
    (((opensTab 1 declW.2.1).filter fun x => x.1 == (1, 2)).map (·.2)) = [101, 51] ∧
    drawnTabAt tabM 1 2 = 101 + 51 ∧ drawnTabAt tabM 1 2 = (codesW.mask.getD 6 default).r := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- OMEGA'S TAIL IS SIZED FOR A BATCH. This file counts one request. The written sizes allow 64 requests in a batch, and each request's
own test opens Omega's tree for 55 positions: the tail 3571 is the 51 of Omega's test and 64 times 55, and the room of
countAtEdges, 3465, is the other 63 requests' lots exactly. That each request draws its 55 here is the planner's reading
(omegaDraws, OnBytes/Params/DeriveLin.lean), not a theorem on a batch's runs. -/
theorem omega_batch : VerifiableInference.PlanWritten.proofSizedFull.batch.lines.requests = 64 ∧
    (codesW.base.getD 11 default).r = 51 + 64 * 55 ∧ 3465 = (64 - 1) * 55 := by
  decide +kernel

/-! ## The test on the table is the test on the description -/

variable {Xi : Type}

theorem one_roundAt (ch c n p : Nat) : ∀ l : List (Fmt.Shape × Fmt.TreeSource),
    (((l.map fun o => (srcOf c o.2, p)).filter fun x => x.1 == (ch, n)).map (·.2)).sum =
      (l.filter fun o => srcOf c o.2 == (ch, n)).length * p
  | [] => by simp
  | o :: l => by
    have ih := one_roundAt ch c n p l
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    cases h : srcOf c o.2 == (ch, n)
    · simpa [h] using ih
    · simp only [h, if_true, List.map_cons, List.sum_cons, List.length_cons, ih, Nat.succ_mul]
      omega

theorem drawnTabAt_append (A B : List ((Nat × Nat) × Nat)) (ch n : Nat) :
    drawnTabAt (A ++ B) ch n = drawnTabAt A ch n + drawnTabAt B ch n := by
  unfold drawnTabAt
  rw [List.filter_append, List.map_append, List.sum_append]

/-- One chain's rounds. -/
theorem opensInAt_tab (ch c n : Nat) : ∀ ds : List Fmt.DeclaredRound,
    opensInAt ch c n ds = drawnTabAt (opensTab c ds) ch n
  | [] => rfl
  | d :: ds => by
    have ih := opensInAt_tab ch c n ds
    have e : opensTab c (d :: ds) =
        (d.opens.map fun o => (srcOf c o.2, d.entry.poss)) ++ opensTab c ds := by
      unfold opensTab
      rw [List.flatMap_cons]
    rw [e, drawnTabAt_append, ← ih]
    show _ + _ = _
    congr 1
    exact (one_roundAt ch c n d.entry.poss d.opens).symm

/-- **The positions that are sampled for a tree of any chain, off the table.** -/
theorem drawnForAt_tab (F : FileDescription Xi) (ch n : Nat) :
    drawnForAt F ch n = drawnTabAt (readsTab F.roundsDeclaredByBlocks) ch n := by
  unfold drawnForAt readsTab
  rw [drawnTabAt_append, drawnTabAt_append, opensInAt_tab, opensInAt_tab, opensInAt_tab]

/-- **The test at a chain's number is the test on the table.** -/
theorem readsWithinAtB_tab (F : FileDescription Xi) (ch : Nat) (P : K1.Par) (n₀ : Nat) :
    readsWithinAtB F ch P n₀ = readsWithinTAt (readsTab F.roundsDeclaredByBlocks) ch P n₀ := by
  unfold readsWithinAtB readsWithinTAt
  congr 1
  funext k
  cases ((Own.treesMade P.codes P.sent).getD {}).tree[k]? with
  | none => rfl
  | some τ => simp only [drawnForAt_tab]

end OnBytes.M1

#print axioms OnBytes.M1.drawnLine1
#print axioms OnBytes.M1.drawnLine2
#print axioms OnBytes.M1.tab_within
#print axioms OnBytes.M1.tab_parts
#print axioms OnBytes.M1.foldSent_is
#print axioms OnBytes.M1.mask6
#print axioms OnBytes.M1.countAt
#print axioms OnBytes.M1.treesTieAt
#print axioms OnBytes.M1.rootsTieAt
#print axioms OnBytes.M1.countAtEdges
#print axioms OnBytes.M1.nine_refused
#print axioms OnBytes.M1.nine_no_offset
#print axioms OnBytes.M1.omega_counted
#print axioms OnBytes.M1.omegaMask_counted
#print axioms OnBytes.M1.omega_batch
#print axioms OnBytes.M1.readsWithinAtB_tab
