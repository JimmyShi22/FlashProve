-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- At the key file: the count at the form of the rows.
/-
Johnson/M1/KeyRows.lean: the number of a sending's first tree, as the rule's BudDebts read it off the chain's rows, and the three sendings of
the first chain that the library's keyPars names, tied to the count's numbers.

1.  rows_take_sum: where a chain's blocks are shaped, the roots that its first n rows tell are the declared rounds'.
2.  roundOfK: the round of a sending; frontK: the roots in front of it are treesBeforeK, by the kernel.
3.  budRow₁, budRow₂, budRow₃: in scope, under KeyNamed, at every due list, budAt at the count's numbers, in the form of BudDebts' fields at n =
    roundOfK: at the sending's first round.
4.  keyParsW_tie: the three of keyParsW are parK at (0, 0), (0, 1), (0, 5), as far as budAt reads them: their codes and messages.

That a member of a side stands at such a round, and which rows of which kind carry budAt, is not said here.
No property of the protocol is claimed here.
-/
import Johnson.M1.KeyNumbersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat
open Johnson.KB8 (declKeyFull)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription)

section Rows
variable {S Cl : Type}

theorem row_roots (b : Block S Cl) (h : b.shaped = true) :
    (b.rounds.zip b.oracles).map (·.2.length) = b.rounds.map (·.entry.roots) := by
  unfold Block.shaped at h
  have h' := Bool.and_eq_true_iff.1 h
  have hl : b.oracles.length = b.rounds.length := beq_iff_eq.1 h'.1
  have e : (b.rounds.zip b.oracles).map (·.2.length) =
      (b.rounds.zip b.oracles).map fun x => x.1.entry.roots :=
    List.map_congr_left fun x hx => by
      have := List.all_eq_true.1 h'.2 x hx
      exact beq_iff_eq.1 (Bool.and_eq_true_iff.1 this).1
  rw [e]
  have m := List.map_fst_zip (l₁ := b.rounds) (l₂ := b.oracles) (Nat.le_of_eq hl.symm)
  conv => rhs; rw [← m]
  rw [List.map_map]
  rfl

theorem rows_roots : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    (rowsOfChain bs).map (·.2.length) = (bs.flatMap (·.rounds)).map (·.entry.roots)
  | [], _ => rfl
  | b :: bs, h => by
    have r1 : rowsOfChain (b :: bs) = b.rounds.zip b.oracles ++ rowsOfChain bs := by
      unfold rowsOfChain
      rw [List.flatMap_cons]
    rw [r1, List.flatMap_cons, List.map_append, List.map_append, row_roots b (h b (List.mem_cons_self ..)),
      rows_roots bs fun x hx => h x (List.mem_cons_of_mem _ hx)]

/-- **The roots that a chain's first n rows tell.** -/
theorem rows_take_sum (bs : List (Block S Cl)) (h : ∀ b ∈ bs, b.shaped = true) (n : Nat) :
    (((rowsOfChain bs).take n).map (·.2.length)).sum =
      (((bs.flatMap (·.rounds)).take n).map (·.entry.roots)).sum := by
  rw [List.map_take, List.map_take, rows_roots bs h]

end Rows

/-- The written declared rounds of the chain number ch. -/
def declChainK (ch : Nat) : List Fmt.DeclaredRound :=
  if ch == 0 then declKeyFull.1 else if ch == 1 then declKeyFull.2.1 else declKeyFull.2.2

/-- The round of the sending number i of the chain number ch: the i-th of that chain's declared rounds that holds a root. -/
def roundOfK (ch i : Nat) : Nat :=
  (((declChainK ch).zipIdx.filter fun x => x.1.entry.roots != 0).map (·.2)).getD i 0

set_option maxRecDepth 1000000 in
/-- The rounds of the sendings. Round 44 of the shared chain is the fold's entry "FOLD epsilon". -/
theorem rounds_writtenK : (List.range 6).map (roundOfK 0) = [0, 2, 18811, 18818, 18824, 18848] ∧
    (List.range 10).map (roundOfK 1) = [1, 4, 17, 25, 32, 39, 44, 49, 56, 63] ∧
    (List.range 4).map (roundOfK 2) = [7, 14, 20, 26] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **NO TREE IS MISSING, at the written declared rounds**: rootsTieK's line at declChainK: every round that holds a root is a sending's, in order. -/
theorem rootsTieDecl : ∀ ch ∈ [0, 1, 2], (((declChainK ch).filter fun d => d.entry.roots != 0).map (·.entry.roots)) =
    (List.range (sendsK ch).length).map fun i => ((Own.treesMade Johnson.G.keyCodesWritten (sentK ch i)).getD {}).shapes.size := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **The roots in front of a sending's round are the trees in front of it.** -/
theorem frontK : ∀ ch ∈ [0, 1, 2], ((List.range (sendsK ch).length).all fun i =>
    decide ((((declChainK ch).take (roundOfK ch i)).map (·.entry.roots)).sum = treesBeforeK ch i)) = true := by
  decide +kernel

section Named
variable {Z : VerifierAndGoals.PublicFiles} {X : Key.Source} {N : H2U.PlaceNums} {P : Key.LaterPlaces}

theorem planOk_named (h : KeyNamed Z X N P) : FileDescription.PlanOk (keyFileDescription X N P) :=
  (keyFileDescription X N P).planOk_ok.1 h.plan

theorem front_at (ch : Nat) (hch : ch ∈ [0, 1, 2]) {i : Nat} (hi : i < (sendsK ch).length) :
    (((declChainK ch).take (roundOfK ch i)).map (·.entry.roots)).sum = treesBeforeK ch i :=
  of_decide_eq_true (List.all_eq_true.1 (frontK ch hch) i (List.mem_range.2 hi))

/-- **BudDebts' form, at the first chain**, at a sending's first round. -/
theorem budRow₁ (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P) {i : Nat}
    (hi : i < (sendsK 0).length) (ρ : Draws) (hρ : ρ.due (keyFileDescription X N P) = true) (rs : List Nat) :
    budAt (parK 0 i) (asksFrom (treeAsks (keyFileDescription X N P) ρ 0) rs
      (((rowsOfChain (keyFileDescription X N P).first.blocksInOrder).take (roundOfK 0 i)).map (·.2.length)).sum) := by
  have e : (keyFileDescription X N P).first.blocksInOrder.flatMap (·.rounds) = declChainK 0 :=
    congrArg Prod.fst (keyDecl_of_named scope h)
  rw [rows_take_sum _ (fun b hb => ((planOk_named h).blocks₁ b hb).2), e, front_at 0 (by simp) hi]
  exact budK scope h (by simp) hi ρ hρ rs

/-- The same at the shared chain. -/
theorem budRow₂ (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P) {i : Nat}
    (hi : i < (sendsK 1).length) (ρ : Draws) (hρ : ρ.due (keyFileDescription X N P) = true) (rs : List Nat) :
    budAt (parK 1 i) (asksFrom (treeAsks (keyFileDescription X N P) ρ 1) rs
      (((rowsOfChain (keyFileDescription X N P).shared.blocksInOrder).take (roundOfK 1 i)).map (·.2.length)).sum) := by
  have e : (keyFileDescription X N P).shared.blocksInOrder.flatMap (·.rounds) = declChainK 1 :=
    congrArg (fun D => D.2.1) (keyDecl_of_named scope h)
  rw [rows_take_sum _ (fun b hb => ((planOk_named h).blocks₂ b hb).2), e, front_at 1 (by simp) hi]
  exact budK scope h (by simp) hi ρ hρ rs

/-- The same at the last chain. -/
theorem budRow₃ (scope : VerifierAndGoals.InScope Z = true) (h : KeyNamed Z X N P) {i : Nat}
    (hi : i < (sendsK 2).length) (ρ : Draws) (hρ : ρ.due (keyFileDescription X N P) = true) (rs : List Nat) :
    budAt (parK 2 i) (asksFrom (treeAsks (keyFileDescription X N P) ρ 2) rs
      (((rowsOfChain (keyFileDescription X N P).second.blocksInOrder).take (roundOfK 2 i)).map (·.2.length)).sum) := by
  have e : (keyFileDescription X N P).second.blocksInOrder.flatMap (·.rounds) = declChainK 2 :=
    congrArg (fun D => D.2.2) (keyDecl_of_named scope h)
  rw [rows_take_sum _ (fun b hb => ((planOk_named h).blocks₃ b hb).2), e, front_at 2 (by simp) hi]
  exact budK scope h (by simp) hi ρ hρ rs

end Named

set_option maxRecDepth 1000000 in
/-- **The library's three numbers are the count's**, as far as budAt reads a Par: its codes and its messages. -/
theorem keyParsW_tie : keyParsW.map (fun x => (x.1.codes, x.1.sent)) =
    [((parK 0 0).codes, (parK 0 0).sent), ((parK 0 1).codes, (parK 0 1).sent),
      ((parK 0 5).codes, (parK 0 5).sent)] := by
  decide +kernel

/-- budAt reads of a Par its codes and its messages. -/
theorem budAt_congr {A B : K1.Par} (hc : A.codes = B.codes) (hs : A.sent = B.sent)
    (asks : List (List (List Nat))) : budAt A asks ↔ budAt B asks := by
  unfold budAt Johnson.Prover.Send.shapeAt
  rw [hc, hs]

end OnBytes.M1

#print axioms OnBytes.M1.rows_take_sum
#print axioms OnBytes.M1.rounds_writtenK
#print axioms OnBytes.M1.frontK
#print axioms OnBytes.M1.budRow₁
#print axioms OnBytes.M1.budRow₂
#print axioms OnBytes.M1.budRow₃
#print axioms OnBytes.M1.keyParsW_tie
#print axioms OnBytes.M1.budAt_congr
