-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/DepthsLaw.lean: `DepthsDeclared` (Honest/Thread/OneState.lean)
at a thread, from one pass over a list alike to its own, and from the depths of its tables at the
sources in hand. General in the thread. A definition and a theorem, with the closed passes at the
written shared and last chains: first by Lean's evaluator, then by the kernel.

  `depthsEach`   every opening of the list declares the depth that a function of its source says
  `declared_of_each`   so `DepthsDeclared` at every border, where the thread's tables at the sources in
                 hand have those depths
  `depthShared`, `depthLast`   the depths of the shared chain's own trees, and of the last chain's
                 sources, as lists written off the places
  `depths_shared`, `depths_last`   the pass says yes at the written lists
  `depths_bent_shared`, `depths_bent_last`   controls: one number changed: no

Why a function of the source. One source is opened at two tests (own 2 at both shared tests): the pass
says that they declare one depth.

Limits. The depths are numbers written by hand off `piUFull`, `piOFull`, `piWFull` and the sendings'
trees: the pass holds them against the declared rounds, the premise of `declared_of_each` against the
tables. `logLength` alone: nothing on what a table holds. Nothing on completeness, on soundness or on
what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OpensLines

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Block Alike₂)

/-- Every opening of the list declares the depth that dep says of its source. -/
def depthsEach (dep : Fmt.TreeSource → Nat) (R : List (List Fmt.DeclaredRound × Nat)) : Bool :=
  R.all fun x => x.1.all fun d => d.opens.all fun o => o.1.a == dep o.2

/-- **`DepthsDeclared` at every border**: the thread's list is alike to a list on which the openings
are in hand and declare dep, and the thread's table at a source in hand has the depth that dep says. -/
theorem declared_of_each {S Cl V W X Pb S' Cl' : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    {l : List (Block S' Cl')} (hl : List.Forall₂ Alike₂ l T.bs) (dep : Fmt.TreeSource → Nat)
    (hd : depthsEach dep (l.map roundsTrees) = true)
    (ho : opensEach T.taken (l.map roundsTrees) = true) (n : Nat)
    (ht : ∀ σ ∈ T.hand n, ∀ k w h, (T.table σ k w h).2.logLength = dep σ) :
    DepthsDeclared T n := by
  intro d hdm o hom k w h
  have hav := opens_of_alike T hl ho n
  have hσ : o.2 ∈ T.hand n :=
    of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1 hav d hdm) o hom)
  rw [ht o.2 hσ k w h]
  rw [decls_rounds, ← rounds_alike hl] at hdm
  obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.1 hdm
  have h1 := List.all_eq_true.1 hd x (List.mem_of_mem_take hx)
  exact (beq_iff_eq.1 (List.all_eq_true.1 (List.all_eq_true.1 h1 d hdx) o hom)).symm

/-- The depths of the shared chain's own trees: the sendings' three, then the two tests'. -/
def depthShared : Fmt.TreeSource → Nat
  | .own n => [24, 22, 13, 21, 17, 13, 14, 13, 18, 14, 15].getD n 0
  | .taken _ _ => 0

/-- The depths at the last chain: its own four trees, and the three that it takes over. -/
def depthLast : Fmt.TreeSource → Nat
  | .own n => [18, 15, 13, 15].getD n 0
  | .taken 0 1 => 13
  | .taken 0 82 => 22
  | .taken 1 1 => 22
  | .taken _ _ => 0

/-- Control: own tree 3 of the shared chain one deeper. -/
def depthSharedBent : Fmt.TreeSource → Nat
  | .own 3 => 22
  | σ => depthShared σ

/-- Control: the tree taken from the shared chain one deeper. -/
def depthLastBent : Fmt.TreeSource → Nat
  | .taken 1 1 => 23
  | σ => depthLast σ

-- Foretold: yes; the controls: no.
#guard depthsEach depthShared sharedR
#guard depthsEach depthLast lastR
#guard !depthsEach depthSharedBent sharedR
#guard !depthsEach depthLastBent lastR

theorem depths_shared : depthsEach depthShared sharedR = true := by decide +kernel

theorem depths_last : depthsEach depthLast lastR = true := by decide +kernel

theorem depths_bent_shared : depthsEach depthSharedBent sharedR = false := by decide +kernel

theorem depths_bent_last : depthsEach depthLastBent lastR = false := by decide +kernel

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.depthsEach
#print axioms ProofFile.Honest.K12.AtFile.declared_of_each
#print axioms ProofFile.Honest.K12.AtFile.depths_shared
#print axioms ProofFile.Honest.K12.AtFile.depths_last
#print axioms ProofFile.Honest.K12.AtFile.depths_bent_shared
#print axioms ProofFile.Honest.K12.AtFile.depths_bent_last
