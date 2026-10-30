-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/NamedOfReach.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE
FIRST SPENDING OF "REACHED": AT EVERY REACHED STATE IN FRONT OF THE DRAW, WHAT THE DRAWN MATRIX
MULTIPLIES IS SENT BEFORE THE MATRIX IS DRAWN. NO SOUNDNESS.

A kind's tie to the table of joints is asked at every statement that meets a border's promise. Each
of its clauses has this premise: the verifier's state in the
statement is REACHED: the first k blocks of the description's first chain hand it on, from the state
at the start of the statement's own public part, at some rounds and columns (`RchAt F k a`,
Johnson/Top/H0/Walk/ReachAt.lean). `k08_named_at_seat` speaks of just such
states. Here the two meet:
  `named_of_reach`: in the goals' scope, under the description's test on the plan and the public
    test `namesDoorB`: at each of the 25 places, at every statement a that is reached at the number
    of the draw's entry: `Named.namedAt` says yes at a's state.
  `namedB_of_reach`: **so a link is open there, with the smallness test's part tl and the link's
    context L, and `Named.namedB` says yes at a's own statement of oracles, book, tl and L**: the
    premise hN of the law `k08_rowT_named` (Johnson/Desc/First/K8/LawTable.lean), whose letters may
    be taken off the statement in front.
THE WITNESSES OF "SOME ROUNDS AND COLUMNS" STAY INSIDE THE PROOFS: both conclusions speak of a's
state alone.
Limits. `namesDoorB F` is a premise: verify() does not ask it yet. That onlineDescription returns in scope is
a premise.

-/
import Johnson.P1K8R.RowAtSeat
import Johnson.Top.H0.Walk.ReachAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8S

open Inst.Model
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (RchAt rchAt_fold)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- At a reached state in front of the draw the test says yes. -/
theorem named_of_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) {x : ℕ × ℕ} (hx : x ∈ places) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) (14 * x.1 + x.2 + 2) a) :
    Named.namedAt (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar a.1.2 = true := by
  obtain ⟨_, rs, cols, f⟩ := rchAt_fold h
  exact named_at_place hS hR O hP hD hx e3 a.1.1 rs cols _ f

/-- **The law's premise, at the statement's own letters.** -/
theorem namedB_of_reach (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) {x : ℕ × ℕ} (hx : x ∈ places) {Xl : LinkH}
    (e3 : Bs.G₀.built[x.1]? = some Xl) {Str : Type} (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) (14 * x.1 + x.2 + 2) a) :
    ∃ tl L, a.1.2.tl? = some tl ∧ a.1.2.link? = some L ∧
      Named.namedB (ProofFile.k8ParW Z Bs.G₀ Xl x.1).toPar a.1.2.st a.1.2.book tl L = true := by
  have hN := named_of_reach hS hR O hP hD hx e3 a h
  unfold Named.namedAt at hN
  cases ht : a.1.2.tl? with
  | none => simp [ht] at hN
  | some tl =>
    cases hl : a.1.2.link? with
    | none => simp [ht, hl] at hN
    | some L =>
      rw [ht, hl] at hN
      exact ⟨tl, L, rfl, rfl, hN⟩

end P1K8S

#print axioms P1K8S.named_of_reach
#print axioms P1K8S.namedB_of_reach
