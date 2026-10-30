-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtHalves.lean: the tie of K4's rows to a filling, as
an equation of lists: where one lot of a list lays K4's halves and no other lot lays a half of the
kind K4, the halves of the kind K4 in the list's first chain are K4's rows' halves, in their order.
A statement and its proof.

  `k4_rows_halves`   the rows' halves are the halves of K4's lot without the simulators.
  `k4_first_halves`   **the prover's halves of the kind K4 are the rows' halves.**

Limits. AN EQUATION OF HALVES AT ONE PUBLIC PART AND GROUND, NOT OF LOTS: in a filling K4's lot reads
the index through the public part. On lists alone. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SLot
import Johnson.Desc.ProofFile.Honest.K4.Law.LotKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (KindName)

variable {W₀ Rc Tr X : Type}

/-- The rows' halves are the halves of K4's lot. -/
theorem k4_rows_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Zq : Pub)
    (G : Ground) :
    ((k4SLot (Rc := Rc) (X := X) cells weights look).rows Zq G).map (·.half) =
      (k4HLot (Rc := Rc) (X := X) cells weights look).halves Zq G :=
  congrArg (fun L : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X => L.halves Zq G)
    (k4SLot_toHLot cells weights look)

/-- **The halves of the kind K4 in a first chain's list of halves are K4's rows' halves, in their
order**, where the lot M lays K4's halves and no other lot of the list lays a half of that kind. -/
theorem k4_first_halves (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Zq : Pub)
    (G : Ground) {M : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X}
    {l₁ l₂ : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X)}
    (hE : M.halves Zq G = (k4HLot (Rc := Rc) (X := X) cells weights look).halves Zq G)
    (h₁ : ∀ M' ∈ l₁, ∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4)
    (h₂ : ∀ M' ∈ l₂, ∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) :
    (firstOf Zq G (l₁ ++ M :: l₂)).filter (fun y => decide (y.place.kind = .K4)) =
      ((k4SLot (Rc := Rc) (X := X) cells weights look).rows Zq G).map (·.half) := by
  have none_of : ∀ l : List (HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X),
      (∀ M' ∈ l, ∀ y ∈ M'.halves Zq G, y.place.kind ≠ .K4) →
      (l.flatMap fun L => L.halves Zq G).filter (fun y => decide (y.place.kind = .K4)) = [] := by
    intro l hl
    refine List.filter_eq_nil_iff.2 fun y hy => ?_
    obtain ⟨M', hM', hyM⟩ := List.mem_flatMap.1 hy
    simpa using hl M' hM' y hyM
  have all_of : ((k4HLot (Rc := Rc) (X := X) cells weights look).halves Zq G).filter
      (fun y => decide (y.place.kind = .K4)) =
      (k4HLot (Rc := Rc) (X := X) cells weights look).halves Zq G :=
    List.filter_eq_self.2 fun y hy => by simpa using k4HLot_kind cells weights look Zq G y hy
  rw [k4_rows_halves]
  unfold firstOf
  rw [List.flatMap_append, List.flatMap_cons, List.filter_append, List.filter_append, none_of _ h₁,
    none_of _ h₂, hE, all_of]
  simp

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4_rows_halves
#print axioms ProofFile.Honest.K4.ExactFresh.k4_first_halves
