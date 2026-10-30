-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/AtBase.lean: the tie of K4's rows to the base filling
`onlineProverPartsInUse`, in the filling's order: the halves of the kind K4 in its first chain are K4's
rows' halves. Statements and proofs. General in the index's type and the value I.

  `k4SLotByPub`, `k4SLotByPub_toHLot`   K4's rows at the filling's reader; forgotten, they are the
      filling's own lot.
  `k4_halves_at_base`   **at one public part and ground, of the filling's lots.**
  `k4_halves_at_maker`   **at a return of the maker at that filling, of its prover's first chain.**

Limits. At the base filling: what the term reads through it is the crossing's, which is not
K4's. Equations on lists. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtHalves

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4.Honest (K4Pub)
open VerifiableInference.Desc (KindName)

variable {W₀ : Type}

/-- **K4's rows with the reader of the index that the filling lays at the public part**: a value of
`SLot` in the form that a filling's lot has (`HLot.byPub`). -/
def k4SLotByPub {Rc Tr X : Type} (cells : Tr → Cells) (weights : Pub → W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    SLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst :=
  { name := "K4"
    rows := fun Z G => (k4SLot cells (weights Z) look).rows Z G }

/-- **By forgetting the simulators, On and bud, that value is the filling's lot.** An equation of
lots: it answers `overlaySlots`'s premise (E2E/TheSides.lean). -/
theorem k4SLotByPub_toHLot {Rc Tr X : Type} (cells : Tr → Cells) (weights : Pub → W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    (k4SLotByPub (Rc := Rc) (X := X) cells weights look).toHLot =
      HLot.byPub weights fun wt => k4HLot cells wt look :=
  congrArg (HLot.mk "K4") (funext fun Z => funext fun G =>
    k4_rows_halves (Rc := Rc) (X := X) cells (weights Z) look Z G)

/-- **The halves of the kind K4 in the base filling's first chain are K4's rows' halves, in their
order**, at every public part and ground. -/
theorem k4_halves_at_base (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Zq : Pub) (G : Ground) :
    (firstOf Zq G (onlineProverPartsInUse I o S O).lots).filter
        (fun y => decide (y.place.kind = .K4)) =
      ((k4SLot (Rc := IndexCommitterCoins) (X := Unit) id (I.weights Zq) fun _ _ => k4LookAt).rows Zq G).map
        (·.half) := by
  have hk₁ : ((fillPairs I o S O).take 6).map (·.2) =
      [KindName.K1, .K2, .K7, .K11, .K13, .K3] := rfl
  have hk₂ : ((fillPairs I o S O).drop 7).map (·.2) =
      [KindName.K5, .K6, .K8, .K10, .K12, .K1] := rfl
  have hs : (onlineProverPartsInUse I o S O).lots =
      ((fillPairs I o S O).take 6).map (·.1) ++
        (HLot.byPub I.weights fun wt => k4HLot id wt fun _ _ => k4LookAt) ::
          ((fillPairs I o S O).drop 7).map (·.1) := rfl
  rw [hs]
  refine k4_first_halves id (I.weights Zq) (fun _ _ => k4LookAt) Zq G rfl ?_ ?_
  · intro M' hM' y hy e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM'
    have hk := fillPairs_kinds I o S O Zq G r (List.mem_of_mem_take hr) y hy
    have hm : r.2 ∈ ((fillPairs I o S O).take 6).map (·.2) := List.mem_map_of_mem hr
    rw [hk₁, ← hk, e] at hm
    exact absurd hm (by decide)
  · intro M' hM' y hy e
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hM'
    have hk := fillPairs_kinds I o S O Zq G r (List.mem_of_mem_drop hr) y hy
    have hm : r.2 ∈ ((fillPairs I o S O).drop 7).map (·.2) := List.mem_map_of_mem hr
    rw [hk₂, ← hk, e] at hm
    exact absurd hm (by decide)

/-- **At a return of the maker at the base filling the halves of the kind K4 in its prover's first
chain are K4's rows' halves, in their order.** -/
theorem k4_halves_at_maker (I : WiderIn W₀) (o o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles o' pol lay KL (onlineProverPartsInUse I o S O) = .ok A) :
    A.H.first.filter (fun y => decide (y.place.kind = .K4)) =
      ((k4SLot (Rc := IndexCommitterCoins) (X := Unit) id (I.weights A.Z) fun _ _ => k4LookAt).rows A.Z A.G).map
        (·.half) := by
  rw [(atPure_ok hA).2.2.2.2.2.2.2.1]
  exact k4_halves_at_base I o S O A.Z A.G

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4SLotByPub
#print axioms ProofFile.Honest.K4.ExactFresh.k4SLotByPub_toHLot
#print axioms ProofFile.Honest.K4.ExactFresh.k4_halves_at_base
#print axioms ProofFile.Honest.K4.ExactFresh.k4_halves_at_maker
