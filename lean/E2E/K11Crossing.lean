-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/K11Crossing.lean: the kind K11's part of the crossing from the base prover of E2E/K11AtTheTerm.lean
to the online prover of E2E/TheHonestProver.lean: the side that the maker's return at onlineFilling
holds at the kind's place is the kind's side at the base filling, read through the table's
randomness; and no other lot lays a side of the kind. This file states; it proves nothing.
-/
import E2E.TheHonestProver
import E2E.K11AtTheTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles.HonestTerm.K11Term
open VerifiableInference.Desc (Chain KindName)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K11
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)

/-- **The side at the kind's place of the online prover's return is the base side read through.**
Second: no lot of the online filling holds a side of the kind but the kind's own. -/
def K11HalfThrough : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineReturn Z)
    (Bs : ProofFile.PureBase),
    onlineMaker Z = .ok A →
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (A.H.first.find? fun g => g.place == IM.k11Place) =
      some ((k11Row (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) (matrixInput.weights Zp) Zp Bs.G₀).half.thru (Local.thru id (tableCoins Z))
        (Local.thru id (tableCoins Z))) ∧
    ∀ M ∈ (onlineFilling Z).lots,
      (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ KindName.K11) ∨
        M.halves A.Z A.G = ((k11Row (Rc := IndexCommitterCoins) (Tr := Cells) (X := Unit) (matrixInput.weights Zp) Zp Bs.G₀).half.thru
          (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))) :: []

/-- **The simulator's three clauses at the online prover.** -/
def K11SimulatorOwedOnline : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place) (A : OnlineReturn Z)
    (Bs : ProofFile.PureBase),
    onlineMaker Z = .ok A →
    AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    K11OwedAt (matrixInput.weights Zp) Zp cF A Bs

end AtPublicFiles.AtFiles.HonestTerm.K11Term
