-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/FiveAtBase.lean: the smallness test at the first chain's thread at the base prover: the
prover that the maker returns at `onlineProverPartsInUse`, the index a letter, at any letters of the thread
and anything said. What stands of the five statements at the kind's 25 borders.

  `playsS_at_base`   the kind's member plays, at every Said
  `half_at_base`     the search of the base prover's first chain finds the kind's half at its place

Nothing is claimed on completeness, soundness or hiding.
-/
import AtFullSide.K8.SimAtFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8
open ProofFile.Honest ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Strs Place)
open VerifiableInference.Desc.Sound (MsgT)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead WtF Script)

variable {W₀ : Type} (I : WiderIn W₀) (o : ProofFile.SecondHashFunctionArgument) (Sz : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
  (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o Sz O) = .ok A)
  {Bk : ProverCoinCounts}
  (Q : Script Bk (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ IndexCommitterCoins ProofFile.Inst Cells → Prop)
  (Rd : Nat → Local W₀ IndexCommitterCoins ProofFile.Inst Cells → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
include h hA

/-- **The kind's member plays at each of its 25 borders, at the base prover, at every Said.** -/
theorem playsS_at_base
    (Said : Nat → Coins Bk → Mid (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) {l : ℕ}
    (hl : l < 25) :
    PlaysS (lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (14 * l + (if l = 24 then 5 else 4) + 2) :=
  playsS_at_ownMats h hA id (hex_base I o Sz O A.Z A.G) (ho_base I o Sz O A.Z A.G) Q test carryX
    item n₁ n₂ b₀ Vd Rd Kp w Said hl

omit h in
/-- **The base prover's search at the kind's place finds the kind's half.** -/
theorem half_at_base {l : ℕ} {Xl : LinkH} (hX : A.G.built[l]? = some Xl) :
    (A.H.first.find? fun g => g.place == ⟨1, some l, (ProofFile.k8Par A.Z A.G Xl l).piece, .K8⟩) =
      some (smallHalf id (ProofFile.k8Par A.Z A.G Xl l, K3.matsOwn A.G.W l)) :=
  k8_half_any_fill id matsO hA (hex_base I o Sz O A.Z A.G) (ho_base I o Sz O A.Z A.G) hX

end AtFullSide.K8

#print axioms AtFullSide.K8.playsS_at_base
#print axioms AtFullSide.K8.half_at_base
