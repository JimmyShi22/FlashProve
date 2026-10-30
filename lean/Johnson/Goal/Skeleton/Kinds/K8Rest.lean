-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/Kinds/K8Rest.lean: the kind K8 (the smallness test; 25 places): A PAYMENT
BENEATH THE KIND's NAMED CONDITION `P5J.AtMgA.K8Cond` (Johnson/Goal/Skeleton/Kinds/K8Bridge.lean),
WHICH DOES NOT TURN: two of its four tests with
code are theorems under the head.
  `AtMgA.k8_planFits`, `AtMgA.k8_gtSizes`: `planFitsAllB Zp.p.X = true` and
    `Second.K08.gtSizesAllB Zp.p.X = true`, from the head alone: other files prove each at
    everything that `publicOf` returns (`planFitsAllB_of_public`, `gtSizesAllB_of_public`,
    Johnson/Desc/Sound/K8Tests/), and the head holds such a return (its field `pubOne`; that
    `At.X Zp` is `Zp.p.X`: by definition).
  `AtMgA.K8Rest h 𝔏`: what is left of the condition: its first, fourth and fifth part, to the
    letter: `namesDoorB`, `smallSizesOwnB`, and: there is n₀ with `K8LeftT` at each of the 25
    places, at the first chain's own pieces and at the fence `h.rchU`.
  **`AtMgA.k8Cond_of_rest`**: `h.K8Rest 𝔏` → `h.K8Cond 𝔏`.
  `k08_kind_rest`: the three lists' heads are 𝔏's → `h.K8Rest 𝔏` → `h.Kind 𝔏 .K8`.

Limits. It pays two closed tests and no law. No member of `K8Rest` is known. At `OnBytes.secondHashFunction`
alone.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.Kinds.K8Bridge
import Johnson.Desc.Sound.K8Tests.GtSizesOfPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/- The names in scope are those of Johnson/Goal/Skeleton/Kinds/K8Bridge.lean. -/
namespace P1K8T

open Iop
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (planFitsAllB)
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)
open ProofFile (Cl)
open P5J (AtMgA mgAtAll)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The condition's second part, from the head alone. -/
theorem _root_.P5J.AtMgA.k8_planFits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    planFitsAllB Zp.p.X = true :=
  LT28.K8Tests.planFitsAllB_of_public (X := Zp.p.X) h.toAtMg.pubOne

/-- The condition's third part, from the head alone. -/
theorem _root_.P5J.AtMgA.k8_gtSizes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Second.K08.gtSizesAllB Zp.p.X = true :=
  LT28.K8Tests.gtSizesAllB_of_public (X := Zp.p.X) h.toAtMg.pubOne

/-- **What is left of the smallness test's kind's named condition.** -/
def _root_.P5J.AtMgA.K8Rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true ∧
  (∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true) ∧
  ∃ n₀ : ℕ → ℕ, ∀ (G : ProofFile.Ground) l Xl q, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl → (h.toAtMg.row 𝔏)[ixOf l]? = some q →
    K8LeftT h (P5J.At.rad3At Zp Z.lay) G l Xl (n₀ l) q h.rchU

/-- **THE PAYMENT: the rest gives the condition.** -/
theorem _root_.P5J.AtMgA.k8Cond_of_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (R : h.K8Rest 𝔏) : h.K8Cond 𝔏 := by
  obtain ⟨hDoor, hOwn, hLeft⟩ := R
  unfold P5J.AtMgA.K8Cond
  exact ⟨hDoor, h.k8_planFits, h.k8_gtSizes, hOwn, hLeft⟩

/-- The field, from the rest. -/
theorem _root_.P5J.k08_kind_rest (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (R : h.K8Rest 𝔏) : h.Kind 𝔏 KindName.K8 :=
  P5J.k08_kind_all h 𝔏 q₁ q₂ q₃ (h.k8Cond_of_rest 𝔏 R)

end P1K8T

#print axioms P5J.AtMgA.k8_planFits
#print axioms P5J.AtMgA.k8_gtSizes
#print axioms P5J.AtMgA.k8Cond_of_rest
#print axioms P5J.k08_kind_rest
