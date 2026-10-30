-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/Kinds/K8Bridge.lean: the kind K8 (the smallness test; 25 places): THE CALL OF
ITS FILES' RULE AT THE SEATED TERM. K8's files' own named conditions, under the head `P5J.AtMgA`,
give the kind's field in the form in which a kind's law is counted, `P5J.AtMgA.Kind h 𝔏 .K8`
(Johnson/P5J/RowsAtAll.lean). The condition stands at the one fence of
Johnson/Goal/Skeleton/Kinds/Unmarked.lean, `h.rchU`: "reached, at a typed instance's public part,
and no mark". The premise hFit is not in the condition: its files pay
it from the head alone: `fit_at_const`, Johnson/P1K8R/FitAt.lean.

  `AtMgA.K8Cond h 𝔏`: the premises of `P1K8T.k08_at_const_tight` (Johnson/P1K8R/TightAt.lean) that
    nothing here pays, to the letter: four tests with code (hDoor: `namesDoorB`; hW: `planFitsAllB`;
    hGt: `gtSizesAllB`; hOwn: `smallSizesOwnB`), and:
    there is n₀ with `K8LeftT` at each of the 25 places, at the first chain's own pieces `h.row 𝔏`
    and AT THE FENCE `h.rchU`.
  `k08_kind_all`: the three lists' heads are 𝔏's → `h.K8Cond 𝔏` → `h.Kind 𝔏 .K8`.
PAID HERE, out of the head and the three equations: hD (the description's data of "proof file" are
the head's, at the frame's depth: `LaidAt.atDepth`, `LaidAt.data`) · hT and hf (the pieces hold the
description's own sub-protocols, and fit: `paidAtDesc`, at T := `atDesc` of the tower's
three rows, whose first row is `h.row 𝔏` by definition) · hE (the seated extractor lays nothing at
the 25 places: `ext_id_k8`) · hRch (`h.rchU` gives `RchAt`: a projection) · hFit
(`SeatFits` at every member of `At.ms`: `fit_at_const`, from the head's own test
`PlanOk.fit`). BY DEFINITION, checked by Lean in the last line: K8's files' description `FD Zp
(seatZ Zp Np) (secondAt Zp Np) cF` is the tower's `F0T OnBytes.secondHashFunction Zp Np cF`; its lists of sorts
and places are the form's.

Limits. IT PAYS NO LAW. The condition holds a tie of the conclusion: `K8LeftT`'s field small. No
member of the condition is known: it follows from the head and the three equations (`k08_cond_head`,
Johnson/P1K8R/KindFromHead.lean), but that there is a head is proved at `VerifierAndGoals.storedPublicFiles` and
`VerifierAndGoals.zGap` (at secondHashFunction, with `fixedConfigurationDigest` in the digest's place; side library AtFullSide/Top/); at
other files: evaluated, not proved; as
read from K8's files, not shown, the four tests are evaluated true at the full size, the test in
the field near is not. At `OnBytes.secondHashFunction` alone.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.Kinds.Unmarked
import Johnson.P1K8R.TightAt
import Johnson.P1K8R.FieldAt
import Johnson.P1K8R.FitAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/- The names in scope are those of Johnson/P1K8R/TightAt.lean. -/
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

/-- **The smallness test's kind's named conditions, at the closed constant, the seated pieces and
the one fence.** -/
def _root_.P5J.AtMgA.K8Cond (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop :=
  namesDoorB (FD Zp (seatZ Zp Np) (secondAt Zp Np) cF) = true ∧
  planFitsAllB Zp.p.X = true ∧
  Second.K08.gtSizesAllB Zp.p.X = true ∧
  (∀ G, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → ProofFile.smallSizesOwnB Zp G = true) ∧
  ∃ n₀ : ℕ → ℕ, ∀ (G : ProofFile.Ground) l Xl q, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G → l ≤ 24 →
    G.built[l]? = some Xl → (h.toAtMg.row 𝔏)[ixOf l]? = some q →
    K8LeftT h (P5J.At.rad3At Zp Z.lay) G l Xl (n₀ l) q h.rchU

set_option maxHeartbeats 4000000 in
/-- **The field.** -/
theorem _root_.P5J.k08_kind_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K8Cond 𝔏) : h.Kind 𝔏 KindName.K8 := by
  obtain ⟨hDoor, hW, hGt, hOwn, n₀, H⟩ := C
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth h.scope h.laid]
    exact h.laid.data
  have hP := paidAtDesc _ (Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT)
    (P5J.F0T OnBytes.secondHashFunction Zp Np cF) "proof file" _ hD
    (sealLast_of_planOk (P5J.F0T OnBytes.secondHashFunction Zp Np cF) h.laid.planOk) (Run.ckP .two)
    𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃ q₁ q₂ q₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd
  have hT := hP.1
  refine h.kind_of_unmarked 𝔏 KindName.K8 ?_
  exact k08_at_const_tight h hDoor hW hGt hOwn (fit_at_const h) hD
    (T := atDesc (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
      (piecesAt (Run.ckP .two) (P5J.F0T OnBytes.secondHashFunction Zp Np cF) (D.at frS.P.T.a) 𝔏.c₁ 𝔏.k₁ 𝔏.c₂
        𝔏.k₂ 𝔏.c₃ 𝔏.k₃ (restCap 𝔏.e₁) (restCap 𝔏.e₂) (restCap 𝔏.e₃) 𝔏.dW 𝔏.wEnd))
    ⟨hT.ft₁, hT.ft₂, hT.ft₃, hT.b₁, hT.b₂, hT.b₃, hT.back₁, hT.back₂, hT.back₃⟩ hP.2.1
    (h.toAtMg.ex 𝔏)
    (fun l hl a b w => by
      unfold P5J.AtMg.ex P5J.exF
      exact ext_id_k8 _ _ _ _ _ _ _ _ _ _ l hl a b w)
    h.rchU (fun _ _ u => u.1.1) n₀ H

end P1K8T

#print axioms P5J.k08_kind_all
