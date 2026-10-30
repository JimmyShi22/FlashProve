-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/PlanesAtAllB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/PlanesAtAll.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: planesLeft4_atAll_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block binds
dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.PlanesAtAll
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmPlanesHostAtB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT CellsQ mgBase seatTab)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6 readsOf)
open VerifiableInference.PlanWritten (forestView forestView_inj sameForestV sameForestV_iff)
open _root_.Desc.K14.Law (seatZ secondAt)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT → Prop}
  {test : ℕ → S → Option String}
include hA

/-- **PlanesLeft4 inside the fence, at the constant.** -/
theorem planesLeft4_atAll_b
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hArr : readsArrB Zp.made.p.built.links (P5J.At.X Zp) = true)
    (hWide : readsWideB Zp.made.p.built.links (P5J.At.X Zp) = true)
    (hLab : labPB Zp.made.p.built.links (P5J.At.X Zp) = true)
    (hSh : shapeHB (P5J.At.X Zp) = true) (dk : K12Data) (J : S → Prop) (aN : ℕ)
    (R₁ R₂ R₃ : Rounds) {X : Stages.LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs}
    {w : Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok MsgT}
    {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFenceB hA.𝔇 mgBase ans test J Zp Bs aN R₁ R₂ R₃ cF 24 X arrs x x' y y' w p A B)
    (L : PlanesLeft6 (P5J.At.X Zp) (hA.𝔇.N.sent 24 0) x.2 A hA.𝔇.arr hA.𝔇.N (P5J.At.num Zp)
      (P5J.At.layout Zp)) :
    PlanesLeft4 (P5J.At.X Zp) (hA.𝔇.N.sent 24 0) (hA.𝔇.N.group 24) x.2 A B
      (seatTab hA.𝔇.cs hA.𝔇.arr hA.𝔇.ms w) := by
  obtain ⟨cU, hU⟩ := hU_atAll hA hArr
  exact planesLeft4_at342_b hA.𝔇 dk J O O.W aN R₁ R₂ R₃ cU (P5J.At.num Zp) (P5J.At.layout Zp)
    hA.plan.laid hU (hKw_atAll hA hWide) (hTh_atAll hA hWide) (hShape_of hSh)
    (hLabP_atAll hA hLab) (hLen_of_shape hA.pubOne (hShape_of hSh)) Fc L

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.planesLeft4_atAll_b
