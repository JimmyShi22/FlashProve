-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmHeadRideB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmHeadRide.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: hK6_of5_b. THE PROOFS ARE COPIES.

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
dk (no twin's statement names it; it is kept so that a copied call has the source's number of
arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmHeadRide
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmHeadLabB
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
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain Link FileDescription Place Strs)
open VerifiableInference.Desc.First (S Here HeadOwn ModelPart Item Pub Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgBase Mem seatTab dataQ)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (K6Name p8K6 ColFour CallsSeated MatsSeated ride_of_seated)
open VerifiableInference.Desc.First.Look (sigListCalls)
open OnBytes.Model.Verify (borderOf)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
open VerifiableInference.Desc.Kinds.Head.Law VerifiableInference.Desc.Kinds.Head
  VerifiableInference.Desc.Kinds
open OnBytes (E zeroE)
open OnBytes.Model (World Reading HFun HTailF2 Fork)
open OnBytes.Model.Verify (borderOf publicOf layerShape)
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.K9 (Readers RunOf)
open VerifiableInference.Desc.Sound (dataQ Mem MsgT cellsAt seatTab worldOwn ArmCellIn)

end

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat}

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
/-- **THE PREMISE hK6 OF arm_at_reads_three, FROM FOUR CLAUSES ON THE STATE IN FRONT ALONE.** -/
theorem hK6_of5_b (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data) (J : S → Prop)
    (hJ : ∀ s, J s → NoTables s) (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₀ B₀) (hDlk : Dm.links = linksFull)
    (hlk : ∀ l, l < 25 → Dm.lk l = c.links[l]?) (hWX : Bs.G₀.W = XV) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (cU : ℕ × String)
    (hU : (Dm.pubD.d3.arrayOf.getD 24 #[])[Kinds.Head.Law.readsOf XV]? = some cU)
    (hK : ∀ t, (Dm.pubD.dS.trees 24)[Kinds.Head.Law.readsOf XV]? = some t →
      XV.H.nU.getD 2 0 ≤ t.2.1)
    (msR : List Mem) (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ)
    (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls Dm.sent rad 24).length → ℕ × ℕ)
    (T : _root_.Meaning.laidThere XV (_root_.Meaning.sizesOf XV) lay6 = true)
    (hC : CallsSeated (ColFour XV.hS XV.HLy (borderOf XV.y)) Dm.arr msR Dm.N XV lay6 num Dm.sent rad
      24 seatT)
    (hsub : ∀ x ∈ Dm.N.sent 24 0, x ∈ Dm.N.group 24)
    (hK6' : ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      HeadLeft6 XV (Dm.N.sent 24 0) x.2 A Dm.arr Dm.N num lay6) :
    ∀ X arrs x x' y y' w p A B,
      ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c 24 X arrs x x' y y' w p A B → K6Name p.2 →
      ∃ l₀ piece states cU, HeadRest XV (Dm.Rd 24) (Dm.N.sent 24 0) p.1 x.2 A B Dm.cs Dm.arr Dm.ms
        Dm.N 24 w l₀ piece states cU :=
  hK6_of4_b Dm dk J hJ hS hR O hDlk hlk hWX aN R₁ R₂ R₃ cU hU hK msR lay6 num rad seatT T hC
    fun X arrs x x' y y' w p A B Fc hn =>
      have L := hK6' X arrs x x' y y' w p A B Fc hn
      ⟨L.hT, L.hRun, ride_of_seated XV (Dm.N.sent 24 0) (Dm.N.group 24) A B _ hsub
        (rides_at_reads_b Fc) Dm.arr Dm.N num lay6 T L.hlay L.hMats⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hK6_of5_b
