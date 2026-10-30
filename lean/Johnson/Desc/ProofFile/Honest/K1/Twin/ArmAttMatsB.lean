-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmAttMatsB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmAttMats.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: attLeft2_of_b. THE PROOFS ARE COPIES.

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
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block
binds dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmAttMats
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
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
open VerifiableInference.Desc.First (S AttOwn)
open VerifiableInference.Desc.First.Look (szOf cellJ)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData symOfData dataByAddr)
open VerifiableInference.Desc.K9L (Bound)

section
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K8.ReadsQuiet (layers_ok head_ok)
open OnBytes.Model.Stages (LinkH)

end

open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn cellsAt cellsAt_name)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.First.Att.P (plannedK inOf seatCO parCOf)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- **AttLeft2 from hin and SymsIn.** -/
theorem attLeft2_of_b {J : S → Prop} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {aN : ℕ} {R₁ R₂ R₃ : Rounds}
    {c : Chain S Cl} {l : ℕ} {X : LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs} {w : Wit (CellsQ rows cols) Tok MsgT} {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B)
    (hsub : ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) {a₀ : AttOwn} {Ap : Attention.Plan}
    {tl' : HTailF2} (hs : x.2.here = .att a₀) (hL : TlLike Ap.seam.tl a₀.tl)
    (htl : x'.2.tl? = some tl') {i : First.Att.P.Runs.In}
    (hin : inOf (seatCO (parCOf Ap)) (parCOf Ap) x.2 = some (i, plannedK Ap))
    (hSy : SymsIn (Dm.N.sent l 0) A Ap.seam.tl) :
    AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w) := by
  refine ⟨hin, fun aI hb hsy μ r cn hμ hr hc => ?_⟩
  obtain ⟨_, rs, gs, hfit, hd⟩ := Fc.yes
  have hlen : (rs.map noDigest).length = 2 := by
    rw [List.length_map, Keeps.fit_length _ _ hfit, rounds_blkL]
  obtain ⟨tl₂, e2, L2⟩ := tlLike_over_reads Z Bs.G₀ l X Fc.built _ arrs x.2 x'.2 _ gs hlen hd a₀ hs
  obtain rfl : tl₂ = tl' := Option.some.inj (e2.symm.trans htl)
  have L := hL.trans L2
  have hr' := rides_at_reads_b Fc
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some Fc.front
  have harr : ((x.2.link?.map (·.arrayOf)).getD #[]) = A.L.arrayOf := by rw [hLa]; rfl
  rw [harr]
  rw [L.NM] at hμ
  rw [L.mats] at hr hc
  refine matsOfData_of_packs Ap.seam.tl A.L.arrayOf _ aI μ r cn hμ hr hc (fun i hi => ?_)
    fun i' hi' => ?_
  · exact hb μ (by rw [L.NM]; exact hμ) cn (by rw [L.mats]; exact hc) i (by rw [L.mats]; exact hi)
  · obtain ⟨nm, hn, hcell⟩ := cell_back (Dm.N.sent l 0) (Dm.N.group l) hsub A B
      (seatTab Dm.cs Dm.arr Dm.ms w) hr' _ (hSy μ hμ)
    have h0 := hsy μ (by rw [L.NM]; exact hμ) cn (by rw [L.mats]; exact hc) i'
      (by rw [L.mats]; exact hi')
    rw [L.gtTree, L.mats] at h0
    show (match A.L.arrayOf[Ap.seam.tl.gtTree.getD μ 0]? with
      | some b => (dataQ (Dm.N.sent l 0) A (seatTab Dm.cs Dm.arr Dm.ms w)).cell b.1 b.2 i' cn
      | none => 0) = _
    rw [hn]
    dsimp only
    rw [← hcell, ← h0]
    exact (cellsAt_name Dm.cs Dm.arr Dm.ms Dm.N l x'.1 x'.2 w B Fc.behind _ nm
      (by rw [hr'.arrays]; exact hn) i' cn).symm

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.attLeft2_of_b
