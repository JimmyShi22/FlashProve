-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmAttPaidB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmAttPaid.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: hAtt_of'_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the source has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm
Mg₀), or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block binds
dk (no statement here names it; it is kept so that a copied call has the source's number of
arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmAttPaid
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmBySortB
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
section
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ linkNo)
open K5Law (Cov)

end

open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- **The premise hAtt of arm_at_reads_of.** -/
theorem hAtt_of'_b (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJ : ∀ s, J s → TlIsPlan XV s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hAtt' : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttLeft4 (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl'
        (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsub a₀ Ap tlF tl' hs hg htlF htl e cc hN
  have hA : XV.A[l / 2]? = some Ap := by
    rw [← hWX, ← group_att hS hR O l Fc.lt hsub X Fc.built]
    exact hg
  have hno : linkNo x.2 = l :=
    linkNo_of_promise_b Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front
  have htlp : TlLike Ap.seam.tl a₀.tl := hJ _ Fc.inv a₀ Ap hs (by rw [hno]; exact hA)
  have etl : tlF = a₀.tl := by
    have h2 : x.2.tl? = some a₀.tl := by
      unfold S.tl?
      rw [hs]
    exact Option.some.inj (htlF.symm.trans h2)
  have hP := K5Law.public_ofPlan O.public X.g Ap hg
  obtain ⟨i, L⟩ := hAtt' l X arrs x x' y y' w p A B Fc hsub a₀ Ap tl' hs hA htlp htl e cc hN
  exact ⟨i, ⟨hA, L.hin, K5Law.ofPlan_size hP, L.hW, L.hE, fun Fn cn sg => by
      rw [etl]
      exact htlp.tabAt Fn cn sg,
    by rw [etl, htlp.u3Of]; exact K5Law.ofPlan_u3Of hP, L.hM⟩⟩

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hAtt_of'_b
