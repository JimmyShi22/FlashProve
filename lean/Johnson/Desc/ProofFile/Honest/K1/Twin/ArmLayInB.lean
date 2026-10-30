-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmLayInB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmLayIn.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: hLay_ofB_b. THE PROOFS ARE COPIES. A TRIAL THAT COUNTS NOTHING.

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
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the elder's block binds
dk (no twin's statement names it any more; it is kept so that a copied call has the elder's number
of arguments). Kept as they stand in the elder: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.ArmLayIn
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttEntryB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmBySortB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmLayMatsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmSymsB
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
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ matsOfData linksFull MsgT MgData CellsQ mgAll mgBase d13
  rowQ seatTab UFn linkNo)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open OnBytes.Road.K4 (uLay InRange)
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- **THE FIELD hLay OF k01_fifty_paid, IN ITS OWN TYPE: a twin, not joined; no call checks that the types agree.** -/
theorem hLay_ofB_b (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀) (hWX : Bs.G₀.W = XV)
    (shp : ReqShape) (lay₀ : ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s)
    (hJf : ∀ s, J s → JFirst Dm.N s) (hJ2 : ∀ s, J s → JLay2 Dm s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (names : ℕ → Array (ℕ × String))
    (hUL : ∀ l X hp, (linksFull[l]?).getD .layers = .layers → Bs.G₀.built[l]? = some X →
      Bs.G₀.W.G[X.g]? = some hp →
      Dm.uL l = uLay hp.tl fun _ D => matsOfData hp.tl (names l) D)
    (hnm : ∀ l, l < 25 → names l = Dm.pubD.d3.arrayOf.getD l #[])
    (hB : ∀ l hp, l < 25 → (linksFull[l]?).getD .layers = .layers → XV.G[l / 2]? = some hp →
      symsSeatedB (Dm.pubD.d3.arrayOf.getD l #[]) lay₀ shp l hp.tl = true)
    (hsub : ∀ l, l < 25 → ∀ u ∈ Dm.N.sent l 0, u ∈ Dm.N.group l) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .layers →
      ∀ b₀ o hp tl', x.2.here = .lay b₀ → b₀.own = some o → Bs.G₀.W.G[X.g]? = some hp →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ M n, Dm.uL l x.2 = uLay hp.tl M x.2 ∧
        LayRest (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) hp.tl tl' M o n
          (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsb b₀ o hp tl' hs ho hg htl e cc hN
  have hno : linkNo x.2 = l :=
    linkNo_of_promise_b Dm dk mgBase rfl l Fc.lt x y Fc.inAt A Fc.front
  have hg2 : XV.G[l / 2]? = some hp := by
    rw [← hWX, ← group_lay hS hR O l Fc.lt hsb X Fc.built]
    exact hg
  obtain ⟨h3, hE⟩ := hJ2 _ Fc.inv b₀ o hp A hs ho (by rw [hno]; exact hg2) Fc.front
  rw [hno] at hE
  obtain ⟨e1, e2, z, z1, z2⟩ := hE p e cc Fc.run hN
  have hF := hJf _ Fc.inv A Fc.front
  rw [hno] at hF
  have hSy := symsIn_at_reads_b Dm dk mgBase rfl Fc hJl (hB l hp Fc.lt hsb hg2) hF
  have harr := arrays_at_reads_b Dm dk mgBase rfl l Fc.lt x y Fc.inAt A Fc.front
  refine ⟨fun _ D => matsOfData hp.tl (names l) D, e.idx + 1, by rw [hUL l X hp hsb Fc.built hg],
    oneEntry_all (P := fun u => u.tree = o.v.iU3 ∧ u.row = 0 ∧ u.idx < e.idx + 1 ∧
      ∃ z : HFun × ℕ × ℕ, z.1 ∈ o.funs ∧ hp.tl.tabAt z.1 z.2.1 z.2.2 = some u.idx)
      ⟨e1, e2, Nat.lt_succ_self _, z, z1, z2⟩ p.1 p.2 x.2, h3, ?_⟩
  show InRange tl' (matsOfData hp.tl (names l) _) _
  rw [hnm l Fc.lt, ← harr]
  exact layM_of_b Dm dk mgBase Fc (hsub l Fc.lt) hs hg htl hSy

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hLay_ofB_b
