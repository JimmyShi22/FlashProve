-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/ArmAttEntryB.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/ArmAttEntry.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 4 OF
ITS DECLARATIONS: arrays_at_reads_b · hAttE_of_b · hAtt_of2'_b · hAtt_of2_b. THE PROOFS ARE COPIES.


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
import Johnson.Desc.K1.Law.ArmAttEntry
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAtReadsB
import Johnson.Desc.ProofFile.Honest.K1.Twin.ArmAttPaidB
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
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ)

end

open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.First.Look (linkFreshC)
open VerifiableInference.Desc.Sound (linksFull MsgT MsgQ MgData CellsQ mgAll mgBase d13 rowQ seatTab
  UFn linkNo ArmCellIn second)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.First.Att.P (plannedK)
open VerifiableInference.Desc.K9 (entInT entIn arrayIn arrayIn_some)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Params (Rounds)
open K5Law (EntIn)
open ProofFile (Cl)

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

variable {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (CellsQ rows cols) Tok MsgT → Prop} {test : ℕ → S → Option String}
include dk
/-- In front of a link's reads, inside the promise, the open link's list of arrays is the written
one. -/
theorem arrays_at_reads_b (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (x : ProofFile.InstPub × S) (y : Strs)
    (hIn : InAt Dm.N (honest (mgAll Dm Mg₀) ans test) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) (A : K9.Part) (hA : K9.segAt? x.2 = some A) :
    A.L.arrayOf = Dm.pubD.d3.arrayOf.getD l #[] := by
  have hin : Pub.linkFresh l ∈
      (First.pubSets (honest (mgAll Dm Mg₀) ans test).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l false)) := by
    have e : (honest (mgAll Dm Mg₀) ans test).more = mgMore :=
      honest_more_closed Dm Mg₀ ans test hM
    rw [e]
    exact open_of (List.all_eq_true.1 freshIn_mg l (List.mem_range.2 hl))
  have h0 : (honest (mgAll Dm Mg₀) ans test).pub (.linkFresh l) x = true := inAt_pub hIn _ hin
  rw [honest_pub_all, First.pubAll_linkFresh] at h0
  unfold linkFreshC at h0
  have h1 := (Bool.and_eq_true_iff.1 h0).2
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some hA
  rw [hLa] at h1
  exact eq_of_beq h1

/-- **hAtt_of's premise hAtt'**, from sentences on letters and AttLeft2. -/
theorem hAttE_of_b (J : S → Prop) (hM : Mg₀.more = {}) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (c : Chain S Cl) (shp : Params.ReqShape) (lay₀ : Params.ReqLayout)
    (hJl : ∀ s, J s → LiveIs shp lay₀ s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttLeft4 (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl'
        (Dm.A1 l x' w) := by
  intro l X arrs x x' y y' w p A B Fc hsub a₀ Ap tl' hs hA htlp htl e cc hN
  obtain ⟨i, L⟩ := hAtt'' l X arrs x x' y y' w p A B Fc hsub a₀ Ap tl' hs hA htlp htl
  obtain ⟨_, _, _, _, _, hin, hc, h2⟩ := hN
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some Fc.front
  have hlive : x.2.live = A.L.check := by
    unfold S.live
    rw [hLa]
  obtain ⟨eS, eL⟩ := hJl _ Fc.inv
  rw [hlive] at eS eL
  have hno : linkNo x.2 = l :=
    linkNo_of_promise_b Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front
  have hlk : A.L.check.frame.link = l := by
    unfold linkNo at hno
    rw [hLa] at hno
    exact hno
  unfold second at h2
  rw [Fc.front] at h2
  dsimp only at h2
  cases hAr : reqArray A.L.check.rows.layout cc.1 cc.2 with
  | none =>
    rw [hAr] at h2
    cases h2
  | some Ar =>
    rw [hAr] at h2
    obtain ⟨r1, r2⟩ := entInT_ranges _ A e cc Ar hc hAr hin
    obtain ⟨t1, t2⟩ := hSec l Fc.lt hsub Ap hA A e.tree cc Ar hlk eS
      (by rw [← arrays_at_reads_b Dm dk Mg₀ hM l Fc.lt x y Fc.inAt A Fc.front]; exact hc)
      (by rw [← eL]; exact hAr) h2
    have hWp := hW _ Ap hA
    have hE : EntIn Ap.iU3 (plannedK Ap) Ap.nW e := by
      obtain ⟨z, hz, z1, z2⟩ := t2 e.row e.idx r1 r2
      exact ⟨z, hz, t1, z1, z2⟩
    exact ⟨i, ⟨L.hin, hWp, fun R hR f hf => oneEntry_all hE p.1 p.2 x.2 R hR f hf, L.hM⟩⟩

/-- **The premise hAtt of arm_at_reads_of, from two of AttRest's eight fields.** -/
theorem hAtt_of2'_b (J : S → Prop) (hM : Mg₀.more = {}) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJt : ∀ s, J s → TlIsPlan XV s) (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm Mg₀ ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_of'_b Dm dk Mg₀ J hM hS hR O hWX hJt aN R₁ R₂ R₃
    (hAttE_of_b Dm dk Mg₀ J hM Z Bs c shp lay₀ hJl aN R₁ R₂ R₃ hW hSec hAtt'')

/-- **THE PREMISE hAtt OF arm_at_reads, TO THE LETTER, FROM TWO OF AttRest's EIGHT FIELDS.** -/
theorem hAtt_of2_b (J : S → Prop) {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)} {c : Chain S Cl}
    {A₀ : ProofFile.SharedSeat} {B₀ : ProofFile.SecondSeat} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A₀ B₀)
    (hWX : Bs.G₀.W = XV) (hJt : ∀ s, J s → TlIsPlan XV s) (shp : Params.ReqShape)
    (lay₀ : Params.ReqLayout) (hJl : ∀ s, J s → LiveIs shp lay₀ s) (aN : ℕ) (R₁ R₂ R₃ : Rounds)
    (hW : ∀ (g : ℕ) Ap, XV.A[g]? = some Ap → Ap.nW ≤ plannedK Ap)
    (hSec : ∀ l, l < 25 → (linksFull[l]?).getD .layers = .attention → ∀ Ap, XV.A[l / 2]? = some Ap →
      ∀ (a : K9.Part) t cn Ar, a.L.check.frame.link = l → a.L.check.frame.shape = shp →
      (Dm.pubD.d3.arrayOf.getD l #[])[t]? = some cn → reqArray lay₀ cn.1 cn.2 = some Ar →
      K9.atMoment1 a cn Ar = true → t = Ap.iU3 ∧ ∀ r i, r < Ar.sizeI → i < Ar.sizeC →
        ∃ z < Ap.nW, r = z / plannedK Ap ∧ i = z % plannedK Ap)
    (hAtt'' : ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tl', x.2.here = .att a₀ → XV.A[l / 2]? = some Ap → TlLike Ap.seam.tl a₀.tl →
      x'.2.tl? = some tl' →
      ∃ i, AttLeft2 (Dm.N.sent l 0) x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) Ap i tl' (Dm.A1 l x' w)) :
    ∀ l X arrs x x' y y' w p A B, ReadsFenceB Dm mgBase ans test J Z Bs aN R₁ R₂ R₃ c l X arrs x x' y y' w p A B →
      (linksFull[l]?).getD .layers = .attention →
      ∀ a₀ Ap tlF tl', x.2.here = .att a₀ → Bs.G₀.W.A[X.g]? = some Ap → x.2.tl? = some tlF →
      x'.2.tl? = some tl' →
      ∀ e cc, NamedEntry (Dm.Rd l) (Dm.N.sent l 0) p.1 p.2 x.2 A e cc →
      ∃ i, AttRest XV (oneEntry e) (Dm.N.sent l 0) p.1 p.2 x.2 A (seatTab Dm.cs Dm.arr Dm.ms w) l Ap i
        tlF tl' (Dm.A1 l x' w) :=
  hAtt_of2'_b Dm dk mgBase J rfl hS hR O hWX hJt shp lay₀ hJl aN R₁ R₂ R₃ hW hSec hAtt''

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.arrays_at_reads_b
#print axioms VerifiableInference.Desc.K1.hAttE_of_b
#print axioms VerifiableInference.Desc.K1.hAtt_of2'_b
#print axioms VerifiableInference.Desc.K1.hAtt_of2_b
