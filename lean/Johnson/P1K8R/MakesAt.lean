-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/MakesAt.lean: THE SMALLNESS TEST AT THE TABLE OF JOINTS: THE FIELD
`makes` OF `K8Fill` (OwesAt.lean) AT THE DESCRIPTION'S OWN 25 PLACES: THE JOIN AT THE FOLD.
NO SOUNDNESS.

The row of the draw opens the run of forms "small"; the table ties a public test to every open run
of forms, and the block that opens the run must make it: behind a yes of the draw, `K9.formsInA` at
the run "K8.equations" says yes. That line is proved under named premises in another file
(`K9.formsInA_row`, Johnson/Desc/First/Batch/SmallNear.lean). Here its premises on the state in
front of the draw are PAID from theorems at the fold, in the goals' scope, at each link l ≤ 24:
  an open segment's part: the link and the smallness test's part (`namedB_of_reach`), the ledger
    (`fork_of_onQ`);
  `Named.namedAt`: `namedB_of_reach`;
  the caller's list of tables is the structure's own, and `FunsAre`: `k8FunsAreR`
    (Johnson/P1K8R/FunsAtSeat.lean);
  every table lies on the third vector of reads; there is a third vector: `k8Front_of_test`;
  the state's value has the seven fields of THE LINK's OWN planned value: `k8LaidOwn`
    (Johnson/P1K8R/FrontAtSeat.lean).
What is left stands in ONE structure:
  `MakesOwes`: the readers give the reader of the single equations at that run; the link's own
    planned value has as many numbers of symbol arrays as matrices (a test on the public
    parameters); and, at a reached statement inside the promise (`atFold`): `formsInA_row`'s test
    on the plan `smallSizesB` at the open link's list of arrays and layout, at the link's own
    planned value; its `SeatsOwn`; its `nearA` at the array of digits.
  `k08_makes`: **`MakesOwes` gives `K8Fill.makes`'s sentence, to the letter**, at
    oS := "`formsInA` at that run says yes".
Limits. `MakesOwes` is shown at no filling. AT `OnBytes.secondHashFunction` ALONE. Nothing on soundness.

-/
import Johnson.P1K8R.FillAt
import Johnson.P1K8R.FunsAtSeat
import Johnson.Desc.First.Batch.SmallNear

set_option autoImplicit false
set_option maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open Inst.Model
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj Johnson.Pack
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc (Block Chain FileDescription Place Claim Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers flatPlacesOf)
open VerifiableInference.Desc.First.K8
open VerifiableInference.Desc.First.K8.Ready (frontB planFitsAllB cond_of_front seven lay7
  lay7_of_test)
open VerifiableInference.Desc.K9 (Readers formsInA smallReader smallSizesB SeatsOwn nearA
  formsInA_row segAt_of)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

section
variable {W' : Type} {Fr : Frame} (Z : ProofFile.Pub) (A : ProofFile.SharedSeat) (B : ProofFile.SecondSeat)
  (c : Chain S Cl) (N : Numbers) (Mg : Meaning ProofFile.InstPub W') (Wp : Verify.Public)
  (Rd : Readers) (bN : ℕ) (p : Par) (l : ℕ) (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop)

/-- **What is left of the field `makes` at link l.** -/
structure MakesOwes : Prop where
  rd : ∀ t : S, Rd.forms bN "K8.equations" t = smallReader t
  gt : ∀ tlP, P1K8S.PlanAt Wp l tlP → tlP.gtTree.size = tlP.NM
  atFold : ∀ (z : ProofFile.InstPub) (a : S × Fr.E.Str) (q : VerifiableInference.Desc.K9.Part)
    (tl : HTailF2),
    onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (drawAt l) a →
    Rch (drawAt l) ((z, a.1), a.2) → a.1.failed = none →
    VerifiableInference.Desc.K9.segAt? a.1 = some q → a.1.tl? = some tl →
    (∀ tlP, P1K8S.PlanAt Wp l tlP →
      smallSizesB q.L.arrayOf q.L.check.rows.layout tlP p = true) ∧
      SeatsOwn (N.group l) p a.1 ∧ nearA (N.sent l) (N.group l) q tl.ix.ZZ = true

end

section
variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {W' : Type} {Fr : Frame} {N : Numbers} {Mg : Meaning ProofFile.InstPub W'}
  {Rd : Readers} {bN l : ℕ} {Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop}

/-- **THE FIELD `makes`, AT THE DESCRIPTION'S OWN PLACE AT LINK l.** -/
theorem k08_makes (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hP : F.planOk = true)
    (hD : namesDoorB F = true) (hW : planFitsAllB Bs.G₀.W = true) (hl : l ≤ 24) {Xl : LinkH}
    (e3 : Bs.G₀.built[l]? = some Xl)
    (hRch : ∀ k a, Rch k a → RchAt (FD Z A B c) k a)
    (H : MakesOwes N Mg Bs.G₀.W Rd bN (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar l Rch)
    (z : ProofFile.InstPub) (a b : S × Fr.E.Str)
    (ha : onQ N Mg linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) (drawAt l) a)
    (hr : Rch (drawAt l) ((z, a.1), a.2)) (hm : ¬ a.1.failed ≠ none)
    (hy : ∃ rs gs, (approximateRangeProofDrawKind (Cl := Claim) atS (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar).decide a.1 rs gs =
      .ok b.1) :
    formsInA Rd (N.sent l) (N.group l) bN "K8.equations" b.1 = true := by
  have hm' : a.1.failed = none := not_not.1 hm
  have hx : ((l, if l = 24 then 5 else 4) : ℕ × ℕ) ∈ P1K8S.places :=
    List.mem_map.2 ⟨l, List.mem_range.2 (by omega), rfl⟩
  have hr' : RchAt (FD Z A B c) (14 * l + (if l = 24 then 5 else 4) + 2) ((z, a.1), a.2) := by
    rw [← drawAt_place]
    exact hRch _ _ hr
  obtain ⟨tl, L, ht, hL, hN⟩ := P1K8S.namedB_of_reach hS hR O hP hD hx e3 ((z, a.1), a.2) hr'
  have hfr := P1K8S.k8Front_of_test hS hR O hW hx ((z, a.1), a.2) hr'
  obtain ⟨tlP, hv, h7, -⟩ := P1K8S.k8LaidOwn hS hR O hx ((z, a.1), a.2) hr'
  obtain ⟨tl₂, ht₂, hfu⟩ := P1K8S.k8FunsAreR hS hR O hx ((z, a.1), a.2) hr'
  obtain rfl : tl = tl₂ := Option.some.inj (ht.symm.trans ht₂)
  obtain ⟨F', hF⟩ := fork_of_onQ N Mg (fun s => (z, s)) l hl a ha hm'
  obtain ⟨q, hq, -, -, -⟩ := segAt_of a.1 L F' tl hL hF ht
  obtain ⟨tl₁, ht₁, -, hX, -, u, hu⟩ := cond_of_front hfr
  obtain rfl : tl = tl₁ := Option.some.inj (ht.symm.trans ht₁)
  obtain ⟨hsz, hso, hnear⟩ := H.atFold z a q tl ha hr hm' hq ht
  have e7 : seven tl = seven tlP := by
    have e := lay7_of_test h7
    unfold lay7 at e
    rw [ht] at e
    exact Option.some.inj e
  have hg : tl.gtTree.size = tl.NM := by
    have e := H.gt tlP hv
    have e1 : tl.gtTree = tlP.gtTree := congrArg (·.1) e7
    have e2 : tl.NM = tlP.NM := congrArg (·.2.2.2.2.1) e7
    rw [e1, e2]
    exact e
  have hU : tl.ix.U.getD 2 none = some u := by
    rw [Array.getD_eq_getD_getElem?, hu]
    rfl
  have hNa : Named.namedAt (ProofFile.k8ParW Z Bs.G₀ Xl l).toPar a.1 = true := by
    unfold Named.namedAt
    rw [ht, hL]
    exact hN
  obtain ⟨rs, gs, hd⟩ := hy
  exact formsInA_row (N.sent l) (N.group l) Rd bN _ a.1 b.1 rs gs (H.rd b.1) hd q tl tlP tl.funs u
    hq ht hfu (fun t e _ => by
      obtain rfl : tl = t := Option.some.inj (ht.symm.trans e)
      exact hfu) (hX tl ht).2 e7 (hsz tlP hv) hNa hso hg hU hnear

end

end P1K8T

#print axioms P1K8T.k08_makes
