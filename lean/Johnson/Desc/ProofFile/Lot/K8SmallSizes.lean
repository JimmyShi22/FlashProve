-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/K8SmallSizes.lean: the named test on sizes of the approximate range
proof's single equations (`K9.smallSizesB`, Johnson/Desc/First/Batch/SmallSizesPlan.lean), asked of
the list of rounds at every segment of the proof file's first chain. Definitions with code, and
theorems with their proofs.

Main names. Z: what hangs on the public files. G: the built segments, the first chain's parameters
and the public files' values.
  `planVals W`: the planned values of the approximate range proof's part of the verifier's state:
    one for each group of layers, one for each attention segment, the output head's.
  `ownVal G X`: the one of them that belongs to the built segment X, by its sort and group.
  `smallSizesAtB Z G X l tlP`: the named test at the built segment X, number l: at X's list of
    arrays, the first chain's layout, the planned value tlP and the numbers of the place l.
  `smallSizesOwnB Z G`: that test at every built segment X, at X's own plan of the part (`X.tl`).
  `smallSizes_of_own`: its yes gives the named test at each built segment.
  `smallSizesB_seven`: the named test reads of the planned value seven fields alone (`Ready.seven`,
    Johnson/Desc/First/K8/Cond.lean): two values with the same seven have one answer.
  `smallSizes_at_state`: so, from a yes of `smallSizesOwnB`: the named test at an open segment's
    context L and a value tlP, where L's list of arrays is X's, L's layout is the first chain's, and
    tlP's seven fields are those of `X.tl`.
  `sevenB`: "the same seven fields", as a test with code. `smallSizesPlanB`, `smallSizesAllB`: the
    named test at every built segment, at `ownVal`; at every planned value. For sheets: no theorem
    ends in them. THE LAST IS FALSE AT THE STORED FULL-SIZE PARAMETER FILES (by evaluation): a
    segment's arrays fit its own planned value, not those of another sort of segment.

Limits. The three premises of `smallSizes_at_state` on the open segment's context are shown at no
state that the verifier reaches. `smallSizesOwnB` is a test on the list of rounds: its yes is had by
evaluation. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.SmallSizesPlan
import Johnson.Desc.ProofFile.Lot.K8

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference.Desc

/-- The planned values: the groups of layers', the attention segments', the output head's. -/
def planVals (W : Verify.Public) : List HTailF2 :=
  W.G.toList.map (·.tl) ++ W.A.toList.map (·.seam.tl) ++ [W.H.tl]

/-- The planned value that belongs to a built segment, by its sort and group. -/
def ownVal (G : Ground) (X : LinkH) : Option HTailF2 :=
  if X.kind == 2 then some G.W.H.tl
  else if X.kind == 1 then (G.W.A[X.g]?).map (·.seam.tl)
  else (G.W.G[X.g]?).map (·.tl)

/-- The named test on sizes at a built segment and a planned value. -/
def smallSizesAtB (Z : Pub) (G : Ground) (X : LinkH) (l : Nat) (tlP : HTailF2) : Bool :=
  K9.smallSizesB X.arrayOf G.first.layout tlP (k8ParW Z G X l).toPar

/-- **At every built segment, at its own plan of the part.** -/
def smallSizesOwnB (Z : Pub) (G : Ground) : Bool :=
  G.built.toList.zipIdx.all fun x => smallSizesAtB Z G x.1 x.2 x.1.tl

/-- At every built segment, at the planned value that belongs to it by its sort and group. -/
def smallSizesPlanB (Z : Pub) (G : Ground) : Bool :=
  G.built.toList.zipIdx.all fun x => (ownVal G x.1).any fun tlP => smallSizesAtB Z G x.1 x.2 tlP

/-- The same seven fields, as a test with code. -/
def sevenB (a b : HTailF2) : Bool :=
  decide (a.gtTree = b.gtTree) && decide (a.ix = b.ix) && decide (a.mz = b.mz) &&
    decide (a.off = b.off) && decide (a.NM = b.NM) && decide (a.shp = b.shp) &&
    decide (a.mats = b.mats)

/-- At every built segment, at every planned value. -/
def smallSizesAllB (Z : Pub) (G : Ground) : Bool :=
  G.built.toList.zipIdx.all fun x => (planVals G.W).all fun tlP => smallSizesAtB Z G x.1 x.2 tlP

/-- A yes of the test gives the equation. -/
theorem seven_of_test {a b : HTailF2} (h : sevenB a b = true) :
    First.K8.Ready.seven a = First.K8.Ready.seven b := by
  simp only [sevenB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  simp only [First.K8.Ready.seven, h1, h2, h3, h4, h5, h6, h7]

/-- **A yes of the test on the list of rounds gives the named test at each built segment.** -/
theorem smallSizes_of_own (Z : Pub) (G : Ground) (h : smallSizesOwnB Z G = true) (l : ℕ)
    (Xl : LinkH) (hX : G.built[l]? = some Xl) :
    K9.smallSizesB Xl.arrayOf G.first.layout Xl.tl (k8ParW Z G Xl l).toPar = true := by
  have hm : (Xl, l) ∈ G.built.toList.zipIdx := by
    rw [List.mk_mem_zipIdx_iff_getElem?, Array.getElem?_toList]
    exact hX
  exact List.all_eq_true.1 h (Xl, l) hm

/-- **The named test reads seven fields of the planned value alone.** -/
theorem smallSizesB_seven (arrayOf : Array (Nat × String)) (layout : Params.ReqLayout)
    (tlP tlP' : HTailF2) (p : First.K8.Par)
    (h7 : First.K8.Ready.seven tlP = First.K8.Ready.seven tlP') :
    K9.smallSizesB arrayOf layout tlP p = K9.smallSizesB arrayOf layout tlP' p :=
  K9.smallFits_seven _ { tlP with tau := p.tau } { tlP' with tau := p.tau } _ h7 rfl

/-- **The named test at an open segment's context**, from the test on the list of rounds and three
equations on the context and the value. -/
theorem smallSizes_at_state (Z : Pub) (G : Ground) (h : smallSizesOwnB Z G = true) (l : ℕ)
    (Xl : LinkH) (hX : G.built[l]? = some Xl) (L : LinkCtx) (tlP : HTailF2)
    (e1 : L.arrayOf = Xl.arrayOf) (e2 : L.check.rows.layout = G.first.layout)
    (h7 : First.K8.Ready.seven tlP = First.K8.Ready.seven Xl.tl) :
    K9.smallSizesB L.arrayOf L.check.rows.layout tlP (k8ParW Z G Xl l).toPar = true := by
  rw [e1, e2, smallSizesB_seven _ _ tlP Xl.tl _ h7]
  exact smallSizes_of_own Z G h l Xl hX

end ProofFile

#print axioms ProofFile.seven_of_test
#print axioms ProofFile.smallSizes_of_own
#print axioms ProofFile.smallSizesB_seven
#print axioms ProofFile.smallSizes_at_state
