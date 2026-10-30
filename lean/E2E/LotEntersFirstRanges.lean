-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/LotEntersFirstRanges.lean: AT THE FULL SIZE: A MATRIX THAT HOLDS AN INDEX MEETS THE KEY FILE's TWO LOOKUPS'
SENTENCES: the converse of `LPFD.inRange_of_ranges` (Johnson/Top/Fire/Code/KeyHeldMeans.lean, "the key file's
lookups enforce InRange"). For the first chain's start: IN SCOPE the items inRange 0 and
inRange 1, which are open at the first chain's border 0, are these two sentences.

  `range0_of_bytes`: every entry a signed byte ⟹ the first lookup's sentence.
  `range1_of_pairs`: every two-byte weight of the library's layout in range ⟹ the second lookup's.
  **`ranges_of_inRange`**: equal readings give `same` · mat says M · `Flat.InRange M` ⟹ both sentences.
  `inRange_iff_ranges`: with the library's direction: if and only if, where `same` IS "read alike" AND mat
    SAYS M. It does not carry to the real reader: see the limits.

Why it is true. A sentence speaks of EVERY place of EVERY run of its lookup. The first lookup's runs stay
inside the matrix's rows (`RangesOK.fit₀`), and every covered place of the second reads a pair of rows of
the library's layout (`RangesOK.P1`): both are fields of `rangesOK_full` (Johnson/Top/H/KeyRangesThm.lean).

Limits. THAT mat SAYS M IS A PREMISE, AND IT IS NOT FREE AT THE REAL READER: the prover's reader of a matrix
over the extension field reads each cell's first coordinate alone (AtPublicFiles.Key.cellsReader), so its table says M
just where every cell of M lies in the base field. A matrix in range is such a one (inBase_of_inRange,
E2E/KeyPlanesAtFull.lean), so the direction from "in range" to the sentences carries to that reader; THE
CONVERSE DOES NOT: a matrix all of whose cells are (0, 1, 0) is out of range, and both sentences hold of what
that reader reads off it . The two lookups are the
written values lk0Full, lk1Full, at the reference sizes alone: that they are the plan's in scope is not said
here. The road is wfPairs_iff_inRange, not PartsIn. Nothing on padding places: a sentence does not speak of
them. No prover, no verifier, no property of a protocol.
-/
import Johnson.Top.Fire.Code.KeyHeldMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.FirstH.Lots
open OnBytes OnBytes.Slice
open OnBytes.Params (WfRun WfPart WfLookup)
open VerifiableInference.Desc.Key (keyAt InRange)
open Johnson.Pack (lk0Full lk1Full rangesOK_full covers_rows hasPl rowOf pairY extE extE_in
  wfPairs_iff_inRange p_big pairY_lt)
open Blocks.Rng (WFPairs IsByte IsPair InTab inTab_byte_iff inTab_pair_iff)
open Inst.Model.Layout (kRef hRef)
open LPFD (rdF rdF_of key0_read key1_read inRange_of_ranges)

section
variable (same : OnBytes.E → OnBytes.E → Prop) (hsame : ∀ a b, readE a = readE b → same a b)
  (m : OnBytes.Wf.Matrix) (hk : m.kCol = kRef) (mat : ℕ → ℕ → OnBytes.F)
include hsame hk

/-- **Signed bytes meet the first lookup's sentence.** -/
theorem range0_of_bytes
    (hb : ∀ y, y < hRef → ∀ c, c < 2 ^ kRef → IsByte (rdF (mat y c))) :
    InRange same m lk0Full mat := by
  intro p hp r hr t ht c hc
  rw [hk] at hc
  have hfit := rangesOK_full.fit₀ p hp r hr
  obtain ⟨hw, -⟩ := covers_rows ⟨18, hRef⟩ lk0Full rangesOK_full.cov₀
  obtain ⟨v, hv, e⟩ := (inTab_byte_iff _).2 (hb (r.firstRow + t) (by omega) c hc)
  have hd : lk0Full.d = 8 := by decide +kernel
  refine ⟨v, by rw [hd]; exact hv, hsame _ _ ?_⟩
  rw [key0_read lk0Full hw rangesOK_full.off₀, e]
  exact (rdF_of v (by omega)).symm

/-- **Two-byte weights in range meet the second lookup's sentence.** -/
theorem range1_of_pairs
    (hq : ∀ q, q < 1527800 → ∀ c, c < 2 ^ kRef →
      IsPair (rdF (mat (Inst.Model.Layout.Bridge.y0 Inst.Model.ppref kRef q) c))
        (rdF (mat (Inst.Model.Layout.Bridge.y1 Inst.Model.ppref kRef q) c))) :
    InRange same m lk1Full mat := by
  intro p hp r hr t ht c hc
  rw [hk] at hc
  obtain ⟨v, hv, hrow⟩ := rangesOK_full.P1 p hp r hr (r.firstPlace + t)
    ⟨Nat.le_add_right _ _, by omega⟩
  have hw := rangesOK_full.w₁
  have r0 : Inst.Model.Layout.Bridge.y0 Inst.Model.ppref kRef v = r.firstRow + t := by
    have := hrow 0 (by rw [hw]; decide)
    simpa [pairY, rowOf] using this
  have r1 : Inst.Model.Layout.Bridge.y1 Inst.Model.ppref kRef v = r.firstRow + t + r.stride := by
    have := hrow 1 (by rw [hw]; decide)
    simpa [pairY, rowOf] using this
  have hpair := hq v hv c hc
  obtain ⟨z₀, z₁, h₀, h₁, -, -⟩ := hpair
  obtain ⟨u, hu, e⟩ := (inTab_pair_iff Cb.Gl.p p_big ⟨z₀, h₀⟩ ⟨z₁, h₁⟩).2 (hq v hv c hc)
  have hd : lk1Full.d = 13 := by decide +kernel
  refine ⟨u, by rw [hd]; exact hu, hsame _ _ ?_⟩
  rw [key1_read lk1Full hw rangesOK_full.off₁, ← r1, ← r0, e]
  exact (rdF_of u (by omega)).symm

/-- **A MATRIX THAT HOLDS AN INDEX MEETS BOTH LOOKUPS' SENTENCES.** -/
theorem ranges_of_inRange (M : Fin hRef → Fin (2 ^ kRef) → GE)
    (hM : ∀ y c, M y c = rdF (mat y.val c.val))
    (h : VerifiableInference.OnPublicFiles.Flat.InRange M) :
    InRange same m lk0Full mat ∧ InRange same m lk1Full mat := by
  obtain ⟨hb, hp⟩ := (wfPairs_iff_inRange M).2 h
  refine ⟨range0_of_bytes same hsame m hk mat fun y hy c hc => ?_,
    range1_of_pairs same hsame m hk mat fun q hq c hc => ?_⟩
  · have e := hb y hy c hc
    rw [extE_in M y c hy hc, hM] at e
    exact e
  · obtain ⟨l0, l1⟩ := pairY_lt q hq
    have l0' : Inst.Model.Layout.Bridge.y0 Inst.Model.ppref kRef q < hRef := by
      simpa [pairY] using l0
    have l1' : Inst.Model.Layout.Bridge.y1 Inst.Model.ppref kRef q < hRef := by
      simpa [pairY] using l1
    have e := hp q hq c hc
    rw [extE_in M _ c l0' hc, extE_in M _ c l1' hc, hM, hM] at e
    exact e

end

/-- **If and only if**, at "read alike", WHERE mat SAYS M. At the prover's own reader of a matrix over the
extension field that premise holds only of matrices over the base field, and there the way back from the two
sentences to "in range" fails: this statement is not to be quoted of that reader. -/
theorem inRange_iff_ranges (m : OnBytes.Wf.Matrix) (hk : m.kCol = kRef) (mat : ℕ → ℕ → OnBytes.F)
    (M : Fin hRef → Fin (2 ^ kRef) → GE) (hM : ∀ y c, M y c = rdF (mat y.val c.val)) :
    VerifiableInference.OnPublicFiles.Flat.InRange M ↔
      InRange (fun a b => readE a = readE b) m lk0Full mat ∧
        InRange (fun a b => readE a = readE b) m lk1Full mat :=
  ⟨ranges_of_inRange _ (fun _ _ h => h) m hk mat M hM,
    fun h => inRange_of_ranges _ (fun _ _ h => h) m hk mat M hM h.1 h.2⟩

end AtPublicFiles.FirstH.Lots

#print axioms AtPublicFiles.FirstH.Lots.range0_of_bytes
#print axioms AtPublicFiles.FirstH.Lots.range1_of_pairs
#print axioms AtPublicFiles.FirstH.Lots.ranges_of_inRange
#print axioms AtPublicFiles.FirstH.Lots.inRange_iff_ranges
