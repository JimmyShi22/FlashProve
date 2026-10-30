-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Weights.lean: the law of kind K5 at the library's letters: the rows'
fourth
equation, from the weights: the kind's own weights (Att/K5LeftAll.lean: wCells, wAtIndex) read as
the
library's weight polynomials at the output's point, for the two sumchecks whose weights are made of
the
kind's own draws alone: the bits' and the score at the index.

Main names:
  `chal_size`, `nat_ini`: the typed output's point, as the library writes a point, is the reading of
    the
    part's record's challenges.
  `cells_weight`, `atIndex_weight`: the weights read as bitWt 4 and Wb … .s16 at that point.
  `cells_hW`, `atIndex_hW`: so the typed weight (the extension of the weight's values on the cube)
    at the
    output's point is the reading of the kind's weight: left3_uholds' premise hW.

Sources: Johnson/Road/Rows/AttRows58.lean (weightBits, weightScore); Cb/Pv/Att/Mean/Weights.lean
(bitWtExt,
wbExt16); BitsSc3.lean; Steps.lean; Inst/Model/Att/Sums.lean (Wb, Pub); Blocks/Basic.lean (nat,
ext);
OnBytes/Model/AttentionDivide.lean (scaled: the kind's "map (mulE · f)" is it by unfolding).
Nothing is claimed on soundness, completeness or hiding.

-/
import Cb.Pv.Att.Mean.Weights
import Cb.Pv.Att.Steps
import Cb.Pv.Att.BitsSc3
import Johnson.Road.Rows.AttRows58
import Johnson.Desc.First.Att.K5LeftAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH)
open VerifiableInference.Desc.Part

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M : Type}

theorem chal_size {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) :
    (chal hh).size = S.T.nv := by
  obtain ⟨vs, e, F, G, used, e1, sd, _⟩ := h
  obtain ⟨n, e2⟩ := hs
  rw [e1] at e2
  injection e2 with e3 e4
  subst e3 e4
  obtain ⟨_, _, hH, _⟩ := hD
  subst hH
  have hl : D.H.rs.map (·.1.length) = List.ofFn S.T.deg := by
    rw [sd.lens, List.map_map]
    exact List.map_id _
  have hlen : D.H.rs.length = S.T.nv := by
    have := congrArg List.length hl
    simpa using this
  unfold chal
  rw [sd.r, List.dropLast_concat]
  simpa using hlen

/-- The typed output's point, as the library writes a point. -/
theorem nat_ini {X : Type} (S : SumL K M X) (D : SumH ρ S) {C : Aff} {st : Stage} {riders : List E} {H : PscH}
    {hh : MaskedSum.Heard} {Gf : Fork} (hs : SizeP S st) (hD : OfP D riders H hh) (h : SumAt C st riders H hh Gf) :
    Blocks.nat (ldPartIni S.T.nv S.T.deg (pDummy K S.T.DY) D.out.pt) =
      fun j => ρ.val ((chal hh).getD j zeroE) := by
  funext j
  unfold Blocks.nat
  split
  · rename_i hj
    exact out_ini S D hs hD h ⟨j, hj⟩
  · rename_i hj
    have hsz := chal_size S D hs hD h
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by omega)]
    simp [ρ.zero]

omit [Fintype K] in
/-- K5's weights of the bits' sumcheck read as the library's weight. -/
theorem cells_weight (D : AttSeg.Dim) (p : AttSeg.Pub K) (g : Geo) (h : Heard) {b : ℕ} (hb : b < h.om''.size)
    (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg) (hpt : 2 * D.lg + 2 * D.lT + 4 ≤ h.point.size)
    (hr : D.lT + D.lg + 4 ≤ (chal h.cells).size) (ho : ρ.val (h.om''.getD b zeroE) = p.o'' b)
    (hk : ∀ k < 4, ρ.val (h.point.getD (D.lg + D.lT + k) zeroE) = p.tk k)
    (hg : ∀ k < D.lg, ρ.val (h.point.getD (D.lg + D.lT + 4 + k) zeroE) = p.tbg k)
    (hi : ∀ k < D.lT, ρ.val (h.point.getD (2 * D.lg + D.lT + 4 + k) zeroE) = p.tbi k) :
    ρ.val ((wCells g h).getD b zeroE) = bitWt 4 D p b fun j => ρ.val ((chal h.cells).getD j zeroE) := by
  unfold wCells
  rw [g1, g2]
  exact OnBytes.Road.Rows.weightBits ρ D p hb (by simp; omega) (by simp; omega) (by simp; omega) hr ho
    (fun k hk' => by
      show ρ.val ((h.point.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact hk k hk')
    (fun k hk' => by
      show ρ.val ((h.point.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact hg k hk')
    (fun k hk' => by
      show ρ.val ((h.point.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact hi k hk')

omit [Fintype K] in
/-- K5's weights of the score at the index read as the library's weight. -/
theorem atIndex_weight (D : AttSeg.Dim) (C : AttSeg.Calls) (p : AttSeg.Pub K) (g : Geo) (h : Heard) {b : ℕ}
    (hb : b < h.om.size) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg) (hpt : D.lg + D.lT ≤ h.point.size)
    (hr : D.lT + D.lg ≤ (chal h.atIndex).size) (ho : ρ.val (h.om.getD b zeroE) = p.o b)
    (hg : ∀ k < D.lg, ρ.val (h.point.getD k zeroE) = p.tg k)
    (hi : ∀ k < D.lT, ρ.val (h.point.getD (D.lg + k) zeroE) = p.ti k) :
    ρ.val ((wAtIndex g h).getD b zeroE) =
      AttSeg.Wb D C p .s16 b fun j => ρ.val ((chal h.atIndex).getD j zeroE) := by
  unfold wAtIndex
  rw [g1, g2]
  exact OnBytes.Road.Rows.weightScore ρ D C p hb (by simp; omega) (by simp; omega) hr ho
    (fun k hk' => by
      show ρ.val ((h.point.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega), Nat.zero_add]
      exact hg k hk')
    (fun k hk' => by
      show ρ.val ((h.point.extract _ _).getD k zeroE) = _
      rw [extract_getD _ _ _ _ (by omega)]
      exact hi k hk')

/-- **The bits' sumcheck: the typed weight at the output's point is the reading of K5's weight.** -/
theorem cells_hW {X J : Type} [Fintype J] (kap : ℕ) (hk4 : kap = 4) (D : AttSeg.Dim)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (D.lT + D.lg + kap) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (bitsSc3 kap D rdc inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage} {riders : List E}
    {H : PscH} {Gf : Fork} (g : Geo) (h : Heard)
    (hs : SizeP (SumL.of3 (bitsSc3 kap D rdc inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H h.cells)
    (hsum : SumAt C st riders H h.cells Gf) (hom : D.nb ≤ h.om''.size) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg)
    (hpt : 2 * D.lg + 2 * D.lT + 4 ≤ h.point.size)
    (ho : ∀ b < D.nb, ρ.val (h.om''.getD b zeroE) = Dd.st.o'' b)
    (hk : ∀ k < 4, ρ.val (h.point.getD (D.lg + D.lT + k) zeroE) = Dd.st.tk k)
    (hg : ∀ k < D.lg, ρ.val (h.point.getD (D.lg + D.lT + 4 + k) zeroE) = Dd.st.tbg k)
    (hi : ∀ k < D.lT, ρ.val (h.point.getD (2 * D.lg + D.lT + 4 + k) zeroE) = Dd.st.tbi k) (b : Fin D.nb) :
    (bitsSc3 kap D rdc inc wAt cAt).W Dd.st b
      (ldPartIni (D.lT + D.lg + kap) (fun _ => 3) (pDummy K 2) Dd.out.pt) = ρ.val ((wCells g h).getD b.1 zeroE) := by
  subst hk4
  have hsz : (chal h.cells).size = D.lT + D.lg + 4 := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  show Blocks.ext (D.lT + D.lg + 4) (fun Y => bitWt 4 D Dd.st b.1 (Blocks.cubePt (D.lT + D.lg + 4) Y))
    (Blocks.nat (ldPartIni (D.lT + D.lg + 4) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [bitWtExt, cells_weight D Dd.st g h (lt_of_lt_of_le b.2 hom) g1 g2 hpt (le_of_eq hsz.symm) (ho b.1 b.2) hk hg hi]
  exact congrArg _ hn

/-- **The score at the index: the typed weight at the output's point is the reading of K5's
weight.** -/
theorem atIndex_hW {X J : Type} [Fintype J] (D : AttSeg.Dim) (Cc : AttSeg.Calls)
    (rdc : (J → K) → AttSeg.Raw → K) (inc : AttSeg.Pub K → J → K)
    (wAt : PIdx (ldPartFmt K (AttSeg.Step.s16.g D) (fun _ => 3) ++ [pDummy K 2]) → J) (cAt : Fin D.nb × Bool → J)
    (n : ℕ) (cl : X → (Fin n → K) → K × AttSeg.Pub K) (msg : M → J → K) (Lc : X → (Fin n → K) → M → Prop)
    (Dd : SumH ρ (SumL.of3 (stepSc3 D Cc rdc .s16 inc wAt cAt) n cl msg Lc)) {C : Aff} {st : Stage}
    {riders : List E} {H : PscH} {Gf : Fork} (g : Geo) (h : Heard)
    (hs : SizeP (SumL.of3 (stepSc3 D Cc rdc .s16 inc wAt cAt) n cl msg Lc) st) (hD : OfP Dd riders H h.atIndex)
    (hsum : SumAt C st riders H h.atIndex Gf) (hom : D.nb ≤ h.om.size) (g1 : g.lt = D.lT) (g2 : g.lgk = D.lg)
    (hpt : D.lg + D.lT ≤ h.point.size) (hnv : D.lT + D.lg ≤ AttSeg.Step.s16.g D)
    (ho : ∀ b < D.nb, ρ.val (h.om.getD b zeroE) = Dd.st.o b)
    (hg : ∀ k < D.lg, ρ.val (h.point.getD k zeroE) = Dd.st.tg k)
    (hi : ∀ k < D.lT, ρ.val (h.point.getD (D.lg + k) zeroE) = Dd.st.ti k) (b : Fin D.nb) :
    (stepSc3 D Cc rdc .s16 inc wAt cAt).W Dd.st b
      (ldPartIni (AttSeg.Step.s16.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt) =
        ρ.val ((wAtIndex g h).getD b.1 zeroE) := by
  have hsz : (chal h.atIndex).size = AttSeg.Step.s16.g D := chal_size _ Dd hs hD hsum
  have hn := nat_ini _ Dd hs hD hsum
  show Blocks.ext (AttSeg.Step.s16.g D)
    (fun Y => AttSeg.Wb D Cc Dd.st .s16 b.1 (Blocks.cubePt (AttSeg.Step.s16.g D) Y))
    (Blocks.nat (ldPartIni (AttSeg.Step.s16.g D) (fun _ => 3) (pDummy K 2) Dd.out.pt)) = _
  rw [wbExt16, atIndex_weight D Cc Dd.st g h (lt_of_lt_of_le b.2 hom) g1 g2 hpt (by rw [hsz]; exact hnv)
    (ho b.1 b.2) hg hi]
  exact congrArg _ hn

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.cells_hW
#print axioms VerifiableInference.Desc.First.Att.P.atIndex_hW
#print axioms VerifiableInference.Desc.First.Att.P.nat_ini
#print axioms VerifiableInference.Desc.First.Att.P.cells_weight
#print axioms VerifiableInference.Desc.First.Att.P.atIndex_weight
