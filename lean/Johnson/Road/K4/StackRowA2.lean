-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowA2.lean: the first side of the library's summand of the batched sumcheck, on
values of its end values, is the element of the field As that the verifier's stackEnd returns on its
own placed list of panels.

Johnson/Road/K4/StackRowA.lean (as_typed) asks, of every pair of the placed list and the library's
list, the panel's fields (EndFields) and that the verifier's weights of the panel's place and rows
are the library's (GeoA). Here GeoA is paid for every pair, with the tools of
Johnson/Road/K4/StackRowB3.lean, and stackEnd_four (Johnson/Road/FormsKeysEnd.lean) is
laid on.

Main names:
  `placed_geoA`: EndFields and GeoA of every pair.
  `as_placed`: the first side's sum reads as s'.As.
Limits. PREMISES: EndFields and the bits of every pair; that stackEnd has returned on the placed
list with as many rounds as the library's sumcheck has variables; that there are as many challenges;
that the typed point reads as the challenges turned round; StackTies; that the weight of claim 0
reads 1; NE = nx; that the values by name are the readings of the shown value and of the never-sent
vectors' values that stackEnd was given. An identity: nothing on a run, on soundness or on hiding.


-/
import Johnson.Road.K4.StackRowA
import Johnson.Road.K4.StackRowB3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World)
open OnBytes.Model.Layer (SBlk Lay StackEnd stackEnd placePanels)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (InnPar0 kS cntA IA IB)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {ρ : Reading K} {P : InnPar0 K} {st : P.St}
  {y : Lay} {sh om rs H1 V : Array E} {z zh : ℕ → K} {bl : Array SBlk} {shA shB : E}
  {s' : StackEnd}

/-- **EndFields and GeoA of every pair of the placed list and the library's list.** -/
theorem placed_geoA
    (FE : List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn) (placePanels bl).1.toList
      (pans P.D))
    (FW : List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.w = pn.wid P.D ∧ b.wy = pn.wcol P.D)
      (placePanels bl).1.toList (pans P.D))
    (hst : stackEnd y (placePanels bl).1 rs (kS P.D) om H1 V shA shB = some s')
    (hl : kS P.D ≤ rs.size) (zp : Fin (kS P.D) → K)
    (hz : ∀ j, j < kS P.D → Blocks.nat zp j = zR ρ rs (kS P.D) j) :
    List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn ∧
      GeoA ρ rs (kS P.D) P.D (Blocks.nat zp) b pn) (placePanels bl).1.toList (pans P.D) := by
  have FO := placed_off P.D bl (FW.imp fun _ _ k => k.1)
  refine (f2_mem_right (f2_mem_left (f2_and (f2_and FE FW) FO))).imp fun b pn k => ?_
  obtain ⟨hp, hm, ⟨En, bw, bwy⟩, off⟩ := k
  obtain ⟨s1, s2, hs⟩ := stackEnd_each hst b hm
  exact ⟨En, geoA_of bw bwy (by rw [off, bw]; rfl) (stackEndOf_ok hs) hl zp hz hp⟩

/-- **The first side's sum reads as the verifier's As.** -/
theorem as_placed (T : StackTies P st ρ y sh om z zh) (hom : ρ.val (om.getD 0 zeroE) = 1)
    (hNE : y.h.NE = P.D.nx)
    (FE : List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn) (placePanels bl).1.toList
      (pans P.D))
    (FW : List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.w = pn.wid P.D ∧ b.wy = pn.wcol P.D)
      (placePanels bl).1.toList (pans P.D))
    (hst : stackEnd y (placePanels bl).1 rs (kS P.D) om H1 V shA shB = some s')
    (hl : kS P.D ≤ rs.size) (zp : Fin (kS P.D) → K)
    (hz : ∀ j, j < kS P.D → Blocks.nat zp j = zR ρ rs (kS P.D) j) (W : World K)
    (v : IA P.D ⊕ IB P.D → K) (ha0 : v (.inl (.inl ())) = ρ.val shA)
    (hv : ∀ i : (Σ p : {p : Pan // p ∈ pans P.D}, Fin (cntA p.1)),
      v (.inl (.inr i)) = valsOf ρ H1 ((virtOf i.1.1).getD 0)) :
    ∑ i : IA P.D, P.sideA.side.c i st zp * v (.inl i) = ρ.val s'.As :=
  (as_typed (W := W) T hom hNE (valsOf ρ H1) (valsOf ρ V) (ρ.val shA)
    (placed_geoA FE FW hst hl zp hz) v ha0 hv).trans
    (stackEnd_four (ρ := ρ) (W := W) (valsOf ρ H1) (valsOf ρ V) hst).2.2.1.symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.placed_geoA
#print axioms OnBytes.Road.K4.as_placed
