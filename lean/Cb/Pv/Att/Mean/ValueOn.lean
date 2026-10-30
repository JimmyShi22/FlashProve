-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/ValueOn.lean: the sum of step s12 of an attention segment, as a read of the
part of the library's sum over a row of scores that runs over the diagonal tile.

The library's rowSum (Inst/Model/Att/Trace.lean) has two parts: the tiles below the diagonal and the
diagonal tile of the row. This file names them (rowBelow, rowOn) and shows that the sum of step s12
(Inst/Model/Att/Sums.lean), the value product on the diagonal tiles, is the batch over the pairs of
the reads of rowOn at the lookup's point, with the function th + (the value at the lookup's point on
the channels) of the key's position.

Main definitions: rowBelow, rowOn, valG.
Main theorems: rowSum_halves, acube12, bcube12, wb12_vertex, yi_cut, sum12.

All of it is algebra on the library's definitions. Nothing is said about a verifier.


-/
import Cb.Pv.Att.Mean.RowSum
import Cb.Pv.Att.Mean.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset Blocks
open Inst.Model.AttSeg

variable {E : Type} [Field E] (D : Dim)

/-- The part of the library's rowSum that runs over the tiles below the diagonal. -/
def rowBelow (t : Raw → E) (G : ℕ → E) (b g i : ℕ) : E :=
  ∑ P ∈ range D.hP, ∑ s ∈ range (D.nBlk - 1), if D.rowBlk P s = i / D.B then
      ∑ j' ∈ range D.B, wtV t .M b (D.codeM g P s (i % D.B) j') * G (D.B * D.colBlk P s + j')
    else 0

/-- The part of the library's rowSum that runs over the diagonal tile of the row. -/
def rowOn (t : Raw → E) (G : ℕ → E) (b g i : ℕ) : E :=
  ∑ j' ∈ range D.B, wtV t .D b (D.codeD g (i / D.B) (i % D.B) j') * G (D.B * (i / D.B) + j')

/-- The library's sum over a row is the two parts. -/
theorem rowSum_halves (t : Raw → E) (G : ℕ → E) (b g i : ℕ) :
    rowSum D t G b g i = rowBelow D t G b g i + rowOn D t G b g i := rfl

variable (C : Calls) (p : Pub E) (t : Raw → E)

/-- The second factor of the value product, as a function of the key's position j: th plus the value
of the pair's layer at head g and position j, at the lookup's point on the channels. -/
def valG (b g j : ℕ) : E := p.th + conN D (yn D C p.z) fun n => valV t (D.lamOf b) g j n

section Vertex
variable (b g : ℕ) {I j' : ℕ} (hI : I < 2 ^ (D.lP + 1)) (hj : j' < 2 ^ D.lB)

include hI hj in
/-- The first map of step s12 at the vertex (g | I | j'). -/
theorem acube12 :
    Acube D C p t .s12 b ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') =
      ∑ i' ∈ range (2 ^ D.lB), eqN D.lB 0 (yi' D C p.z) i' * wtV t .D b (D.codeD g I i' j') := by
  have e1 := Dim.div_step (a := g * 2 ^ (D.lP + 1) + I) (Nat.two_pow_pos D.lB) hj
  have e2 := Dim.div_step (a := g) (Nat.two_pow_pos (D.lP + 1)) hI
  show ∑ i' ∈ range (2 ^ D.lB), eqN D.lB 0 (yi' D C p.z) i' * wtV t .D b
    (D.codeD (((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') / 2 ^ D.lB / D.nBlk)
      (((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') / 2 ^ D.lB % D.nBlk) i'
      (((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') % 2 ^ D.lB)) = _
  rw [← nBlk_pow, e1.1, e1.2, e2.1, e2.2]

include hI hj in
/-- The second map of step s12 at the vertex (g | I | j'). -/
theorem bcube12 :
    Bcube D C p t .s12 b ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') =
      valG D C p t b g (2 ^ D.lB * I + j') := by
  have e1 := Dim.div_step (a := g * 2 ^ (D.lP + 1) + I) (Nat.two_pow_pos D.lB) hj
  have e2 := Dim.div_step (a := g) (Nat.two_pow_pos (D.lP + 1)) hI
  show p.th + conN D (yn D C p.z) (fun n => valV t (D.lamOf b)
    (((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') / 2 ^ D.lB / D.nBlk)
    (2 ^ D.lB * (((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') / 2 ^ D.lB % D.nBlk) +
      ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') % 2 ^ D.lB) n) = _
  rw [← nBlk_pow, e1.1, e1.2, e2.1, e2.2]
  rfl

include hI hj in
/-- The weight of step s12 at the vertex (g | I | j'). -/
theorem wb12_vertex :
    Wb D C p .s12 b (cubePt (D.lg + (D.lP + 1) + D.lB)
        ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j')) =
      wp D C p.z .w3 b * eqN D.lg 0 (yg D C p.z) g * eqN (D.lP + 1) 0 (yI D C p.z) I := by
  show wp D C p.z .w3 b *
      eqPt D.lg (yg D C p.z) (cubePt (D.lg + (D.lP + 1) + D.lB)
        ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j')) *
      eqPt (D.lP + 1) (yI D C p.z) (sh (cubePt (D.lg + (D.lP + 1) + D.lB)
        ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j')) D.lg) = _
  rw [vertex_fst D.lg (D.lP + 1) D.lB (yg D C p.z) g hI hj,
    vertex_snd D.lg (D.lP + 1) D.lB (yI D C p.z) g hI hj]

end Vertex

/-- The lookup's point on a position, by block and place. -/
theorem yi_cut (I : ℕ) {i' : ℕ} (h : i' < 2 ^ D.lB) :
    eqN D.lT 0 (yi D C p.z) (I * 2 ^ D.lB + i') =
      eqN (D.lP + 1) 0 (yI D C p.z) I * eqN D.lB 0 (yi' D C p.z) i' := by
  have e := yi_split D C p I (i' := i') h
  rw [Nat.mul_comm] at e
  exact e

/-- **The sum of step s12 is the batch of the reads of the diagonal tile's part of rowSum.** -/
theorem sum12 :
    sumPhi D C p t .s12 =
      ∑ b ∈ range D.nb, wp D C p.z .w3 b *
        rd2 D (yg D C p.z) (eqT D (yi D C p.z)) fun g i => rowOn D t (valG D C p t b g) b g i := by
  rw [sumPhi_cube, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  show ∑ X ∈ range (2 ^ (D.lg + (D.lP + 1) + D.lB)),
    Wb D C p .s12 b (cubePt (D.lg + (D.lP + 1) + D.lB) X) * Acube D C p t .s12 b X *
      Bcube D C p t .s12 b X = _
  rw [pow_add 2 (D.lg + (D.lP + 1)) D.lB, Alg.sum_range_mul_add, pow_add 2 D.lg (D.lP + 1),
    Alg.sum_range_mul_add]
  unfold rd2 eqT
  rw [D.T_eq, mul_sum]
  refine sum_congr rfl fun g _ => ?_
  show _ = wp D C p.z .w3 b * ∑ i ∈ range (2 ^ (D.lP + 1 + D.lB)), _
  rw [pow_add 2 (D.lP + 1) D.lB, Alg.sum_range_mul_add, mul_sum]
  refine sum_congr rfl fun I hI => ?_
  have l : ∀ j' ∈ range (2 ^ D.lB),
      Wb D C p .s12 b (cubePt (D.lg + (D.lP + 1) + D.lB)
          ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j')) *
        Acube D C p t .s12 b ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') *
        Bcube D C p t .s12 b ((g * 2 ^ (D.lP + 1) + I) * 2 ^ D.lB + j') =
      ∑ i' ∈ range (2 ^ D.lB), wp D C p.z .w3 b * (eqN D.lg 0 (yg D C p.z) g *
        (eqN (D.lP + 1) 0 (yI D C p.z) I * eqN D.lB 0 (yi' D C p.z) i') *
        (wtV t .D b (D.codeD g I i' j') * valG D C p t b g (2 ^ D.lB * I + j'))) := by
    intro j' hj
    rw [wb12_vertex D C p b g (mem_range.mp hI) (mem_range.mp hj),
      acube12 D C p t b g (mem_range.mp hI) (mem_range.mp hj),
      bcube12 D C p t b g (mem_range.mp hI) (mem_range.mp hj), mul_sum, sum_mul]
    exact sum_congr rfl fun i' _ => by ring
  rw [sum_congr rfl l, sum_comm, mul_sum]
  refine sum_congr rfl fun i' hi => ?_
  have e := Dim.div_step (a := I) (Nat.two_pow_pos D.lB) (mem_range.mp hi)
  rw [yi_cut D C p I (mem_range.mp hi)]
  show _ = wp D C p.z .w3 b * (eqN D.lg 0 (yg D C p.z) g *
    (eqN (D.lP + 1) 0 (yI D C p.z) I * eqN D.lB 0 (yi' D C p.z) i') *
    ∑ j' ∈ range (2 ^ D.lB), wtV t .D b
      (D.codeD g ((I * 2 ^ D.lB + i') / 2 ^ D.lB) ((I * 2 ^ D.lB + i') % 2 ^ D.lB) j') *
      valG D C p t b g (2 ^ D.lB * ((I * 2 ^ D.lB + i') / 2 ^ D.lB) + j'))
  rw [e.1, e.2, mul_sum, mul_sum]

end Cb.Pv.Att

#print axioms Cb.Pv.Att.sum12
