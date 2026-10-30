-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowD4.lean: the summand of the library's typed batched sumcheck at its end
values is the product As · Bs that the verifier computes at the end of its batched sumcheck, read.

The verifier closes the batched sumcheck with the claim "the last claimed value is As · Bs"
(`stackEnd`, OnBytes/Model/LayerPanels.lean). The library's ledger has the sumcheck's own row, in
which the summand stands as a polynomial in the end values. To carry the one claim to the other, the
two numbers must be one: the premise (D4) of stgT_rowUp (Johnson/Road/K4/OwnRows.lean).

  `d4_inn`: P.inn.Sm.pol st zp v = ρ.val (mulE s'.As s'.Bs).
It joins: inn_pol (StackRowSums.lean: the summand is a product of two sums) · as_placed
(StackRowA2.lean: the first sum is As, read) · bs_of_fields over placed_bfields (StackRowB2.lean,
StackRowB3.lean: the second is BsAt) · stackEnd_four (Johnson/Road/FormsKeysEnd.lean: As
and Bs read as AsAt and BsAt at the values that stackEnd was given).
Limits. Premises: StackTies; EndFields and the bits of every pair of the placed list and the
library's list; stackEnd's return; that the typed point reads as the challenges turned round; that
the end values by name are the shown values by number: the A side's, the never-sent vectors' by
virtOf, the B side's, and the weight claims' by v0Of, a letter of which it is asked that it gives
the verifier's number of each weight panel's first claim (placed_v0, Johnson/Road/K4/WalkV0.lean,
shows that of the running sums v0Of D of Johnson/Road/K4/NumPieces.lean). Identities on public
numbers and given values: nothing on a world, on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StackRowA2
import Johnson.Road.K4.StackRowB3
import Johnson.Road.K4.StackRowSums

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading World)
open OnBytes.Model.Layer (SBlk Lay StackEnd stackEnd placePanels)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (IA IB cntA cntB InnPar0 kS)

variable {K : Type} [Field K] [Fintype K] [scl : Scl] {ρ : Reading K} {P : InnPar0 K} {st : P.St}

/-- **(D4) of the batched sumcheck.** -/
theorem d4_inn {y : Lay} {sh om : Array E} {z zh : ℕ → K} (T : StackTies P st ρ y sh om z zh)
    (hom : ρ.val (om.getD 0 zeroE) = 1) (hNE : y.h.NE = P.D.nx) {bl : Array SBlk}
    (FE : List.Forall₂ (fun b pn => EndFields ρ y sh P.D z b pn) (placePanels bl).1.toList
      (pans P.D))
    (FW : List.Forall₂ (fun (b : SBlk) (pn : Pan) => b.w = pn.wid P.D ∧ b.wy = pn.wcol P.D)
      (placePanels bl).1.toList (pans P.D))
    {rs H1 V : Array E} {shA shB : E} {s' : StackEnd}
    (hst : stackEnd y (placePanels bl).1 rs (kS P.D) om H1 V shA shB = some s')
    (hl : kS P.D ≤ rs.size) (zp : Fin (kS P.D) → K)
    (hz : ∀ j, j < kS P.D → Blocks.nat zp j = zR ρ rs (kS P.D) j) (v0Of : Pan → ℕ)
    (F0 : List.Forall₂ (fun (b : SBlk) (pn : Pan) => pn.weight = true → b.v0 = some (v0Of pn))
      (placePanels bl).1.toList (pans P.D))
    (v : IA P.D ⊕ IB P.D → K) (ha0 : v (.inl (.inl ())) = ρ.val shA)
    (hvA : ∀ i : (Σ p : {p : Pan // p ∈ pans P.D}, Fin (cntA p.1)),
      v (.inl (.inr i)) = valsOf ρ H1 ((virtOf i.1.1).getD 0))
    (hb0 : v (.inr (.inl ())) = ρ.val shB)
    (hvB : ∀ (p : {p : Pan // p ∈ pans P.D}) (i : Fin (cntB P.D p.1)),
      v (.inr (.inr ⟨p, i⟩)) = valsOf ρ V (v0Of p.1 + i)) (W : World K) :
    P.inn.Sm.pol st zp v = ρ.val (mulE s'.As s'.Bs) :=
  have A : ∑ i : IA P.D, P.sideA.side.c i st zp * v (.inl i) = ρ.val s'.As :=
    as_placed T hom hNE FE FW hst hl zp hz W v ha0 hvA
  have F2B : List.Forall₂ (fun b pn => BFields P st ρ rs (kS P.D) b pn (v0Of pn))
      (placePanels bl).1.toList (pans P.D) :=
    placed_bfields (P := P) (st := st) (ρ := ρ) (y := y) (sh := sh) (z := z) (bl := bl) FE FW T.z0
      (rs := rs) (om := om) (H1 := H1) (V := V) (lam := kS P.D) (shA := shA) (shB := shB)
      (s' := s') hst v0Of F0
  have B0 : ∑ j : IB P.D, P.sideB.side.c j st zp * v (.inr j) =
      BsAt ρ W y rs (kS P.D) om (valsOf ρ H1) (valsOf ρ V) (v (.inr (.inl ())))
        (placePanels bl).1.toList :=
    bs_of_fields v0Of F2B hl rfl zp hz W y om (valsOf ρ H1) (valsOf ρ V) (fun j => v (.inr j)) hvB
  have B : ∑ j : IB P.D, P.sideB.side.c j st zp * v (.inr j) = ρ.val s'.Bs :=
    (B0.trans (by rw [hb0])).trans
      (stackEnd_four (ρ := ρ) (W := W) (valsOf ρ H1) (valsOf ρ V) hst).2.2.2.symm
  calc P.inn.Sm.pol st zp v
      = (∑ i : IA P.D, P.sideA.side.c i st zp * v (.inl i)) *
          ∑ j : IB P.D, P.sideB.side.c j st zp * v (.inr j) := inn_pol P.par st zp v
    _ = ρ.val s'.As * ρ.val s'.Bs := by rw [A, B]
    _ = ρ.val (mulE s'.As s'.Bs) := (ρ.mul _ _).symm

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.d4_inn
