-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerNoData.lean: IN THE LEDGER's ROW f :: PT :: MM THE PIECES NUMBER 3 AND 6
("(rec_gamma)", "joins") HAVE NO WRITTEN ROUND: two premises of tiesJoin
(Johnson/Desc/K14/Law/LedgerTiesJoin.lean), had from three binders of ledger_whole_at_sh
(Johnson/Desc/K14/Law/LedgerAtSh.lean): hbl, ht, hps.
HOW. The piece holds b3.retype | b6.retype in the wrap (piece_retype_at); it is owed as many rounds
as its block declares and nothing is put behind it (the tiling); these blocks declare none
(rounds_counts).
What is not claimed. Nothing on the front piece's rounds. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerFormsAll
import Johnson.Desc.Sound.PointSeated

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Cb Johnson.Pack Desc.Plain
open Iop Run OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Block Strs Wit FileDescription)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared

variable {P₁ Cl Cells Tok : Type} {Fr : Frame} (Q : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
  (hbl : blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
  (base : Nat) (d : RDT)
  (ext : (P₁ × St) × Fr.E.Str → Tr (uLT (ckP .two) [d]) → Wit Cells Tok MsgT → Wit Cells Tok MsgT)
  (err : Err (uLT (ckP .two) [d]))
  (f x3 x6 x8 x9 x10 x11 : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (base2 : ℕ) (d21 d22 : RDT)
  (ex2 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d21, d22]) → Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er2 : Err (uLT (ckP .two) [d21, d22])) (base4 : ℕ) (d4 : RDT)
  (ex4 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d4]) → Wit Cells Tok MsgT → Wit Cells Tok
    MsgT)
  (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 d52 : RDT)
  (ex5 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d51, d52]) → Wit Cells Tok MsgT → Wit Cells
    Tok MsgT)
  (er5 : Err (uLT (ckP .two) [d51, d52])) (base7 : ℕ) (d7 : RDT)
  (ex7 : (P₁ × St) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d7]) → Wit Cells Tok MsgT → Wit Cells Tok
    MsgT)
  (er7 : Err (uLT (ckP .two) [d7]))
  (ht : Tiled (pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2) [x3, (pc1 (b4.retype (Cl' := Cl))
    base4 d4 ex4 er4), (pc2 (b5.retype (Cl' := Cl)) base5 d51 d52 ex5 er5), x6, (pc1 (b7.retype (Cl'
      := Cl)) base7 d7 ex7 er7), x8, x9, x10, x11])
  (ch : Model.Verify.Chains) (tests : List (Block St Unit))
  (last : List (Block St Unit) → Block St Unit)
  (hps : (f :: (seatedPiece (W := Wit Cells Tok MsgT) (Cl' := Cl) (F := Fr) (P₁ := P₁) b1 base d ext
    err) :: [(pc2 (b2.retype (Cl' := Cl)) base2 d21 d22 ex2 er2), x3, (pc1 (b4.retype (Cl' := Cl))
      base4 d4 ex4 er4), (pc2 (b5.retype (Cl' := Cl)) base5 d51 d52 ex5 er5), x6, (pc1 (b7.retype
        (Cl' := Cl)) base7 d7 ex7 er7), x8, x9, x10, x11]).map (·.b) =
    (((chainOf ch Q tests last).retype (Cl' := Cl)).blocksInOrder.map below).map
      (Block.lift Prod.snd fun t s => (t.1, s)))
include hbl ht hps
/-- The piece of "(rec_gamma)" has no written round. -/
theorem x3_no_data : x3.ds = [] := by
  obtain ⟨q, e, h⟩ := piece_retype_at _ ch Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl hps 2 b3 rfl
  obtain rfl : x3 = q := Option.some.inj e
  have hcn := rounds_counts Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcn
  obtain ⟨-, -, c3, -⟩ := hcn
  obtain ⟨-, -, -, -, o3, -, k3, -⟩ := ht
  have h' := o3.1
  rw [k3, h] at h'
  have h'' : x3.ds.length + 0 = b3.rounds.length := h'
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- The piece of "joins" has no written round. -/
theorem x6_no_data : x6.ds = [] := by
  obtain ⟨q, e, h⟩ := piece_retype_at _ ch Q b1 b2 b3 b4 b5 b6 b7 b8 tests last hbl hps 5 b6 rfl
  obtain rfl : x6 = q := Option.some.inj e
  have hcn := rounds_counts Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hcn
  obtain ⟨-, -, -, -, -, c6, -⟩ := hcn
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, o6, -, k6, -⟩ := ht
  have h' := o6.1
  rw [k6, h] at h'
  have h'' : x6.ds.length + 0 = b6.rounds.length := h'
  exact List.eq_nil_of_length_eq_zero (by omega)

end Desc.K14.Law

#print axioms Desc.K14.Law.x3_no_data
#print axioms Desc.K14.Law.x6_no_data
