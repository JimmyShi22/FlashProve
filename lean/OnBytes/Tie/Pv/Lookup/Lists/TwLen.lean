-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwLen.lean.
How many forms the read-out of the assembled lookup's last state has.

Statements and proofs, general in `A : LkAsmH E`: the read-out of every last state `o : A.XB` has
(n + 1) + (v' + 1) + (d + 3) + 1 rows (`rd_len`); with the keys' row one more (`outA_len`). At the
builder that is `nClaims` of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean, where 1 ≤ S.v (`keyA_len`); 17
at the small lookup (`o65_len`). The proof follows `ldLkpAsm2_len`
(Cb/Ld/LdLkpAsm2PullProofs.lean), with the tie's lemma written for Cb/Pv/Lookup/Blocks/TieF.lean.
Limits: a count of rows at states; it names no verifier, and it says nothing on what the rows hold.

-/
import OnBytes.Tie.Pv.Lookup.Value.TwForms
import Cb.Ld.LdLkpAsmMore

set_option autoImplicit false

namespace Cb.Tw
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Finset
open TwNums (Sizes)

section
variable {E : Type} [Field E] [Fintype E]

theorem tieF_rowsAt_len (D : TieF E) : ∀ (l : ℕ) (s : (D.lv l).T.St), (D.rowsAt l s).length = l
  | 0, _ => rfl
  | l + 1, s => congrArg (· + 1) (tieF_rowsAt_len D l s.st)

theorem rd_len (A : LkAsmH E) (o : A.XB) : (A.rd o).2.2.length = (A.n + 1) + ((A.v' + 1) + ((A.d +
    3) + 1)) := by
  show (A.rows2 (A.oR (A.o4 (A.oldT o))) ++ (A.rows4 (A.oldT o) ++ (A.rowsB o ++
      [A.numRow]))).length = _
  have h2 : (A.rows2 (A.oR (A.o4 (A.oldT o)))).length = A.n + 1 := tieF_rowsAt_len A.H.tie (A.n + 1)
      _
  have h4 : (A.rows4 (A.oldT o)).length = A.v' + 1 := (A.IK.setV (A.v' + 1)).DK.rowsAt_len E (A.v' +
      1) _
  have hB : (A.rowsB o).length = A.d + 3 :=
    (List.length_append (as := A.D.rowsAt A.d (A.outE o).st)).trans (congrArg (· + 3)
        (A.D.rowsAt_len E A.d _))
  rw [List.length_append, List.length_append, List.length_append, h2, h4, hB]
  rfl

theorem outA_len (A : LkAsmH E) (kAt : ℕ → A.J ⊕ E) (o : A.XB) :
    (outA A kAt (A.rd o)).length = (A.n + 1) + ((A.v' + 1) + ((A.d + 3) + 1)) + 1 := by
  unfold outA
  rw [outL_length, rd_len]

end

/-- at the builder that is `nClaims` of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean, where a key's number
has a bit -/
theorem keyA_len (E : Type) [Field E] [Fintype E] (S : Sizes) (hv : 1 ≤ S.v) (o : (keyA E S).XB) :
    (outA (keyA E S) (kAt E S) ((keyA E S).rd o)).length = S.nClaims := by
  rw [outA_len]
  show (S.n + 1) + ((S.v' + 1) + ((S.d + 3) + 1)) + 1 = S.scs.length + 3
  have e : S.v' + 1 = S.v := Nat.sub_add_cancel hv
  unfold Sizes.scs
  simp only [List.length_append, List.length_map, List.length_range, List.length_cons,
      List.length_nil]
  omega

/-- seventeen at the small lookup -/
theorem o65_len (o : o65A.XB) : (o65Out (o65A.rd o)).length = 17 := outA_len o65A (kAt Cb.Gl.E
    TwNums.o65S) o
/-- and that is the number of OnBytes/Tie/Pv/Lookup/Port/TwNums.lean -/
example : TwNums.o65S.nClaims = 17 := rfl

end Cb.Tw
#print axioms Cb.Tw.o65_len
