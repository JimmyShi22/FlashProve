-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoOutLen.lean.
How many rows the typed lookup's out-statement has, and how many end claims the flat function has.

The third part of a lookup's out-statement is a list of rows. This file counts it: on every
transcript on which the typed verifier puts out a statement, the list has one and the same length,
a number of the lookup's public numbers alone.

Main names:
  `tieRowsR_length`, `lvRowsR_len`, `tie_len`, `tabl_len`, `r16_len`: the flat function's rows,
    counted: the tie's n + 1 steps, the key side's v' + 1 levels, the table's d levels, and four
    more.
  `all_rows_len`: for every assembly A0 and shift P: what (P.allK A0 several V₀ V₀C) puts out has
    (A0.n + 1) + (A0.v' + 1) + A0.d + 4 rows.
  `nRows h` := (FoNums.n + 1) + (FoNums.v' h + 1) + h.d + 4.
  `out_rows_len`: what Cb.Fo.forB E h L V₀ V₀C puts out has nRows h rows. No premise on h.
  `ends_rows_len`, `claims_count`: the record of end values has nRows h - 3 rows that read mask
    entries alone, and Fo.claimsOf has nRows h + 1 values.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoClaims
import OnBytes.Tie.Pv.Lookup.Forest.FoJoinOut
import OnBytes.Tie.Pv.Lookup.Forest.FoTieKit

set_option autoImplicit false

namespace Fo
open Iop IOR Cb Cb.Tw Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwV Tw3 Tw Cb.Fo

section
variable {P K : Type} [CommRing K]

theorem lvRowsR_len (led : ℕ → Led P) (g : ℕ) (inc0 : List (P × K)) : ∀ l : List (Sc K × K),
    (lvRowsR led g inc0 l).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (lvRowsR_len led g inc0 l)

theorem tieRowsR_length (N : Nums P K) (lam : K) : ∀ l : List (Sc K),
    (tieRowsR N lam l).length = l.length
  | [] => rfl
  | _ :: l => congrArg (· + 1) (tieRowsR_length N lam l)

theorem tie_len (N : Nums P K) (rs : Rounds K) : (traceOfFlat N rs).tie.length = N.n + 1 :=
  tieGo_len (N.n + 1) 0 _ _

theorem tabl_len (N : Nums P K) (rs : Rounds K) : (traceOfFlat N rs).tabl.length = N.d :=
  lvGo_len N.oT N.d 0 _ _ _

theorem r16_len (N : Nums P K) (rs : Rounds K) :
    (r16 N (traceOfFlat N rs)).length = (N.n + 1) + (N.v' + 1) + N.d + 4 := by
  unfold r16
  simp only [List.length_append, tieRowsR_length, lvRowsR_len, List.length_reverse, tie_len,
    keys_len, tabl_len, List.length_cons, List.length_nil]
  omega

end

section
variable {E St : Type} [Field E] [Fintype E] (Ex : ExtSpec) (A0 : LkAsmH E)
  (P : ShiftQ E St (A0.J → E)) (several : Bool)

theorem all_rows_len (a : St × Ex.Str) (τ : Tr (P.allK A0 several V₀ V₀C (Ex := Ex)).R.shape)
    (b : TX (St × E) E A0.J × Ex.Str)
    (hb : (P.allK A0 several V₀ V₀C (Ex := Ex)).R.red.out a τ = some b) :
    b.1.2.2.length = (A0.n + 1) + (A0.v' + 1) + A0.d + 4 := by
  rw [allK₀_out] at hb
  obtain rfl := Option.some.inj hb
  have h := (rd_read Ex (P.asmH A0) (a.1, thT Ex A0 P several τ) id
    (numsA (P.asmH A0) (a.1, thT Ex A0 P several τ)) (placesAre_self _ _)
    (reT Ex A0 P several τ)).2.1
  show ((P.asmH A0).rd _).2.2.length = _
  rw [h, List.length_map, List.length_map, r16_len]
  rfl

end

/-- The number of rows of the out-statement of the sub-proofs' lookup. -/
def nRows (h : FoNums.Sh) : ℕ := (FoNums.n + 1) + (FoNums.v' h + 1) + h.d + 4

section
variable {E : Type} [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

theorem out_rows_len (h : FoNums.Sh) (L : Lay E St₀ J₀) (Ex : ExtSpec) (a : St₀ × Ex.Str)
    (τ : Tr (forB E h L V₀ V₀C (Ex := Ex)).R.shape) (b : TX (St₀ × E) E (Option J₀) × Ex.Str)
    (hb : (forB E h L V₀ V₀C (Ex := Ex)).R.red.out a τ = some b) : b.1.2.2.length = nRows h :=
  all_rows_len Ex (forA E h L) (forP E h L) (FoNums.several h) a τ b hb

end

section
variable {K : Type} [CommRing K]

theorem ends_rows_len (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) :
    (endsOf h lm jLK rs).rows.length + 3 = nRows h := by
  unfold Ends.rows endsOf nRows
  simp only [List.length_append, List.length_reverse, tieRowsR_length, lvRowsR_len,
    List.length_cons, List.length_nil]
  have h1 := tie_len (forN h lm jLK rs) (afterShift h rs)
  have h2 := keys_len (forN h lm jLK rs) (afterShift h rs)
  have h3 := tabl_len (forN h lm jLK rs) (afterShift h rs)
  have e1 : (forTrace h lm jLK rs).tie.length = FoNums.n + 1 := h1
  have e2 : (forTrace h lm jLK rs).keys.length = FoNums.v' h + 1 := h2
  have e3 : (forTrace h lm jLK rs).tabl.length = h.d := h3
  omega

theorem claims_count (h : FoNums.Sh) (lm jLK : ℕ) (rs : Rounds K) (ν : Pl → K)
    (bit0 bit1 pin kf : ℕ → K) :
    (claimsOf h lm jLK rs ν bit0 bit1 pin kf).length = nRows h + 1 := by
  rw [claims_len, ← ends_rows_len h lm jLK rs]

end
end Fo
