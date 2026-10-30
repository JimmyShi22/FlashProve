-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/ZeroRows.lean: a row of zeros in the word is a row of zeros in every witness,
at every radius below the stage's distance. Statements and proofs.

Why: a group's tables have 2 ^ k rows; its members fill fewer (18 of 32 at one place of the example
proofs). A structured vector's coefficient is not 0 on the other rows, so what a group's row says of
tables hangs on what stands there. The relation before a fold (`Sg.RIn`, OnBytes/Slice/Stage.lean)
speaks of a witness's message, which fills all rows. This file shows that the code makes it 0 where
the word is 0: the tables before the fold are interleaved, row by row under one code; a witness
within e positions of the word is, row by row, within e positions of the word's row; and a code word
that is not 0 at fewer positions than the distance is the encoding of 0.
Main names:
  `zero_of_few`: of any code of the library's kind with the distance d (`LdCode.Dist`): fewer than d
    positions other than 0 give that message and tail are 0.
  `zero_row_main`, `zero_row_mask`: from `s.Sized`, e < s.d, the witness's encoding within e
    positions of y, and y's symbols of the row i being 0 at every position: the witness's message
    and tail are 0 in the row i.
It holds at every radius below the distance: so also at the Johnson radii, and of every member of
the list of witnesses.
Limits: it is not said that y has rows of zeros where no member has a row: that belongs to the
reading (how the group's word is made of the members' trees). The bridge to `Padded`, `Laid` and
`tablesOf` (Johnson/Desc/Means/Says.lean) is Johnson/Desc/K12/Law/TabWords.lean. No soundness is
claimed, and nothing is said on hiding.
Lemmas of `verify-on-bytes`'s library that are called (none runs in a context of that program):
`Sg.fit_cM`, `Sg.fit_cZ` (OnBytes/Slice/Numbers.lean) with `Fit.dist`; `cnt_mono` (Prob/Cnt.lean).
No sorry, no axiom of ours; each theorem has its premises; what the main ones rest on is printed at
the file's end.

-/
import Johnson.Desc.K12.Law.RInSays
import OnBytes.Slice.Numbers

set_option autoImplicit false
namespace H2K.ClaimSays
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open OnBytes.Means

/-- A code word (the encoding of a message and a tail) that is not 0 at fewer positions than the
distance is the encoding of 0 and 0. -/
theorem zero_of_few {P : Type} [Fintype P] (C : LdCode GE P) (d e : ℕ) (hd : C.Dist d) (he : e < d)
    (m : C.J → GE) (r : C.Q → GE) (h : cnt (fun x => C.T (C.enc m r) x ≠ 0) ≤ e) : m = 0 ∧ r = 0 :=
        by
  by_contra hn
  exact absurd (le_trans (hd m r hn) h) (by omega)

/-- A main row of zeros. Where the word y has the symbol 0 at every position of the main row i,
every witness whose encoding is within e < d positions of y has the message 0 and the tail 0 in that
row. -/
theorem zero_row_main (s : Sg) (hs : s.Sized) (e : ℕ) (he : e < s.d) (y : s.cIn.Word)
    (w : s.cIn.N.Wit) (hw : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e)
    (i : Fin (s.h + s.g) → Bool) (h0 : ∀ x : s.Ps, s.cIn.T y x (.inl (i, ())) = 0) :
    (∀ j, w.1 (.inl (i, j)) = 0) ∧ ∀ q, w.2 (.inl (i, q)) = 0 := by
  have hcnt : cnt (fun x : s.Ps => s.cM.T (s.cM.enc (fun j => w.1 (.inl (i, j))) (fun q => w.2
      (.inl (i, q)))) x ≠ 0) ≤ e := by
    refine le_trans (cnt_mono ?_) hw
    intro x hx hxy
    apply hx
    funext α
    have h1 := congrFun hxy (Sum.inl (i, α))
    rw [show s.cIn.ext.rd y x (Sum.inl (i, α)) = 0 from h0 x] at h1
    exact h1.symm
  have hz := zero_of_few s.cM s.d e (Sg.fit_cM hs).dist he _ _ hcnt
  exact ⟨fun j => congrFun hz.1 j, fun q => congrFun hz.2 q⟩

/-- A mask row of zeros: the like. -/
theorem zero_row_mask (s : Sg) (hs : s.Sized) (e : ℕ) (he : e < s.d) (y : s.cIn.Word)
    (w : s.cIn.N.Wit) (hw : offCnt (Ex := s.cIn.ext) y (s.cIn.N.enc w.1 w.2) ≤ e)
    (i : Fin s.h → Bool) (h0 : ∀ x : s.Ps, s.cIn.T y x (.inr (i, ())) = 0) :
    (∀ j, w.1 (.inr (i, j)) = 0) ∧ ∀ q, w.2 (.inr (i, q)) = 0 := by
  have hcnt : cnt (fun x : s.Ps => s.cZ.T (s.cZ.enc (fun j => w.1 (.inr (i, j))) (fun q => w.2
      (.inr (i, q)))) x ≠ 0) ≤ e := by
    refine le_trans (cnt_mono ?_) hw
    intro x hx hxy
    apply hx
    funext α
    have h1 := congrFun hxy (Sum.inr (i, α))
    rw [show s.cIn.ext.rd y x (Sum.inr (i, α)) = 0 from h0 x] at h1
    exact h1.symm
  have hz := zero_of_few s.cZ s.d e (Sg.fit_cZ hs).dist he _ _ hcnt
  exact ⟨fun j => congrFun hz.1 j, fun q => congrFun hz.2 q⟩

end H2K.ClaimSays

#print axioms H2K.ClaimSays.zero_row_main
#print axioms H2K.ClaimSays.zero_row_mask
