-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/AtTypedData.lean: the data of a course over the field, read off
the description's own data; at them the conditions of
Johnson/Desc/First/Look/KeyLaw/Mid/AtStdPlaces.lean are met under the public record's admissibility
alone.

Johnson/Desc/First/Look/KeyLaw/Mid/AtStdPlaces.lean shows that the course over the field, read, is
the plain function that the described lookup's verifier puts out, under `StdC`: the course has the
description's public record, public factor and table. Here a course's data get a value at which
these three hold by definition.

  `dtOf A st ms ix` the public record of A; the two numberings ms, ix of the ledgers' entries; the
    public factor `A.fac st`; the table's extension: the multilinear extension of `A.tab st` at the
    first d coordinates of a list (0 where the list ends).
  `stdC_of` `A.toPub.Adm p` ⇒ `StdC A (dtOf A st ms ix) st p`.
  `course_of` so under `A.toPub.Adm p` alone, on every flat list whose first rounds fit: `A.lamRun
    (plAt A sl (dtOf A st ms ix) own idx)` on these rounds is the course's claims and rows, read.
What this moves, and does not shut: that the PROGRAM's factor and table, read into the field, are
`A.fac st` and the extension of `A.tab st` is then a condition on how the program's run is read, not
on this course. The course over the field is our text of the program's lookup, over the field; that
the program's run, read in the field, is this course is not shown in this file.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.AtStdPlaces

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim
open OnBytes OnBytes.Slice Flat Lev Cb Cb.LdLkp

variable (A : Dat GE) (st : A.St) (ms ix : ℕ → Slot)

/-- The data of a course, read off the description's. -/
noncomputable def dtOf : Dt where
  S := A.toPub
  ms := ms
  ix := ix
  fac := A.fac st
  tabAt := fun l =>
    Alg.mle (fun r : Fin A.d → Bool => A.tab st (numLE r)) fun t : Fin A.d => l.getD t.val 0

theorem stdC_of {p : ℕ} (h : A.toPub.Adm p) : StdC A (dtOf A st ms ix) st p where
  pub := rfl
  adm := h
  fac := fun _ => rfl
  tab := fun q => by
    show Alg.mle _ (fun t : Fin A.d => (List.ofFn q).getD t.val 0) = _
    congr 1
    funext t
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact t.isLt), List.getElem_ofFn]

variable {A st ms ix}

theorem course_of (sl : Slot → A.J) (own idx : ℕ) {p : ℕ} (h : A.toPub.Adm p) (f : List (RV GE))
    (hf : fitsAll (A.runD (plAt A sl (dtOf A st ms ix) own idx)).fm
      (f.take (A.runD (plAt A sl (dtOf A st ms ix) own idx)).fm.length) = true) :
    A.lamRun (plAt A sl (dtOf A st ms ix) own idx) st
        (f.take (A.runD (plAt A sl (dtOf A st ms ix) own idx)).fm.length) =
      ((st, fun i : Fin A.m =>
          rdCl A sl (course (dtOf A st ms ix) f own idx).alpha (A.v i)
            ((course (dtOf A st ms ix) f own idx).leaves i),
        (course (dtOf A st ms ix) f own idx).rows.map (rdRow A sl)) : A.Out) ∧
      (course (dtOf A st ms ix) f own idx).rounds =
        f.drop (A.runD (plAt A sl (dtOf A st ms ix) own idx)).fm.length :=
  course_std own idx (stdC_of A st ms ix h) f hf

end Lk6.Mid

#print axioms Lk6.Mid.stdC_of
#print axioms Lk6.Mid.course_of
