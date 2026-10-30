-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/AllStretches.lean: the course over the field (our text of the
program's lookup, over the field; that the program's run, read in the field, is this course is
shown, under conditions on public data, in files that are not in this library yet), read, IS the
plain function that the described lookup's verifier puts out: whole, under conditions on public
numbers, on the public factor and the table, and on where the mask entries stand.

Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean shows it under the premise that each of the eight
stretches keeps the reading `Sim` (`Sims`). Each stretch's statement is proved in a file of its own:
the head (Johnson/Desc/First/Look/KeyLaw/Mid/TieSims.lean), the parts' steps (PartsSim.lean), the
join point and the zero point (CloseGoes.lean), the key trees (LevSimF.lean), the table's tree
(LevSimE.lean), the closing (CloseGoesC.lean), the bits (CloseGoesD.lean). This file gathers their
conditions in one record and joins them.

Main names:
  `Std A sl P D st own idx`: the conditions. Numbers: the course has the description's public
  record; 2 <= pl <= 2^mu; 1 <= d; a part or more, each of two keys or more. The course's public
  factor and table are the description's. Places: each name of a mask entry in the description's
  records of places is `sl` of the entry that the course's two enumerations give at that count; the
  orders of the levels' rounds are the description's.
  `sims_of_std`: `Std` gives `Sims`.
  `course_is_lamRun`: under `Std`, on every flat list whose first rounds fit: `A.lamRun P` on these
  rounds = (the state; for each part the course's claim on its leaves, read as a claim on the keys;
  the course's rows, read), and the course leaves the rounds behind them.

Limits. That records of places with `Std` exist is not shown here. Nothing on the program's blocks:
the course is a text of ours over the field (Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean), so the
statement is an equation between two things of our own, and no step from the program.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.CountRow
import Johnson.Desc.First.Look.KeyLaw.Mid.TieSims
import Johnson.Desc.First.Look.KeyLaw.Mid.PartsSim
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoesC
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoesD
import Johnson.Desc.First.Look.KeyLaw.Mid.LevSimF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

open OnBytes OnBytes.Slice Flat Lev Cb Cb.LdLkp

variable (A : Dat GE) (sl : Slot → A.J)

/-- **The conditions.** -/
structure Std (P : Pl A) (D : Dt) (st : A.St) (own idx : ℕ) : Prop where
  pub : D.S = A.toPub
  pl2 : 2 ≤ A.pl
  plLe : A.pl ≤ 2 ^ A.mu
  d1 : 1 ≤ A.d
  m1 : 1 ≤ A.m
  v1 : ∀ i < A.m, 1 ≤ A.v i
  fac : ∀ al, D.fac al = A.fac st al
  tab : ∀ p : Fin A.d → GE,
    D.tabAt (List.ofFn p) = Alg.mle (fun r : Fin A.d → Bool => A.tab st (numLE r)) p
  tie : TieSim.Places A sl P.tie D own
  parts : PlacesAt A sl D P.wP P.cP (own + ownAt A.toPub 1)
  keys : ∀ i < A.m, ∀ l < A.v i, PlAt sl D (partD (A.part P.lev i)) (decide (l + 1 = A.v i)) l
    (own + ownAt A.toPub 3 + ownP A i + ownN 0 l) (idx + idxAt A.toPub 3 + 2 * i)
  table : ∀ l < A.d, PlAt sl D (A.tabD P.lev) false l (own + ownAt A.toPub 4 + ownN A.mu l)
    (idx + idxAt A.toPub 4)
  wE : ∀ i, P.cl.wE i = sl (D.ms (own + ownAt A.toPub 5 + Cf.portIdx _ i))
  wB : ∀ i, P.cl.wB i =
    sl (D.ms (own + ownAt A.toPub 7 + Cf.portIdx (Lev.lk GE (A.mu + A.d)) i))
  cB : P.cl.cB = sl (D.ms (own + ownAt A.toPub 7 + (1 + 2 * (A.mu + A.d) + 2)))

variable {A sl}

/-- **Each of the eight stretches keeps the reading.** -/
theorem sims_of_std {P : Pl A} {D : Dt} {st : A.St} {own idx : ℕ} (h : Std A sl P D st own idx) :
    Sims A (A.runD P) D (Sim A sl st own idx) st own idx where
  head := TieSim.head_field P st idx (by rw [h.pub]) h.pl2 h.fac h.tie
  parts := parts_goes A sl D P.wP P.cP st own idx h.pub h.parts
  join := Clo.join_goes A sl st own idx D h.pub
  keys := keys_goes A sl P.lev D st own idx h.pub h.m1 h.v1 h.keys
  table := table_goes A sl P.lev D st own idx h.pub h.d1 h.table
  clo := Clo.clo_goes A sl st own idx P.cl D h.pub (by have := h.d1; omega) h.plLe h.tab h.wE
  zero := Clo.zero_goes A sl st own idx D h.pub
  bits := Clo.bits_goes A sl st own idx P.cl D h.pub h.plLe h.wB h.cB

/-- **The course over the field, read, is the described verifier's plain function.** -/
theorem course_is_lamRun {P : Pl A} {D : Dt} {st : A.St} {own idx : ℕ}
    (h : Std A sl P D st own idx) (f : List (RV GE))
    (hf : fitsAll (A.runD P).fm (f.take (A.runD P).fm.length) = true) :
    A.lamRun P st (f.take (A.runD P).fm.length) =
      ((st, fun i : Fin A.m =>
          rdCl A sl (course D f own idx).alpha (A.v i) ((course D f own idx).leaves i),
        (course D f own idx).rows.map (rdRow A sl)) : A.Out) ∧
      (course D f own idx).rounds = f.drop (A.runD P).fm.length :=
  course_lamRun A sl P D st own idx (sims_of_std h) (numRow_eq A sl D h.pub h.plLe) f hf

end Lk6.Mid

#print axioms Lk6.Mid.sims_of_std
#print axioms Lk6.Mid.course_is_lamRun
