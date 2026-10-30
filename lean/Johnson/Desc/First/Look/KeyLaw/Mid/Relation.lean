-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean: how a stand of the course over the field is read
as a state of the described lookup, seam by seam; and what follows for the whole lookup if each
stretch keeps that reading.

Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean has the course (our text of the program's lookup,
over the field; that the program's run, read in the field, is this course is shown, under conditions
on public data, in files that are not in this library yet): claims with mask forms as lists of (mask
entry, coefficient), rows with terms on the table of bits. Cb/Pv/KeyLookup/Letters.lean has the
description's state: claims and rows as functions on a type of entries.
Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean joins eight statements on stretches for any relation.
This file fixes the relation.

Main names:
  `rdS`, `rdRow`, `rdCl`: a claim on a value, a row, and a claim on a part's leaves alpha - key (as
  a claim on the keys), read; `sl` says where a mask entry stands among the entries.
  `ownAt`, `idxAt`: how many mask entries of either message are taken up to a seam.
  `Sim`: the relation at seam k = 1 .. 8: the state handed on; alpha; the rows; the entries taken;
  and the claims that a later stretch reads: at seam 1 the claim on all roots' product; up to seam 2
  the planes' claims; at seams 2 and 3 the roots' claims; at seams 3 to 5 the table side's claim and
  its point; from seam 4 on the parts' claims; at seam 7 the zero point.
  `course_lamRun`: if the eight stretches keep `Sim` and the row on the number of keys reads as the
  description's, then on every flat list whose first rounds fit, the description's plain function
  puts out on these rounds: the state; for each part the course's claim on its leaves, read; the
  course's rows, read. The course leaves the rounds behind them.

Limits. That the stretches keep `Sim` is a premise (`Sims`,
Johnson/Desc/First/Look/KeyLaw/Mid/Seams.lean). Nothing on the program's blocks: both sides of the
statements are texts of ours.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.Seams
import Cb.Pv.KeyLookup.LamRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid
open Lk6.PortSim

open OnBytes OnBytes.Slice Flat Finset Cb.LdLkp

variable (A : Dat GE) (sl : Slot → A.J)

/-- A claim on a value, read. -/
def rdS (c : PscF.PointClaim) : SCl GE A.J := ⟨rdMF sl c.masks, c.value⟩

/-- The mask entries of the first message that are taken up to seam k. -/
def ownAt (S : Pub) : ℕ → ℕ
  | 0 => 0
  | 1 => 7 + 6 * (S.pl - 2)
  | 2 => ownAt S 1 + 5 * (S.m - 1)
  | 3 => ownAt S 2
  | 4 => ownAt S 3 + (S.parts.map fun v => ((List.range v).map fun l => 2 * l + 5).sum - 2).sum
  | 5 => ownAt S 4 + ((List.range S.d).map fun l => 2 * (S.mu + l) + 5).sum
  | 6 => ownAt S 5 + (1 + S.mu + 2 * S.d)
  | 7 => ownAt S 6
  | _ + 8 => ownAt S 7 + (1 + 2 * (S.mu + S.d) + 2 + 1)

/-- The mask entries of the second message that are taken up to seam k. -/
def idxAt (S : Pub) (k : ℕ) : ℕ := if k < 4 then 0 else 2 * S.m

/-- **The relation at seam k.** st: the caller's state; own, idx: the mask entries taken before the
lookup. -/
structure Sim (st : A.St) (own idx k : ℕ) (s : Cs) (x : A.XS) : Prop where
  st : x.st = st
  al : x.al = s.alpha
  rows : x.rows = s.rows.map (rdRow A sl)
  own : s.own = own + ownAt A.toPub k
  idx : s.idx = idx + idxAt A.toPub k
  all : k = 1 → x.all = rdS A sl s.rest
  planes : k ≤ 2 → ∀ j < A.pl, x.planes j = rdS A sl (s.planes j)
  roots : 2 ≤ k → k ≤ 3 → ∀ i < A.m, x.roots i = rdS A sl (s.roots i)
  top : 3 ≤ k → k ≤ 5 → x.top = rdS A sl s.top ∧
    s.top.point.length = A.mu + (if k = 5 then A.d else 0) ∧
    ∀ t < s.top.point.length, x.pt t = s.top.point.getD t 0
  cls : 4 ≤ k → ∀ i < A.m, x.cls i = rdCl A sl s.alpha (A.v i) (s.leaves i)
  zt : k = 7 → s.zt.length = A.mu + A.d ∧ ∀ t < A.mu + A.d, x.zt t = s.zt.getD t 0

/-- **The whole lookup.** -/
theorem course_lamRun (P : Pl A) (D : Dt) (st : A.St) (own idx : ℕ)
    (h : Sims A (A.runD P) D (Sim A sl st own idx) st own idx)
    (hc : A.numRow = rdRow A sl (cntRowF D)) (f : List (RV GE))
    (hf : fitsAll (A.runD P).fm (f.take (A.runD P).fm.length) = true) :
    A.lamRun P st (f.take (A.runD P).fm.length) =
      ((st, fun i : Fin A.m =>
          rdCl A sl (course D f own idx).alpha (A.v i) ((course D f own idx).leaves i),
        (course D f own idx).rows.map (rdRow A sl)) : A.Out) ∧
      (course D f own idx).rounds = f.drop (A.runD P).fm.length := by
  obtain ⟨hs, hr⟩ := chn_sim A (A.runD P) D _ st own idx h f hf
  refine ⟨?_, hr⟩
  generalize f.take (A.runD P).fm.length = g at hs
  show ((((A.runD P).chn st g).st, fun i : Fin A.m => ((A.runD P).chn st g).cls i,
    ((A.runD P).chn st g).rows ++ [A.numRow]) : A.Out) = _
  refine Prod.ext hs.st (Prod.ext ?_ ?_)
  · funext i
    exact hs.cls (by omega) i i.isLt
  · show ((A.runD P).chn st g).rows ++ [A.numRow] =
      ((chnC D f own idx).rows ++ [cntRowF D]).map (rdRow A sl)
    rw [List.map_append, hs.rows, hc]
    rfl

end Lk6.Mid

#print axioms Lk6.Mid.course_lamRun
