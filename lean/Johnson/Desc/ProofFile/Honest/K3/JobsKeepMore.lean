-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeepMore.lean: three small things that the two stages over a
lookup's whole table side need beside Honest/K3/JobsKeep.lean: binding treats its tables one by one;
the count in a kept state; and the bits' table, off a store or made anew. Definitions with code, one
definition of a hypothesis, and theorems; one theorem is conditional on `BitOk`.

Terms. Honest/K3/GLOSSARY.md. In this file: a cube is a value of `Fast.Cube`
(Honest/K3/JobsFast.lean); a store is a value of `Store`, a kept state a value of `Kept`
(Honest/K3/KeptTypes.lean).

Why. The bits' stage sums over two tables, the bits and the bits less 1, and its end value is the
first table's alone: Honest/K3/JobsFast.lean binds the first table alone for it. A kept state holds
both. So it must be known that the first tables of a list, bound alone, are the first of the list
bound together.

What is defined.
  `bitOff`: the bits' table: off the store where one is passed on, made anew where none is. It takes
    the input as a function of the challenges heard (`Ask`) and applies it only where no store is
    passed on: an application may be costly.
  `BitOk`: the hypothesis: where a store is passed on, its bits' table is the one that
    Honest/K3/JobsFast.lean makes. Where none is passed on it holds.

What is shown.
  `Fast.fold_bind_take`, `Fast.bindAll_take`: bound at the same bits and challenges, the first n
    tables of a list are the first n of the list's tables, and the free bits are the same.
  `Fast.prodEnds_take`: so the end values of the first n tables are the first n end values.
  `Fast.bound_made`: the kept state made of `keptStart` by `keptBind` counts the challenges.
  `bitOk_none`: at no store `BitOk` holds.
  `bitOff_ok`: under `BitOk` the table that `bitOff` returns is the one that
    Honest/K3/JobsFast.lean makes.

Hypotheses that remain.
  `hOk`, in `bitOff_ok` alone: `BitOk R row a w h x`. No store at which it holds is exhibited in
    this file; at `none` it holds.

Imported. Honest/K3/JobsKeepKey.lean, and through it Honest/SumKeep.lean, Honest/Sum.lean,
Honest/Side.lean, Honest/Frame.lean and Honest/ForKinds.lean.

Users. Honest/K3/JobsKeepLeaves.lean, Honest/K3/JobsKeepBits.lean.

Limits. The first four theorems are on lists and arrays alone: nothing is said on what the tables
hold; n may be larger than the list is long, and then both sides are the whole. Nothing is said on
who makes a store, nor that `BitOk` stays true as more is heard.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)

namespace Fast

/-- Bound at the same bits and challenges, the first n tables of a cube are the first n of the
cube's tables; the free bits are the same. -/
theorem fold_bind_take (n : Nat) : ∀ (l : List (Nat × E)) (c : Cube),
    l.foldl (fun (c : Cube) x => c.bind x.1 x.2) (⟨c.free, c.tabs.take n⟩ : Cube) =
      (⟨(l.foldl (fun (c : Cube) x => c.bind x.1 x.2) c).free,
        (l.foldl (fun (c : Cube) x => c.bind x.1 x.2) c).tabs.take n⟩ : Cube)
  | [], _ => rfl
  | x :: l, c => by
    have e : Cube.bind ⟨c.free, c.tabs.take n⟩ x.1 x.2 =
        ⟨(c.bind x.1 x.2).free, (c.bind x.1 x.2).tabs.take n⟩ := by
      show (⟨c.free.filter (· != x.1), (c.tabs.take n).map (bindAt (c.pos x.1) x.2)⟩ : Cube) =
        ⟨c.free.filter (· != x.1), (c.tabs.map (bindAt (c.pos x.1) x.2)).take n⟩
      rw [List.map_take]
    have ih := fold_bind_take n l (c.bind x.1 x.2)
    show l.foldl (fun (c : Cube) x => c.bind x.1 x.2)
        (Cube.bind ⟨c.free, c.tabs.take n⟩ x.1 x.2) =
      (⟨(l.foldl (fun (c : Cube) x => c.bind x.1 x.2) (c.bind x.1 x.2)).free,
        (l.foldl (fun (c : Cube) x => c.bind x.1 x.2) (c.bind x.1 x.2)).tabs.take n⟩ : Cube)
    rw [e]
    exact ih

/-- The same of `bindAll`. -/
theorem bindAll_take (m : Nat) (order : List Nat) (tabs : List (Array E)) (n : Nat)
    (xs : List E) :
    bindAll m order (tabs.take n) xs =
      ⟨(bindAll m order tabs xs).free, (bindAll m order tabs xs).tabs.take n⟩ :=
  fold_bind_take n (order.zip xs) ⟨List.range m, tabs⟩

/-- The end values of the first n tables are the first n end values. -/
theorem prodEnds_take (m : Nat) (order : List Nat) (tabs : List (Array E)) (n : Nat)
    (xs : List E) :
    prodEnds m order (tabs.take n) xs = (prodEnds m order tabs xs).take n := by
  show (bindAll m order (tabs.take n) xs).tabs.map (·.getD 0 zeroE) =
    ((bindAll m order tabs xs).tabs.map (·.getD 0 zeroE)).take n
  rw [bindAll_take]
  show ((bindAll m order tabs xs).tabs.take n).map (·.getD 0 zeroE) =
    ((bindAll m order tabs xs).tabs.map (·.getD 0 zeroE)).take n
  rw [List.map_take]

/-- The kept state made of `keptStart` by `keptBind` counts the challenges. -/
theorem bound_made (m : Nat) (order : List Nat) (tabs : List (Array E)) (z : Array E)
    (rs : List E) :
    (rs.foldl (keptBind order) (keptStart m tabs z)).bound = rs.length := by
  rw [kept_made]

end Fast

/-- The bits' table, by the leaf's number: off the store where one is passed on, made anew where
none is. The input is asked for in the second case alone. -/
def bitOff (f : LFace) (row : E → Nat → E) (w : Ask) (p : Pts) : Option Store → Array E
  | some st => st.bitTab
  | none => (Fast.srcOf f row (w p.heard) p.theta p.alpha).bitTab ()

/-- The hypothesis: where a store is passed on, its bits' table is the one that
Honest/K3/JobsFast.lean makes of the input, the shift and alpha. A definition, meant as a
hypothesis. -/
def BitOk (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st → st.bitTab =
    (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
      (R.pts a.face a.base h).alpha).bitTab ()

/-- Where no store is passed on `BitOk` holds. -/
theorem bitOk_none (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn) :
    BitOk R row a w h none :=
  fun _ e => nomatch e

/-- Under `BitOk` the table that `bitOff` returns is the one that Honest/K3/JobsFast.lean makes.
Conditional on `BitOk`. -/
theorem bitOff_ok (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) (hOk : BitOk R row a w h x) :
    bitOff a.face row w (R.pts a.face a.base h) x =
      (Fast.srcOf a.face row (w (R.pts a.face a.base h).heard) (R.pts a.face a.base h).theta
        (R.pts a.face a.base h).alpha).bitTab () := by
  cases x with
  | none => rfl
  | some st => exact hOk st rfl

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.Fast.fold_bind_take
#print axioms ProofFile.Honest.K3.Fast.bindAll_take
#print axioms ProofFile.Honest.K3.Fast.prodEnds_take
#print axioms ProofFile.Honest.K3.Fast.bound_made
#print axioms ProofFile.Honest.K3.bitOk_none
#print axioms ProofFile.Honest.K3.bitOff_ok
