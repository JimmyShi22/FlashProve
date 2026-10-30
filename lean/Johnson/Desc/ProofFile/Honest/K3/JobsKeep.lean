-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/JobsKeep.lean: the round polynomial and the end values of
Honest/K3/JobsFast.lean as functions of a kept state, and the theorems that at the kept state made
by binding challenge after challenge they are `prodRound` and `prodEnds`. Definitions with code, and
theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md. In this file: a kept state is a value of `Kept`
(Honest/K3/KeptTypes.lean); a cube is a value of `Fast.Cube` (Honest/K3/JobsFast.lean): tables on
the same bits, some of which are bound.

Why. `prodRound` binds the challenges of all rounds in front anew at every call (`bindAll`). A part
that passes a kept state on binds one challenge at each move. For that the sum must be a function of
the tables as they stand.

What is defined.
  `Kept.cube`: a kept state's free bits and tables, as a cube.
  `cubeRound`: the text of `prodRound` behind its first line: of a cube and of the number of rounds
    that are bound.
  `keptStart`: the kept state in front of the first variable's round: all bits free, nothing bound.
  `keptBind`: the kept state behind a challenge: the order's next bit is bound. Where the order has
    no further bit the tables stay and the count goes on: as `bindAll`, which drops challenges
    beyond the order's length.
  `keptRound`, `keptEnds`: the round polynomial and the end values, of a kept state.

What is shown.
  `prodRound_cube`: `prodRound` is `cubeRound` at the cube of `bindAll`: by `rfl`.
  `fold_keptBind`, `kept_made`: the kept state made of `keptStart` by `keptBind`, challenge after
    challenge, holds the cube of `bindAll` and the number of the challenges: at every list of
    challenges.
  `prodRound_made`, `prodEnds_made`: so `keptRound` and `keptEnds` at that kept state are
    `prodRound` and `prodEnds`.

Imported, through Honest/K3/JobsFast.lean: Honest/Sum.lean, Honest/Side.lean, Honest/Frame.lean and
Honest/ForKinds.lean.

Users. Honest/K3/JobsKeepKey.lean, JobsKeepTab.lean, JobsKeepLeaves.lean and JobsKeepBits.lean: the
stages of a lookup's row that have variables. There the theorems serve the hypothesis
`KeepJob.FaithfulOn` (Honest/SumKeepLaw.lean; not imported here).

Limits. On lists and arrays alone: nothing is said on what the tables hold. How long either form
takes is not said and has not been measured. As in Honest/K3/JobsFast.lean no function rejects: an
order that names a bit twice, or a bit that is not free, still halves the tables; and beyond the
order's length `keptRound` takes bit 0 in silence, as `prodRound` does: the equation holds there
too, and what it equates means nothing.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsFast
import Johnson.Desc.ProofFile.Honest.K3.KeptTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE addE subE mulE)

/-- A kept state's free bits and tables, as a cube. -/
def Kept.cube (k : Kept) : Fast.Cube := ⟨k.free, k.tabs⟩

namespace Fast

/-- The text of `prodRound` behind its first line. Here c holds the two tables with the rounds in
front bound, and n says how many rounds are bound. -/
def cubeRound (kappa : E) (m : Nat) (order : List Nat) (z : Array E) (c : Cube) (n : Nat) :
    List E :=
  let b := order.getD n 0
  let p := c.pos b
  let s := 2 ^ p
  let ta := c.tabs.getD 0 #[]
  let tb := c.tabs.getD 1 #[]
  let w := OnBytes.Model.eqTab ((c.free.filter (· != b)).reverse.map (coord m z)).toArray
  let out := (Array.range w.size).foldl
    (fun (acc : E × E × E) i =>
      let a0 := ta.getD (at0 p i) zeroE
      let a1 := subE (ta.getD (at0 p i + s) zeroE) a0
      let b0 := tb.getD (at0 p i) zeroE
      let b1 := subE (tb.getD (at0 p i + s) zeroE) b0
      let wi := w.getD i zeroE
      (addE acc.1 (mulE wi (addE kappa (mulE a0 b0))),
       addE acc.2.1 (mulE wi (addE (mulE a0 b1) (mulE a1 b0))),
       addE acc.2.2 (mulE wi (mulE a1 b1))))
    (zeroE, zeroE, zeroE)
  [out.1, out.2.1, out.2.2]

/-- `prodRound` is `cubeRound` at the cube that `bindAll` makes. -/
theorem prodRound_cube (kappa : E) (m : Nat) (order : List Nat) (z A B : Array E) (rs : List E) :
    prodRound kappa m order z A B rs =
      cubeRound kappa m order z (bindAll m order [A, B] rs) rs.length := rfl

/-- The kept state in front of the first variable's round. -/
def keptStart (m : Nat) (tabs : List (Array E)) (z : Array E) : Kept :=
  ⟨List.range m, tabs, 0, z, []⟩

/-- The kept state behind a challenge. -/
def keptBind (order : List Nat) (k : Kept) (r : E) : Kept :=
  match order[k.bound]? with
  | some b => ⟨(k.cube.bind b r).free, (k.cube.bind b r).tabs, k.bound + 1, k.z, k.vals⟩
  | none => { k with bound := k.bound + 1 }

/-- The round polynomial, of a kept state. -/
def keptRound (kappa : E) (m : Nat) (order : List Nat) (k : Kept) : List E :=
  cubeRound kappa m order k.z k.cube k.bound

/-- The tables' values, of a kept state in which all variables are bound. -/
def keptEnds (k : Kept) : List E := k.tabs.map (·.getD 0 zeroE)

/-- From a cube with n rounds bound on: `keptBind`, challenge after challenge, binds the bits of the
order from number n on. -/
theorem fold_keptBind (order : List Nat) (z : Array E) : ∀ (rs : List E) (c : Cube) (n : Nat),
    rs.foldl (keptBind order) ⟨c.free, c.tabs, n, z, []⟩ =
      ⟨(((order.drop n).zip rs).foldl (fun c x => c.bind x.1 x.2) c).free,
        (((order.drop n).zip rs).foldl (fun c x => c.bind x.1 x.2) c).tabs, n + rs.length, z, []⟩
  | [], c, n => by simp
  | r :: rs, c, n => by
    have hl : n + 1 + rs.length = n + (r :: rs).length := by
      rw [List.length_cons]
      omega
    rw [List.foldl_cons]
    cases h : order[n]? with
    | none =>
      have hn : order.length ≤ n := List.getElem?_eq_none_iff.1 h
      have hd : order.drop n = [] := List.drop_eq_nil_iff.2 hn
      have hd' : order.drop (n + 1) = [] := List.drop_eq_nil_iff.2 (by omega)
      have e : keptBind order ⟨c.free, c.tabs, n, z, []⟩ r = ⟨c.free, c.tabs, n + 1, z, []⟩ := by
        unfold keptBind
        simp only [h]
      rw [e, fold_keptBind order z rs c (n + 1), hd, hd', hl]
      rfl
    | some b =>
      have hd : order.drop n = b :: order.drop (n + 1) := by
        obtain ⟨hn, hb⟩ := List.getElem?_eq_some_iff.1 h
        rw [← hb]
        exact List.drop_eq_getElem_cons hn
      have e : keptBind order ⟨c.free, c.tabs, n, z, []⟩ r =
          ⟨(c.bind b r).free, (c.bind b r).tabs, n + 1, z, []⟩ := by
        unfold keptBind
        simp only [h]
        rfl
      rw [e, fold_keptBind order z rs (c.bind b r) (n + 1), hd, List.zip_cons_cons,
        List.foldl_cons, hl]

/-- The kept state made of `keptStart` by `keptBind` holds the cube of `bindAll` and the number of
the challenges. -/
theorem kept_made (m : Nat) (order : List Nat) (tabs : List (Array E)) (z : Array E)
    (rs : List E) :
    rs.foldl (keptBind order) (keptStart m tabs z) =
      ⟨(bindAll m order tabs rs).free, (bindAll m order tabs rs).tabs, rs.length, z, []⟩ := by
  have h := fold_keptBind order z rs ⟨List.range m, tabs⟩ 0
  rw [List.drop_zero, Nat.zero_add] at h
  exact h

/-- `keptRound` at the kept state that is made challenge after challenge is `prodRound`. -/
theorem prodRound_made (kappa : E) (m : Nat) (order : List Nat) (z A B : Array E) (rs : List E) :
    keptRound kappa m order (rs.foldl (keptBind order) (keptStart m [A, B] z)) =
      prodRound kappa m order z A B rs := by
  rw [kept_made, prodRound_cube]
  rfl

/-- `keptEnds` at that kept state is `prodEnds`. -/
theorem prodEnds_made (m : Nat) (order : List Nat) (tabs : List (Array E)) (z : Array E)
    (xs : List E) :
    keptEnds (xs.foldl (keptBind order) (keptStart m tabs z)) = prodEnds m order tabs xs := by
  rw [kept_made]
  rfl

end Fast

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.Fast.prodRound_cube
#print axioms ProofFile.Honest.K3.Fast.fold_keptBind
#print axioms ProofFile.Honest.K3.Fast.kept_made
#print axioms ProofFile.Honest.K3.Fast.prodRound_made
#print axioms ProofFile.Honest.K3.Fast.prodEnds_made
