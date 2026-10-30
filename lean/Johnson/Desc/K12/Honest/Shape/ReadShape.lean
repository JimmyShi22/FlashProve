-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/ReadShape.lean: a Boolean test on shapes, `readPubB`, and a theorem,
`readPub_sh`: where the test is true, `ReadPub` (Johnson/Desc/K12/Honest/ReadPub.lean) holds. In a
code switch of a proximity test, the reading of the old rows (`Tw.L9.readOld`,
Johnson/Top/H0/Tw/L9/Switch.lean) accepts under the hypotheses `ReadAsks` (`read_yes_trees`,
Johnson/Desc/K12/Honest/ReadWhole.lean). `ReadPub` is the half of `ReadAsks` that depends on the
statement (`Statement`), on the book (`TreeBook`, OnBytes/Iop/Ground.lean: the trees sent so far,
and each oracle message's place, which is its tree and its number among that tree's parts) and on
the single rows' own numbers (`SingleRows`, OnBytes/Iop/Fold.lean). The test reads the three through
their shapes only: `coreSh` (Johnson/Desc/Ground/Shape/Core.lean) for statement and book, `singleSh`
(Johnson/Desc/K12/Honest/Shape/Test.lean) for the single rows. So the theorem holds at every
statement, book and single rows with these shapes. The four clauses at one tree (`TreePub`) are
tested by `openG` (Johnson/Desc/Ground/Shape/More.lean). Computable definitions, two theorems and
their proofs.

  `readPub_sh`: if `readPubB (coreSh ⟨S, B0, roots⟩) (singleSh old) logN` is true, then there are
    `places` with `ReadPub S B0 old logN places (treeOf B0)`. `treeOf B0 t`
    (Johnson/Desc/K12/Honest/ReadTest.lean) is entry t of `B0.trees`, or the default tree where
    there is no such entry. S, B0, roots, old and logN are free parameters; the test does not read
    roots
  `readPubB c r logN`: a definition: the test. It is true where all of these hold: `r.masks` is 2;
    `r.keptRows` is 0; `fitsS r`; every message of `idsS r` has a place in the book's shape; the
    trees of these places hold no message outside `idsS r`; `openG` is true at each of these trees,
    with the one book's shape at both of its book arguments; every message of `idsS r` is in the
    statement's shape; `memberS c r w` for every w below the number of members; the message
    `r.fresh` has `maskRows` equal to 2 ^ `r.lay.h`. logN: the positions' range
  `idsS r`: a definition: the oracle messages asked for, read off the rows' shape: the members of
    the layout (`r.lay.members`) and then `r.fresh`. At `singleSh old` with `old.masks` = 2 that is
    the list of `singleRowsOracles old` (OnBytes/Iop/Fold.lean): shown inside the proof of
    `readPub_sh`, not as a lemma
  `fitsS r`: a definition: the test on the rows' own numbers, read off their shape: `r.gamma` (the
    number of challenges) is `r.lay.k`; `r.lay.h` ≤ `r.lay.k`; the layout's `kept`, `mainFirst` and
    `maskFirst` have as many entries as `members`. `fitsS (singleSh old)` unfolds to
    `Own.shapeFits old` (Johnson/Desc/Own/Symbols.lean)
  `memberS c r w`: a definition: the clauses on member number w of the layout: it is not kept; its
    message is in the statement's shape; its main rows pass `fitB`
    (Johnson/Desc/K12/Honest/ReadTest.lean) at the bound 2 ^ `r.lay.k` and its mask rows at
    2 ^ `r.lay.h`. `fitB` is true where there are no such rows, or where the layout gives them a
    first row and first row + number of rows ≤ the bound
  `shareOk_eq`: `shareOk S tree` (Johnson/Desc/K12/Honest/ReadTrees.lean) equals `sharesOk`
    (Johnson/Desc/Ground/Shape/More.lean) at `tree.oneList` and at the groups of the tree's sampled
    parts, that is of those that are in the statement with `shape.answers` other than 0. The two
    definitions state one test, each written separately

By what. `place_get`, `orc_get` and `tree_get` (Johnson/Desc/Ground/Shape/Core.lean) turn a lookup
in a shape into the lookup in the book or the statement. `openG_eq`
(Johnson/Desc/Ground/Shape/More.lean) turns `openG` into `openB`, which unfolds to the four fields
of `TreePub`. `fit_of` (Johnson/Desc/K12/Honest/ReadTest.lean) turns `fitB` into the fields `main`
and `mask` of `ReadPub`. `shareOk_eq` holds by `rfl`; the proof of `readPub_sh` does not call it.

Limits. Nothing says which shape a run reaches. The view's half (`ReadView`) is not treated. Only
one direction is proved here: that `ReadPub` makes the test true is not stated. The test is
evaluated at no value in this file. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.Test
import Johnson.Desc.Ground.Shape.More
import Johnson.Desc.K12.Honest.ReadPub
import Johnson.Desc.K12.Honest.ReadTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Ground.Sh
open ProofFile.Honest.K12 (ReadPub TreePub treesAt treeOf shareOk fitB fit_of)

/-- `shareOk` equals `sharesOk` at the groups of the tree's sampled parts and at `tree.oneList`. -/
theorem shareOk_eq (S : Statement) (tree : Tree) :
    shareOk S tree = sharesOk (tree.parts.toList.filterMap fun o =>
      (S.oracles[o]?).bind fun x => if x.shape.answers == 0 then none else some x.groups)
      tree.oneList := rfl

/-- The oracle messages asked for, read off the rows' shape: the members, then `r.fresh`. At
`singleSh old` that is the list of `singleRowsOracles old` only where `old.masks` is 2. -/
def idsS (r : SingleSh) : List Nat := r.lay.members.toList ++ [r.fresh]

/-- The test on the rows' own numbers (`Own.shapeFits`), read off their shape. -/
def fitsS (r : SingleSh) : Bool :=
  r.gamma == r.lay.k && decide (r.lay.h ≤ r.lay.k) && r.lay.kept.size == r.lay.members.size &&
    r.lay.mainFirst.size == r.lay.members.size && r.lay.maskFirst.size == r.lay.members.size

/-- The clauses on member number w: not kept; its message is there; its rows pass `fitB`. -/
def memberS (c : CoreSh) (r : SingleSh) (w : Nat) : Bool :=
  !r.lay.kept.getD w false &&
  match c.st.oracles[r.lay.members.getD w 0]? with
  | some x =>
    fitB (r.lay.mainFirst.getD w none) x.shape.mainRows (2 ^ r.lay.k) &&
      fitB (r.lay.maskFirst.getD w none) x.shape.maskRows (2 ^ r.lay.h)
  | none => false

/-- The test on shapes. logN: the positions' range. -/
def readPubB (c : CoreSh) (r : SingleSh) (logN : Nat) : Bool :=
  decide (r.masks = 2) && decide (r.keptRows = 0) && fitsS r &&
  match (idsS r).mapM fun o => c.book.place[o]? with
  | some places =>
    ((listOfT (places.map (·.1))).all fun t =>
      (((c.book.trees[t]?).map (·.parts)).getD []).all fun o => (idsS r).contains o) &&
    ((listOfT (places.map (·.1))).all fun t => openG c.st c.book c.book logN t) &&
    ((idsS r).all fun o => (c.st.oracles[o]?).isSome) &&
    ((List.range r.lay.members.size).all (memberS c r)) &&
    (match c.st.oracles[r.fresh]? with
      | some x => decide (x.shape.maskRows = 2 ^ r.lay.h)
      | none => false)
  | none => false

/-- **Where the test is true, `ReadPub` holds**, at some `places` and at the trees of the book. -/
theorem readPub_sh {S : Statement} {B0 : TreeBook} {roots : Nat} {old : SingleRows} {logN : Nat}
    (h : readPubB (coreSh ⟨S, B0, roots⟩) (singleSh old) logN = true) :
    ∃ places, ReadPub S B0 old logN places (treeOf B0) := by
  unfold readPubB at h
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨m1, m2⟩, m3⟩, h⟩ := h
  have hm : old.masks = 2 := of_decide_eq_true m1
  have hk : old.keptRows = 0 := of_decide_eq_true m2
  have hids : singleRowsOracles old = old.layout.members.push old.fresh := by
    unfold singleRowsOracles
    rw [hm]
    rfl
  have hidl : (singleRowsOracles old).toList = idsS (singleSh old) := by
    rw [hids, Array.toList_push]
    rfl
  have hpl : (fun o : Nat => (coreSh ⟨S, B0, roots⟩).book.place[o]?) =
      fun o : Nat => B0.place[o]? := by
    funext o
    exact place_get B0 o
  rw [hpl] at h
  cases hp : (idsS (singleSh old)).mapM fun o : Nat => B0.place[o]? with
  | none => simp [hp] at h
  | some pl =>
    simp only [hp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩ := h
    have hts : treesAt pl.toArray = listOfT (pl.map (·.1)) := by
      unfold treesAt
      simp
    have horc : ∀ o, (coreSh ⟨S, B0, roots⟩).st.oracles[o]? = (S.oracles[o]?).map orcSh :=
      fun o => orc_get S o
    have htree : ∀ t, (coreSh ⟨S, B0, roots⟩).book.trees[t]? = (B0.trees[t]?).map treeSh :=
      fun t => tree_get B0 t
    have hmem : ∀ w, w < old.layout.members.size →
        memberS (coreSh ⟨S, B0, roots⟩) (singleSh old) w = true := fun w hw =>
      List.all_eq_true.1 a4 w (List.mem_range.2 hw)
    have hget : ∀ w (hw : w < old.layout.members.size),
        old.layout.members.getD w 0 = old.layout.members[w] := fun w hw => by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hw]
      rfl
    refine ⟨pl.toArray, ?_, ?_, fun t ht => ?_, fun o ho => ?_, m3, hm, hk, fun w hw => ?_,
      fun w hw x hx => ?_, fun w hw x hx => ?_, fun x hx => ?_⟩
    · rw [Array.mapM_eq_mapM_toList, hidl, hp]
      rfl
    · rw [hts]
      refine List.all_eq_true.2 fun t ht => ?_
      have k := List.all_eq_true.1 a1 t ht
      rw [htree] at k
      cases hT : B0.trees[t]? with
      | none => simp
      | some T =>
        rw [hT] at k
        refine Array.all_eq_true_iff_forall_mem.2 fun o ho => ?_
        have k2 := List.all_eq_true.1 k o (Array.mem_toList_iff.2 ho)
        rw [← hidl] at k2
        exact Array.contains_iff_mem.2 (Array.mem_toList_iff.1 (List.contains_iff_mem.1 k2))
    · rw [hts] at ht
      have k := List.all_eq_true.1 a2 t ht
      have k' : openB S B0 B0 logN t = true := (openG_eq S B0 B0 logN t).symm.trans k
      unfold openB at k'
      cases hT : B0.trees[t]? with
      | none => simp [hT] at k'
      | some T =>
        simp only [hT, Bool.and_eq_true, decide_eq_true_eq] at k'
        have eT : treeOf B0 t = T := by
          unfold treeOf
          rw [hT]
          rfl
        rw [eT]
        exact ⟨hT, k'.1.1, k'.1.2, k'.2⟩
    · rw [hidl] at ho
      have k := List.all_eq_true.1 a3 o ho
      rw [horc] at k
      cases hx : S.oracles[o]? with
      | none => simp [hx] at k
      | some x => exact ⟨x, rfl⟩
    · have k := hmem w hw
      unfold memberS at k
      rw [Bool.and_eq_true] at k
      simpa using k.1
    · have k := hmem w hw
      unfold memberS at k
      rw [horc] at k
      have e : (singleSh old).lay.members.getD w 0 = old.layout.members[w] := hget w hw
      rw [e, hx, Bool.and_eq_true] at k
      have k2 := k.2
      simp only [Option.map_some, Bool.and_eq_true] at k2
      exact fit_of k2.1
    · have k := hmem w hw
      unfold memberS at k
      rw [horc] at k
      have e : (singleSh old).lay.members.getD w 0 = old.layout.members[w] := hget w hw
      rw [e, hx, Bool.and_eq_true] at k
      have k2 := k.2
      simp only [Option.map_some, Bool.and_eq_true] at k2
      exact fit_of k2.2
    · rw [horc] at a5
      have e : (singleSh old).fresh = old.fresh := rfl
      rw [e, hx] at a5
      exact of_decide_eq_true a5

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.shareOk_eq
#print axioms ProofFile.Honest.Sh.readPub_sh
#print axioms ProofFile.Honest.Sh.idsS
#print axioms ProofFile.Honest.Sh.fitsS
#print axioms ProofFile.Honest.Sh.memberS
#print axioms ProofFile.Honest.Sh.readPubB
