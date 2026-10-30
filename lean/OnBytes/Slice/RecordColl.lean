-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/RecordColl.lean: a count of the seeds at which the record of a stored table does not
single one table out, for the programs' sample map, at every radius within the Johnson bound.
Nothing is assumed.

`DecR.coll f ρ` (OnBytes/Slice/DecoderRec.lean; the library's `LdIx.Coll`): at the seed ρ two
members of the table's list WITH DIFFERENT MESSAGE PARTS (pads counted in; two that part in the
random tails alone count as one) have the same answers. The list: the tables of polynomials whose
words are within eM columns of f. The proof is that of the library's `ldFc_binds`
(Cb/Ld/LdFoldEqCodeProofs.lean), with the entries of a message numbered as the programs number them:
a stored table has its symbols in the base field (`tab_lift`), so every member of its list has
(`ldFc_overF`), so the difference of two members has its pad entries in the base field, where the
sample map has the library's property (`recZ_okOn`, OnBytes/Slice/RecordOK.lean). The list's bound
is the library's `listMax` under `InJohnson` (`ldFc_list_johnson`); the code is the library's
Reed-Solomon code at the format's points (OnBytes/Slice/CodeFacts.lean).

Main theorems.
 `coll_count_of_list`   with any bound L on the list, eM below the distance: at most (L choose 2)
                        `err` seeds.
 `coll_count`           within the Johnson bound: L is `listMax`.
 `collRaw_count`        the same on raw strings.
 `recT_dist`, `coll_count_full`   at the sizes of OnBytes/Slice/RecordFull.lean: the distance is
                        3848273922; the radius is an argument.
 `recZ_err`             `err` as an expression: the s-th power of max (lg |E|^(lg - 1) |B|, |E|^lg),
                        where the seeds are (|E|^lg |B|)^s; B: the factors, the elements other than
                        0.

WHAT IT IS, AND IS NOT. A COUNT OF SEEDS AMONG ALL SEEDS OF THE SAMPLE MAP, FOR ONE TABLE f. NOT A
PROBABILITY: the program makes its seeds from hash blocks by trying an element of the base field at
most six times and then taking 0; as a probability over uniform blocks: OnBytes/Slice/SeedBias.lean.
NOT A BOUND FOR A COMMITTER THAT TRIES MANY ROOTS: one count for each table. That `recZ` is the
programs' sample map is a reading of their text (OnBytes/Slice/RecordRead.lean) (of the Lean port
one part is shown: the coefficients of its row of a record's answer are `recZ`'s matrix:
`coefAt_recRow`, OnBytes/Slice/BlkRecRow.lean; of the C++ programs nothing is shown); that `genOf`'s
points are the programs' is not a matter of this file. Nothing on proof of work. Nothing on which
radius a parameter file or the planner takes: no number for eM, `listMax` or `err` is evaluated. It
is laid into no join in this file: the way out "the record does not single one out" of the three
languages is bounded by nothing here. Where `coll_count` is called: `coll_pr`
(OnBytes/Slice/SeedBias.lean), as a probability over uniform blocks, and `RecFits.record`
(OnBytes/Flat/EntryRecord.lean); through `coll_pr_bytes` (OnBytes/Slice/SeedRow.lean) it stands
under `RecFits.seedLawB` there. Where the bound reaches the number of seeds it says nothing. Nothing
on any hash function.

-/
import OnBytes.Slice.RecordOK
import OnBytes.Slice.RecordFull
import OnBytes.Slice.CodeFacts

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood Blocks

variable (T : Fmt.M1.Code) (v eM lg s : ℕ)

/-- A stored table over the base field: a missing word is read as 0. -/
noncomputable def baseTab (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    (Fin v → Bool) → Fin (2 ^ T.a) → GF :=
  fun r j => toF ((f j).2.getD (Sz.rowNo r) 0)

/-- The table that the decoder reads is that table, read over the extension field. -/
theorem tab_lift (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    (decRec T v eM lg s).tab f = fun a => Code.liftWord GE (baseTab T v f a) := rfl

/-- **A COUNT OF THE SEEDS AT WHICH THE RECORD DOES NOT SINGLE ONE TABLE OUT.** For ONE stored table
f, at the programs' sample map, with L a bound on the number of tables of polynomials whose words
are within eM columns of f, and eM below the code's distance: among ALL seeds (s points of lg
coordinates, each with a factor other than 0) at most (L choose 2) `err` are such that two members
of the table's list with different message parts (pads counted in; two that part in the random tails
alone count as one) have the same answers. -/
theorem coll_count_of_list (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1) (h3 : 3 * s ≤ T.l) (hl : T.l - 3 * s ≤ 2 ^ lg)
    (f : Fin (2 ^ T.a) → Run.PQ.SgX) (L : ℕ)
    (hL : ListLE (DecodesTo (genOf T) eM ((decRec T v eM lg s).tab f)) L) :
    cnt ((decRec T v eM lg s).coll f) ≤ L.choose 2 * (recZ T.l lg s).err := by
  refine ood_cnt_clash_on GE ((Fin v → Bool) × Fin T.l) ((recZ T.l lg s).rows (Fin v → Bool))
    (fun u => ∀ a, ∀ p : Fin T.l, T.l - 3 * s ≤ p.val →
      u (a, p) ∈ Set.range (algebraMap GF GE)) _ L
    (ood_list_view GE _ _ _ _ (genOf T) eM _ _ L hL)
    (ood_okOn_rows GE (Fin T.l) (Fin v → Bool) (recZ T.l lg s) _ (recZ_okOn T.l lg s h3 hl)) ?_
  rintro u u' ⟨M, hM, rfl⟩ ⟨M', hM', rfl⟩ a p -
  change DecodesTo (genOf T) eM ((decRec T v eM lg s).tab f) M at hM
  change DecodesTo (genOf T) eM ((decRec T v eM lg s).tab f) M' at hM'
  rw [genOf_eq_GE, tab_lift] at hM hM'
  obtain ⟨M₀, -, rfl⟩ := ldFc_overF GF GE (rsCode T) eM (hasDist_rsCode T ha hk) he _
    (baseTab T v f) M hM
  obtain ⟨M₀', -, rfl⟩ := ldFc_overF GF GE (rsCode T) eM (hasDist_rsCode T ha hk) he _
    (baseTab T v f) M' hM'
  exact ⟨M₀ a (Fin.natAdd T.r p) - M₀' a (Fin.natAdd T.r p), map_sub _ _ _⟩

/-- **The same within the Johnson bound, nothing assumed**: L is the library's `listMax`. -/
theorem coll_count (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (f : Fin (2 ^ T.a) → Run.PQ.SgX) :
    cnt ((decRec T v eM lg s).coll f) ≤
      (listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err :=
  coll_count_of_list T v eM lg s ha hk he h3 hl f _ (by
    rw [genOf_eq_GE]
    exact ldFc_list_johnson GF GE (rsCode T) eM (hasDist_rsCode T ha hk) hJ _ _)

/-- **The same on raw strings** (`DecR.collRaw`, which the way out of the three languages reads):
for every raw string F. -/
theorem collRaw_count (ha : T.a ≤ 32) (hk : T.r + T.l ≤ 2 ^ T.a)
    (he : eM < 2 ^ T.a - (T.r + T.l) + 1)
    (hJ : InJohnson (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM) (h3 : 3 * s ≤ T.l)
    (hl : T.l - 3 * s ≤ 2 ^ lg) (F : Raw Run.PQ.SgX) :
    cnt ((decRec T v eM lg s).collRaw F) ≤
      (listMax (2 ^ T.a) (2 ^ T.a - (T.r + T.l) + 1) eM).choose 2 * (recZ T.l lg s).err :=
  (cnt_mono fun _ h => h.2).trans
    (coll_count T v eM lg s ha hk he hJ h3 hl fun p => (F p.val).getD (0, []))

/-! ## At the sizes of OnBytes/Slice/RecordFull.lean -/

/-- The distance of the code of a row at these sizes: 2^32 - (44040191 + 402653184) + 1. -/
theorem recT_dist : 2 ^ recT.a - (recT.r + recT.l) + 1 = 3848273922 := by decide

/-- **The count at the sizes of the parameter file with a record**; the radius eM is an argument,
within the Johnson bound. -/
theorem coll_count_full (eM : ℕ) (he : eM < 3848273922)
    (hJ : InJohnson (2 ^ 32) 3848273922 eM) (f : Fin (2 ^ recT.a) → Run.PQ.SgX) :
    cnt ((decRecFull eM).coll f) ≤
      (listMax (2 ^ 32) 3848273922 eM).choose 2 * (recZ recT.l recLg recS).err :=
  coll_count recT recV eM recLg recS (by decide) (by decide) he hJ recT_room.1 recT_room.2 f

/-- The number `err`, as an expression in the numbers of elements of the extension field and of
factors. -/
theorem recZ_err (l : ℕ) :
    (recZ l lg s).err =
      (max (lg * Fintype.card GE ^ (lg - 1) * Fintype.card NZ) (Fintype.card GE ^ lg)) ^ s := by
  show (max (Fintype.card (Fin lg) * Fintype.card GE ^ (Fintype.card (Fin lg) - 1) *
    Fintype.card NZ) (Fintype.card GE ^ Fintype.card (Fin lg))) ^ s = _
  rw [Fintype.card_fin]

end OnBytes.Slice
