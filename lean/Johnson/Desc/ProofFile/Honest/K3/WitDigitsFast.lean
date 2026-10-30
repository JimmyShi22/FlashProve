-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/WitDigitsFast.lean: the honest side of the kind "lookup" (K3): the
structure of the lookup on the digits with the counts of a call made in one pass and kept in an
array, and the theorem that it is `lookZ`. Definitions with code, and theorems without a hypothesis.

Terms. Honest/K3/GLOSSARY.md.

Why. A bit of `lookZ` (Honest/K3/WitFill.lean) is a bit of a count (`count`,
Johnson/HonestTrace/Counts.lean): the number of the places of a call that are no padding places and
whose chosen row is the table's row. The term makes that count anew for every row and every plane,
and at every place it looks the key up in the table anew. Here the counts of all rows of a call are
made in one pass over the call's places and kept in an array. The key is `lookZ`'s own term; the bit
writes out the cast that `lookZ` has through `bzIn` (WitFill.lean).

What is defined.
  `hist`: one pass: for each row below K the number of places below N that are no padding places and
    whose row it is.
  `countsOf`, `countFast`: the arrays of all calls; the array's entry where there is one, the count
    itself elsewhere.
  `bitFast`, `planeFast`, `bzFast`, `fastLookZ`: the texts of `bit`, `plane` (Counts.lean), `bzOf`
    (Johnson/HonestTrace/CountsDigits.lean) and `lookZ` with `countFast` in the place of `count`.
  `fastAsk`: the structure of the lookup on the digits of a link, at the cells and at the entries
    that round number rng sampled.

What is shown.
  `hist_get`: **its entry at a row below K is the count's own number.**
  `countFast_eq`: **`countFast` is `count` at every argument.**
  `bzFast_eq`: `bzFast` at the arrays of `countsOf` is `bzOf`.
  `fastLookZ_eq`: **`fastLookZ tl zz = lookZ tl zz`.**
  `fastAsk_is`, `fastAsk_eq`, `fastAsk_tied`: **what `askOf` yields at a link's digits over
    `ownSources`, and over `tiedOwnSources`, is the structure of `fastLookZ`.**

Hypotheses that remain. None.

Imported. Honest/K3/WitOwner.lean. Beneath it lies Honest/K8/Digits.lean, two
of whose names this file opens.

Users. Honest/K3/LotDigitsFast.lean, Honest/K3/WitDigitsTab.lean and
Honest/K3/WitDigitsFastGuards.lean [not in this library] (the tests by evaluation) import this file.

Limits. A key is `lookZ`'s own term at every call: in `fastAsk` what its digit reads is bound once,
the digit itself is made anew. That the arrays are made once is a matter of how a program evaluates
the term: whoever calls `fastLookZ` binds its value once; no statement and no test of this file says
it.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.WitOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (Hits count hitsZ tOf cOf plane bzOf)
open ProofFile.Honest.K8 (parOfTail cellsAtOf)
open VerifiableInference.Desc.First.K8.Honest (digitAt)

/-! ## 1 The counts in one pass -/

/-- One pass over the places below N: for each row below K, how many of them are no padding places
and have that row. A row from K on is not counted. -/
def hist (N K : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) : Array ℕ :=
  (List.range N).foldl (fun a i => if pad i then a else a.modify (row i) (· + 1))
    (Array.replicate K 0)

/-- **The entry at a row below K is the number of the places below N that are no padding places and
whose row it is**; there is no entry from K on. -/
theorem hist_get (N K : ℕ) (pad : ℕ → Bool) (row : ℕ → ℕ) (t : ℕ) :
    (hist N K pad row)[t]? =
      if t < K then
        some ((Finset.range N).filter fun i => pad i = false ∧ row i = t).card
      else none := by
  induction N with
  | zero =>
    unfold hist
    simp [Array.getElem?_replicate]
  | succ n ih =>
    have step : hist (n + 1) K pad row =
        if pad n then hist n K pad row else (hist n K pad row).modify (row n) (· + 1) := by
      unfold hist
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [step, Finset.range_add_one, Finset.filter_insert]
    cases hp : pad n with
    | true => simp [ih]
    | false =>
      simp only [Bool.false_eq_true, if_false, true_and]
      rw [Array.getElem?_modify, ih]
      by_cases hr : row n = t
      · by_cases hK : t < K
        · simp [hr, hK, Finset.card_insert_of_notMem]
        · simp [hr, hK]
      · simp [hr]

/-- The counts of all rows of all calls. -/
def countsOf (h : OnBytes.Model.Forest.Shape) (H : Hits) : Array (Array ℕ) :=
  (Array.range h.NC).map fun c => hist (2 ^ FoNums.nOf h c) (2 ^ h.kT) (H.pad c) (H.row c)

/-- The array's entry where there is one; the count itself elsewhere. -/
def countFast (h : OnBytes.Model.Forest.Shape) (H : Hits) (A : Array (Array ℕ)) (c t : ℕ) : ℕ :=
  match (A[c]?).bind (·[t]?) with
  | some v => v
  | none => count h H c t

/-- **At the arrays of countsOf, countFast is count at every argument.** -/
theorem countFast_eq (h : OnBytes.Model.Forest.Shape) (H : Hits) (c t : ℕ) :
    countFast h H (countsOf h H) c t = count h H c t := by
  unfold countFast countsOf
  by_cases hc : c < h.NC
  · by_cases ht : t < 2 ^ h.kT
    · simp [hc, hist_get, ht, count]
    · simp [hc, hist_get, ht]
  · simp [hc]

/-! ## 2 lookZ's text with countFast in count's place -/

/-- Johnson/HonestTrace/Counts.lean's bit. -/
def bitFast (h : OnBytes.Model.Forest.Shape) (H : Hits) (A : Array (Array ℕ)) (t c j : ℕ) : Bool :=
  decide (c < h.NC) && decide (j < 32) && (countFast h H A c t).testBit j

/-- That file's plane. -/
def planeFast (h : OnBytes.Model.Forest.Shape) (lm : ℕ) (H : Hits) (A : Array (Array ℕ))
    (r col : ℕ) : ℕ :=
  if r < 2 ^ lm ∧ bitFast h H A (tOf h lm r col) (cOf h lm col) (r % 32) = true then 1 else 0

/-- Johnson/HonestTrace/CountsDigits.lean's bzOf, at given padding places, rows and arrays. -/
def bzFast (tl : HTailF2) (H : Hits) (A : Array (Array ℕ)) (row col : ℕ) : ℕ :=
  planeFast tl.f9 5 H A ((row * tl.bzColumns + col) % 32)
    ((row * tl.bzColumns + col) / 32 % 2 ^ tl.f9.cK * 2 ^ tl.f9.kT +
      (row * tl.bzColumns + col) / 32 / 2 ^ tl.f9.cK)

theorem bzFast_eq (tl : HTailF2) (zz : ℕ → ℕ → Cb.Gl.E) (row col : ℕ) :
    bzFast tl (hitsZ tl zz) (countsOf tl.f9 (hitsZ tl zz)) row col = bzOf tl zz row col := by
  unfold bzFast bzOf planeFast plane bitFast OnBytes.HonestTrace.bit
  simp only [countFast_eq]

/-- **The digits of a smallness test, the counts of a call made in one pass.** -/
def fastLookZ (tl : HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) : LookIn :=
  let H := hitsZ tl (inExt zz)
  let A := countsOf tl.f9 H
  ⟨(lookZ tl zz).key,
   fun u j => ((bzFast tl H A ((OnBytes.DgP.portQ tl).bAt u j).2.1
     ((OnBytes.DgP.portQ tl).bAt u j).2.2 : ℕ) : Cb.Gl.E)⟩

/-- **It is lookZ.** -/
theorem fastLookZ_eq (tl : HTailF2) (zz : ℕ → ℕ → Cb.Gl.F) : fastLookZ tl zz = lookZ tl zz := by
  show (⟨(lookZ tl zz).key, fun u j =>
    ((bzFast tl (hitsZ tl (inExt zz)) (countsOf tl.f9 (hitsZ tl (inExt zz)))
      ((OnBytes.DgP.portQ tl).bAt u j).2.1 ((OnBytes.DgP.portQ tl).bAt u j).2.2 : ℕ) :
      Cb.Gl.E)⟩ : LookIn) = _
  simp only [bzFast_eq]
  rfl

/-! ## 3 At the seated filling -/

/-- The structure of the lookup on the digits of a link, at the cells and at the entries that round
number rng sampled, the counts of a call made in one pass. The array ZZ, the function that
`fastLookZ` is handed here, is zzOwn's own term (Honest/K8/Digits.lean: zzOf) with its three
arguments that do not depend on the place bound in front: the numbers of the smallness test, the
reader of the cells, and the sampled entries as an array, which zzOf makes of the list anew at every
entry. -/
def fastAsk (X : OnBytes.Model.Verify.Public) (link rng : ℕ) (C : Cells)
    (heard : List Fmt.Drawn) : Hidden :=
  let tl := tlOf X link
  let P := parOfTail tl
  let R := cellsAtOf C (matsOwn X link)
  let A := (tritsAt heard rng).toArray
  (fastLookZ tl fun u col => ((digitAt P R A u col : ℕ) : Cb.Gl.F)).hidden

/-- It is fastLookZ's structure at zzOwn. -/
theorem fastAsk_is (X : OnBytes.Model.Verify.Public) (link rng : ℕ) (C : Cells)
    (heard : List Fmt.Drawn) :
    fastAsk X link rng C heard =
      (fastLookZ (tlOf X link) (zzOwn X link C (tritsAt heard rng))).hidden := rfl

/-- **What askOf yields at a link's digits over ownSources is that structure.** -/
theorem fastAsk_eq {W₀ Rc Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (pubH : Xi → OnBytes.Ends.H.PubH) (link rng : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) :
    askOf (ownSources X cells weights pubH) (.digits link rng) t heard =
      fastAsk X link rng (cells t.trace) heard := by
  rw [fastAsk_is, fastLookZ_eq]
  rfl

/-- **The same over tiedOwnSources, the filling that is seated.** -/
theorem fastAsk_tied {W₀ Rc Xi Tr' : Type} (X : OnBytes.Model.Verify.Public) (cells : Tr' → Cells)
    (weights : W₀ → Weights) (req : Xi → OnBytes.Model.Head.Covered × Array ℕ) (link rng : ℕ)
    (t : Local W₀ Rc Xi Tr') (heard : List Fmt.Drawn) :
    askOf (tiedOwnSources X cells weights req) (.digits link rng) t heard =
      fastAsk X link rng (cells t.trace) heard :=
  fastAsk_eq X cells weights (fun x => headPub X (req x).1 (req x).2) link rng t heard

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.hist_get
#print axioms ProofFile.Honest.K3.countFast_eq
#print axioms ProofFile.Honest.K3.bzFast_eq
#print axioms ProofFile.Honest.K3.fastLookZ_eq
#print axioms ProofFile.Honest.K3.fastAsk_is
#print axioms ProofFile.Honest.K3.fastAsk_eq
#print axioms ProofFile.Honest.K3.fastAsk_tied
