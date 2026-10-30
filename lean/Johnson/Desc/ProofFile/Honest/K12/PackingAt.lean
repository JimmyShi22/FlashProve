-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PackingAt.lean: the two packings of a fold's fresh mask table are
one, at two parts' own texts. The proximity test's part lays a fold's fresh table as `packedN` of
the coefficients `hideAt k c` (Johnson/Desc/ProofFile/Honest/K12/Coins.lean); a sending's part lays
a table that rides in its message, a `K1.Ride` ⟨k, h⟩, by `K1.Ride.lay`
(Johnson/Desc/ProofFile/Honest/K1/Coins.lean). Off the same coins, in the same order, `packedN` and
that laying are equal entry by entry; and so is the table that the sending's part lays (`rowsR`)
where such a table rides, inside the message's mask table. Both equations have the hypothesis that
the stage has room for the packing. Five theorems, no definition. General in the stage and in c;
`packing_sent` also in the sending's parameters, its riding tables and its data. `same_one`
(SameAtOne.lean in this folder) calls `packing_sent`.

In the list: a part (`Part`, in the frame, Johnson/Desc/ProofFile/Honest/Frame.lean) is the prover's
side of a stretch of a sub-protocol's rounds; a text is the body of a Lean definition. The two
texts: `TestJob.first` (Test.lean in this folder), at the first fold's table, which the test's parts
reach through `testAll` (Parts.lean, Test.lean); and the field `mask` of `rowsR` (K1/Coins.lean),
which `SendJob.rows` calls (Johnson/Desc/ProofFile/Honest/K1/Part.lean). A stage s (`Sg`,
OnBytes/Slice/Stage.lean) has the numbers h and g and the code `Z` of a mask row; `s.Z.l` is the
number of entries of that code's messages. `packedN s W r j` (Johnson/Prover/Link/BodyPack.lean) is
the library's packing of the coefficients W at row number r and place j. A `K1.Ride` R has two
numbers, k and h; `R.lay c r j` is the word at place j of the row
`Fmt.M1.FoldOwn.freshRow .two R.k R.h (hideOfCoins R.k c) r` (Fmt/M1Fold.lean), read in the field
`GE`; 0 past the row's end. W is indexed by the library's names: `hIx` for a variable and an
exponent, `hCst` for the constant (Cb/Ld/LdSumPack.lean). `byName k w w0` (K12/Coins.lean) is such a
W, made of a function w of two numbers and a value w0; `hideAt k c` is `byName` at values of c, in
the order that the head of K12/Coins.lean gives for a fresh table. In `packing_at` c is any function
from numbers to the extension field `GE`; in `packing_sent` c has the type `Cs` (the frame) at the
sending's count `K1.dueR P ride`, and `K1.ce c i` is its value number i in `GE`, 0 beyond the count.
A sending has the parameters P (`K1.Par`, Johnson/Desc/K1/Send.lean); `shapeAt P k`
(Johnson/Prover/Send/Core.lean) is the shape of its message number k; `ride k` is the table that
rides in that message, or none. `(K1.rowsR P ride data c k).mask r j` is the entry at row number r
and place j of that message's mask table.

  `packing_at`: where the stage has room for the packing, at all coins c, every row's number r and
    every place j:
    `packedN s (hideAt (s.h + s.g) c) r j = (⟨s.h + s.g, s.h⟩ : K1.Ride).lay c r j`.
  `packing_sent`: at a message in which ⟨s.h + s.g, s.h⟩ rides, at a row's number below the
    message's number of mask rows and a place below the mask code's message length: the entry that
    `rowsR` lays is `packedN`'s, at the message's own coins, cut at their count 2 (h + g) + 1.
    In Lean: `packedN s` is at `hideAt (s.h + s.g)` of the function that gives `K1.ce c (m + i)` at
    i below 2 (h + g) + 1 and 0 from there on; m is `(K1.startR P ride k).e`, plus, where the
    shape's `mainDeg` is 3 (main rows over the extension field), the message's `Steps.main`: the
    number of its main rows' coins
  `named_byName`: at all k, w, w0: `Named k (byName k w w0) w w0` (`Named`:
    Johnson/Desc/K12/Honest/Packing.lean). So `Named` can be met at all w, w0
  `byName_coeff`, `byName_const`: the two fields of that `Named`: `byName k w w0` is
    w (l + 1) (p + 1) at the name `hIx` of l and p, both counted from 0, and w0 at the name `hCst`

By what. `packing_at` is `packing_one` (Johnson/Desc/K12/Honest/Packing.lean) at `named_byName`.
That the right side of `packing_one` is `K1.Ride.lay` there holds by unfolding: `hideAt`
(K12/Coins.lean) and `hideOfCoins` (K1/Coins.lean) have the same index expression in c.
`packing_sent` rewrites by `packing_at` and unfolds the field `mask` of `rowsR`. `byName_coeff` and
`byName_const` go by recursion on k and unfold `byName`, `hIx` and `hCst`.

Hypotheses of `packing_sent`. hl: s.h + 2 * s.g + 1 ≤ s.Z.l: the stage has room for the packing;
`packing_at` has this one only. hR: `ride k` is ⟨s.h + s.g, s.h⟩. hr: r is below the field
`maskRows` of `shapeAt P k`. hj: j is below the field `ell` (the message length) of the code that
`P.codes.mask` has at the number `maskCode` of `shapeAt P k`; of the default code where it has none.

Limits.
- The room (h + 2 g + 1 places in a mask row's message) is asked: without it `packedN` is 0.
- The two numbers of the riding table are the stage's: h + g rounds, 2 ^ h rows; that a sending's
  job is handed this table at these numbers, that the stage's mask code is the message's, and that
  the two parts read the same coins, is not shown here.
- Outside the message's mask table `rowsR` lays 0, and nothing is said here of `packedN` there.
- `packing_sent` has no hypothesis that k is below the number of the sending's messages, and none
  that the numbers m + i are below the count. From the number of messages on, `shapeAt P k` is the
  default shape, which has no mask row: hr cannot be met, and the statement is vacuous there. Beyond
  the count `K1.ce` gives 0, on both sides: the equation holds also where a 0 is read in a coin's
  place, and nothing is said here on whether that happens.
- An equation between texts: nothing on how a coin is sampled, on a tail. Nothing on completeness,
  on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Packing
import Johnson.Desc.ProofFile.Honest.K12.Coins
import Johnson.Desc.ProofFile.Honest.K1.Coins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

theorem byName_coeff : ∀ (k : ℕ) (w : ℕ → ℕ → GE) (w0 : GE) (l : Fin k) (p : Fin 2),
    byName k w w0 (hIx GE 2 k l p) = w (l.val + 1) (p.val + 1)
  | 0, _, _, l, _ => l.elim0
  | k + 1, w, w0, l, p => by
    refine Fin.cases ?_ (fun l' => ?_) l
    · rfl
    · show byName k (fun l t => w (l + 1) t) w0 (hIx GE 2 k l' p) = _
      rw [byName_coeff k _ w0 l' p]
      rfl

theorem byName_const : ∀ (k : ℕ) (w : ℕ → ℕ → GE) (w0 : GE), byName k w w0 (hCst GE 2 k) = w0
  | 0, _, _ => rfl
  | k + 1, w, w0 => byName_const k (fun l t => w (l + 1) t) w0

/-- `byName k w w0` has the coefficients w and w0 under the library's names (`hIx`, `hCst`). -/
theorem named_byName (k : ℕ) (w : ℕ → ℕ → GE) (w0 : GE) : Named k (byName k w w0) w w0 :=
  ⟨byName_coeff k w w0, byName_const k w w0⟩

/-- **`packedN` of `hideAt` is the laying of a fold's fresh table** (`K1.Ride.lay`). c: the coins,
by number. r: the row's number. j: the place. hl: the stage has room for the packing. -/
theorem packing_at (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) (c : ℕ → GE) (r j : ℕ) :
    packedN s (hideAt (s.h + s.g) c) r j = (⟨s.h + s.g, s.h⟩ : K1.Ride).lay c r j :=
  packing_one s hl _ _ _ (named_byName _ _ _) r j

/-- **The table that a sending's part lays, where a fold's fresh table rides, is `packedN`'s**, at
every row and place inside the message's mask table, at the message's own coins, cut at their
count. k: the message's number in the sending. hl: the stage has room for the packing. -/
theorem packing_sent (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l) (P : VerifiableInference.Desc.K1.Par)
    (ride : ℕ → Option K1.Ride) (data : ℕ → ℕ → ℕ → Option (GF ⊕ GE))
    (c : Cs (K1.dueR P ride))
    (k r j : ℕ) (hR : ride k = some ⟨s.h + s.g, s.h⟩)
    (hr : r < (Johnson.Prover.Send.shapeAt P k).maskRows)
    (hj : j < (P.codes.mask.getD (Johnson.Prover.Send.shapeAt P k).maskCode default).ell) :
    (K1.rowsR P ride data c k).mask r j =
      packedN s (hideAt (s.h + s.g) fun i =>
        if i < 2 * (s.h + s.g) + 1 then
          K1.ce c ((K1.startR P ride k).e +
            (if (Johnson.Prover.Send.shapeAt P k).mainDeg == 3 then
              (K1.stepsOf P.codes (Johnson.Prover.Send.shapeAt P k) (ride k)).main else 0) + i)
        else 0) r j := by
  rw [packing_at s hl]
  show (match ride k with
    | some R =>
        if r < (Johnson.Prover.Send.shapeAt P k).maskRows ∧
            j < (P.codes.mask.getD (Johnson.Prover.Send.shapeAt P k).maskCode default).ell then
          R.lay (fun i => if i < R.count then K1.ce c ((K1.startR P ride k).e +
            (if (Johnson.Prover.Send.shapeAt P k).mainDeg == 3 then
              (K1.stepsOf P.codes (Johnson.Prover.Send.shapeAt P k) (ride k)).main else 0) + i)
            else 0) r j
        else 0
    | none => _) = _
  split
  · rename_i R hR'
    rw [hR] at hR'
    cases hR'
    rw [if_pos ⟨hr, hj⟩]
    rfl
  · rename_i hR'
    rw [hR] at hR'
    cases hR'

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.byName_coeff
#print axioms ProofFile.Honest.K12.byName_const
#print axioms ProofFile.Honest.K12.named_byName
#print axioms ProofFile.Honest.K12.packing_at
#print axioms ProofFile.Honest.K12.packing_sent
