-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FreshCols.lean: what `read3` reads in the column, as words, of a
tree that holds a fresh table and nothing else (`freshCol`,
Johnson/Desc/ProofFile/Honest/K12/Test.lean: the tree that the first fold of a proximity test sends
itself, where the job's field `fresh` is `none`). `read3` (Johnson/Desc/K12/Honest/Written.lean) is
the reader in which `frOf_enc` of that file states its hypothesis hF on a tree's columns; the two
main theorems prove the equation of hF for `freshCol`. They hold at every stage s, every state P
of a prover and every position x. A fifth theorem, `first_packs`, is on the fresh table in a job's
first state, at every job. Theorems with their proofs; no definition.

In the list: s is a stage (`Sg`, OnBytes/Slice/Stage.lean), h is `s.h`, and `s.Z` is the code of a
mask row; a code's length is 2 ^ a at its own a. P is what a prover holds at a stage (`PS`,
Johnson/Prover/Link/BodyState.lean). Row b of its fresh table has the message `P.fM b` and the tail
`P.fT b`; `freshCol s P x` writes one symbol for each row b below 2^h. A row's symbol at a position
is `symG` (Johnson/Prover/Link/Base.lean).

  `fresh_own`: from word 0 on stand the symbols of the table's rows at x modulo the mask code's
    length: the premise of `frOf_enc` on the columns, at a cut of 0, up to the form of the rows. In
    Lean: for b below 2^h, `read3 (freshCol s P x) (0 + 3 * b)` is
    `symG s.Z (x % 2 ^ s.Z.a) (P.fM b) (P.fT b)`. The premise is the hypothesis hF; the cut is its
    oF, the first word of these symbols in a column
  `fresh_own_ext`: the same with the rows as functions on the table's entries (`φOf`, `ψOf`,
    Johnson/Prover/Link/BodyState.lean), each made a function on ℕ by `ext0`
    (Johnson/Prover/Link/SymTie.lean: 0 beyond the function's own entries), and with `Sz.rowNo b`
    (OnBytes/Slice/LinkAt.lean) as the row's number, b being its binary digits. That is the equation
    of hF word for word, but for the name of a bound variable, at f := `freshCol s P`, oF := 0,
    φ := `φOf s P`, ψ := `ψOf s P`. No hypothesis: it holds at every x, where hF asks it below 2 ^ a
  `length_freshCol`: the column has 3 · 2^h words: three for each row
  `read3_wordsOf`: for a list l of elements written as three words each (`Fmt.M1.E`) and i below
    its length: `read3` at word 3 i of `wordsOf l` (Johnson/Prover/Link/SwitchCols.lean) is
    `lst l i` (OnBytes/Slice/SimBasic.lean), entry i of l read in the extension field
  `first_packs`: a job's first state has for its fresh table the packing of the hiding polynomial of
    which the term's first fold is made: by unfolding. In Lean: `(J.first w fr C).fM` is `packedN`
    (Johnson/Prover/Link/BodyPack.lean) at `sgOf J.s₀` and
    `(coinsOf J.p.nums.stages C.hide C.rest).W (sgOf J.s₀) 0`. A job is a `TestJob`, its first state
    `TestJob.first`, its first stage `TestJob.s₀` (all in Test.lean); `coinsOf` is in Coins.lean in
    this folder. The term is `testAll` (Test.lean): it passes this value of `coinsOf` to `stagesAll`
    (Johnson/Desc/K12/Honest/Stages.lean), where the fold of stage number 0 (`aFold`) reads the
    field `W` at the first stage and the number 0

By what. `read3_wordsOf` is `sym3_wordsOf` (SwitchCols.lean) with `toE` (OnBytes/Slice/Field.lean)
applied to both sides. `length_freshCol`: `length_wordsOf` (SwitchCols.lean) and `length_wr`
(Base.lean). `fresh_own`: `read3_wordsOf`, `lst_wr` (Base.lean), and unfolding `freshSym`
(SwitchCols.lean). `fresh_own_ext`: `fresh_own` at the row number `Sz.rowNo b`, which is below 2^h
by `rowNo_lt` (OnBytes/Slice/Cells.lean), and `symG_congr` (Base.lean): `symG` reads a message and
a tail only at numbers at which `ext0` returns the function's own value. `first_packs`: `rfl`.

Limits. That the book of trees (`TreeBook`, OnBytes/Iop/Ground.lean: the trees sent so far, each
with its shape) states 0 as the first word of the symbols and the width 3 · 2^h for such a tree is
not shown here. `frOf_enc` is not called here; its hypotheses hpos, hlen and hz are not shown here.
`first_packs` holds at every job, also where the list of stages has fewer than two stages: there the
term has no fold. Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Test
import Johnson.Desc.K12.Honest.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link
open H2K.Pub (sgOf)

theorem read3_wordsOf (l : List Fmt.M1.E) (i : ℕ) (hi : i < l.length) :
    read3 (wordsOf l) (3 * i) = lst l i :=
  congrArg toE (sym3_wordsOf l i hi)

theorem length_freshCol (s : Sg) (P : PS) (x : ℕ) : (freshCol s P x).length = 3 * 2 ^ s.h := by
  unfold freshCol
  rw [length_wordsOf, length_wr]

/-- **The column of a fresh table's own tree holds the symbols of the table's rows.** For b below
2^h: the three words from word 0 + 3 b on, read by `read3`, are `symG` at the code `s.Z`, the
position `x % 2 ^ s.Z.a`, the message `P.fM b` and the tail `P.fT b`. -/
theorem fresh_own (s : Sg) (P : PS) (x b : ℕ) (hb : b < 2 ^ s.h) :
    read3 (freshCol s P x) (0 + 3 * b) = symG s.Z (x % 2 ^ s.Z.a) (P.fM b) (P.fT b) := by
  unfold freshCol
  rw [Nat.zero_add, read3_wordsOf _ _ (by rw [length_wr]; exact hb), lst_wr _ _ _ hb]
  rfl

/-- The same with the rows as functions on the table's entries (`φOf`, `ψOf`), made functions on ℕ
by `ext0`, and with the row's number `Sz.rowNo b`: the equation in the hypothesis hF of `frOf_enc`
(Johnson/Desc/K12/Honest/Written.lean) at oF := 0. -/
theorem fresh_own_ext (s : Sg) (P : PS) (x : ℕ) (b : Fin s.h → Bool) :
    read3 (freshCol s P x) (0 + 3 * Sz.rowNo b) =
      symG s.Z (x % 2 ^ s.Z.a) (ext0 fun e => φOf s P (b, e)) (ext0 fun q => ψOf s P (b, q)) :=
  (fresh_own s P x _ (rowNo_lt b)).trans
    (symG_congr s.Z _ _ _ _ _
      (fun j hj => (show ext0 (fun e : Fin s.Z.l => φOf s P (b, e)) j = P.fM (Sz.rowNo b) j from
        dif_pos hj).symm)
      fun q hq => (show ext0 (fun e : Fin s.Z.r => ψOf s P (b, e)) q = P.fT (Sz.rowNo b) q from
        dif_pos hq).symm)

/-- The first stage's state of a job has for its fresh table the packing of the hiding polynomial of
which the term's first fold is made. -/
theorem first_packs {W X : Type} (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) :
    (J.first w fr C).fM =
      packedN (sgOf J.s₀) ((coinsOf J.p.nums.stages C.hide C.rest).W (sgOf J.s₀) 0) := rfl

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.first_packs
#print axioms ProofFile.Honest.K12.read3_wordsOf
#print axioms ProofFile.Honest.K12.length_freshCol
#print axioms ProofFile.Honest.K12.fresh_own
#print axioms ProofFile.Honest.K12.fresh_own_ext
