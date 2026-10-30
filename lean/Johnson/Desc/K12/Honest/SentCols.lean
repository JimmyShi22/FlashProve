-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/SentCols.lean: the written column of a sending (the kind K1), word by word,
under the readers of a proximity test's theorems on reading a tree. The prover's side of a sending
writes a tree's column from the rows that its caller gives (`col`, Johnson/Prover/Send/Core.lean),
and Johnson/Prover/Send/Enc.lean says at which words of the column a message's words are. Here these
lemmas are stated with the readers `read1` and `read3` of Johnson/Desc/K12/Honest/Written.lean, with
which `ofOrc_enc` and `frOf_enc` (same file) state their hypotheses on a column's symbols. Theorems
with their proofs; no definition. General in the place and in the rows, at a place that passes its
own test on the plan. The file uses nothing of the frame for an honest side
(Johnson/Desc/ProofFile/Honest/Frame.lean), and its imports do not reach that file.

In the list: a sending is a sub-protocol of the kind K1 (Johnson/Desc/K1/Own.lean). Its place P
(`K1.Par`, Johnson/Desc/K1/Send.lean) has its public numbers: among them the codes (`P.codes`) and
the oracle messages in the order of sending (`P.sent`). `shapeAt P k` (Core.lean) is the shape of
message number k (`OracleShape`, OnBytes/Iop/Ground.lean): its numbers of main rows and of mask
rows, the numbers of their two codes, and `mainDeg`: 1 if the main rows are over the base field
`GF`, 3 if over the extension field `GE`. V gives for each message's number what the caller gives
of that message (`Rows`, Core.lean): every row and every row's tail, as field values. Ly is a layout
(`TreeLay`, Ground.lean): for each message its tree and its part, that is its number among the
messages of that tree, and each tree's shape (`TreeShape`). `col P V t x` is the written column of
the place's tree number t at the position x: a list of 64-bit words, numbered from 0. A message's
two skips are `skipMain T p` and `skipMask T p` (Johnson/Prover/Send/Front.lean) at its tree's shape
T and its part p: the numbers of the words at which its main symbols and its mask symbols begin in a
column. `symG C x m r` (Johnson/Prover/Link/Base.lean) is the symbol at the position x of the code
word of C for the message m and the tail r; the length of C is 2 ^ `C.a`. `ofF` writes an element of
`GF` as one word and `ofE` an element of `GE` as three (OnBytes/Slice/Field.lean); `words3`
(Johnson/Prover/Link/SwitchCols.lean) lists the three.

  `sent_main3`, `sent_main1`, `sent_mask`: at every position x, for message number k of the place:
    behind the message's two skips stand the symbols at x of its main rows (three words each, or one
    over the base field) and, at x modulo the mask code's length, of its mask rows. In Lean: c is
    the column of the message's tree at x, and r is a row's number. Where `mainDeg` is 3, `read3 c`
    at word `skipMain` + 3 r is `symG` at x of main row r and its tail (`mainE`, `mainTlE`). Where
    it is 1, `read1 c` at word `skipMain` + r is `symG` at x of main row r and its tail (`mainF`,
    `mainTlF`), each entry taken into `GE`. `read3 c` at word `skipMask` + 3 r is `symG`, at x
    modulo the code's length, of `mask r` and `maskTl r`. The code is the one whose number the shape
    has, in `P.codes.base` or `P.codes.mask`, as `codeOf` (OnBytes/Slice/ProgCodes.lean) returns it
  `read3_of`, `read1_of`: for a list of words c. If the three words of c from word number k on are
    the three words of `ofE y`, then `read3 c k` is y. If word number k of c is `ofF y`, then
    `read1 c k` is y in the extension field
  `skipMain_eq`, `skipMask_eq`: the two skips are the library's `skipM` and `skipZ`
    (OnBytes/Slice/BlkProxGp.lean). The public facts on a group's data (`GpData.Pub`, same file)
    equate these two, at a member's tree's shape and part, with the first words `oM` and `oZ` of the
    member's `Lay` (OnBytes/Slice/KeyGroup.lean)

By what. `read3_of` unfolds `read3` and ends by `toE_ofE`, `read1_of` unfolds `read1` and ends by
`toF_ofF` (both OnBytes/Slice/Field.lean). The two on the skips hold by unfolding. The other lemmas
are all in Johnson/Prover/Send/Enc.lean. `col_main_at`: word number j of the message's main symbols
(`mainSyms`, Core.lean) is word number `skipMain` + j of the column; `col_mask_at`: the same for
`maskSyms` and `skipMask`. `length_mainSyms` and `length_maskSyms` give the lengths of these two
lists; `mainSyms_three`, `mainSyms_one` and `maskSyms_three` give their words. `sent_main3` and
`sent_mask` call `read3_of`. `sent_main1` calls `read1_of`, after `symG_ofF`: a symbol over the
base field (`symF`, Core.lean), taken into `GE`, is `symG` of the row and the tail taken into `GE`.

Hypotheses of the three main theorems. hP: `K1.planOkOwn P` passes (Johnson/Desc/K1/Own.lean: tests
on the plan only). hL: `layTrees P.codes P.sent` (Ground.lean) returns Ly. hk: k is below
`P.sent.size`. h, for a main row: `mainDeg` of the message's shape is 3, or is 1; under hP and hk it
is one of the two (`deg_of_plan`, Enc.lean). hr: r is below the shape's number of main rows, or of
mask rows. None of them reads V.

Limits.
- The three main theorems are not the hypotheses of `ofOrc_enc` and `frOf_enc` word for word. There
  the rows are functions on a message's entries; the codes are a member's (`Mb`), or a stage's
  (`Sg`); the first words of the symbols (`L.oM`, `L.oZ`, oF) are those of a group's public data;
  and the column's width is that of a round's data (`PQ.colW d.tree`). No theorem here goes from the
  one form to the other, and none states the width of `col` (`length_col`, Enc.lean, does).
- The three main theorems are proved only at a place that passes its own test on the plan (hP).
- The position x is any natural number: it is not asked to be a position of the tree.
- The statements look up the layout's arrays and the codes with defaults (`getD`), as the lemmas of
  Enc.lean do. That a look-up is in range is not stated here.
- Nothing on trees' hashes or salts, on a decision, on completeness, on soundness or on what is
  hidden.
-/
import Johnson.Desc.K12.Honest.Written
import Johnson.Prover.Send.Enc
import OnBytes.Slice.BlkProxGp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice OnBytes.Slice.ProxRun Cb VerifiableInference.Desc
open Johnson.Prover.Link (symG words3)
open Johnson.Prover.Send

/-- If the three words of c from word number k on are the three words of `ofE y`, then `read3 c k`
is y. -/
theorem read3_of (c : List UInt64) (k : ℕ) (y : GE)
    (h : ∀ t, t < 3 → c[k + t]? = (words3 (ofE y))[t]?) : read3 c k = y := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  rw [Nat.add_zero] at h0
  unfold read3
  simp only [List.getD_eq_getElem?_getD, h0, h1, h2]
  show toE (ofE y) = y
  exact toE_ofE y

/-- If word number k of c is `ofF y`, then `read1 c k` is y in the extension field. -/
theorem read1_of (c : List UInt64) (k : ℕ) (y : GF) (h : c[k]? = some (ofF y)) :
    read1 c k = algebraMap GF GE y := by
  unfold read1
  rw [List.getD_eq_getElem?_getD, h]
  show algebraMap GF GE (toF (ofF y)) = _
  rw [toF_ofF]

theorem skipMain_eq (T : TreeShape) (p : ℕ) : skipMain T p = skipM T p := rfl

theorem skipMask_eq (T : TreeShape) (p : ℕ) : skipMask T p = skipZ T p := rfl

section Sent
variable (P : K1.Par) (V : ℕ → Rows) (hP : K1.planOkOwn P = true) (Ly : TreeLay)
  (hL : layTrees P.codes P.sent = some Ly) (k x : ℕ) (hk : k < P.sent.size)
include hP hL hk

/-- A main row over the extension field. `read3` at word `skipMain` + 3 r of the column at x is the
symbol at x of main row r and its tail. -/
theorem sent_main3 (h : (shapeAt P k).mainDeg = 3) (r : ℕ) (hr : r < (shapeAt P k).mainRows) :
    read3 (col P V (Ly.tree.getD k 0) x)
        (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r) =
      symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x ((V k).mainE r)
        ((V k).mainTlE r) := by
  refine read3_of _ _ _ fun t ht => ?_
  have hlen : 3 * r + t < (mainSyms P V k x).length := by
    rw [length_mainSyms P V k x (Or.inr h)]
    show 3 * r + t < (shapeAt P k).mainRows * (shapeAt P k).mainDeg
    rw [h]
    omega
  rw [Nat.add_assoc, col_main_at P V hP Ly hL k x _ hk hlen, mainSyms_three P V k x r t h hr ht]

/-- A main row over the base field. `read1` at word `skipMain` + r of the column at x is the symbol
at x of main row r and its tail, each entry taken into the extension field. -/
theorem sent_main1 (h : (shapeAt P k).mainDeg = 1) (r : ℕ) (hr : r < (shapeAt P k).mainRows) :
    read1 (col P V (Ly.tree.getD k 0) x)
        (skipMain (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + r) =
      symG (codeOf (P.codes.base.getD (shapeAt P k).code default)) x
        (fun j => algebraMap GF GE ((V k).mainF r j))
        (fun q => algebraMap GF GE ((V k).mainTlF r q)) := by
  have hlen : r < (mainSyms P V k x).length := by
    rw [length_mainSyms P V k x (Or.inl h)]
    show r < (shapeAt P k).mainRows * (shapeAt P k).mainDeg
    rw [h]
    omega
  rw [← symG_ofF]
  refine read1_of _ _ _ ?_
  rw [col_main_at P V hP Ly hL k x _ hk hlen, mainSyms_one P V k x r h hr]

/-- A mask row. `read3` at word `skipMask` + 3 r of the column at x is the symbol of `mask r` and
`maskTl r` at x modulo the length of the message's mask code. -/
theorem sent_mask (r : ℕ) (hr : r < (shapeAt P k).maskRows) :
    read3 (col P V (Ly.tree.getD k 0) x)
        (skipMask (Ly.shapes.getD (Ly.tree.getD k 0) {}) (Ly.part.getD k 0) + 3 * r) =
      symG (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default))
        (x % 2 ^ (codeOf (P.codes.mask.getD (shapeAt P k).maskCode default)).a) ((V k).mask r)
        ((V k).maskTl r) := by
  refine read3_of _ _ _ fun t ht => ?_
  have hlen : 3 * r + t < (maskSyms P V k x).length := by
    rw [length_maskSyms P V k x]
    show 3 * r + t < (shapeAt P k).maskRows * 3
    omega
  rw [Nat.add_assoc, col_mask_at P V hP Ly hL k x _ hk hlen, maskSyms_three P V k x r t hr ht]

end Sent

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.read3_of
#print axioms ProofFile.Honest.K12.read1_of
#print axioms ProofFile.Honest.K12.skipMain_eq
#print axioms ProofFile.Honest.K12.skipMask_eq
#print axioms ProofFile.Honest.K12.sent_main3
#print axioms ProofFile.Honest.K12.sent_main1
#print axioms ProofFile.Honest.K12.sent_mask
