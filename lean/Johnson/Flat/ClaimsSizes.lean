-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ClaimsSizes.lean: what the statements read of a decoded stored table, how an instance
is built, and the next token, as terms at the two sizes of the default setting.

Definitions, and equations on numbers. The decoders are those at which OnBytes/Flat/FilesAt.lean
takes its letter A: `frS.toDecR frZ 402653181` (OnBytes/Slice/FullRecLink.lean) and `srS.toDecR srZ
524285` (OnBytes/Slice/SmallRecLink.lean): a row's message less its three pads.

Main names:
  `numsFull`, `numsSmall`: the committed matrix's rows and k_lo: 3,076,096 and 7; 59,392 and 3
    (docs/format/11-5-weights-in-the-table.md, the table of the two example configurations).
  `sizesSmall`: the small example's ten sizes, as `sizesOf` makes them of its parameter file's
    lines.
  `claimsFull s`, `buildFull`, `nextFull s`: at the full size, by Johnson/Flat/Claims.lean
    (`buildFull`: Johnson/Flat/Instance.lean). `claimsFullAny s`, `nextFullAny s`: the same size by
    Johnson/Flat/ClaimsAny.lean.
  `claimsSmall s`, `buildSmall`, `nextSmall s`: at the small size, by Johnson/Flat/ClaimsAny.lean.
  `buildFull_eq`: `buildFull` is `requestOfTokens`.
  `full_rows`, `full_columns`, `full_fits`, `small_columns`, `small_fits`: at the full size the
    matrix has the rows and columns of the library's reference layout; at both sizes it fits a row's
    message before the pads.
Limits: those of the three files named. AT THE FULL SIZE TOO THE TERMS MEAN A PARAMETER FILE's MODEL
ONLY IF ITS OTHER MODEL LINES ARE THE LIBRARY's: `sizesAt` reads ten lines and `scalesOfFiles`
(Johnson/Flat/ScalesOf.lean) the scale file and eight lines; the lines cs, theta0, the digit forms,
S, rx and the four tables' digests are read by nothing here, and the library's integer program has
them fixed (Inst/Model/Scales.lean: its settings cover a file's only with the reference parameter
file's sizes, digit forms, tables and rotary pattern). That a row's message has 402,653,184 and
524,288 entries is held here only as far as `full_fits` and `small_fits` go (the cut is at most the
message). AT THE FULL SIZE THE A THAT STANDS IS `claimsLedger` (Johnson/Flat/ClaimsLedger.lean),
over the matrices of Johnson/Flat/Claims.lean; `claimsFull`, `claimsFullAny`, `nextFull`,
`nextFullAny` are kept beside it. The numbers are typed here; that they are the words of the hashed
item "the test on the table" is not shown here (`matrixNumsOf`, Johnson/Flat/ClaimsAt.lean, reads
them out of a declared structure).

-/
import Johnson.Flat.ClaimsAny
import OnBytes.Slice.FullRecLink
import OnBytes.Slice.SmallRecLink

set_option autoImplicit false

/- No default table of scales here: each table is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model VerifiableInference

/-- The decoder of a stored table at the full size. -/
noncomputable abbrev decFull : DecR := frS.toDecR frZ 402653181

/-- The decoder of a stored table at the small size. -/
noncomputable abbrev decSmallR : DecR := srS.toDecR srZ 524285

/-- The committed matrix's numbers at the full size. -/
def numsFull : MatrixNums := ⟨3076096, 7⟩

/-- The committed matrix's numbers at the small size. -/
def numsSmall : MatrixNums := ⟨59392, 3⟩

/-- The small example's ten sizes. They are the lines lt, L, d, H, G, dh, f, fe, NE and V of
prover/examples/target_small_f2/policy.txt; prover/examples/target_small_f2_roomy/policy.txt has the
same ten lines (compared outside Lean: no theorem). -/
def sizesSmall : Params :=
  sizesOf { lt := 6, V := 512, L := 8, d := 512, H := 4, Gk := 2, dh := 128, f := 1024, fe := 512,
            NE := 4 }

/-- At the full size the matrix has the rows of the library's reference layout. -/
theorem full_rows : numsFull.rows = Layout.hRef := rfl

/-- At the full size the matrix has the columns of the library's reference layout. -/
theorem full_columns : numsFull.kLo + decFull.v = Layout.kRef := rfl

/-- At the full size the matrix fits a row's message before the pads. -/
theorem full_fits : numsFull.rows * 2 ^ numsFull.kLo ≤ decFull.cut ∧ decFull.cut ≤ decFull.T.l := by
  decide +kernel

/-- At the small size the matrix has 2 ^ 11 columns. -/
theorem small_columns : numsSmall.kLo + decSmallR.v = 11 := rfl

/-- At the small size the matrix fits a row's message before the pads. -/
theorem small_fits :
    numsSmall.rows * 2 ^ numsSmall.kLo ≤ decSmallR.cut ∧ decSmallR.cut ≤ decSmallR.T.l := by
  decide +kernel

/-- What the statements read of a decoded table, at the full size, by `claims`. AT
THE FULL SIZE THE A THAT STANDS IS `claimsLedger` (Johnson/Flat/ClaimsLedger.lean): the same
matrices, the same "in range"; its claim is the library's relaxed relation, from which the request's
truth is proved. Its claim `Rel` is an implication: never to be laid as a relation without `inRange`
before it (the docstring of `claims`, Johnson/Flat/Claims.lean). -/
noncomputable def claimsFull (s : Cm.Scales) : decFull.Claims (Instance' ppref) :=
  claims decFull numsFull s

/-- How an instance is built at the full size. It is `requestOfTokens` (`buildAt_ppref`). -/
def buildFull : List Token × List Token → List Token → Option (Instance' ppref) := buildOf ppref

/-- At the full size an instance is built as `requestOfTokens` builds a request. -/
theorem buildFull_eq (x : List Token × List Token) (padding : List Token) :
    buildFull x padding = requestOfTokens x padding := by
  unfold buildFull buildOf
  rw [dif_pos (by decide : 0 < ppref.V)]
  exact buildAt_ppref _ x padding

/-- The next token at the full size, by `nextTokenOf`. Not the one that stands with
`claimsLedger` (Johnson/Flat/ClaimsLedger.lean). -/
noncomputable def nextFull (s : Cm.Scales) : (claimsFull s).Mat → List Token → Option Token :=
  nextTokenOf decFull numsFull s

/-- What the statements read of a decoded table, at the full size, by the layout and the program.
Not the A that stands at the full size: see `claimsFull`. Its claim `Rel` is an implication: never
to be laid as a relation without `inRange` before it (the docstring of `claims`,
Johnson/Flat/Claims.lean). -/
noncomputable def claimsFullAny (s : Cm.Scales) : decFull.Claims (Instance' ppref) :=
  claimsAt decFull numsFull ppref s

/-- The next token at the full size, by the layout and the program. -/
noncomputable def nextFullAny (s : Cm.Scales) : (claimsFullAny s).Mat → List Token → Option Token :=
  nextTokenIn decFull numsFull ppref s

/-- What the statements read of a decoded table, at the small size. It type-checks; it is not the
small example's model (the head of Johnson/Flat/ClaimsAny.lean). Its claim `Rel` is an implication:
never to be laid as a relation without `inRange` before it (the docstring of `claims`,
Johnson/Flat/Claims.lean). -/
noncomputable def claimsSmall (s : Cm.Scales) : decSmallR.Claims (Instance' sizesSmall) :=
  claimsAt decSmallR numsSmall sizesSmall s

/-- How an instance is built at the small size. -/
def buildSmall : List Token × List Token → List Token → Option (Instance' sizesSmall) :=
  buildOf sizesSmall

/-- The next token at the small size. It is not the small example's model's. -/
noncomputable def nextSmall (s : Cm.Scales) : (claimsSmall s).Mat → List Token → Option Token :=
  nextTokenIn decSmallR numsSmall sizesSmall s

end OnBytes.Flat
