-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawGuard.lean: tests that the block sampler of a round runs, and gives what the functions on
bytes give.

Tests (#guard) only (evaluations by Lean's evaluator when the file is compiled: they leave no
declaration, and nothing here is to be quoted as proved). Four definitions serve the tests: `blk`,
`nat3`, `ext3`, `tb`; the tests of Run/PlanDrawsSix.lean use `blk` and `tb`.
The sampler `bsOf f ds` of Run/DrawPage.lean makes a round's verifier message from 256-bit blocks.
A bound on its bias is a theorem for lists of `Lawful` draws (Run/DrawPageProofs.lean:
`drawPage_bs`). Here the sampler is evaluated on blocks given as bytes (Run/CodingBits.lean:
`bytesToDig`) and held against the format's own functions on the row of these bytes
(Fmt/Rules6.lean, which renders section 6 of the format page, docs/format/FORMAT.md; this file was
written against an edition of the page that is not the one that ships). Tested are: positions; an
element of the extension field in both fields; one that is not 0; pairs of bits against matrix
entries; a round with several draws, where a try that fails moves the places of all later draws. Of
four words the number of blocks alone is tested.
That the two agree on all blocks is a statement of Run/DrawTie.lean, not of this file. (There,
through `outAll`, on the row of the blocks' words: `Spec.drawTie_bs`. On the blocks' bytes:
`Spec.bs_bytes`, Run/ToyChalLaw.lean.)
The format's two fields (`Fld`, Fmt/Rules1.lean): `.one`, p = 2^61-1; `.two`, p = 2^64-2^32+1.

Terms: lean/GLOSSARY.md.
-/
import Run.DrawPage
import Run.ToyChal

set_option autoImplicit false

namespace Run

/-- blocks from bytes -/
def blk (bs : Array ByteArray) (b : ℕ) : Fin b → Iop.Dig 256 := fun i =>
  bytesToDig (bs.getD i.val ByteArray.empty)

/-- an element as three numbers -/
def nat3 {f : _root_.Fmt.Fld} (e : EV f) : ℕ × ℕ × ℕ := (e.1.val, e.2.1.val, e.2.2.val)
def ext3 (e : _root_.Fmt.Ext) : ℕ × ℕ × ℕ := (e.1.toNat, e.2.1.toNat, e.2.2.toNat)

/-- five blocks of test bytes; the words of the first are made to fail in both fields -/
def tb : Array ByteArray :=
  #[_root_.Fmt.cat (List.replicate 4 (_root_.Fmt.u64 18446744073709551615)), _root_.Fmt.pattern 32,
    _root_.Fmt.pattern 32 11 5, _root_.Fmt.pattern 32 13 9, _root_.Fmt.pattern 32 17 1]

-- the numbers of blocks
#guard (bsOf .two [.elem]).b = 5
#guard (bsOf .two [.elemNZ]).b = 9
#guard (bsOf .two [.pos 4, .pos 4, .pos 4]).b = 1
#guard (bsOf .one [.trits 40]).b = 1
#guard (bsOf .one [.sealed]).b = 1

-- three positions of four bits from `toyBlock`: what `toyChal` gives (tested in Run/ToyChal.lean)
#guard (let v := (bsOf .two [.pos 4, .pos 4, .pos 4]).φ (blk #[toyBlock] 1); [v.1.val, v.2.1.val, v.2.2.1.val]) = List.ofFn fun i => (toyChal (K := 1) (fun _ => bytesToDig toyBlock) i).val

-- an element, both fields: four words that fail come first, so the places move
#guard nat3 ((bsOf .two [.elem]).φ (blk tb 5)).1 = ext3 (_root_.Fmt.drawE .two (_root_.Fmt.rowOfBlocks tb) 0).1
#guard nat3 ((bsOf .one [.elem]).φ (blk tb 5)).1 = ext3 (_root_.Fmt.drawE .one (_root_.Fmt.rowOfBlocks tb) 0).1
#guard nat3 ((bsOf .two [.elemNZ]).φ (blk tb 9)).1.1 = ext3 (_root_.Fmt.drawNZ .two (_root_.Fmt.rowOfBlocks tb) 0).1

-- a row of zeros: the element is 0; the one that must not be 0 is 1
#guard nat3 ((bsOf .two [.elem]).φ (blk #[] 5)).1 = (0, 0, 0)
#guard nat3 ((bsOf .two [.elemNZ]).φ (blk #[] 9)).1.1 = (1, 0, 0)

-- forty pairs of bits against forty matrix entries
#guard (List.ofFn fun j : Fin 40 => (let x := ((bsOf .two [.trits 40]).φ (blk #[tb[1]!] 1)).1 j; if x.1 then (if x.2 then (-1 : Int) else 1) else 0)) = (_root_.Fmt.drawTrits 40 (_root_.Fmt.rowOfBlocks #[tb[1]!]) 0).1

-- several draws in one round (a position, an element, a position): the second position stands
-- behind the words that the element has used
#guard (let v := (bsOf .two [.pos 8, .elem, .pos 8]).φ (blk tb 5); (v.1.val, nat3 v.2.1, v.2.2.1.val)) =
  (let r := _root_.Fmt.rowOfBlocks tb; let a := _root_.Fmt.drawPos 8 r 0; let e := _root_.Fmt.drawE .two r a.2; let c := _root_.Fmt.drawPos 8 r e.2; (a.1, ext3 e.1, c.1))

end Run
