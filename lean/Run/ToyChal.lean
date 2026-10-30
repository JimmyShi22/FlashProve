-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyChal.lean: how K blocks of 256 bits give a round's verifier message by the programs' format
(section 6 of the page, in an edition that is not the one that ships): the map that a wiring needs,
made of the functions on bytes.

Definitions that compute, tests (#guard), two small theorems.
The file is about the Fiat-Shamir step: how a round's verifier message is drawn from blocks of hash
output. A wiring (Iop/BatchWire.lean: `WireRB`, field `chal`) takes a function from K blocks
(`Iop.Dig 256` each) to the round's verifier message. The format draws that message from a row of
64-bit words, four to a block of 32 bytes (R6.1, R1.5). Between the two is the order of bits of
Fmt/Rules1.lean (`bitAt`) and Run/CodingBits.lean (`digToBytes`): bit i of a block is bit (i mod 8),
from the lowest, of byte (i div 8).

Main names:
  `rowOfDigs u`: the row of words of the blocks u: word t is word (t mod 4) of block (t div 4); 0
    beyond the last block.
  `chalRound f e k u`: the whole message of a round with the plan's entry e and the kind k
    (`drawRound`, Fmt/Rules6Round.lean), as the record `Fmt.Drawn`.
  `chalAll f ds u`: the same for draws given as a list (`readAll`, Fmt/Rules6.lean).
  `chalPoss k n u`: n positions below 2^k: the draws, in the order drawn, repeats kept (R6.6).
  `toyChal u`: the message of the toy of Run/ToyQ.lean (`Run.Toy1`: this library's own, not the
    programs'). That the toy's own map is this one at one block (K = 1) is `toy1_chal`
    (Run/ToyChalTie.lean).
  `chalPoss_draw`: `chalPoss` is the format's `drawPoss` on that row, from the place 0 (the same
    numbers in the same order).
  `drawPoss_eq`: what `drawPoss` gives, in closed form.

The tests: a block, `toyBlock` (made by the reference program from the page's lines), gives 3, 12,
9, and the list 3, 9, 12. It is not the block from which the round of `ParseEx.file`, a file of that
toy, draws (Run/ParseChain.lean: see the tests there).

Limits: this file says nothing on the law of these maps on uniform blocks (for positions: uniform if
n is at most 4 K and k at most 64): the files Run/Draw*.lean, and Run/ToyChalLaw.lean, which joins
them to these maps. No wiring is built here.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules6Round
import Run.CodingBits

set_option autoImplicit false

namespace Run
open Iop

/-- The row of words of K blocks. -/
def rowOfDigs {K : ℕ} (u : Fin K → Dig 256) : _root_.Fmt.Row :=
  _root_.Fmt.rowOfBlocks (Array.ofFn fun i => digToBytes (u i))

/-- The verifier's message of a round, from its blocks. -/
def chalRound (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind)
    {K : ℕ} (u : Fin K → Dig 256) : _root_.Fmt.Drawn :=
  _root_.Fmt.drawRound f e k (rowOfDigs u)

/-- The same for draws given as a list. -/
def chalAll (f : _root_.Fmt.Fld) (ds : List _root_.Fmt.Draw) {K : ℕ} (u : Fin K → Dig 256) :
    List _root_.Fmt.Val :=
  (_root_.Fmt.readAll f ds (rowOfDigs u) 0).1

/-- n positions below 2^k, as drawn. -/
def chalPoss (k n : ℕ) {K : ℕ} (u : Fin K → Dig 256) : Fin n → Fin (2 ^ k) := fun i =>
  ⟨(rowOfDigs u i.val).toNat % 2 ^ k, Nat.mod_lt _ (Nat.two_pow_pos k)⟩

/-- The message of the toy of Run/ToyQ.lean: three positions below 16. -/
def toyChal {K : ℕ} (u : Fin K → Dig 256) : Fin 3 → Fin 16 := chalPoss 4 3 u

/-- What the format's draw of n positions gives, from every place c of every row. -/
theorem drawPoss_eq (k : ℕ) (r : _root_.Fmt.Row) :
    ∀ (n c : ℕ),
      _root_.Fmt.drawPoss k n r c = ((List.range n).map fun i => (r (c + i)).toNat % 2 ^ k, c + n)
  | 0, c => rfl
  | n + 1, c => by
    have ih := drawPoss_eq k r n (c + 1)
    have e : _root_.Fmt.drawPoss k (n + 1) r c =
        ((r c).toNat % 2 ^ k :: (_root_.Fmt.drawPoss k n r (c + 1)).1,
          (_root_.Fmt.drawPoss k n r (c + 1)).2) := rfl
    rw [e, ih, List.range_succ_eq_map, List.map_cons, List.map_map]
    refine Prod.ext ?_ (by show c + 1 + n = c + (n + 1); omega)
    show _ :: _ = _ :: _
    congr 1
    refine List.map_congr_left fun i _ => ?_
    show (r (c + 1 + i)).toNat % 2 ^ k = (r (c + (i + 1))).toNat % 2 ^ k
    rw [show c + 1 + i = c + (i + 1) by omega]

/-- The vector is the format's draw on the row of the blocks, from the place 0. -/
theorem chalPoss_draw (k n : ℕ) {K : ℕ} (u : Fin K → Dig 256) :
    List.ofFn (fun i => (chalPoss k n u i).val) = (_root_.Fmt.drawPoss k n (rowOfDigs u) 0).1 := by
  rw [drawPoss_eq, List.ofFn_eq_map]
  show _ = (List.range n).map fun i => (rowOfDigs u (0 + i)).toNat % 2 ^ k
  rw [← List.map_coe_finRange_eq_range, List.map_map]
  refine List.map_congr_left fun i _ => ?_
  show (rowOfDigs u i.val).toNat % 2 ^ k = (rowOfDigs u (0 + i.val)).toNat % 2 ^ k
  rw [Nat.zero_add]

/-- A block for the tests below; see the head. -/
def toyBlock : ByteArray :=
  _root_.Fmt.unhex "b39ce491e904165c2ce2a9e24698ea6bb9a9093b2f8edfeb966ed06dd998dc48"

#guard List.ofFn (fun i => (toyChal (K := 1) (fun _ => bytesToDig toyBlock) i).val) = [3, 12, 9]
#guard _root_.Fmt.listOf (List.ofFn fun i => (toyChal (K := 1) (fun _ => bytesToDig toyBlock) i).val) = [3, 9, 12]
#guard (chalRound .two { name := "", work := 8, msg := 32, roots := 1, poss := 3, logN := 4 } .positions (K := 1) fun _ => bytesToDig toyBlock).poss = [3, 12, 9]
#guard chalAll .two [.pos 4, .pos 4, .pos 4] (K := 1) (fun _ => bytesToDig toyBlock) = [.pos 3, .pos 12, .pos 9]
-- the row of the blocks is the row of their bytes; 0 beyond
#guard (List.range 5).map (rowOfDigs (K := 1) fun _ => bytesToDig toyBlock) = (List.range 5).map (_root_.Fmt.rowOfBlocks #[toyBlock])
-- a second block is reached by word 4
#guard (chalPoss 8 5 (K := 2) (fun i => bytesToDig (if i.val = 0 then toyBlock else _root_.Fmt.pattern 32)) 4).val = 3

end Run
