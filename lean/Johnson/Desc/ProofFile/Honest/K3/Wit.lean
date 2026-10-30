-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Wit.lean: the honest side of the kind "lookup" (K3): how a lookup's
row is handed its keys and bits. Definitions with code, and tests by evaluation; no theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: the wit is the argument wit of `Part.lift`
(Honest/Frame.lean).

What is defined. A lookup's row is seated at the small structure `Ask` (Honest/K3/Stages.lean): of
the challenges heard in front, the keys and the bits of the counts. `Part.lift` asks for a function
wit that makes this structure of what a half of the first chain is handed (`Local`,
Honest/Frame.lean: index, the index committer's coins, instance, trace). This file is that function,
at each of the four sorts of lookup: on the calls of a link of layers, of an attention link, of the
head; and on the digits of a link's smallness test.
  1 `inE`, `outE`: between the program's elements (`OnBytes.E`), in which the row computes, and the
    library's (`Cb.Gl.E`), in which keys and bits are written. They write out the library's
    `OnBytes.Slice.readE` (OnBytes/Slice/ProgField.lean) and `D6.Bridge.liftGl`
    (OnBytes/Desc/First/NormBridge/HonestGl.lean); the ties are `inE_eq_readE` and `outE_eq_liftGl`
    (Honest/K3/Law/TiesSealed.lean).
  2 `LookIn`, `LookIn.hidden`: a lookup's joint key vector and its bits in the library's field; the
    same as the row's structure.
  3 `tritsAt`: the sampled matrix of a smallness test, out of the challenges heard, by the round's
    number.
  4 `Sources`: the letters: the two readers of trace and index, and for each sort of lookup its keys
    and bits as a function of what that sort may read.
  5 `Who`, `askOf`: which lookup; the function wit there.
  6 Tests at synthetic letters.

What each sort is handed, by type (the fields of `Sources`).
  layers: the cells, the weights' digits.
  attention: the cells.
  head: the instance, the cells, the weights' digits.
  digits: the cells, the sampled matrix.
No sort is handed the index committer's coins. No sort is handed trace or index but through
`Cells.cell` and `Weights.entry` (Honest/ForKinds.lean).

The numbering. In key theta n, n is the number of a key in the joint key vector as
`OnBytes.Ends.jointKey` counts (OnBytes/Tie/Pv/Lookup/Ends/Joint.lean): n = x * 2^rK + y, with y the
tree and x the place in the tree: the tree's number stands in the low bits. In bit u j, u is the row
of the joint table as `OnBytes.Ends.jointTab` counts: u = t * 2^cK + c, with c the call; j is the
plane. The row's structure numbers the parts of the key vector; at the faces of a proof file there
is one part, and `LookIn.hidden` gives the same vector at every part's number.

Imported, through Honest/K3/Stages.lean. Files directly under Honest/.

Limits. The four functions of `Sources` are letters: this file says nothing on what they hold. That
a filling's keys are those of the verifier's claims, that its bits are the cells which the callers'
claims on the planes read, and that the two meet the lookup's relation, is for whoever fills them to
show. Shown in part: `lookG_meets`, `lookA_meets`, `lookH_meets` and `lookZ_meets`
(Honest/K3/WitFill.lean) state `LookIn.Meets` (Honest/K3/WitLaw.lean) of the four sorts' keys and
bits of that file's filling, each conditional on hypotheses of which no instance is exhibited there.
`LookIn.Meets` speaks of the joint key vector, of the verifier's places of the bits and of the
lookup's relation, not of the verifier's claims. `tritsAt` yields the empty list where no round has
the number. On the digits, where a combination leaves its window its digits do not give it back: the
smallness test's own part stops in front of the lookup; what a filling yields there is not asked
here. (The seated array has digits in range there too, under two hypotheses on public data:
`digitsIn_zzOf`, Johnson/HonestTrace/DigitsAtTrace.lean.)
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Stages

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)

/-! ## 1 The two sorts of elements -/

/-- The program's element, read in the library's field. -/
def inE (x : E) : Cb.Gl.E := OnBytes.Slice.toE x.triple

/-- The library's element, as the program's: three words below the prime. -/
def outE (x : Cb.Gl.E) : E := OnBytes.E.ofTriple (OnBytes.Slice.ofE x)

/-! ## 2 A lookup's keys and bits -/

/-- **A lookup's keys and bits, in the library's field.** -/
structure LookIn where
  /-- of the shift: key number n of the joint key vector; a padding place holds its public key -/
  key : (theta : Cb.Gl.E) → (n : Nat) → Cb.Gl.E
  /-- the row first, the plane second: of the count of row u of the joint table, the bit of plane j
  -/
  bit : (u j : Nat) → Cb.Gl.E

/-- The same as the row's structure: one part of keys. -/
def LookIn.hidden (L : LookIn) : Hidden :=
  { key := fun theta _ n => outE (L.key (inE theta) n)
    bit := fun u j => outE (L.bit u j) }

/-! ## 3 The sampled matrix -/

/-- **The entries in {-1, 0, 1} that round number rng sampled**, as sampled; rng counts as the
challenges heard are counted (in the first chain: the chain's rounds, from 0). Empty where no round
has the number. -/
def tritsAt (heard : List Fmt.Drawn) (rng : Nat) : List Int := ((heard[rng]?).map (·.trits)).getD []

/-! ## 4 The letters -/

/-- **What the lookups' rows are made of.** Here W₀, Xi and Tr are the index, the instance and the
trace, as the chain's halves are handed them. A group's number counts from 0 among its like; a
link's number is the segment's, from 0. -/
structure Sources (W₀ Xi Tr : Type) where
  /-- the trace's reader -/
  cells : Tr → Cells
  /-- the index's reader -/
  weights : W₀ → Weights
  /-- the calls of group g's layers -/
  layers : (g : Nat) → Cells → Weights → LookIn
  /-- the calls of group g's attention -/
  attention : (g : Nat) → Cells → LookIn
  /-- the head's calls: the covered positions and the checked tokens are the instance's -/
  head : Xi → Cells → Weights → LookIn
  /-- the digits of the smallness test of the link with the given number: of the cells and the
  sampled matrix -/
  digits : (link : Nat) → Cells → List Int → LookIn

/-! ## 5 The function wit -/

/-- **Which lookup.** -/
inductive Who where
  | layers (g : Nat)
  | attention (g : Nat)
  | head
  /-- link: the link's number; rng: the number of the round that samples its smallness test's
  matrix, among the challenges heard: public data -/
  | digits (link rng : Nat)
  deriving DecidableEq, Repr

variable {W₀ Rc Xi Tr : Type}

/-- **What a lookup's row is handed**: the wit of `Part.lift`. On the calls it reads no challenge.
-/
def askOf (S : Sources W₀ Xi Tr) : Who → Local W₀ Rc Xi Tr → Ask
  | .layers g, t => fun _ => (S.layers g (S.cells t.trace) (S.weights t.w₀)).hidden
  | .attention g, t => fun _ => (S.attention g (S.cells t.trace)).hidden
  | .head, t => fun _ => (S.head t.x (S.cells t.trace) (S.weights t.w₀)).hidden
  | .digits link rng, t => fun heard =>
    (S.digits link (S.cells t.trace) (tritsAt heard rng)).hidden

/-! ## 6 Tests at synthetic letters -/

namespace WitTest
open OnBytes.Slice (toF toE)

/-- A number as the program's element. -/
def eN (a b c : Nat) : E := OnBytes.E.ofTriple (a.toUInt64, b.toUInt64, c.toUInt64)

/-- A base-field element in the library's extension field. -/
def up (x : Cb.Gl.F) : Cb.Gl.E := ⟨x, 0, 0⟩

/-- Synthetic letters. The trace is a number s, the index a number w, the instance a number x: cell
(k, name, r, c) is s + 1000 k + 100 (the name's length) + 10 r + c; entry (r, c) is w + 10 r + c.
Each sort's key n is: theta + n + a mark of the sort + what it reads at one place. -/
def src : Sources Nat Nat Nat :=
  { cells := fun s => ⟨fun k nm r c => toF (s + 1000 * k + 100 * nm.length + 10 * r + c).toUInt64⟩
    weights := fun w => ⟨fun r c => toF (w + 10 * r + c).toUInt64⟩
    layers := fun g C W =>
      ⟨fun th n => th + up (toF n.toUInt64) + up (C.cell g "af0" 1 2) + up (W.entry 3 4),
       fun u j => up (C.cell g "b" u j)⟩
    attention := fun g C =>
      ⟨fun th n => th + up (toF n.toUInt64) + up (C.cell g "as0" 1 2), fun u j =>
        up (C.cell g "bA" u j)⟩
    head := fun x C W =>
      ⟨fun th n => th + up (toF (n + x).toUInt64) + up (C.cell 24 "hd" 1 2) + up (W.entry 3 4),
       fun u j => up (C.cell 24 "bH" u j)⟩
    digits := fun link C ts =>
      ⟨fun th n => th + up (toF n.toUInt64) + up (C.cell link "b" 0 0) *
        ((ts.getD n 0 : Int) : Cb.Gl.E),
       fun u j => up (toF (ts.length + u * 32 + j).toUInt64)⟩ }

/-- What a half is handed: index 7, coins (), instance 5, trace 20000. -/
def loc : Local Nat Unit Nat Nat := ⟨7, (), 5, 20000⟩

/-- A challenge that holds elements alone; one that holds a sampled matrix. -/
def dE (n : Nat) : Fmt.Drawn := ⟨[(n.toUInt64, 0, 0)], [], [], none⟩
def dT (ts : List Int) : Fmt.Drawn := ⟨[], [], ts, none⟩

-- there and back: it would fail if a coordinate were dropped or two were swapped
#guard outE (inE (eN 3 4 5)) == eN 3 4 5
#guard inE (eN 3 4 5) == (⟨toF 3, toF 4, toF 5⟩ : Cb.Gl.E)
-- layers, group 2, key 9 at the shift (1, 2, 3): 1 + 9 + (20000 + 2000 + 300 + 12) + (7 + 34). It
-- would fail if the shift's coordinates, the group, the trace or the index did not come through
#guard ((askOf src (.layers 2) loc []).key (eN 1 2 3) 0 9) == eN (1 + 9 + 22312 + 41) 2 3
-- the part's number is not read
#guard ((askOf src (.layers 2) loc []).key (eN 1 2 3) 4 9) == eN (1 + 9 + 22312 + 41) 2 3
-- the row first: bit 6 1 is the cell (row 6, column 1) of "b": 20000 + 2000 + 100 + 61; it would
-- fail if the two were swapped (16)
#guard ((askOf src (.layers 2) loc []).bit 6 1) == eN 22161 0 0
#guard ((askOf src (.layers 2) loc []).bit 1 6) != eN 22161 0 0
-- on the calls no challenge is read
#guard ((askOf src (.layers 2) loc [dE 1, dT [1, -1]]).key (eN 1 2 3) 0 9) ==
  ((askOf src (.layers 2) loc []).key (eN 1 2 3) 0 9)
-- attention: the index is not read (by type); 1 + 9 + (20000 + 3000 + 300 + 12)
#guard ((askOf src (.attention 3) loc []).key (eN 1 0 0) 0 9) == eN (1 + 9 + 23312) 0 0
-- the head: the instance is read: 9 + 5; (20000 + 24000 + 200 + 12) + 41
#guard ((askOf src .head loc []).key (eN 0 0 0) 0 9) == eN (9 + 5 + 44212 + 41) 0 0
#guard ((askOf src .head { loc with x := 6 } []).key (eN 0 0 0) 0 9) != eN (9 + 5 + 44212 + 41) 0 0
-- the digits read the sample by its number: round 1 of three sampled [1, 0, -1]; cell (4, "b", 0,
-- 0) is 24100: key 0 is 0 + 24100; key 1 is 1; key 2 is 2 - 24100, in the field
#guard tritsAt [dE 8, dT [1, 0, -1], dT [1, 1, 1]] 1 == [1, 0, -1]
#guard tritsAt [dE 8, dT [1, 0, -1]] 0 == []
#guard tritsAt [dE 8] 5 == []
#guard ((askOf src (.digits 4 1) loc [dE 8, dT [1, 0, -1], dT [1, 1, 1]]).key (eN 0 0 0) 0 0) ==
  eN 24100 0 0
#guard ((askOf src (.digits 4 1) loc [dE 8, dT [1, 0, -1], dT [1, 1, 1]]).key (eN 0 0 0) 0 1) ==
  eN 1 0 0
#guard ((askOf src (.digits 4 1) loc [dE 8, dT [1, 0, -1], dT [1, 1, 1]]).key (eN 0 0 0) 0 2) ==
  eN (2 ^ 64 - 2 ^ 32 + 1 + 2 - 24100) 0 0
-- at another number another sample: other keys
#guard ((askOf src (.digits 4 2) loc [dE 8, dT [1, 0, -1], dT [1, 1, 1]]).key (eN 0 0 0) 0 1) ==
  eN 24101 0 0
-- the bits depend on the sample too (here: on its length, 3): 3 + 2 * 32 + 5
#guard ((askOf src (.digits 4 1) loc [dE 8, dT [1, 0, -1], dT [1, 1, 1]]).bit 2 5) == eN 72 0 0

end WitTest

end ProofFile.Honest.K3
