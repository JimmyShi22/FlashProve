-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/ToyData.lean: THE CLOSING OF A SEGMENT (K10): THE DATA OF TWO TOYS: a small
input, coins by number, the place's parameters, the statement in front of "BAT" with rows whose
targets are true, and the request's frame: at k = 3, h = 0 (with a kept member) and, under `H`, at
k = 2, h = 1. Definitions with code; no theorem; no honest side's frame in them.

WHO READS THEM: Johnson/Desc/K10/Honest/BaseToys.lean, HoldsToy.lean (lemmas on the verifier's own
text); Johnson/Desc/ProofFile/Honest/K10/Toy.lean, ToyH.lean and the toys over these (the honest
side's frame at work; a tree may hold this file without them).

Limits. Made-up data. Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.First.Close.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Toy
open OnBytes (E zeroE oneE addE subE mulE Statement)
open VerifiableInference.Desc.First.Close (Par)

def e (n : Nat) : E := E.ofTriple (n.toUInt64, 0, 0)
def dE (x : Nat) : Fmt.Drawn := ⟨[(x.toUInt64, 0, 0)], [], [], none⟩
def dE3 (x y z : Nat) : Fmt.Drawn := ⟨[(x.toUInt64, y.toUInt64, z.toUInt64)], [], [], none⟩

/-- The small record: what this kind's part needs of the prover's input. -/
structure Ask where
  /-- the oracle message's number, the row, the place -/
  cell : Nat → Nat → Nat → E

def ask₀ : Ask := ⟨fun o b p => e (1000 + 100 * o + 10 * b + p)⟩
def ask₁ : Ask := ⟨fun o b p => E.ofTriple ((3 * o + 7 * b + 31 * p + 2).toUInt64, (o + p).toUInt64,
  (b * p + 1).toUInt64)⟩

/-- The owner's 41 coins, message by message: A (numbers 0 to 19): nine of three tails, the mask
row's eight entries, its tail's three · B (20 to 23): its tail's three, the pad · C (24 to 30): six
of two tails, the pad · the fresh mask (31 to 40): the seven coefficients, its tail's three. In the
statement the oracle messages have the numbers A 0, the fresh mask 1, B 2, C 3. -/
def coin₀ : Nat → E := fun j => e (30 + j)
def coin₁ : Nat → E := fun j => E.ofTriple ((7 * j + 3).toUInt64, (j * j).toUInt64, 5)

def P : Par := { link := 0, piece := 4, k := 3, h := 0, rows := 4, workField := 0, workClose := 0
                 sent := [] }

/-- The rows of the four oracle messages' main tables: A, the fresh mask, B, C. -/
def mainRows (o : Nat) : Nat := [3, 0, 1, 2].getD o 0
def rowBits (o : Nat) : Nat := [2, 0, 0, 1].getD o 0

/-- The second making, off the owner's coins by their numbers: an entry of a main row's message. -/
def mainT (w : Ask) (cn : Nat → E) (o b p : Nat) : E :=
  if o == 2 && p == 7 then cn 23 else if o == 3 && b == 1 && p == 7 then cn 30 else w.cell o b p

/-- The entry at an index of an oracle message's own table. -/
def entryT (w : Ask) (cn : Nat → E) (o : Nat) (part : OnBytes.Part) (i : Nat) : E :=
  match part with
  | .mask => if o == 0 && i < 8 then cn (9 + i) else zeroE
  | .main =>
    let b := i % 2 ^ rowBits o
    if b < mainRows o && i / 2 ^ rowBits o < 8 then mainT w cn o b (i / 2 ^ rowBits o) else zeroE

/-- The open rows, without their targets. Between them they read every entry of every member's
message. -/
def rawRows : List OnBytes.Row :=
  [{ units := #[⟨0, .main, 0, e 1⟩, ⟨0, .mask, 0, e 1⟩] },
   { units := ((List.range 8).map fun j => (⟨0, .mask, j, e (j + 2)⟩ : OnBytes.Single)).toArray ++
       ((List.range 8).map fun j => (⟨2, .main, j, e (j + 11)⟩ : OnBytes.Single)).toArray },
   { terms := #[⟨0, .main, OnBytes.Tensor.eq [e 2, e 3, e 5, e 7, e 11]⟩] },
   { units := ((List.range 16).map fun j => (⟨3, .main, j, e (j + 21)⟩ : OnBytes.Single)).toArray
     terms := #[⟨3, .main, OnBytes.Tensor.eq [e 13, e 17, e 19, e 23]⟩] }]

/-- A row's true value. -/
def valueOf (w : Ask) (cn : Nat → E) (r : OnBytes.Row) : E :=
  let a := r.units.foldl (fun s u => addE s (mulE u.coeff (entryT w cn u.oracle u.part u.index)))
    zeroE
  r.terms.foldl (fun s t =>
    (List.range (2 ^ t.v.vars)).foldl (fun s j =>
      addE s (mulE (t.v.entry j) (entryT w cn t.oracle t.part j))) s) a

/-- **The statement in front of "BAT"**, with the rows' targets true at an input and coins. -/
def stOf (w : Ask) (cn : Nat → E) : Statement :=
  { codes := { base := #[⟨4, 8, 3⟩], mask := #[⟨4, 8, 3⟩] }
    oracles := #[
      { shape := { code := 0, mainRows := 3, mainDeg := 3, maskRows := 1, maskCode := 0,
                   answers := 1 } },
      { shape := { code := OnBytes.noId, mainRows := 0, maskRows := 1, maskCode := 0,
                   answers := 0 } },
      { shape := { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0, maskCode := 0,
                   answers := 1 } },
      { shape := { code := 0, mainRows := 2, mainDeg := 3, maskRows := 0, maskCode := 0,
                   answers := 1 } }]
    groups := #[{ code := 0, maskCode := 0, members := #[0, 2, 3], kept := #[false, false, true]
                  rows := (rawRows.map fun r => { r with target := valueOf w cn r }).toArray }] }

/-- The frame at the end of link 0, which has no message of its own in the shape (so no moment). -/
def fr : OnBytes.ReqFrame :=
  { shape := { (default : OnBytes.Params.ReqShape) with
      code := 0, maskCode := 0, link := [{ plain := 0, messages := [] }] }
    groups := #[{ k := 3, h := 0 }], next := .laterOrClose, link := 0, moment := 0, group := 0
    mask := some 1 }

namespace H

def P : Par := { link := 0, piece := 4, k := 2, h := 1, rows := 2, workField := 0, workClose := 0
                 sent := [] }

/-- The second making: the entry at an index of an oracle message's own table: A is number 0, D
number 2. -/
def entryT (w : Ask) (cn : Nat → E) (o : Nat) (part : OnBytes.Part) (i : Nat) : E :=
  match part with
  | .mask => if i < 8 then (if o == 0 then cn (6 + i) else if o == 2 then cn (20 + i) else zeroE)
    else zeroE
  | .main =>
    if o == 0 && i < 16 then w.cell 0 (i % 2) (i / 2) else if o == 2 && i < 8 then w.cell 2 0 i
    else zeroE

def units (o : Nat) (part : OnBytes.Part) (n first : Nat) : Array OnBytes.Single :=
  ((List.range n).map fun j => (⟨o, part, j, e (j + first)⟩ : OnBytes.Single)).toArray

def rawRows : List OnBytes.Row :=
  [{ units := units 0 .main 16 1 ++ units 0 .mask 8 31 },
   { units := units 2 .main 8 51 ++ units 2 .mask 8 71
     terms := #[⟨2, .mask, OnBytes.Tensor.eq [e 2, e 3, e 5]⟩] }]

def valueOf (w : Ask) (cn : Nat → E) (r : OnBytes.Row) : E :=
  let a := r.units.foldl (fun s u => addE s (mulE u.coeff (entryT w cn u.oracle u.part u.index)))
    zeroE
  r.terms.foldl (fun s t =>
    (List.range (2 ^ t.v.vars)).foldl (fun s j =>
      addE s (mulE (t.v.entry j) (entryT w cn t.oracle t.part j))) s) a

def stOf (w : Ask) (cn : Nat → E) : Statement :=
  { codes := { base := #[⟨4, 8, 3⟩], mask := #[⟨4, 8, 3⟩] }
    oracles := #[
      { shape := { code := 0, mainRows := 2, mainDeg := 3, maskRows := 1, maskCode := 0,
                   answers := 1 } },
      { shape := { code := OnBytes.noId, mainRows := 0, maskRows := 2, maskCode := 0,
                   answers := 0 } },
      { shape := { code := 0, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 0,
                   answers := 1 } }]
    groups := #[{ code := 0, maskCode := 0, members := #[0, 2], kept := #[false, false]
                  rows := (rawRows.map fun r => { r with target := valueOf w cn r }).toArray }] }

def fr : OnBytes.ReqFrame := { Toy.fr with groups := #[{ k := 2, h := 1 }] }

end H

end ProofFile.Honest.K10.Toy
