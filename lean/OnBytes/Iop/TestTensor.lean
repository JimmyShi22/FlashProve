-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/TestTensor.lean: tests of OnBytes/Iop/Tensor.lean at small sizes. That file's head
explains the words used here (tensor, form, dense variable, slice, choice).
Most tests compare a function on tensors or forms with the same thing computed entry by entry from
Tensor.entry or Form.entry. Some compare Form.fixLow and Form.dot with their plain versions, or ask
that a bad input is refused. The verifier program does not import this file.
-/
import OnBytes.Iop.Tensor

namespace OnBytes.TestTensor

/-- A fixed element of the extension field E for each n. The tests use it as an arbitrary one. -/
def rnd (n : Nat) : E :=
  E.mk3 (normF (UInt64.ofNat (n * 2654435761 + 12345))) (normF (UInt64.ofNat (n * n * 40503 + 7)))
    (normF (UInt64.ofNat (n * 97 + n * n * n)))

/-- The elements rnd (1000 s), .., rnd (1000 s + count - 1). -/
def rv (s count : Nat) : List E := (List.range count).map fun i => rnd (1000 * s + i)

/-- The sum of a list of elements. -/
def sumE (l : List E) : E := l.foldl addE zeroE

/-- A tensor of product form on four variables. -/
def t4 : Tensor := { scalar := rnd 1, pairs := (rv 2 4).zip (rv 3 4) }

/-- A tensor on five variables of which the variables 1 and 3 are dense. -/
def d5 : Tensor :=
  { scalar := rnd 4
    pairs := [(rnd 5, rnd 6), (oneE, oneE), (rnd 7, rnd 8), (oneE, oneE), (rnd 9, rnd 10)]
    denseVars := [1, 3], values := (rv 11 7).toArray, first := 2 }

/-- A tensor on three variables, all dense. -/
def d3 : Tensor := (({ scalar := rnd 12 } : Tensor).pushDense 3).setValues (rv 13 8).toArray 0

/-- A form on five variables: two tensors and three single entries, two of them at index 7. -/
def f5 : Form :=
  ((((Form.ofTensor d5).add (t4.insertChoice 2 1 1)).addEntry 7 (rnd 20)).addEntry 30
    (rnd 21)).addEntry 7 (rnd 22)

/-- All entries of a tensor. -/
def all (v : Tensor) : List E := (List.range (2 ^ v.vars)).map v.entry

/-- The vector given by the function entry, on vars variables, with its low variables fixed at g. -/
def fixedBy (entry : Nat → E) (vars : Nat) (g : List E) : List E :=
  (List.range (2 ^ (vars - g.length))).map fun j =>
    sumE ((List.range (2 ^ g.length)).map fun low =>
      eqWeight g low (entry (low + 2 ^ g.length * j)))

#guard t4.ok && d5.ok && d3.ok && t4.vars == 4 && d3.vars == 3
#guard !({ d5 with first := 4 } : Tensor).ok
#guard !({ d5 with denseVars := [1, 1] } : Tensor).ok
#guard !({ d5 with denseVars := [0, 3] } : Tensor).ok
-- at most 63 variables
#guard ({ pairs := List.replicate 63 (oneE, zeroE) } : Tensor).ok
#guard !({ pairs := List.replicate 64 (oneE, zeroE) } : Tensor).ok

-- the equality vector and the product vector
#guard (Tensor.eq (rv 30 3)).entry 5 ==
  mulE (mulE (rnd 30000) (subE oneE (rnd 30001))) (rnd 30002)
#guard (Tensor.product [3, 5, 7] (ofF 2)).entry 5 == ofF 42
#guard sumE (all (Tensor.eq (rv 30 3))) == oneE

-- addTo and part, which write a tensor out, against the entries
#guard (t4.addTo (Array.replicate 16 zeroE)).toList == all t4
#guard (d5.addTo (Array.replicate 32 zeroE)).toList == all d5
#guard (d3.addTo (Array.replicate 8 zeroE)).toList == (rv 13 8).map (mulE (rnd 12))
#guard ((t4.insertChoice 1 2 2).addTo (Array.replicate 64 zeroE)).toList ==
  all (t4.insertChoice 1 2 2)
#guard (t4.part 1 2).toList ==
  (List.range 4).map fun j => ({ pairs := (t4.pairs.drop 1).take 2 } : Tensor).entry j

-- insertChoice: the old entries stand where the inserted bits have the chosen value, 0 elsewhere
#guard (List.range 64).all fun j =>
  (t4.insertChoice 1 2 2).entry j ==
    if j / 2 % 4 == 2 then t4.entry (j % 2 + 2 * (j / 8)) else zeroE
#guard (List.range 128).all fun j =>
  (d5.insertChoice 2 2 1).entry j ==
    if j / 4 % 4 == 1 then d5.entry (j % 4 + 4 * (j / 16)) else zeroE

-- fixing low variables
#guard (List.range 5).all fun c => all (t4.fixLow (rv 40 c)) == fixedBy t4.entry 4 (rv 40 c)
#guard (List.range 6).all fun c => all (d5.fixLow (rv 41 c)) == fixedBy d5.entry 5 (rv 41 c)
#guard (List.range 4).all fun c => all (d3.fixLow (rv 42 c)) == fixedBy d3.entry 3 (rv 42 c)
#guard [t4.mle (rv 43 4)] == fixedBy t4.entry 4 (rv 43 4)
#guard [d5.mle (rv 44 5)] == fixedBy d5.entry 5 (rv 44 5)

/-- The entries of the sum of the tensors from tensorBelow; nothing if it returns nothing. -/
def cutAll (v : Tensor) (start count len : Nat) : Option (List E) :=
  (tensorBelow v start count len).map fun l =>
    (List.range (2 ^ v.vars)).map fun j => sumE (l.map (·.entry j))

/-- v with 0 at each index whose count bits from bit start on give a number not below len. -/
def cutBy (v : Tensor) (start count len : Nat) : List E :=
  (List.range (2 ^ v.vars)).map fun j =>
    if j / 2 ^ start % 2 ^ count < len then v.entry j else zeroE

#guard (List.range 9).all fun len => cutAll t4 1 3 len == some (cutBy t4 1 3 len)
#guard (List.range 17).all fun len => cutAll t4 0 4 len == some (cutBy t4 0 4 len)
#guard (List.range 9).all fun len => cutAll d3 0 3 len == some (cutBy d3 0 3 len)
#guard (List.range 9).all fun len =>
  cutAll (t4.insertChoice 1 1 1) 0 3 len == some (cutBy (t4.insertChoice 1 1 1) 0 3 len)
#guard (tensorBelow t4 0 4 17).isNone && (tensorBelow t4 2 3 1).isNone
-- no cut: of the variables 0 and 1 of d5, one is dense and the other is not
#guard (tensorBelow d5 0 2 3).isNone
-- as many summands as len has bits that are 1
#guard ((tensorBelow t4 0 4 11).map (·.length)) == some 3

-- how a vector lies in a table
#guard (List.range 32).all fun j =>
  let l : VectorLay := ⟨2, 3, true⟩
  l.entryAt (l.index j) == j && l.index j == j / 8 + (j % 8) * 4
#guard (List.range 32).all fun j => (⟨2, 3, false⟩ : VectorLay).index j == j
#guard [true, false].all fun high =>
  let l : VectorLay := ⟨2, 3, high⟩
  (List.range 32).all fun j =>
    (l.onTable t4).entry (l.index j) == (if j < 16 then t4.entry j else zeroE) &&
    (l.onTable d5).entry (l.index j) == d5.entry j &&
    (l.onTable d3).entry (l.index j) == (if j < 8 then d3.entry j else zeroE)
#guard [d3, d5, t4].all fun v => ((⟨2, 3, true⟩ : VectorLay).onTable v).ok

-- forms
#guard f5.fits 5 && !f5.fits 4 && !f5.fits 6
#guard f5.entry 7 == addE (addE (addE (d5.entry 7) ((t4.insertChoice 2 1 1).entry 7)) (rnd 20))
  (rnd 22)
#guard (f5.writeOut 5).toList == (List.range 32).map f5.entry
#guard (List.range 6).all fun c =>
  (List.range (2 ^ (5 - c))).map ((f5.fixLow (rv 50 c)).entry) == fixedBy f5.entry 5 (rv 50 c)
#guard (List.range (2 ^ 3)).map ((f5.fixLow (rv 50 2) (rnd 51)).entry) ==
  (fixedBy f5.entry 5 (rv 50 2)).map (mulE (rnd 51))
#guard [f5.mle (rv 52 5)] == fixedBy f5.entry 5 (rv 52 5)
#guard (List.range 128).all fun j =>
  (f5.insertChoice 3 2 3).entry j ==
    if j / 8 % 4 == 3 then f5.entry (j % 8 + 8 * (j / 32)) else zeroE
#guard (List.range 32).all fun j =>
  (f5.addForm f5 (rnd 53)).entry j == addE (f5.entry j) (mulE (f5.entry j) (rnd 53))
#guard f5.dot 5 (rv 54 32).toArray ==
  sumE ((List.range 32).map fun j => mulE (f5.entry j) (rnd (54000 + j)))
-- Tensor.fixLow on a slice, against the entries: several orders of dense variables, three starts
/-- A tensor on seven variables with the dense variables dv, whose slice begins at entry first. -/
def dense7 (dv : List Nat) (first : Nat) : Tensor :=
  { scalar := rnd 70, pairs := (List.range 7).map fun t =>
      if dv.contains t then (oneE, oneE) else (rnd (71 + t), rnd (81 + t)),
    denseVars := dv, values := (rv 72 40).toArray, first := first }

#guard [[0, 1, 2], [4, 5, 0, 1], [5, 0, 6, 2, 1], [2], [6, 3], [3, 4, 5, 6, 0]].all fun dv =>
  [0, 3, 8].all fun first =>
    (dense7 dv first).ok &&
    (List.range 8).all fun c =>
      all ((dense7 dv first).fixLow (rv 74 c)) == fixedBy (dense7 dv first).entry 7 (rv 74 c)
-- tensorBelow where the cut's variables are all dense and further dense variables lie outside it
#guard (List.range 5).all fun len =>
  cutAll (dense7 [5, 0, 6, 2, 1] 3) 5 2 len == some (cutBy (dense7 [5, 0, 6, 2, 1] 3) 5 2 len)
#guard (List.range 9).all fun len =>
  cutAll (dense7 [5, 0, 6, 2, 1] 3) 0 3 len == some (cutBy (dense7 [5, 0, 6, 2, 1] 3) 0 3 len)
-- no cut: of the variables 4 and 5, only 5 is dense
#guard (tensorBelow (dense7 [5, 0, 6, 2, 1] 3) 4 2 3).isNone
-- tensors that share slices: fixLow, which folds each distinct slice once, against fixLowPlain
/-- On seven variables: three tensors hold one slice, two another with equal first and denseVars. -/
def shared7 : Form :=
  let a := dense7 [5, 0, 6, 2, 1] 3
  let b := { a with values := (rv 78 40).toArray }
  [a, b, a.scale (rnd 79), { a with pairs := a.pairs.map fun p => (p.2, p.1) }, b.scale (rnd 80),
    dense7 [2] 0, t4.insertChoice 4 3 5].foldl Form.add ({} : Form) |>.addEntry 9 (rnd 81)

#guard shared7.fits 7
#guard (List.range 8).all fun c =>
  (shared7.fixLow (rv 82 c) (rnd 83)).writeOut (7 - c) ==
    (shared7.fixLowPlain (rv 82 c) (rnd 83)).writeOut (7 - c)
#guard (shared7.fixLow (rv 82 3)).tensors.map (·.values.size) ==
  (shared7.fixLowPlain (rv 82 3)).tensors.map (·.values.size)
#guard (shared7.tensors.foldl (fun s v => Form.fixLowShared (rv 82 3) s v) ([], {})).2.size == 3
-- two slices under one key: they differ at no entry that the key holds. A slice whose key another
-- slice has taken is folded by itself; fixLow must still agree with fixLowPlain
/-- shared7 and one more tensor: dense7 [5, 0, 6, 2, 1] 3 with entry 1 of its slice changed. -/
def sameKey7 : Form :=
  let a := dense7 [5, 0, 6, 2, 1] 3
  shared7.add { a with values := a.values.modify 4 fun x => addE x oneE }

#guard (List.range 8).all fun c =>
  (sameKey7.fixLow (rv 82 c) (rnd 83)).writeOut (7 - c) ==
    (sameKey7.fixLowPlain (rv 82 c) (rnd 83)).writeOut (7 - c)
#guard (sameKey7.tensors.foldl (fun s v => Form.fixLowShared (rv 82 3) s v) ([], {})).2.size == 3

-- addTo against the entries, on arrays that are shorter, as long and longer than the vector
#guard [t4, d3, d5, dense7 [5, 0, 6, 2, 1] 3, t4.insertChoice 1 2 2,
    { t4 with scalar := zeroE }].all fun v =>
  [0, 5, 2 ^ v.vars, 2 ^ v.vars + 3].all fun n =>
    (v.addTo (rv 77 n).toArray).toList == (rv 77 n).zipIdx.map fun y =>
      if y.2 < 2 ^ v.vars then addE y.1 (v.entry y.2) else y.1

-- the fast inner product against the plain one
/-- f5 and seven tensors that Tensor.dotInF serves, with pairs in the base field: one of the form of
a generator matrix's row, five from two cuts of it, and one with a choice inserted. -/
def g5 : Form :=
  let gen := Tensor.product [3, 9, 81, 6561, 43046721] (rnd 60)
  let cuts := ((tensorBelow gen 0 5 21).getD []) ++ ((tensorBelow gen 1 3 5).getD [])
  cuts.foldl Form.add ((f5.add gen).add ((Tensor.product [5, 25, 625] (rnd 61)).insertChoice 1 2 2))

#guard g5.fits 5 && (g5.tensors.filter fun v => (v.dotInF #[]).isSome).length == 7
#guard [32, 31, 17, 1, 0].all fun n =>
  g5.dot 5 (rv 62 n).toArray == g5.dotPlain 5 (rv 62 n).toArray
#guard g5.dot 5 (rv 62 40).toArray == g5.dotPlain 5 (rv 62 40).toArray
#guard g5.dotPlain 5 (rv 62 32).toArray ==
  sumE ((List.range 32).map fun j => mulE (g5.entry j) (rnd (62000 + j)))
#guard (Tensor.product [] (rnd 63)).dotInF #[rnd 64] == some (mulE (rnd 63) (rnd 64))
#guard (t4.dotInF #[]).isNone && (d3.dotInF #[]).isNone
#guard mergeEntries [(3, ofF 1), (1, ofF 2), (3, ofF 4), (0, ofF 8), (1, ofF 16)] ==
  [(0, ofF 8), (1, ofF 18), (3, ofF 5)]

end OnBytes.TestTensor
