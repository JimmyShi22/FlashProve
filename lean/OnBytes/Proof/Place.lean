-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/Place.lean: a request's place in its batch, and the binding tree's root.

The requests of a batch share one chain. That chain must depend on every request's first chain.
So the prover puts the closing value (the seal) of each first chain into a leaf of a hash tree, the
binding tree, and starts the shared chain from the tree's root. A file shows one leaf's path: the
place, the leaf's salt, and one sibling for each level, the leaf's sibling first
(docs/format/FORMAT.md, R14.6, R14.7, R7.18). A key file has such a tree of depth 0 (R13.6).

Like the strict reader, this file reads bytes and calls the hash. It refuses for form only, and it
compares the root with nothing: the root is no byte of the file (R14.7), and every well-formed path
leads to some root. The caller makes that root an item of the shared chain's statement and puts it
in the place of that chain's random bytes, so that another root gives another chain. The depth is
the shape's, not the file's. A leaf's hash takes in the depth with the place, and leaves and inner
vertices are hashed under different numbers.
The C++ counterpart is lin_binding_root (blocks/iop/lin.h).

Main definitions: `bindingOk`, `Place`, `climb`, `readPlace`.
-/
import OnBytes.Params.Items

namespace OnBytes.Proof

/-- The name of the parameter item that holds the tree's shape. -/
def bindingName : String := "binding tree"

/-- True if the format admits the shape: at most 48 levels, and a salt of an admitted length. -/
def bindingOk (s : Params.LinBindingShape) : Bool :=
  Fmt.depthOK s.logLeaves && Fmt.saltLenOK s.saltBytes

/-- What the bytes between a first chain and a shared chain give. -/
structure Place where
  /-- the request's place among the tree's leaves -/
  place : Nat
  /-- the root to which the leaf and its path lead -/
  root : ByteArray
  /-- the number of the tree's leaves -/
  places : Nat
  /-- the place of the first byte after the path -/
  next : Nat

/-- Goes up from a vertex to the root. `levels` is the number of levels that are left, x the value
of the vertex, p its place in its level, i the place in b of the next sibling. At each level the
lowest bit of p says on which side the sibling is: at 1 it is the left child. -/
def climb (cfg b : ByteArray) : (levels : Nat) → (x : ByteArray) → (p i : Nat) →
    Option (ByteArray × Nat)
  | 0, x, _, i => some (x, i)
  | levels + 1, x, p, i =>
    match Fmt.slice b i 32 with
    | none => none
    | some sib =>
      let up := if p % 2 == 1 then Fmt.vertexB cfg sib x else Fmt.vertexB cfg x sib
      climb cfg b levels up (p / 2) (i + 32)

/-- Reads a place at byte i of b. cfg is the digest of the public files and `closing` the seal of
the first chain. Returns nothing if the format does not admit the shape, if the bytes end early, or
if the place is not below the number of leaves. -/
def readPlace (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : Nat) : Option Place :=
  if !bindingOk s then none
  else
    match Fmt.rdWord b i with
    | none => none
    | some (w, i1) =>
      if 2 ^ s.logLeaves ≤ w.toNat then none
      else
        match Fmt.slice b i1 s.saltBytes with
        | none => none
        | some salt =>
          (climb cfg b s.logLeaves (Fmt.bindLeaf s.logLeaves w.toNat cfg closing salt) w.toNat
            (i1 + s.saltBytes)).map fun x => ⟨w.toNat, x.1, 2 ^ s.logLeaves, x.2⟩

end OnBytes.Proof
