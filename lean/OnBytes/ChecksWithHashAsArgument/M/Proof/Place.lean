-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Proof/Place.lean: CUT OUT BY A PROGRAM FROM A TEXT WRITTEN BY HAND: the program
chooses the declarations that differ from the port's and turns names; it does not make the turn over
m. The definitions of OnBytes/Proof/Place.lean that hash, or hand a hash on, written once more
over a monad m in which the hash is asked. The port's own file is untouched. What does not hash is
the port's own. The text written by hand is this project's authors' own rewriting of the port's
file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM

namespace OnBytes.TwoPort.M.Proof

open OnBytes.Proof

/-- Goes up from a vertex to the root. `levels` is the number of levels that are left, x the value
of the vertex, p its place in its level, i the place in b of the next sibling. At each level the
lowest bit of p says on which side the sibling is: at 1 it is the left child. -/
def climb {m : Type → Type} [Monad m] (hh : HashM m) (cfg b : ByteArray) :
    (levels : Nat) → (x : ByteArray) → (p i : Nat) → m (Option (ByteArray × Nat))
  | 0, x, _, i => pure (some (x, i))
  | levels + 1, x, p, i =>
    match Fmt.slice b i 32 with
    | none => pure none
    | some sib => do
      let up ← if p % 2 == 1 then Fmt.vertexBW hh cfg sib x else Fmt.vertexBW hh cfg x sib
      climb hh cfg b levels up (p / 2) (i + 32)

/-- Reads a place at byte i of b. cfg is the digest of the public files and `closing` the seal of
the first chain. Returns nothing if the format does not admit the shape, if the bytes end early, or
if the place is not below the number of leaves. -/
def readPlace {m : Type → Type} [Monad m] (hh : HashM m) (s : Params.LinBindingShape)
    (cfg closing b : ByteArray) (i : Nat) : m (Option Place) :=
  if !bindingOk s then pure none
  else
    match Fmt.rdWord b i with
    | none => pure none
    | some (w, i1) =>
      if 2 ^ s.logLeaves ≤ w.toNat then pure none
      else
        match Fmt.slice b i1 s.saltBytes with
        | none => pure none
        | some salt => do
          let leaf ← Fmt.bindLeafW hh s.logLeaves w.toNat cfg closing salt
          let r ← climb hh cfg b s.logLeaves leaf w.toNat (i1 + s.saltBytes)
          pure (r.map fun x => ⟨w.toNat, x.1, 2 ^ s.logLeaves, x.2⟩)

end OnBytes.TwoPort.M.Proof
