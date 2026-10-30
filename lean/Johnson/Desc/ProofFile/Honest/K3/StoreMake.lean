-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/StoreMake.lean: the store of one lookup (`Store`,
Honest/K3/KeptTypes.lean) made once of the input, the shift and alpha; the same of the input and the
challenges heard; and the sentence "the store that is passed on is that store". Definitions with
code, and one definition that is meant as a hypothesis. No theorem.

Terms. Honest/K3/GLOSSARY.md. In this file: a lookup's two sides are its keys and its table; each
side has a product tree over its leaves (Honest/K3/JobsFast.lean, under "How indices and points
lie"). In a list of levels the highest level stands first. On the key side the highest is the root.
On the table side only the d levels above the leaves are made: the highest has 2 ^ mu entries, the
planes' roots.

Why. Honest/K3/JobsFast.lean makes a side's leaves and the tree's levels anew at every call. A row
that passes a store on (`RowOwn`) makes them once for each lookup.

What is defined.
  `Fast.lvlsFrom`, `Fast.lvlsUp`: given leaves and the n levels above them, the highest first, by n
    calls of `up`: each level is made of the level below it, which is kept.
  `Fast.storeOf`: the store. The bits, the table side's factors and each part's leaves are asked of
    `Fast.srcOf`, each once; no text of theirs is written a second time. The table side's leaves are
    made of the two tables that are kept, by the line of `Fast.srcOf`.
  `storeAt`: the store at the shift and alpha as they are read off the challenges heard, once. Meant
    for the move at `Stage.alpha` of a row that keeps a store: behind that round's challenge.
  `StoreOk`: where a store is passed on, it is `storeAt` at the input and the challenges heard.
    Where none is passed on it holds.

Imported, through Honest/K3/Row.lean and Honest/K3/JobsFast.lean: Honest/Sum.lean, Honest/Side.lean,
Honest/Frame.lean and Honest/ForKinds.lean.

Users. Honest/K3/Law/Keep/StoreLaw.lean (the store's fields are those of `Fast.srcOf`; `StoreOk`
has a member with a store), Honest/K3/Law/Keep/StoreStays.lean (`StoreOk` stays as more is heard),
Honest/K3/Law/Keep/StoreGives.lean (`StoreOk` gives each sort's own hypothesis),
Honest/K3/StoreToy.lean [not in this library] (guards). `storeAt` fills the letter `Keeps.store` of
the row beside `lookRow` (Honest/K3/RowKeep.lean) in Honest/K3/RowKeepFill.lean.

Limits. Nothing rejects. A part's number from the number of parts on, and a level's number beyond
the leaves', have no entry in the store: a reader by `getD` finds the empty array there, where
`Fast.srcOf` makes something. `storeAt` reads the shift and alpha off the challenges by the letter
R: that R finds them there is not said here. Room, reckoned and not measured, in elements: less than
twice the keys' leaves, less than twice the table side's leaves, and that side's leaves twice more
for the bits and the factors. How long the making takes is not said and has not been measured.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.JobsFast
import Johnson.Desc.ProofFile.Honest.K3.KeptTypes
import Johnson.Desc.ProofFile.Honest.K3.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E addE mulE oneE)

namespace Fast

/-- The level a, the n levels above it, and what was gathered: the highest first. One call of `up`
for each level above a. -/
def lvlsFrom : Nat → Array E → List (Array E) → List (Array E)
  | 0, a, acc => a :: acc
  | n + 1, a, acc => lvlsFrom n (up a) (a :: acc)

/-- **The leaves and the n levels above them**, n + 1 entries, the highest first: entry j lies n - j
levels above the leaves; entry n: the leaves. -/
def lvlsUp (n : Nat) (leaves : Array E) : Array (Array E) := (lvlsFrom n leaves []).toArray

/-- **The store of a lookup**, of the face's numbers, the table's rows, the input, the shift and
alpha. -/
def storeOf (f : LFace) (row : E → Nat → E) (w : Hidden) (theta alpha : E) : Store :=
  let S := srcOf f row w theta alpha
  let b := S.bitTab ()
  let a := S.facTab ()
  { keyLvls := (Array.range f.parts.length).map fun i =>
      lvlsUp (f.parts.getD i 0) (S.keyLvl i (f.parts.getD i 0))
    tabLvls := lvlsUp f.d (Array.zipWith (fun b a => addE oneE (mulE b a)) b a)
    bitTab := b
    facTab := a }

end Fast

/-- **The store of a lookup at its place**, of the input and the challenges heard: the points are
read once. -/
def storeAt (R : Reads) (row : E → Nat → E) (a : At) : Ask → List Fmt.Drawn → Store :=
  fun w h =>
  let p := R.pts a.face a.base h
  Fast.storeOf a.face row (w p.heard) p.theta p.alpha

/-- **The store that is passed on is the lookup's store** at the input and the challenges h. A
definition, meant as a hypothesis. Where none is passed on it holds; that it holds of the store that
`storeAt` makes is shown in Honest/K3/Law/Keep/StoreLaw.lean (`storeOk_at`). -/
def StoreOk (R : Reads) (row : E → Nat → E) (a : At) (w : Ask) (h : List Fmt.Drawn)
    (x : Option Store) : Prop :=
  ∀ st, x = some st → st = storeAt R row a w h

end ProofFile.Honest.K3
