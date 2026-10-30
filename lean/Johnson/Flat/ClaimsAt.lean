-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ClaimsAt.lean: the committed matrix's two numbers, read out of a declared structure.

Definitions. Johnson/Flat/Claims.lean takes the numbers m0 and k_lo of the committed matrix as
`MatrixNums`. A declared structure (Decl/Declared.lean) holds them as words of a hashed parameter
item: "the test on the table", of a key file's first chain (docs/format/09-key-and-leaf-files.md,
R13.13). Here they are read out of that item's bytes by the program's own reader of the item
(`Params.readLin`, OnBytes/Params/Items.lean).

Main names:
  `matrixNumsIn c`: the two numbers, and v, in a chain's item; nothing if the chain has no such item
    or the reader refuses it.
  `matrixNumsOf D`: those of the key file's first chain, if the three other chains that have the
    item (the key file's shared chain, the proof file's first and shared chain) give the same, and
    the item's v is that of the declared tables' shape.
Limits: nothing is proved here.

-/
import Johnson.Flat.Claims
import OnBytes.Params.Items
import Fmt.Parsed

set_option autoImplicit false

namespace OnBytes.Flat

/-- The committed matrix's rows and k_lo, and the logarithm v of the table's rows, in a chain's item
"the test on the table". -/
def matrixNumsIn (c : Fmt.ChainDecl) : Option (Nat × Nat × Nat) :=
  ((c.others.lookup "the test on the table").bind Params.readLin).map fun l =>
    (l.matrixRows, l.kLo, l.fold.index.v)

/-- The committed matrix's numbers, out of a declared structure. -/
def matrixNumsOf (D : Fmt.Declared) : Option MatrixNums :=
  (matrixNumsIn D.key.first).bind fun n =>
    if [D.key.shared, D.proof.first, D.proof.shared].all (matrixNumsIn · == some n) &&
        n.2.2 == D.table.logRows then
      some ⟨n.1, n.2.1⟩
    else none

end OnBytes.Flat
