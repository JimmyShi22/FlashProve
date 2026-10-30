-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SpentOf.lean: the coins that the parts of a list spend: two
definitions in a file of their own, low in the frame. On `Part`, `RowCoins` (Honest/Frame.lean) and
`coinsE` (Honest/Sum.lean): no kind's definition is used.

  1  `runsE`, `spentOf`   the coins of a list of blocks; the coins that the parts of a list spend,
     part by part, and in a part block by block. The definitions of these two were written, letter
     for letter alike, for two other parts of this project (the kinds K5 and K4), each in its own
     folder, and were taken over from there

Why the file is so small. Lemmas on the two stand in Honest/Law/Rule/Spent.lean and in files
that import it. Spent.lean imports this file and, beside it, files of Honest/Law/Rule/. A kind's
folder that wants the two definitions alone imports this file, and has none of these beneath it.

The two folders' files with these texts: Honest/K5/Law/Script.lean and Honest/K4/Law/Script.lean.
Neither is imported here.

Limits.
  * Coins of the extension field alone (`coinsE` reads no other).
  * Blocks that are spent, not those that are carried.
  * Two definitions; no lemma.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E)

variable {V W X : Type}

/-- The coins of a list of blocks, as the program's elements, block by block. -/
def runsE : (ds : List (String × Due)) → CsAll ds → List E
  | [], _ => []
  | d :: ds, c =>
    let c' : Cs d.2 × CsAll ds := c
    coinsE c'.1 ++ runsE ds c'.2

/-- **The coins that the parts of a list spend**, part by part. -/
def spentOf : (ps : List (Part V W X)) → RowCoins ps → List E
  | [], _ => []
  | p :: ps, c =>
    let c' : p.Coins × RowCoins ps := c
    runsE p.spends c'.1.2.1 ++ spentOf ps c'.2

end ProofFile.Honest

#print axioms ProofFile.Honest.runsE
#print axioms ProofFile.Honest.spentOf
