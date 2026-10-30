-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3ParOfLaws.lean: the entry file. Under the hypothesis below, what Fmt/M3ParOf.lean reads out of
the parameters is what was spelled into them. That is the sizes and the number of salt bytes in a
leaf of a stored table. This file has the statement; the proof is in
Fmt/M3ParOfLawsProofs.lean.

An entry file comes with a further stored copy of a committed table. The link is a protocol whose
purpose is to show that the copy holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). An entry file holds the prover's messages,
proof-of-work nonces and Merkle openings of the link (Fmt/M3Entry.lean says more).
"The programs" are the C++ implementation that comes with this Lean code; "the format page" is
docs/format/FORMAT.md, which comes with the programs. The file is a companion of
Fmt/M1ParOfLaws.lean.
The sizes are those of the link protocol (`Par`, Fmt/M3Types.lean). The head of that file says what
the group is and what T, v, s, nu_0, nu_j (there nu0, nuj), R, C and Z are. The numbers k and h are
those of a stage (`Stage`, Fmt/M1Types.lean). The description is a Lean value (`SpecX`,
Fmt/Rules8X.lean), which the strict reader (`wholeChainX`) takes beside the chain's bytes.
To spell a value is to write it as the bytes that the format fixes for it. A word is a number
written in eight bytes, the lowest first (`u64n`, Fmt/Rules1.lean).

Why. FORMAT.md, R0.4 and R0.5: every public fact has one home, and what a verifier follows stands in
what is hashed. The digest of the parameter bytes is hashed into the chain's first value
(`firstBytes`, Fmt/Rules4.lean). Under the hypothesis below, the parameters determine the sizes.




1. What the file contains. Two definitions.
   `Par.small P tsalt`: What spelling needs, and no more (it is wider than the format's own bounds).
     - Every number that becomes a word of the two items "codes" and "the link" is below 2^64.
       These numbers are the tables' code, v, s, the salt of a table's leaf (`tsalt`), nu_0, nu_j,
       R; each stage's two codes, k and h; the number of stages. (For the plan's words see
       `Params.fit`.)
     - The first stage is the group: its codes are the sizes' C and Z, its k = 1 + clog R, its
       h = 0. (FORMAT.md, R13.10: that stage is not written in the item, so sizes in which it is
       another cannot come back.)
   `theParams P cfg nonceB tsalt`: This structure (`Params`) has three parts.
     - The plan of these sizes is `planOf P nonceB` (Fmt/M3Plan.lean). `nonceB` is the number of
       bytes of a nonce.
     - The digest of the public files is `cfg`.
     - The items of these sizes are `itemsOf` (Fmt/M3Items.lean) with its arguments `withTree` and
       `tabIn` both `false`. That is the format page's form: no tree's number, and the tables' code
       not in "codes".

2. What is checked when the file compiles. Only the types: the file has no test.







3. Theorem stated here (`Fmt.M3.Spec.par_back`), for every P, cfg, nonceB, tsalt. The proof is in
Fmt/M3ParOfLawsProofs.lean, as a theorem of the same name. No Mathlib.
   `par_back`: small ⇒ `parOf (theParams ..) = some (P, tsalt)`.







   `par_back` holds also at s > 0 (the word s is read as it stands).
   `planOf` builds the plan of `theParams`. It is defined in Fmt/M3Plan.lean, which has no entry
   RECORD. The head of that file says under 4 that tables with a record (s > 0) are not covered,
   and what more the plan has for them.


4. What is not claimed.
   The other direction is not claimed: that parameters from which `parOf` gives sizes are the
   spelling of sizes that are small.

   It is not claimed that any hypothesis holds at given sizes.
   `par_back` starts from the structure `Params`, not from bytes: that the parameter bytes are read
   as `theParams` is not stated here.
   It is not claimed that the sizes follow from the public files.
   Nothing is claimed on a file.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M3ParOf
import Fmt.M1ParOfLaws

namespace Fmt
namespace M3
open Fmt.M1 Fmt.M2

def Par.small (P : Par) (tsalt : Nat) : Bool :=
  P.T.small && decide (P.v < 2 ^ 64) && decide (P.s < 2 ^ 64) && decide (tsalt < 2 ^ 64) &&
    decide (P.nu0 < 2 ^ 64) && decide (P.nuj < 2 ^ 64) && decide (P.R < 2 ^ 64) &&
  decide (P.stages.length < 2 ^ 64) && P.stages.all Stage.small &&
  (match P.stages with
   | s :: _ => s.C == P.C && s.Z == P.Z && s.k == 1 + clog P.R && s.h == 0
   | [] => false)

/-- The parameters (`Params`) of the description at the sizes `P`: plan, digest, items. -/
def theParams (P : Par) (cfg : ByteArray) (nonceB tsalt : Nat) : Params :=
  ⟨planOf P nonceB, cfg, itemsOf P false false tsalt⟩

namespace Spec

def par_back : Prop :=
  ∀ (P : Par) (cfg : ByteArray) (nonceB tsalt : Nat),
    P.small tsalt = true → parOf (theParams P cfg nonceB tsalt) = some (P, tsalt)

end Spec



end M3
end Fmt
