-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/Arrays.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE: two arrays that
this test defines and other blocks send: the vector of reads and the array of digits: each entry as
a plain function of the cells and of challenges. DEFINITIONS, WITH CODE. NO THEOREM. NOTHING IS
CLAIMED ON COMPLETENESS, SOUNDNESS OR HIDING.

NO COIN IS IN THEM. What an oracle message holds beside an array's entries (the random entries of
its encoded rows, pads, mask rows) is the sender's matter.
The formulas are the format's (docs/format/11-1-machinery.md, "The cells, the arrays of the
matrices, U3 and ZZ").

  `readAt p parts cell n`   entry n of the vector of reads U3: of the part in which n lies, for its
      column c and block b: the sum over r of phi[r] * cell (mat, b * len + r, c). It is sent IN
      FRONT OF this kind's round. parts: the closed list of parts, as the verifier holds it
      (`HFun`, OnBytes/Model/Look.lean, which calls a part a table): each part's matrix, the length
      len of its weight vector, the weights, its first entry. THE LIST IS A PARAMETER: which parts a
      segment (a link of the first chain) has, and their weights as functions of the challenges
      heard, is the segment's own kind's to say
  `digitAt` (Johnson/Desc/K8/Honest/Window.lean)   the entry of the array of digits ZZ; `zzRows`,
      `zzColumns`: its shape. It is sent BEHIND this kind's round
NOT HERE: the bits of the multiplicities of the lookup on the digits, which are sent with the array
of digits: they are the lookup's honest side's.

Limits. Outside the window (`leaves`) the digits do not give the combination back. Beyond an array's
shape the functions yield 0 (of `digitAt`: Johnson/Desc/K8/Honest/DigitsLaw.lean: `digitAt_rows`,
`digitAt_columns`). `readAt` takes a part's first entry from the list and does not ask that the
parts follow one another without a gap or an overlap: where two parts hold an entry the first in the
list wins. A part with len = 0, or on a matrix beyond the place's list, has no entry. Of a weight
vector with fewer than len weights every weight beyond its end counts as 0. `readAt` does not look
at which vector a part names (`HFun.tree`): the format has the one vector U3. Nothing in this folder
sends these entries.

-/
import Johnson.Desc.K8.Honest.Window

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model

/-! ## The vector of reads -/

/-- The entries of one part: its matrix's columns times its blocks. -/
def partLength (p : Par) (f : HFun) : Nat := p.ks.getD f.mat 0 * (p.ms.getD f.mat 0 / f.len)

/-- The entry of a part for column c and block b. -/
def readOf (f : HFun) (cell : CellsAt) (c b : Nat) : E :=
  (List.range f.len).foldl
    (fun s r => addE s (mulE (f.phi.getD r zeroE) (ofInt (cell f.mat (b * f.len + r) c)))) zeroE

/-- Entry n of the vector of reads. 0 where n lies in no part. -/
def readAt (p : Par) (parts : List HFun) (cell : CellsAt) (n : Nat) : E :=
  match parts.find? fun f => decide (f.start ≤ n) && decide (n < f.start + partLength p f) with
  | some f =>
    let nb := p.ms.getD f.mat 0 / f.len
    readOf f cell ((n - f.start) / nb) ((n - f.start) % nb)
  | none => zeroE

/-- The parts' numbers of entries together: the length of the vector of reads where the parts follow
one another from entry 0 on. -/
def readsLength (p : Par) (parts : List HFun) : Nat :=
  parts.foldl (fun n f => n + partLength p f) 0

/-! ## The array of digits -/

/-- The rows of the array of digits: one for each combination. -/
def zzRows (p : Par) : Nat := p.tau

/-- Its columns: the low digits of all rows of cells, then the high digits. -/
def zzColumns (p : Par) : Nat := 2 * allRows p

end VerifiableInference.Desc.First.K8.Honest
