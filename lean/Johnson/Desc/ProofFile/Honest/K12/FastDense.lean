-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastDense.lean: `denseAtFast`, a `denseAt` (Run.lean) that is
meant to be faster: it expands a claim's row of coefficients into two arrays of words. Definitions
only. It imports RunBy.lean alone, so no Mathlib.

It repeats code of the verifier's side. `spreadFast` repeats the eight lines of `Tensor.spreadTo`
(OnBytes/Iop/Tensor.lean), which writes out one tensor. For a tensor with a written-out factor,
`spreadTo` computes at every entry where that entry's factor lies in the slice (`denseIndex`: a
power of two, a division and a remainder for each dense variable). `spreadFast` carries that index
down the recursion: when bit d of the entry's index is set, the index within the slice grows by a
number that depends on d alone, and these numbers are computed once for each tensor (`stepsBelow`).

Each definition repeats one, and FastDenseLaw.lean proves the two equal for all arguments, without
hypothesis:
  `spreadFast`   `Tensor.spreadTo` (`spreadFast_eq`, at the arguments that `addToFast` passes)
  `addToFast`    `Tensor.addTo` (`addToFast_eq`). A tensor without a written-out factor goes to
                 `Tensor.addTo` itself
  `formAddToFast`, `writeOutFast`   `Form.addTo`, `Form.writeOut` (`formAddToFast_eq`,
                 `writeOutFast_eq`)
  `denseFast`    `dense` (Johnson/Desc/K12/JoinGuarded.lean; `denseFast_eq`)
  `denseAtFast`  `denseAt` (`denseAtFast_eq`)

Limits.
- Where some tensor's number of variables is not the stage's, `denseAtFast` takes the same slow
  branch as `denseAt`.
- `runBy` calls it at `Seams.fast` (FastW.lean) alone, and not for the last stage's claim.
- Cost is not measured. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Tensor Form denseIndex isZeroE timesOne addE mulE zeroE)
open Fmt.M1 (Stage GRow)

/-- For d = n - 1 down to 0: by how much the index within the slice grows when bit d of the entry's
index is set. ds: the dense variables. -/
def stepsBelow (ds : List Nat) : Nat → List Nat
  | 0 => []
  | n + 1 => denseIndex ds 0 (2 ^ n) :: stepsBelow ds n

/-- `Tensor.spreadTo` with the index within the slice, idx, carried beside off. Each pair comes with
the number that idx grows by in the pair's high half. -/
def spreadFast (v : Tensor) : List ((OnBytes.E × OnBytes.E) × Nat) → Nat → Nat → Nat → OnBytes.E →
    Array OnBytes.E → Array OnBytes.E
  | [], _, off, idx, s, out =>
    out.modify off fun y =>
      addE y (if v.denseVars.isEmpty then s else mulE s (v.values.getD (v.first + idx) zeroE))
  | (p, c) :: ps, w, off, idx, s, out =>
    let out1 := if isZeroE p.1 then out else spreadFast v ps (w / 2) off idx (timesOne s p.1) out
    if isZeroE p.2 then out1
    else spreadFast v ps (w / 2) (off + w / 2) (idx + c) (timesOne s p.2) out1

/-- Adds all entries of a tensor to out, as `Tensor.addTo` does. -/
def addToFast (v : Tensor) (out : Array OnBytes.E) : Array OnBytes.E :=
  if v.denseVars.isEmpty then v.addTo out
  else if isZeroE v.scalar then out
  else
    spreadFast v (v.pairs.reverse.zip (stepsBelow v.denseVars v.vars)) (2 ^ v.vars) 0 0 v.scalar out

/-- Adds all entries of a form to out, as `Form.addTo` does. -/
def formAddToFast (f : Form) (out : Array OnBytes.E) : Array OnBytes.E :=
  f.entries.foldl (fun o e => o.modify e.1 fun y => addE y e.2)
    (f.tensors.foldl (fun o v => addToFast v o) out)

/-- A form written out, 2 ^ vars entries, as `Form.writeOut` does. -/
def writeOutFast (f : Form) (vars : Nat) : Array OnBytes.E :=
  formAddToFast f (Array.replicate (2 ^ vars) zeroE)

/-- A form written out as triples of words, as `dense` does. -/
def denseFast (f : Form) (vars : Nat) : Array Fmt.M1.E := (writeOutFast f vars).map (·.triple)

/-- `denseAt` with `denseFast` in the place of `dense`. -/
def denseAtFast (row : OnBytes.GroupRow) (s : Stage) : GRow :=
  let n := s.k + OnBytes.ceilLog2 s.C.l
  ⟨if row.c.tensors.all (fun v => v.vars == n) then denseFast row.c n
    else Array.ofFn (n := 2 ^ n) fun i => (row.c.entry i.val).triple,
    Array.ofFn (n := 2 ^ s.h * s.Z.l) fun i => (row.d.getD i.val OnBytes.zeroE).triple,
    row.target.triple⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.stepsBelow
#print axioms ProofFile.Honest.K12.Light.spreadFast
#print axioms ProofFile.Honest.K12.Light.addToFast
#print axioms ProofFile.Honest.K12.Light.formAddToFast
#print axioms ProofFile.Honest.K12.Light.writeOutFast
#print axioms ProofFile.Honest.K12.Light.denseFast
#print axioms ProofFile.Honest.K12.Light.denseAtFast
