-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/FamThin.lean: the typed oracle functions that an encoding reads out of the single oracle
(`readBlocks`, Rom/Prefix.lean), in a form made for the evaluator (`famM`): the interface behind a
function of `Unit`; every block's hash computed once; and the theorem that the two are equal.

Definitions that compute; three theorems. Generic in the encoding of the queries.
An encoding (`OracleCoding`, Rom/Family.lean) has the number of blocks of each typed answer and a bijection
between points (oracle, query, number of a block) and all bit strings.

Why: two findings on compiled Lean (Run/CodingFnThin.lean's head has them at length): (1) a function
that has the interface, or a family of oracles made from it, as a parameter may get it built at the
call, with the lists of all verifier messages of its rounds: so here the interface stands behind a
function of `Unit`, an explicit first argument Lf, the types are written at Lf (), and no function
has a parameter of the type of a family's description (`OSpec`); (2) a digest is a function of the
bit's number, and what stands under its λ is computed anew for every bit: so an answer's blocks are
computed first, as data (an array of byte strings), in a function whose result type is not visibly a
function's, and decoded afterwards.

Main names:
  `famM_eq`: famM (fun _ => L) K m O = readBlocks m (fun _ s => bytesToDig (O s)).
  `famM_oBits`: at the format's oracle asked at `toBytes s` for a bit string s
  (Run/OracleBits.lean).
  `famM_one`: the same with the single oracle written as a function f: readBlocks m (fun _ => f), if
    f s = bytesToDig (O s) for all s.

Limits: `famM` is a term to state with; for a run take Run/CodingThin.lean's `famC`. Tried, with a
trace in a round's instance: at this library's small toy's encoding (`mT`, Run/ToyCode.lean), and
also at a record (`OracleCoding`) put together from functions written for the evaluator, the list of all
verifier messages was built as soon as a field of the record was read; the family made directly of
the writing function that is written for the evaluator (`famC`; `famC_famM` ties it to `famM`) did
not build it.
What the evaluator builds, or computes how often, is a fact about a compiler and no theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingFnThin
import Run.OracleBits
import Rom.Prefix

set_option autoImplicit false

namespace Run
open Compile Compile.Batch Iop Rom

variable {I X : Type} (Lf : Unit → BatchProtocol I X)

/-- The blocks of an answer, as bytes: data. -/
def famMB (K : ℕ) (m : OracleCoding (spec 256 K (Lf ())) 256) (O : List Bool → ByteArray)
    (o : (spec 256 K (Lf ())).ι) (q : (spec 256 K (Lf ())).Dom o) : Array ByteArray :=
  Array.ofFn (n := m.blocks o) fun j => O (m.code o q j)

/-- The bytes as a typed answer. -/
def famMD (K : ℕ) (m : OracleCoding (spec 256 K (Lf ())) 256)
    (o : (spec 256 K (Lf ())).ι) (a : Array ByteArray) : (spec 256 K (Lf ())).Rng o :=
  (m.rng o).symm fun j => digS (a.getD j.val ByteArray.empty)

/-- The typed oracle functions that the encoding reads out of the single oracle. -/
def famM (K : ℕ) (m : OracleCoding (spec 256 K (Lf ())) 256) (O : List Bool → ByteArray) :
    Fam (spec 256 K (Lf ())) :=
  fun o q => famMD Lf K m o (famMB Lf K m O o q)

/-- The format's oracle asked at `toBytes s` for a bit string s (Run/OracleBits.lean), into bytes.
-/
def oBy (s : List Bool) : ByteArray := _root_.Fmt.oracle (toBytes s)

variable {L : BatchProtocol I X}

/-- At the constant function Lf := fun _ => L, `famM` is `readBlocks` (Rom/Prefix.lean) at the
single oracle s ↦ bytesToDig (O s). -/
theorem famM_eq (K : ℕ) (m : OracleCoding (spec 256 K L) 256) (O : List Bool → ByteArray) :
    famM (fun _ => L) K m O = readBlocks m (fun _ s => bytesToDig (O s)) := by
  funext o q
  show (m.rng o).symm (fun j =>
      digS ((Array.ofFn (n := m.blocks o) fun j => O (m.code o q j)).getD j.val ByteArray.empty)) =
    (m.rng o).symm fun j => bytesToDig (O (m.code o q j))
  congr 1
  funext j
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos j.isLt]
  exact digS_eq _

theorem famM_oBits (K : ℕ) (m : OracleCoding (spec 256 K L) 256) :
    famM (fun _ => L) K m oBy = readBlocks m oBits := famM_eq K m oBy

theorem famM_one (K : ℕ) (m : OracleCoding (spec 256 K L) 256) (O : List Bool → ByteArray)
    (f : List Bool → Fin 256 → Bool) (h : ∀ s, f s = bytesToDig (O s)) :
    famM (fun _ => L) K m O = readBlocks m (fun _ => f) := by
  rw [famM_eq]
  congr 1
  funext _ s
  exact (h s).symm

end Run
