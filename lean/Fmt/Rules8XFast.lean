-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8XFast.lean: the reader of a proof file that opens stored tables (Fmt/Rules8X.lean), with
the hash in its fast form, and the theorems that it is the same function.

The reader (`wholeChainX`, Fmt/Rules8X.lean) parses a proof file's bytes in one pass. A stored table
is a Merkle tree whose root the reader takes from the statement (`itemRoot`).

Why: an entry file of the programs has hundreds of opened columns under trees of
depth 14, that is, thousands of calls of the hash. Fmt/Rules5Fast.lean has the format's hash in a
form that the evaluator runs fast (`HF`), proved to be the format's hash (`HF` = `formatHash`). The reader of
Fmt/Rules8X.lean takes its hash as an argument, so the fast reader is that very reader at `HF`.
No Mathlib.

1. What the file contains.
   `readChainXF`, `wholeChainXF`, `verifyXF`: the reader from a place on; the reader of a whole
   file; the verifier on bytes. Each is Fmt/Rules8X.lean's function at `HF`.

2. What is checked when the file compiles. Three tests (#guard), at the made-up example of
   Fmt/Rules8X.lean: the honest file is read by the fast form, with the same last value of the chain
   and the same opened columns of the view; an altered one is refused. (What the theorems say for
   all files, once by evaluation.)

3. Theorems.
   `X8.readXF_eq`, `X8.wholeXF_eq`, `X8.verifyXF_eq`: each is the function at the format's hash, for
   every description and all bytes.
   Many statements of this library are written twice: a definition in the namespace `Spec` states a
   proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

4. What is not claimed. How fast it is. A round's queries are asked block by block as in the slow
   form: the shared first part of a query's calls (Fmt/Rules5Fast.lean) is not used here.
   (`shared` in that file: all calls of a round share everything but their last sixteen bytes.)

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.Rules8X
import Fmt.Rules5Fast

namespace Fmt

def readChainXF (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) : Option (ChainOut × Nat) :=
  readChainX (m := Id) HF S seen b i

/-- The fast reader of a whole file. -/
def wholeChainXF (S : SpecX) (b : ByteArray) : Option ChainOut := wholeChainX (m := Id) HF S b

def verifyXF {Y : Type} (S : SpecX) (dec : Y → View → Bool) (y : Y) (file : ByteArray) : Bool :=
  verifyXW (m := Id) HF S dec y file

namespace X8
namespace Spec

def readXF_eq : Prop :=
  ∀ (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat),
    readChainXF S seen b i = readChainX (m := Id) formatHash S seen b i

def wholeXF_eq : Prop :=
  ∀ (S : SpecX) (b : ByteArray), wholeChainXF S b = wholeChainX (m := Id) formatHash S b

def verifyXF_eq : Prop :=
  ∀ (Y : Type) (S : SpecX) (dec : Y → View → Bool) (y : Y) (file : ByteArray),
    verifyXF S dec y file = verifyX S dec y file

end Spec

theorem readXF_eq : Spec.readXF_eq := by
  intro S seen b i
  unfold readChainXF
  rw [HF_eq]

theorem wholeXF_eq : Spec.wholeXF_eq := by
  intro S b
  unfold wholeChainXF
  rw [HF_eq]

theorem verifyXF_eq : Spec.verifyXF_eq := by
  intro Y S dec y file
  unfold verifyXF verifyX
  rw [HF_eq]

end X8

open ToyX8 in
#guard ((wholeChainXF spec honest).map fun o => (hex o.rho, (viewX spec o).opened)) == ((read spec honest).map fun o => (hex o.rho, (viewX spec o).opened)) && (wholeChainXF spec honest).isSome
open ToyX8 in
#guard (wholeChainXF spec (flipAt honest 50)).isNone && (wholeChainXF spec (honest ++ zeroBytes 1)).isNone
open ToyX8 in
#guard verifyXF spec (fun (_ : Unit) v => v.opened.length == 4) () honest && !verifyXF spec (fun (_ : Unit) v => v.opened.length == 5) () honest

end Fmt
