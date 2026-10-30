-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/FitOwn.lean: the tests of OnBytes/Maker/Page/FitSilent.lean on the silent rounds'
messages hold at the messages that a file's typing lays, under what is named.

One definition (`tlOf`), statements and proofs. The typing lays the front round's message as the
table's answers with the stored copy's number, and the joining round's as these answers with a run's
value (OnBytes/Maker/SilentParts.lean). The verifier hands its chains a list of outer roots: the
table's root and, behind it, a list rest.

Main names: `fFrontK_own`, `fFrontP_own`, `fJoin_own`; `tlOf g`, `tlOf_eq`: a value of tl that pays
hrest: whatever list g the verifier lays behind the root as a function of the table, read at the
table that the first root and the answers name. g has to be one public function of the table: a g
that holds a datum of one call would make the test, and an encoding made from it, hang on that call.
Premises: rest is tl of the root and of the answers (hrest): at use a law that ties the code of the
record's answers, which the verifier lays, to the table's answers, which the messages bear; the item
"table" is shorter than 2^64 bytes (`tableSmall`); for a proof file: the instance passes okX, its
two strings (req: the item's value, then the request file's bytes) and the copy's number are below
the bounds.
No letter stands under "there is".

What is not claimed. The premises at any file. Nothing on any hash. Nothing on soundness.


-/
import OnBytes.Maker.Page.FitSilent
import Run.ParserHashProofs

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run
open _root_.Iop (Dig)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.Maker (FrontMsg frontOf)

variable {X : Type} (tl : Dig 256 → List E → List (Dig 256))

theorem cmsFit_own (c : Dig 256) (ans : List E) (rest : List (Dig 256)) (hrest : rest = tl c ans) :
    cmsFit tl (c :: rest) ans = true :=
  decide_eq_true hrest

/-- **A key file's front message passes.** -/
theorem fFrontK_own (c : Dig 256) (ans : List E) (rest : List (Dig 256)) (hrest : rest = tl c ans)
    (hs : tableSmall (c :: rest) ans = true) :
    fFrontK tl (c :: rest) (none : Option X) (frontOf ans 0) = true := by
  show ((none : Option X).isNone && decide ((0 : ℕ) = 0) && cmsFit tl (c :: rest) ans &&
    tableSmall (c :: rest) ans) = true
  rw [cmsFit_own tl c ans rest hrest, hs]
  rfl

/-- **A proof file's front message passes.** -/
theorem fFrontP_own (req : X → ByteArray × ByteArray) (okX : X → Bool) (c : Dig 256) (ans : List E)
    (rest : List (Dig 256)) (hrest : rest = tl c ans) (hs : tableSmall (c :: rest) ans = true)
    (x0 : X) (ho : okX x0 = true)
    (hz : (req x0).1.size + 8 < 2 ^ 64 ∧ (req x0).2.size + 8 < 2 ^ 64) (copy : ℕ)
    (hcp : copy < 2 ^ 64) : fFrontP tl req okX (c :: rest) (some x0) (frontOf ans copy) = true := by
  show (okX x0 && decide ((req x0).1.size + 8 < 2 ^ 64) && decide ((req x0).2.size + 8 < 2 ^ 64) &&
    decide (copy < 2 ^ 64) && cmsFit tl (c :: rest) ans && tableSmall (c :: rest) ans) = true
  rw [cmsFit_own tl c ans rest hrest, hs, ho, decide_eq_true hz.1, decide_eq_true hz.2,
    decide_eq_true hcp]
  rfl

/-- **A joining round's message passes.** -/
theorem fJoin_own (c : Dig 256) (ans : List E) (rest : List (Dig 256)) (hrest : rest = tl c ans)
    (hs : tableSmall (c :: rest) ans = true) (run : ByteArray) :
    fJoin tl (c :: rest) ⟨ans, run⟩ = true := by
  show (cmsFit tl (c :: rest) ans && tableSmall (c :: rest) ans) = true
  rw [cmsFit_own tl c ans rest hrest, hs]
  rfl

/-- What stands behind the first root, from a function g of the table: g at the table that the first
root and the answers name. -/
def tlOf (g : Params.TableName → List (Dig 256)) (c : Dig 256) (ans : List E) : List (Dig 256) :=
  g ⟨digToBytes c, ans⟩

/-- **At a table's own root and answers it is g of that table**, for a root of 32 bytes: so hrest
holds at `tl := tlOf g`, `c := bytesToDig table.root`, `rest := g table`. -/
theorem tlOf_eq (g : Params.TableName → List (Dig 256)) (table : Params.TableName)
    (h : table.root.size = 32) : g table = tlOf g (bytesToDig table.root) table.answers := by
  unfold tlOf
  rw [digToBytes_bytesToDig table.root h]

end OnBytes.Maker.Page
