-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FitsReadAt.lean: the hypothesis `FitsRead` of OnBytes/Slice/OneWorldChain.lean holds
at the encoding by the format's rules.

`FitsRead S0 stm dec m` says, of an encoding m of the typed queries into bit strings: on what the
reader has read under any roots and the typing has typed, a yes of the compiled verifier under the
typed oracle functions that the oracle induces by the format's spelling (`Run.PQ.famX`) is a yes
under the family that is read out of the oracle through m. Here m is `Tie.implAt`: the bijection of
OnBytes/Tie/PageX.lean at the data that OnBytes/Tie/PageXFit.lean makes of the fixed description.
"The format's" means: as the library's Lean text renders the format page (`Run.PQ.famX`,
`Fmt.oStr`). Nothing here compares that text with the page or with the C++ programs.

Main theorems.
 `withStatement_eq`   `Tie.withStatement` is `reStated`.
 `theRunAny_read`   the two runs of the compiled Link verifier of the whole wiring are equal.
 `fitsRead_implAt`   `FitsRead S0 stm dec (Tie.implAt S0 stm dec hcfg V)`.
 `fitsRead_implAt_of_bounds`   the same, with the library's bounds as one test on numbers.

The hypotheses, all on what is fixed: the configuration's digest has 32 bytes; a reader for the
statement (`Tie.StmInv`); the library's bounds `Run.PQ.FitsS`; S0's own part is within the library's
limits; the chain has random bytes; the statement `stm a b` of any two strings of 32 bytes has fewer
than 2^64 bytes.

What is not claimed. Nothing on soundness, and no probability. Nothing on BLAKE2b, but that its
digest of the parameter bytes stands as a constant in the reader's function and in the first query's
string. That the verifier says yes on anything is not said. The hypotheses are shown at no
description here. The program (the Lean
port built from OnBytes/, not the C++ verifier) does not call any function of this file.

-/
import OnBytes.Slice.OneWorldChain
import OnBytes.Tie.PageXTop

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Tie (xdOf inFile pinned StmInv implAt withStatement pinned_verifyBS)

/-- The two names for "a description with another statement" are one function. -/
theorem withStatement_eq (S : Fmt.SpecX) (x : ByteArray) : withStatement S x = reStated S x := rfl

variable (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm))

/-- **On what the typing makes of a chain that was read under any roots, the run of the compiled
Link verifier of the whole wiring at `famX` is its run at what the one encoding reads out of g.**
The hypotheses are those of `Tie.pinned_verifyBS`.
An equation between two runs: of neither is it said that it accepts. Nothing on soundness; no
probability. -/
theorem theRunAny_read (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hok : PQ.ok (inFile S0.base) = true) (hn : S0.base.rand.isNone = false)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64)
    (g : Fam (rom 256)) (r0 r1 : ByteArray)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO (pinned (oB (g ())) S0.base.params))
      (reStated S0 (stm r0 r1)) seen b i = some (o, j))
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up)
    (hπ : toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
      (xdOf S0 stm).xs dec o = some π) :
    (theRunAny (xdOf S0 stm) dec r0 r1 π).det
        (famX (xdOf S0 stm) dec (oB (g ())) ((xdOf S0 stm).K + 1)) =
      (theRunAny (xdOf S0 stm) dec r0 r1 π).det (readBlocks (implAt S0 stm dec hcfg V) g) := by
  have E := pinned_verifyBS S0 stm dec hcfg V F hok hn hstm g r0 r1 seen b i o j e π hπ
  have hv := vls_any (xdOf S0 stm) dec (256 + 8 * (xdOf S0 stm).base.plan.salt) (bytesToDig r0)
    (bytesToDig r1) π
  unfold theRunAny
  rw [← hv]
  exact E

/-- **`FitsRead` holds at the encoding `Tie.implAt`.** For every oracle g, all byte strings r0 and
r1 and all bytes: if the strict reader, at g for every hash but the digest of the parameter bytes,
has read a chain under S0 with the statement `stm r0 r1`, and the typing has made π of it, then a
yes of the compiled Link verifier on π under `famX` at g is a yes under the family that `Tie.implAt`
reads out of g. Asked, all of S0 and `stm`: the six hypotheses of the head. Nothing is asked of g,
the roots, the bytes or π. By `theRunAny_read` the two runs are equal, so a no is a no as well. That
the verifier says yes on anything is not said. Nothing on soundness; no probability. -/
theorem fitsRead_implAt (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hok : PQ.ok (inFile S0.base) = true) (hn : S0.base.rand.isNone = false)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64) :
    FitsRead S0 stm dec (implAt S0 stm dec hcfg V) := by
  intro g r0 r1 b i o n π e hπ hacc
  exact (theRunAny_read S0 stm dec hcfg V F hok hn hstm g r0 r1 [] b i o n e π hπ).symm.trans hacc

/-- The same with the library's bounds as its one test on numbers (`Run.PQ.fourBounds`:
Run/OneIsTypedTop.lean), which can be evaluated at a closed description. -/
theorem fitsRead_implAt_of_bounds (hok : PQ.ok (inFile S0.base) = true)
    (hb : fourBounds (inFile S0.base) (xdOf S0 stm).K = true) (hn : S0.base.rand.isNone = false)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64) :
    FitsRead S0 stm dec (implAt S0 stm dec hcfg V) := by
  simp only [fourBounds, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact fitsRead_implAt S0 stm dec hcfg V
    (fitsS_of (inFile S0.base) (xdOf S0 stm).K hok hb.1.1.1 hb.1.1.2 hb.1.2 hb.2) hok hn hstm

end OnBytes.Slice
