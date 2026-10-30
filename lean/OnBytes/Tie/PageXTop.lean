-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/PageXTop.lean: one encoding for all roots: the theorem of OnBytes/Tie/PageXRead.lean at
a fixed description, for readings under every statement, with the parameters' digest pinned.

A maker picks the two roots, and the statement under which the reader reads is `stm r0 r1`. The
encoding must not move with them. So a description S0 and a function `stm` are fixed; the typing,
the verifier, `famX` and the encoding stand at `xdOf S0 stm`; the reader reads under S0 with the
statement `stm r0 r1` in the place of its own, at the hash of `pinned (oB (g ())) S0.base.params`
(OnBytes/Tie/DigestPoint.lean: the function that g induces on byte strings, but for the one string
of the call that hashes the parameter bytes).

Main definitions: `withStatement`, `implAt`; `implAtPd`: the encoding with any 256 bits in the place
of the format's digest of the parameter bytes.
Main theorems.
 `pinned_verifyBS`   on what the typing makes of a chain so read, the run of the compiled verifier
                at `famX (xdOf S0 stm) dec (oB (g ())) _` is its run at `readBlocks (implAt ..) g`.
 `implAt_leaf1`, `implAt_node1`   under that encoding a leaf's and a vertex's answer is one block.

What is not claimed. Nothing on soundness, and no probability. An equation between two runs of the
verifier: of neither is it said that it accepts. Nothing on BLAKE2b, but that its digest of the
parameter bytes stands as a constant in the reader's function and in the first query's string. The
hypotheses `StmInv`, `FitsS` and the bound on the statements' lengths are shown at no description
here. "The format's" means: as the
library's Lean text renders the format page (`Run.PQ.famX`, `Fmt.oStr`). Nothing here compares that
text with the page or with the C++ programs. The program (the Lean port built from OnBytes/, not the
C++ verifier) does not call any function of this file.

-/
import OnBytes.Tie.PageXRead
import OnBytes.Tie.DigestPoint

set_option autoImplicit false

namespace OnBytes.Tie
open Rom Iop Compile Compile.Batch Run Run.PQ Run.Twin Run.Thin

/-- A description with another statement; all else is kept. The same function as `Slice.reStated`
(`Slice.withStatement_eq`); stated here so that Tie/ need not import Slice/. -/
def withStatement (S : Fmt.SpecX) (x : ByteArray) : Fmt.SpecX :=
  ⟨{ S.base with statement := x }, S.stored⟩

variable (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm))

/-- **The one encoding**: `theImplX` at the data of `xdOf S0 stm`. It does not depend on roots. -/
def implAt : OracleCoding (spec 256 ((xdOf S0 stm).K + 1) ((xdOf S0 stm).L dec)) 256 :=
  theImplX (pageX (D := xdOf S0 stm) dec ((xdOf S0 stm).K + 1) hcfg V)

/-- The same encoding with pd in the place of the format's digest of the parameter bytes, in the
string of the first chain query. -/
def implAtPd (pd : Dig 256) : OracleCoding (spec 256 ((xdOf S0 stm).K + 1) ((xdOf S0 stm).L dec)) 256 :=
  theImplX (pageXPd (D := xdOf S0 stm) dec pd ((xdOf S0 stm).K + 1) hcfg V)

/-- `implAt` is `implAtPd` at the format's own digest. -/
theorem implAt_eq_pd : implAt S0 stm dec hcfg V = implAtPd S0 stm dec hcfg V (pdX (xdOf S0 stm)) :=
  rfl

/-- Under `implAtPd` a leaf's answer is one block. -/
theorem implAtPd_leaf1 (pd : Dig 256) : (implAtPd S0 stm dec hcfg V pd).blocks .leaf = 1 := rfl

/-- Under `implAtPd` a vertex's answer is one block. -/
theorem implAtPd_node1 (pd : Dig 256) : (implAtPd S0 stm dec hcfg V pd).blocks .node = 1 := rfl

/-- Under the one encoding a leaf's answer is one block. -/
theorem implAt_leaf1 : (implAt S0 stm dec hcfg V).blocks .leaf = 1 := rfl

/-- Under the one encoding a vertex's answer is one block. -/
theorem implAt_node1 : (implAt S0 stm dec hcfg V).blocks .node = 1 := rfl

/-- **ONE ENCODING, ALL ROOTS.** S0, `stm`, the decision and the encoding are fixed. For every g on
bit strings and all byte strings r0, r1: if the strict reader, at the hash of `pinned (oB (g ()))
S0.base.params`, has read o under S0 with the statement `stm r0 r1`, from any byte and under any
record of vertices, and the typing at `xdOf S0 stm` makes π of o, then the run of the compiled
verifier on π under the two roots at `famX (xdOf S0 stm) dec (oB (g ())) _` is its run at
`readBlocks (implAt ..) g`. The other hypotheses, all on what is fixed: the bounds `FitsS`; S0's own
part is within the library's limits (`Run.PQ.ok`, the random bytes counted as standing in the file);
the chain has random bytes; the statement `stm a b` of any two strings of 32 bytes has fewer than
2^64 bytes. Of neither run is it said that it accepts. Nothing on soundness; no probability. -/
theorem pinned_verifyBS (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hok : PQ.ok (inFile S0.base) = true) (hn : S0.base.rand.isNone = false)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64)
    (g : Fam (rom 256)) (r0 r1 : ByteArray)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (o : Fmt.ChainOut) (j : ℕ)
    (e : Fmt.readChainX (m := Id) (Fmt.HO (pinned (oB (g ())) S0.base.params))
      (withStatement S0 (stm r0 r1)) seen b i = some (o, j))
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up)
    (hπ : toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
      (xdOf S0 stm).xs dec o = some π) :
    (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L dec)
      (256 + 8 * S0.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
      (wqX (xdOf S0 stm).C (xdOf S0 stm).K (chalP S0.base.plan.field (xdOf S0 stm).K)
        (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec
        (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
      (famX (xdOf S0 stm) dec (oB (g ())) ((xdOf S0 stm).K + 1)) =
    (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L dec)
      (256 + 8 * S0.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
      (wqX (xdOf S0 stm).C (xdOf S0 stm).K (chalP S0.base.plan.field (xdOf S0 stm).K)
        (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec)
      (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
      (embPX (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec
        (fun _ _ p => (p.val, [])) (fun _ => some ()))
      (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
      (readBlocks (implAt S0 stm dec hcfg V) g) :=
  read_verifyBS (xdOf S0 stm) dec hcfg V F g (withStatement S0 (stm r0 r1)) rfl
    (pinned (oB (g ())) S0.base.params) (size_pinned _ (size_oB (g ())) _)
    (own_of_ok (inFile S0.base) hok) hn seen b i o j e (bytesToDig r0) (bytesToDig r1)
    (hstm _ _ (size_digToBytes _) (size_digToBytes _)) π hπ

end OnBytes.Tie
