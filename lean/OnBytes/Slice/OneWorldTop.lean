-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneWorldTop.lean: the bound for a checker on bytes over one random oracle, for a chain
that opens stored tables, two at most, with the typed queries spelled by the format's rules.

OnBytes/Slice/OneWorldChain.lean has the bound for any implementation m of the typed oracles by one
oracle that meets `FitsRead`. OnBytes/Slice/FitsReadAt.lean shows that the implementation
`Tie.implAt` meets it: there a typed query that the format writes is coded as the bit string of the
format's hash call. This file joins the two. No hypothesis on an implementation is left. "The
format's" means: as the library's Lean text renders the format page (`Run.PQ.famX`, `Fmt.oStr`).
Nothing here compares that text with the page or with the C++ programs.

Main theorem. `one_world_at`: for a description S0 within the limits, a function `stm` from two
roots to the statement's bytes, and a decision. The oracle is a function from all bit strings to
strings of 256 bits, each value drawn uniformly and independently. A maker with at most t queries
and any coins puts out a value; `pre` reads off it two roots, bytes, the offset where the chain
begins, and a test on the offset where it ends; the checker `chainChk` reads the chain from the
bytes, asking the same oracle for every hash but the digest of the parameter bytes, takes the
decision on the view, and turns what was read into the library's typed proof string
(`Run.PQ.toBPrfX`). With probability at most (t + 2 + tR + tV) * e + 2 (t + 2 + tR + tV + 1)^2 /
2^256 it says yes while the pair of strings that is read off the maker's own queries under the two
roots is outside the language.

What "read off the maker's queries" means here. Every bit string stands for exactly one typed point
(`Tie.implAt`). Vertices: the walk uses the maker's queries at the strings of the format's call
number 166 that start from S0's configuration digest and hold two digests, and no others. Leaves:
its queries at the strings of the calls number 164 and 174 in the shapes that the encoding writes
(174: from S0's configuration digest, with a salt of S0's length), AND at strings that are no hash
call: the byte 2 and then the library's spelling of a leaf query that the format does not write, a
stored table's symbol with another start or another length of salt among them. A symbol is taken
from a leaf query on a stored table's symbol, of either sort. A digest is the oracle's answer
itself. All other strings count for nothing, the format's calls number 173 and 178 among them. From
these entries the library's extractor walks down from a root, at each step by the first entry in the
list with the wanted answer (`Rom.singleTr`, `Compile.Batch.extEnc`, `Merkle.firstPre`). Where the
entries determine no symbol at a place, the string has the library's fixed filling there.

The hypotheses, all on what is fixed before the oracle is drawn: S0 is within the limits
(`withinX`); its configuration digest has 32 bytes; `stm` has an inverse on roots (`Tie.StmInv`),
puts the roots into the items of the opened tables (`RootsIn`) and gives fewer than 2^64 bytes; the
library's test on four numbers (`Run.PQ.fourBounds`: K + 1 below 2^48, K the number of blocks `(xdOf
S0 stm).K`; S0's own statement below 2^64 bytes; fewer than 2^64 rounds; the first tree's number and
the number of roots together at most 2^48; the second is idle here, as no run reads S0's own
statement); and `SoundLAny`: the protocol made from S0 and the decision is round-by-round sound for
the language, each error count at most e as a share of its round's challenge values.

What is not claimed. The checker is not the program, which is the Lean port built from OnBytes/: the
program does not call it and hashes with BLAKE2b. Nothing here ties the checker at BLAKE2b to the
program, and no probability is stated of the program or of BLAKE2b. The language and e are
variables: all content lies in `SoundLAny` at a named language and a small e. With a language that
holds of every pair, or with e at 1, the theorem is true and empty. `pre`, its last test, `stm` and
`dec` are plain functions, fixed before the oracle is drawn. They cannot ask it: a hash inside one
of them is a fixed function. A chain whose statement or decision takes more from the maker than the
two roots is not covered; an entry for tables with a record is such a chain. BLAKE2b's digest of the
parameter bytes stands in the checker as a plain value, and so does the configuration's digest in
S0. The limits allow a chain that opens one table or none; nothing is opened under the root of a
table that is not opened. The checker also tests that both roots have 32 bytes and that S0 with
their statement is within the limits; the program does not test the limits. That the hypotheses hold
together at any description is not shown here.


That the checker says yes on any bytes under any oracle is not proved.


One chain; the key is not checked: both roots are the maker's
choice and are tied to nothing published. Nothing on the C++ verifier. The bound says nothing once
it reaches 1. Where a round's e rests on proof of work, the queries that a maker spends on that work
are among the t.

-/
import OnBytes.Slice.FitsReadAt

set_option autoImplicit false

namespace OnBytes.Slice
open _root_.Iop Rom Prob Compile Compile.Batch _root_.Run _root_.Run.PQ MeasureTheory
open scoped ENNReal
open OnBytes.Tie (xdOf inFile withinX within within_of_withinX implAt implAt_leaf1 implAt_node1
  StmInv)

variable {γ : Type}

/-- **The bound for the checker on bytes over one random oracle, with the typed queries spelled by
the format's rules.** See the head for the experiment, for what is read off the maker's queries, and
for what is not claimed. tR is `CostX.fileNX S0 * 2`, a bound on the strings that the checker asks;
tV is the library's bound on the compiled verifier's typed queries; t bounds the strings that the
maker asks, a repeated one counted again. The 2 and tV come from the proof: in the experiment no
compiled verifier runs. Asked, all of what is fixed before the oracle is drawn: S0 within the
limits; a configuration digest of 32 bytes; `StmInv`; `fourBounds`; statements of fewer than 2^64
bytes; `RootsIn`; `SoundLAny` at e. The language and e are variables: all content lies in
`SoundLAny`. The strings are read off through `Tie.implAt`. BLAKE2b's digest of the parameter bytes
and the configuration's digest are plain values in the checker. The checker is not the program; no
probability is stated of the program or of BLAKE2b; that the checker says yes on anything is not
shown; the roots are the maker's choice; the bound says nothing once it reaches 1. -/
theorem one_world_at (S0 : Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (dec : View → Bool) (hw : withinX S0 = true) (hcfg : S0.base.cfg.size = 32)
    (V : StmInv (xdOf S0 stm)) (hb : fourBounds (inFile S0.base) (xdOf S0 stm).K = true)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64)
    (hroots : RootsIn S0 stm)
    (Lg : Unit → (twoExternalStrings ((xdOf S0 stm).L dec).wordLength ((xdOf S0 stm).L dec).Symbol).Str → Prop) (εs : ℝ≥0∞)
    (hs : SoundLAny (xdOf S0 stm) dec Lg εs)
    (pre : γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool)))
    (A : OComp (rom 256) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr (twoExp A (chainChk S0 stm dec pre))
        (fun _ => twoWinOne (WkAny (xdOf S0 stm) dec) (implAt S0 stm dec hcfg V) Lg
          fun _ y => y) ≤
      ((t + 2 + Tie.CostX.fileNX S0 * 2 +
          tVQB (WkAny (xdOf S0 stm) dec).Lk (WkAny (xdOf S0 stm) dec).depthReq : ℕ) : ℝ≥0∞) * εs +
        2 * ((t + 2 + Tie.CostX.fileNX S0 * 2 +
          tVQB (WkAny (xdOf S0 stm) dec).Lk (WkAny (xdOf S0 stm) dec).depthReq + 1 : ℕ) : ℝ≥0∞) ^ 2
          / 2 ^ 256 := by
  have hwi := within_of_withinX S0 hw
  unfold within at hwi
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hwi
  exact one_world_chain S0 stm dec hw Lg εs hs hroots (implAt S0 stm dec hcfg V)
    (implAt_leaf1 S0 stm dec hcfg V) (implAt_node1 S0 stm dec hcfg V)
    (fitsRead_implAt_of_bounds S0 stm dec hcfg V hwi.1 hb hwi.2 hstm) pre A t hA

end OnBytes.Slice
