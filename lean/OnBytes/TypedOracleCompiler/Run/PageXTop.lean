-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/PageXTop.lean: the encoding at a fixed description: the theorem of
OnBytes/TypedOracleCompiler/Run/PageXRead.lean for readings under every statement. (The join "one encoding for all
roots": OnBytes/TypedOracleCompiler/Run/AllRoots.lean.)
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/PageXTop.lean (9 declarations, 118 lines). A maker picks the two
roots, and the statement under which the reader reads is `stm r0 r1`. The encoding must not move
with them. So a description S0 and a function `stm` are fixed; the typing, the verifier, `famXPd`
and the encoding stand at `xdOf S0 stm`; the reader reads under S0 with the statement `stm r0 r1` in
the place of its own.

WHAT IT IMPORTS: the sibling alone (PageXRead.lean, PageIsReaders.lean for `own_of_ok`). The
original imports OnBytes/Tie/DigestPoint.lean, with which 36 files of OnBytes/ come in (itself
counted), four of OnBytes/Hash/ among them, for `pinned`, in which the format's digest of the
parameter bytes is a constant. Here the pinned value is an argument.

AS TEXT BUT FOR NAMES AND THE NEW ARGUMENTS (4). `withStatement`, `implAtPd`, `implAtPd_leaf1`,
`implAtPd_node1`.
TURNED (1).
 `pinned_verifyBSPd`   the original's `pinned_verifyBS`, with ONE value pd in the three places where
                    the original has the format's digest: the reader's answer at the string of the
                    call on the parameter bytes, the first query's string, `famXPd`.
NEW (6).
 `all_verifyBSPd`   the same at EVERY function O' on byte strings with answers of 32 bytes;
                    `pinned_verifyBSPd` is one application.
 `inFile`, `xdOf`, `digestStr`, `pinnedAt`   the text of OnBytes/Tie/Limits.lean, StoredMain.lean,
                    DigestPoint.lean and OnBytes/Slice/ChainChkAsk.lean, the second at the sibling's
                    `XD`.
 `size_pinnedAt`    `size_pinned` with the value as an argument.
NO COUNTERPART (4). `implAt`, `implAt_eq_pd`, `implAt_leaf1`, `implAt_node1`: the encoding at the
format's own digest.

WHAT IS NOT SAID. Nothing on soundness, and no probability. An equation between two runs of the
verifier: of neither is it said that it accepts. pd is any 256 bits: nothing ties it to the
parameter bytes. `StmInv`, `FitsS`, `OwnFits` and the bound on the statements' lengths are shown at
no description here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXRead
import OnBytes.TypedOracleCompiler.Run.PageIsReaders

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run

/-- The same description, with the chain's random bytes in the file. -/
def inFile (S : _root_.Fmt.Spec) : _root_.Fmt.Spec := { S with rand := .inFile }

/-- A description with stored tables in the sibling's form. `stm` gives the statement's bytes as a
function of the two tables' roots. The chain's random bytes count as standing in the file. -/
def xdOf (S : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray) : XD :=
  ⟨inFile S.base, stm, S.stored⟩

/-- A description with another statement; all else is kept. -/
def withStatement (S : _root_.Fmt.SpecX) (x : ByteArray) : _root_.Fmt.SpecX :=
  ⟨{ S.base with statement := x }, S.stored⟩

/-- The string of the call that hashes the parameter bytes. -/
def digestStr (params : ByteArray) : ByteArray :=
  _root_.Fmt.oStr 0 169 0 1 _root_.Fmt.zero32 params

/-- O, but for one string: the string of the call that hashes `params` is answered with pd. -/
def pinnedAt (O : ByteArray → ByteArray) (params pd : ByteArray) : ByteArray → ByteArray :=
  fun s => if s = digestStr params then pd else O s

/-- If O's answers and pd have 32 bytes, so have the answers of `pinnedAt O params pd`. -/
theorem size_pinnedAt (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (params pd : ByteArray) (hpd : pd.size = 32) : ∀ s, (pinnedAt O params pd s).size = 32 := by
  intro s
  unfold pinnedAt
  split
  · exact hpd
  · exact hO s

variable {Bd : Type} (B : BodyD Bd) (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (Lf : LeafD (xdOf S0 stm) B) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm))

/-- The one encoding: `theImpl` at the data of `xdOf S0 stm`, with pd in the place of the
format's digest of the parameter bytes, in the string of the first chain query. It does not depend
on roots. -/
def implAtPd (pd : Dig 256) : OracleCoding (typedOracleFamily 256 ((xdOf S0 stm).K + 1) ((xdOf S0 stm).L Bd dec)) 256 :=
  theImpl (pageXPd (D := (xdOf S0 stm)) dec pd B Lf ((xdOf S0 stm).K + 1) hcfg V)

/-- Under `implAtPd` a leaf's answer is one block. -/
theorem implAtPd_leaf1 (pd : Dig 256) : (implAtPd B S0 stm Lf dec hcfg V pd).blocks .leaf = 1 := rfl

/-- Under `implAtPd` a vertex's answer is one block. -/
theorem implAtPd_node1 (pd : Dig 256) : (implAtPd B S0 stm Lf dec hcfg V pd).blocks .node = 1 := rfl

variable (embS : (p : OPos (Twin.up (SOf (xdOf S0 stm).C (xdOf S0 stm).ds))) →
  OSym (Twin.up (SOf (xdOf S0 stm).C (xdOf S0 stm).ds)) p → Bd)

/-- ONE ENCODING, ALL ROOTS, AT EVERY FUNCTION ON BYTE STRINGS. S0, `stm`, the decision, the
bodies' data, pd and with them the encoding are fixed. For every g on bit strings, every function O'
on byte strings with answers of 32 bytes and all byte strings r0, r1: if the strict reader, at the
hash of O', has read o under S0 with the statement `stm r0 r1`, from any byte and under any record
of vertices, and the typing at `xdOf S0 stm` makes π of o, then the run of the compiled verifier on
π under the two roots at `famXPd .. (digToBytes pd) (oB (g ())) _` is its run at
`readBlocks (implAtPd .. pd) g`. The other hypotheses, all on what is fixed: the bounds `FitsS`;
`OwnFits`; S0's own part is within the sibling's limits (`PQ.ok`, the random bytes counted as
standing in the file); the chain has random bytes; the statement `stm a b` of any two strings of 32
bytes has fewer than 2^64 bytes. O', g and pd are tied to one another by nothing. Of neither run is
it said that it accepts. Nothing on soundness; no probability. -/
theorem all_verifyBSPd (pd : Dig 256) (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf embS)
    (hok : PQ.ok (inFile S0.base) = true) (hn : S0.base.rand.isNone = false)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64)
    (g : Fam (rom 256)) (O' : ByteArray → ByteArray) (hO : ∀ s, (O' s).size = 32)
    (r0 r1 : ByteArray)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O')
      (withStatement S0 (stm r0 r1)) seen b i = some (o, j))
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up)
    (hπ : toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
      (xdOf S0 stm).xs dec o = some π) :
    (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
      (256 + 8 * S0.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
      (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
      (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
      (famXPd B (xdOf S0 stm) dec (digToBytes pd) (oB (g ())) ((xdOf S0 stm).K + 1)) =
    (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
      (256 + 8 * S0.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
      (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
      (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
      (readBlocks (implAtPd B S0 stm Lf dec hcfg V pd) g) :=
  read_verifyBSPd (xdOf S0 stm) dec B Lf embS pd hcfg V F hOwn g (withStatement S0 (stm r0 r1)) rfl
    O' hO (own_of_ok (inFile S0.base) hok) hn seen b i o j e (bytesToDig r0) (bytesToDig r1)
    (hstm _ _ (size_digToBytes _) (size_digToBytes _)) π hπ

/-- THE SAME WITH THE PARAMETERS' DIGEST PINNED AT pd. The reader stands at the hash of the
function that g induces on byte strings, but for the one string of the call that hashes the
parameter bytes, which is answered with the bytes of pd: the same pd that stands in the first
query's string and in `famXPd`. The original's `pinned_verifyBS` is the case of the format's own
digest. -/
theorem pinned_verifyBSPd (pd : Dig 256) (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf embS)
    (hok : PQ.ok (inFile S0.base) = true) (hn : S0.base.rand.isNone = false)
    (hstm : ∀ a b : ByteArray, a.size = 32 → b.size = 32 → (stm a b).size < 2 ^ 64)
    (g : Fam (rom 256)) (r0 r1 : ByteArray)
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id)
      (_root_.Fmt.HO (pinnedAt (oB (g ())) S0.base.params (digToBytes pd)))
      (withStatement S0 (stm r0 r1)) seen b i = some (o, j))
    (π : OneProtocolProof 256 (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up)
    (hπ : toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
      (xdOf S0 stm).xs dec o = some π) :
    (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
      (256 + 8 * S0.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
      (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
      (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
      (famXPd B (xdOf S0 stm) dec (digToBytes pd) (oB (g ())) ((xdOf S0 stm).K + 1)) =
    (verifyOneProtocol (lam := 256) (K := (xdOf S0 stm).K + 1) (L := (xdOf S0 stm).L Bd dec)
      (256 + 8 * S0.base.plan.salt) 256 .link
      (skeletonOverBothExternalStrings (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a (xdOf S0 stm).xs dec).up
      (wX (xdOf S0 stm) dec) embS (embX Bd (xdOf S0 stm) dec)
      (fun _ => none) B.embE 0 [bytesToDig r0, bytesToDig r1] () π).det
      (readBlocks (implAtPd B S0 stm Lf dec hcfg V pd) g) :=
  all_verifyBSPd B S0 stm Lf dec hcfg V embS pd F hOwn hok hn hstm g
    (pinnedAt (oB (g ())) S0.base.params (digToBytes pd))
    (size_pinnedAt _ (fun _ => size_digToBytes _) _ _ (size_digToBytes _)) r0 r1 seen b i o j e π hπ

end TypedOracleCompiler.Run.PQ
