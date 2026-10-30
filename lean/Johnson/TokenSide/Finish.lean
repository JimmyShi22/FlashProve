-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/Finish.lean: THE COMPILED PROVER OF ONE SLOT AS A TOKEN PROGRAM, for the second
form: the coins, ALL HASHING OF A RUN (hashT: the chain of Johnson/TokenSide/Chain.lean behind its
coins, with no reveal), and the way from tokens to values, at which the proof string is made.
DEFINITIONS ALONE.

The whole run is proveC (Johnson/TokenRules/Chunks.lean): hashT, then the end of a run (endC,
there). It is the twin of "the compiled prover, and then what is handed out of its outcome": of
shown stop (proveX ..) (OnBytes/Prover/Defs.lean; shown: Johnson/WholeKey/Defs.lean). Its order:
  1. the first salt: a token of sFS bits; the coins that are values (drawD);
  2. the chain: all hashing, no reveal;                                    (1 and 2: hashT, here)
  3. if the chain has no value (a round without a format; a search that ran out): "none";
  4. THE TEST FOR A STOP, on the verifier messages, which are values: if it says stop: "none";
  5. else the reveals and the proof string.                                (3 to 5: endC, there)
In the cases 3 and 4 no token of the run is ever shown, so in the mode in which marked evaluations
are deferred (mode I of Rom/Defer.lean) nothing of that run is ever written into the table. The test
has to stand before the reveals for that; in the plain scheme, where a reveal is a read, the order
makes no difference.

WHAT IS SHOWN if the string is handed out: the first salt; the chain's tokens (OutT.toks: the
chaining values of all tries, the slot value, the request path); for each position that the verifier
reads in the prover's own oracles, the two tokens of its leaf; for each position that it reads in
the external strings, the two tokens of that leaf in the committer's tree. Which positions are read
is a function of values: the instance, the verifier messages, the plain parts as hashed. openT names
a read position's tokens by the leaf at which the wire says that the position stands. endC picks a
leaf by its place (it is shown if the position that the wire lays at it is read): under the wire's
laws the same leaves (mem_shownK, Johnson/TokenSide/TieRun.lean).

THE PROOF STRING IS MADE BY THE COMPILED PROVER's OWN finish (OnBytes/Prover/Defs.lean), called at
what the chain has yielded with the revealed values in the place of the tokens (outK, TreeT.toK). A
leaf that was not opened has no revealed value, and its salt in these trees is the start alone;
finish reads a tree's salts at opened leaves alone.

Main names (namespace OnBytes.TokenSide).
  RunLen   the lengths and the fixed values of a run's coins.
  drawD    the coins that are values.
  trT, openT   the transcript as hashed; a position's tokens.
  keptK, outK, coinsK  from tokens to values.
  hashT    ALL HASHING OF A RUN (no reveal).

Limits. Definitions alone: that hashT erases to the compiled prover's chain behind its coins, keeps
the rules, and how many evaluations it makes, is not shown here (the first:
Johnson/TokenSide/TieHash.lean; for the whole run proveC: Johnson/TokenSide/TieRun.lean). One slot.
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Chain

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The coins -/

/-- The lengths and the fixed values of the coins of a compiled run. -/
structure RunLen (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  /-- the bits of the first salt -/
  sFS : ℕ
  /-- the free bits of a leaf's salt -/
  fr : ℕ
  /-- the free bits of the string behind the slot value -/
  rs : ℕ
  /-- the public end of that string -/
  rsw : Bits
  /-- the number of sibling digests: the depth of the request tree -/
  dq : ℕ
  /-- the body of a leaf at which no position stands -/
  pad : Body L
  /-- the slot -/
  slot : ℕ

/-- The coins that are values: the free bits of the string behind the slot value, the sibling
digests. -/
def drawD (ln : RunLen lam L) : StT lam K L (CoinsD lam L) :=
  (bitsT (K := K) (L := L) ln.rs).bind fun u =>
    (digsT (K := K) (L := L) ln.dq).bind fun ds => .pure ⟨ln.pad, ln.slot, ds, u ++ ln.rsw⟩

/-! ## The transcript, and a position's tokens -/

/-- the transcript as it was hashed: the twin of trK -/
def trT : (s : Shape) → KeptT lam L s → Rho s → Tr s
  | [], _, _ => ()
  | _ :: s, (kp, ks), (c, ρ) => (kp.1, c, trT s ks ρ)

/-- the tokens of the leaf at which a position stands: the leaf that opensK opens -/
def openT : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → KeptT lam L s → OPos s → List Tok
  | [], _, _, _, p => nomatch p
  | _ :: _, (a, _), (w, _), (kp, _), .inl p =>
      match (if a.own p then kp.2.2 else kp.2.1)[w.tree p]? with
      | some T => T.toksAt (w.place p)
      | none => []
  | _ :: s, (_, A), (_, W), (_, ks), .inr q => openT s A W ks q

/-! ## From tokens to values -/

/-- what is kept, at values of the tokens; st i b: the start of a leaf's salt in round number i, in
a tree over the slot's component (b = true) or over the shared one -/
def keptK (val : Tok → Bits) (st : ℕ → Bool → Bits) : (s : Shape) → ℕ → KeptT lam L s → Kept lam L s
  | [], _, _ => ()
  | _ :: s, i, (kp, ks) =>
      ((kp.1, kp.2.1.map (TreeT.toK val (st i false)), kp.2.2.map (TreeT.toK val (st i true))),
        keptK val st s (i + 1) ks)

/-- what the chain yields, at values of the tokens: the compiled prover's OutP -/
def outK (val : Tok → Bits) (st : ℕ → Bool → Bits) {s : Shape} (z : OutT lam L s) : OutP lam L s :=
  (z.rho, keptK val st s 0 z.kept, z.ph.val lam val, z.rq.map fun u => digOf lam (val u))

/-- the compiled prover's coins, as far as finish reads them -/
def coinsK (salt : Bits) (cd : CoinsD lam L) : Coins lam L :=
  ⟨salt, fun _ _ _ _ => [], cd.pad, cd.slot, cd.path, cd.rsalt⟩

section Prove
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L)
  (pre : ℕ → Bool → Bits → Bits) (cap : ℕ → ℕ)

/-- **All hashing of a run**: the first salt, the coins that are values, the chain. NO REVEAL. It
gives the token of the first salt, these coins, and what the chain yields. -/
def hashT : StT lam K L (Tok × CoinsD lam L × Res (OutT lam L Q.loc.shape)) :=
  Step.fresh ln.sFS fun salt =>
  (drawD (K := K) ln).bind fun cd =>
  (chainT t cms (xin x) ln.fr pre salt cd cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ).bind
    fun r => .pure (salt, cd, r)

end Prove

end OnBytes.TokenSide
