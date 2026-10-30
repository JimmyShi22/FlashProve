-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseLax.lean: the lenient reader of a proof file: it cuts the file (what it refuses: part 1).

Why. The strict reader (Fmt/Rules8.lean: `wholeChain`; this library's rendering of the format
page's verifier up to its decision) is a whole verifier of the format: it makes the tests of proof
of work, hashes the opened leaves, walks to the Merkle roots. The compiled verifier
(`Compile.Batch.verifyOneProtocol`, the function that the compiler's verifier runs on each proof string; this
head also calls it the typed verifier) hashes the leaves and walks to the roots again, on its own
queries; proof of work is tested where the protocol's `accept` tests it (`Q.loc.accept`). If the
strict reader stands in front of the typed verifier, most altered files never reach it. So that a
refusal comes from the typed verifier itself wherever it can, this reader leaves these tests out.
That is the point of the file, not a gap. The readers and the parser are generic in a monad and in
the hash (h is their first argument), as in Fmt/Rules8.lean. The rule numbers are those of the
format page (docs/format/FORMAT.md, which comes with the programs).

1. What the file contains.  Definitions that can be evaluated.
 What it still has to ask the hash. A file holds no lengths. How many columns and given digests an
 opening has follows from the drawn positions. So this reader computes the parameters' digest, the
 run's value, the first value and each round's blocks, as the strict fold does, in the same order. A
 block is a piece of fixed length, 256 bits, of a round's hash answer (`block`, Fmt/Rules5.lean).
 What it refuses. It refuses data that fail `Spec.ok` or the conditions on a query's data (`askOK`).
 It refuses a file that ends before the last item or has a byte behind it (R8.1). It refuses words
 that spell no element (R1.3), and a run's value of 32 zero bytes (R4.5). It refuses listed
 positions that differ from the derived list (R8.2: the listed positions enter no query and no typed
 string). At an opening it refuses a list of positions that is empty or out of order (R7.8).
 What it does not test. It does not make the test of work (R5.5). It hashes no leaf and no vertex.
 It compares no root (R7.10). It does not test that a vertex has one value under one root (R7.14).
    `laxQueryW h c msg kind work nonce K`: the step of a chain without the test of work.
    `laxOpens P roots poss b os i`: the openings after one draw: parsed only (Fmt/Rules7.lean:
      `rdOpening`). In what it returns, "root" is the root that was sent (or given), "seen" is
      empty.
    `cutStep`, `cutFold`, `cutChain`, `cutWhole`: the counterparts of `step`, `foldRounds`,
      `readChain`, `wholeChain` (Fmt/Rules8.lean), with the reader of openings as a parameter.
    `laxWhole h S b`: `cutWhole` at the reader that only parses.
    `parseLaxW h S T file`: the parser of Run/ParseChain.lean on this reader.

2. What is checked when the file compiles.  Eleven tests (#guard).

3. Theorems. None in this file. That the two readers' outputs have the same `ParseEx.view` is tested
   here at one file. A theorem of that kind is in Run/PageIsReaders.lean (`pi_strict1`, stated in
   Run/PageIs.lean): at the identity monad, at a description within the limits (`ok S`,
   Run/PlanQTypes.lean) and a hash with the format's digest lengths, whatever the strict reader
   reads the lenient one reads, with the same view (`Fmt.viewOf`, Fmt/M1View.lean), every round's
   test of work passed and every opening walking to the root that was sent.

Notation:
  `c : Chain`: a hash chain: the non-interactive form of one protocol, from which its verifier
    messages are drawn (Fmt/Rules5.lean);
  `rho`: its value between two rounds (Fmt/Rules5.lean);
  `kind`: what the verifier's message of a round consists of (`Fmt.Kind`, Fmt/Plan.lean);
  `work`: the round's number of test bits of the proof of work (`Entry.work`, Fmt/Plan.lean);
  `K`: the number of blocks of the verifier's message (`Chain.queryW`, Fmt/Rules5.lean);
  `S`: a description (`Fmt.Spec`, Fmt/Rules8.lean), the data under which a file is read;
  `T`: what the protocol `Q` supplies to the parser (`Typing`, Run/ParseChain.lean);
  `b`, `file`: the file, as bytes.

4. What is not claimed.  This file has no theorem (see 3). What the reader does not test: see 1.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParseChain

namespace Run
open Iop Rom Compile Compile.Batch
open _root_.Fmt (Plan Src OpenOut Spec St ChainOut Chain)

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- The step of a chain, without the work test. -/
def laxQueryW (c : Chain) (msg : ByteArray) (kind : _root_.Fmt.Kind) (work nonce K : Nat) :
    m (Option (Chain × Array ByteArray)) :=
  if _root_.Fmt.askOK c.label c.rho (c.round + 1) msg kind work nonce then do
    let bs ← _root_.Fmt.fetchW h c.label c.rho (c.round + 1)
      msg kind work nonce (_root_.Fmt.firstBlock work + K)
    pure (some (⟨c.label, _root_.Fmt.nextA work bs, c.round + 1⟩, _root_.Fmt.msgA work bs))
  else pure none

end

/-- The openings after one draw of positions: parsed only. -/
def laxOpens (P : Plan) (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) :
    List (_root_.Fmt.Shape × Src) → Nat →
    Option (List (_root_.Fmt.Shape × List Nat × OpenOut) × Nat)
  | [], i => some ([], i)
  | (sh, src) :: os, i =>
    let root : Option ByteArray :=
      match src with
      | .own n => roots[n]?
      | .given r _ => some r
    let xs := _root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))
    match root, _root_.Fmt.listOK sh.a xs, _root_.Fmt.rdOpening P.field P.salt sh xs b i with
    | some r, true, some ((cs, gv), j) =>
        (laxOpens P roots poss b os j).map fun x =>
          ((sh, xs, ⟨cs.map Prod.fst, cs.map Prod.snd, gv, r, [], j⟩) :: x.1, x.2)
    | _, _, _ => none

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- a reader of the openings after one draw of positions: (the run's value, the roots sent so far,
the drawn positions, which trees, the place) ↦ what was read and the place behind it, or a refusal
-/
abbrev OpsW (m : Type → Type) : Type :=
  Option ByteArray → Array ByteArray → List Nat → List (_root_.Fmt.Shape × Src) → Nat →
  m (Option (List (_root_.Fmt.Shape × List Nat × OpenOut) × Nat))

/-- One round: as `Fmt.step`, at `laxQueryW` and the reader of openings `ops`. -/
def cutStep (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s : St) (r : _root_.Fmt.Round) : m (Option St) :=
  match _root_.Fmt.slice b s.pos r.entry.msg with
  | none => pure none
  | some msg =>
    match _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) msg with
    | none => pure none
    | some vals =>
      match _root_.Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => pure none
      | some (nonce, i1) => do
        match ← laxQueryW h s.chain msg r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => pure none
        | some (c, vb) =>
          let drawn := _root_.Fmt.drawRound P.field r.entry r.kind (_root_.Fmt.rowOf vb)
          let l := _root_.Fmt.listOf drawn.poss
          match _root_.Fmt.readList P r.entry.poss l b i1 with
          | none => pure none
          | some (_, i2) =>
            let roots := s.roots ++ (_root_.Fmt.rootsOf vals).toArray
            match ← ops run roots drawn.poss r.opens i2 with
            | none => pure none
            | some (cols, i3) =>
              pure (some ⟨i3, c, roots, s.seen, s.out.push ⟨msg, vals, nonce, drawn, l, cols⟩⟩)

/-- The fold of `cutStep` over the rounds. -/
def cutFold (ops : OpsW m) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List _root_.Fmt.Round → St → m (Option St)
  | [], s => pure (some s)
  | r :: rs, s => do
    match ← cutStep h ops P run b s r with
    | none => pure none
    | some s' => cutFold ops P run b rs s'

/-- A chain in a file, from the place i on. -/
def cutChain (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) (i : Nat) :
    m (Option (ChainOut × Nat)) :=
  if !S.ok then pure none
  else
    let rnd : Option (Option ByteArray × Nat) :=
      match S.rand with
      | .inFile => (_root_.Fmt.slice b i 32).map fun x => (some x, i + 32)
      | .given x => some (some x, i)
      | .none => some (none, i)
    match rnd with
    | none => pure none
    | some (x, i0) => do
      let pd ← _root_.Fmt.paramsDigestW h S.params
      match ← _root_.Fmt.startChainW h S.label pd S.statement x with
      | none => pure none
      | some hd =>
        match ← cutFold h (ops b) S.plan hd.run b S.rounds
            ⟨i0, ⟨S.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
        | none => pure none
        | some s => pure (some (⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩, s.pos))

/-- The same, and nothing stands behind the chain. -/
def cutWhole (ops : ByteArray → OpsW m) (S : Spec) (b : ByteArray) : m (Option ChainOut) := do
  match ← cutChain h ops S b 0 with
  | some (o, j) => pure (if j == b.size then some o else none)
  | none => pure none

/-- The lenient reader: openings are parsed only. -/
def laxWhole (S : Spec) (b : ByteArray) : m (Option ChainOut) :=
  cutWhole h (fun b _ roots poss os i => pure (laxOpens S.plan roots poss b os i)) S b

/-- The lenient parser: the lenient reader, then `toBPrf` (Run/ParseChain.lean). -/
def parseLaxW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (file : ByteArray) :
    m (Option (List (Dig 256) × OneProtocolProof 256 Q)) := do
  let o ← laxWhole h S file
  pure (o.bind (toBPrf T))

end

/-! ## Guards, at the example file of Run/ParseChain.lean and at copies altered here -/

namespace ParseEx

def lax (c : UInt64 × UInt64 × UInt64) (b : ByteArray) : Option ChainOut :=
  laxWhole (m := Id) _root_.Fmt.formatHash (spec c) b
def strict (c : UInt64 × UInt64 × UInt64) (b : ByteArray) : Option ChainOut :=
  _root_.Fmt.wholeChain (m := Id) _root_.Fmt.formatHash (spec c) b

/-- what of an output the first test below compares: the parameters' digest, the run's value, the
roots, the nonces, and of each opening the tree's number, depth, list, columns, salts and given
digests (not `root`, `seen`, `next`) -/
def view (o : ChainOut) :
    String × Option String × List String × List Nat ×
      List (Nat × Nat × List Nat × List (List UInt64) × List String × List String) :=
  (_root_.Fmt.hex o.pd,
    o.run.map _root_.Fmt.hex,
    (rootsB o).map _root_.Fmt.hex,
    o.rounds.toList.map (·.nonce),
    (opensB o).map fun x =>
      (x.1, x.2.2.a, x.2.2.idx, x.2.2.cols,
        x.2.2.salts.map _root_.Fmt.hex, x.2.2.given.map _root_.Fmt.hex))

/-- bit 0 of byte i flipped -/
def flip (b : ByteArray) (i : Nat) : ByteArray := _root_.Fmt.flipAt b i

/-- the word at byte i replaced -/
def setWord (b : ByteArray) (i x : Nat) : ByteArray :=
  b.extract 0 i ++ _root_.Fmt.u64n x ++ b.extract (i + 8) b.size

end ParseEx

-- on the honest file both readers' outputs have the same `ParseEx.view`
#guard (ParseEx.lax (1, 2, 3) ParseEx.file).map ParseEx.view == (ParseEx.strict (1, 2, 3) ParseEx.file).map ParseEx.view
#guard (ParseEx.lax (1, 2, 3) ParseEx.file).isSome
-- read by the lenient reader, refused by the strict one: a byte of a column, of a salt, of a given
-- digest
#guard (ParseEx.lax (1, 2, 3) (ParseEx.flip ParseEx.file 72)).isSome && (ParseEx.strict (1, 2, 3) (ParseEx.flip ParseEx.file 72)).isNone
#guard (ParseEx.lax (1, 2, 3) (ParseEx.flip ParseEx.file 96)).isSome && (ParseEx.strict (1, 2, 3) (ParseEx.flip ParseEx.file 96)).isNone
#guard (ParseEx.lax (1, 2, 3) (ParseEx.flip ParseEx.file 264)).isSome && (ParseEx.strict (1, 2, 3) (ParseEx.flip ParseEx.file 264)).isNone
-- read by both: the last message alone differs: only the protocol's decision can refuse
#guard (ParseEx.lax (1, 2, 3) (ParseEx.flip ParseEx.file 488)).isSome && (ParseEx.strict (1, 2, 3) (ParseEx.flip ParseEx.file 488)).isSome
-- Another nonce, root or random byte moves the drawn positions, and with them the cut of the file:
-- whether the lenient reader then reads depends on whether the new list asks for as many bytes
#guard ((ParseEx.lax (1, 2, 3) (ParseEx.setWord ParseEx.file 64 58)).map fun o => (opensB o).map fun x => x.2.2.idx) == some [[5, 11, 14]]
-- refused by the lenient reader too: one byte short; one byte long; a word that is no element, in a
-- column and in the last message
#guard (ParseEx.lax (1, 2, 3) (ParseEx.file.extract 0 511)).isNone
#guard (ParseEx.lax (1, 2, 3) (ParseEx.file ++ _root_.Fmt.zeroBytes 1)).isNone
#guard (ParseEx.lax (1, 2, 3) (ParseEx.setWord ParseEx.file 72 18446744069414584321)).isNone
#guard (ParseEx.lax (1, 2, 3) (ParseEx.setWord ParseEx.file 488 (30 + 18446744069414584321))).isNone

end Run
