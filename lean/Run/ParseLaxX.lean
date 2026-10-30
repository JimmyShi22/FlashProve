-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ParseLaxX.lean: the lenient reader for a proof file that opens stored tables, and the run
function for an entry file behind it. Definitions only.

A proof file of the programs (the C++ implementation that comes with this Lean code) has no lengths
in it: a reader cuts it into its parts by the description (here a value of `Fmt.SpecX`) and by the
positions that the verifier draws. The strict reader (Fmt/Rules8X.lean, `wholeChainX`: this
library's rendering of the format page's verifier up to its decision; the format page is
docs/format/FORMAT.md, which comes with the programs; here in an edition that is not the one that
ships) also tests the proof of work, recomputes every Merkle path and compares every opened tree's
root, so that a verifier behind it never meets a bad opening. The lenient reader of this file only
cuts the file and checks the form of its parts. To cut it, it too recomputes the hash chain
(`laxQueryW`). Behind it these three checks of the strict reader are made inside the compiled
verifier's run. A stored table's tree (a stored tree) is a Merkle tree whose root is read from the
statement, not from a message of the chain (`Fmt.Stored`, `Fmt.itemRoot`, Fmt/Rules8X.lean).

1. What the file contains.
     `laxStored`: the openings of a round's stored trees, parsed only (`Fmt.rdOpening` at the
       table's own salt length, at the list made from that tree's part of the draws). As the root it
       notes the root in the statement's item; nothing is hashed or compared.
     `cutStepX`, `cutFoldX`, `cutChainX`: after a round's list of positions come first the stored
       trees' openings, then those of the chain's own trees (FORMAT.md, R8.7).
     `laxWholeX h S b`: the lenient reader: the whole file b at the description S (`Fmt.SpecX`) and
       the hash function h, with nothing left behind the chain.
     `runEntryLax D dec r0 file`: the run function for an entry file.
   What the lenient reader still refuses: a description that is not admissible (`S.ok`); a file that
   cannot be cut (too short, too long, a list of positions other than the draws', a word that spells
   no field element, an opening that has not the digests that its list needs); a query that the
   format does not allow (`askOK`); a run value of 32 zero bytes (`Fmt.startChainW` refuses it, here
   as in the strict reader). This list names the main refusals, not every check of form.
   The draws are formed from the file's own bytes. An altered byte that enters the hash chain in
   front of a draw of positions moves the positions, and whether the file can then still be cut
   depends on the bytes.
2. What is checked when the file compiles. Only the types. No file of the programs is read here.
3. Theorems. Nothing is proved in this file. Run/ParseLaxXIs.lean states, and
   Run/ParseLaxXIsProofs.lean proves: whatever the strict reader reads, this reader reads and hands
   on the same but for the strict reader's record of vertices (`laxX_reads`, under the hypotheses of
   its statement); and wherever the run behind the strict reader does not answer "reader",
   `runEntryLax` gives the same outcome (`entry_lax`).
4. What is not claimed. The converse: that a file which the compiled verifier accepts behind this
   reader is read by the strict one. No statement on soundness follows.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Sources. A layer on two files. From Run/ParseLax.lean (the lenient reader for files without stored
tables): `laxQueryW`, a step of the hash chain without the test of work, and `laxOpens`, which
parses the openings of the chain's own trees. From Fmt/Rules8X.lean (at an edition of the format
page that is not the one that ships): `Stored`, `partOf`, `itemRoot`, and the course of `roundX`,
`foldRoundsX`, `readChainX`,
`wholeChainX`, which `cutStepX`, `cutFoldX`, `cutChainX`, `laxWholeX` follow step for step but for
three replacements: `laxQueryW` for `Chain.queryW`, `laxStored` for `readStored`, `laxOpens` for
`readOpens`. Afterwards compared with FORMAT.md, R7.19, R8.7 and R4.6 at a second edition, and
clause by clause with Fmt/Rules8X.lean, in two further, independent readings.

Terms: lean/GLOSSARY.md.
-/
import Run.ParseLax
import Run.PlanQXFast
import Fmt.Rules8XFast

set_option autoImplicit false

namespace Run
open Iop Rom Compile Compile.Batch
open _root_.Fmt (Plan Src OpenOut Spec SpecX Stored St ChainOut Chain)

/-- The openings of a round's stored trees: parsed only. -/
def laxStored (statement : ByteArray) (P : Plan) (poss : List Nat) (b : ByteArray) :
    List Stored → Nat → Option (List (_root_.Fmt.Shape × List Nat × OpenOut) × Nat)
  | [], i => some ([], i)
  | t :: ts, i =>
    let xs := _root_.Fmt.listOf ((_root_.Fmt.partOf t poss).map (· % 2 ^ t.sh.a))
    match _root_.Fmt.itemRoot statement t.item,
      _root_.Fmt.listOK t.sh.a xs,
      _root_.Fmt.rdOpening P.field t.salt t.sh xs b i with
    | some r, true, some ((cs, gv), j) =>
        (laxStored statement P poss b ts j).map fun x =>
          ((t.sh, xs, ⟨cs.map Prod.fst, cs.map Prod.snd, gv, r, [], j⟩) :: x.1, x.2)
    | _, _, _ => none

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- One round: as `Fmt.roundX`, at `laxQueryW`, `laxStored` and `laxOpens`. -/
def cutStepX (statement : ByteArray) (P : Plan) (b : ByteArray) (s : St)
    (r : _root_.Fmt.Round) (ts : List Stored) : m (Option St) :=
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
            match laxStored statement P drawn.poss b ts i2 with
            | none => pure none
            | some (colsS, i2') =>
              match laxOpens P roots drawn.poss b r.opens i2' with
              | none => pure none
              | some (cols, i3) =>
                pure (some
                    ⟨i3, c, roots, s.seen, s.out.push ⟨msg, vals, nonce, drawn, l, colsS ++ cols⟩⟩)

/-- The fold of `cutStepX` over the rounds, each with its stored trees. -/
def cutFoldX (statement : ByteArray) (P : Plan) (b : ByteArray) :
    List (_root_.Fmt.Round × List Stored) → St → m (Option St)
  | [], s => pure (some s)
  | r :: rs, s => do
    match ← cutStepX h statement P b s r.1 r.2 with
    | none => pure none
    | some s' => cutFoldX statement P b rs s'

/-- A chain in a file, from the place i on. -/
def cutChainX (S : SpecX) (b : ByteArray) (i : Nat) : m (Option (ChainOut × Nat)) :=
  if !S.ok then pure none
  else
    let rnd : Option (Option ByteArray × Nat) :=
      match S.base.rand with
      | .inFile => (_root_.Fmt.slice b i 32).map fun x => (some x, i + 32)
      | .given x => some (some x, i)
      | .none => some (none, i)
    match rnd with
    | none => pure none
    | some (x, i0) => do
      let pd ← _root_.Fmt.paramsDigestW h S.base.params
      match ← _root_.Fmt.startChainW h S.base.label pd S.base.statement x with
      | none => pure none
      | some hd =>
        match ← cutFoldX h S.base.statement S.base.plan b (S.base.rounds.zip S.stored)
            ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], [], #[]⟩ with
        | none => pure none
        | some s => pure (some (⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩, s.pos))

/-- The lenient reader of a chain that reads stored tables: and nothing stands behind the chain. -/
def laxWholeX (S : SpecX) (b : ByteArray) : m (Option ChainOut) := do
  match ← cutChainX h S b 0 with
  | some (o, j) => pure (if j == b.size then some o else none)
  | none => pure none

end
end Run

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- Run/PlanQXFast.lean's `runEntryK` with the lenient reader in the place of the strict one: the
eight-byte head and the further table's root (`readHead`); `laxWholeX` at the format's hash in its
fast form; the typing `toBPrfX`; the evaluable form of the compiled verifier under the two roots
(`VXK`). -/
def runEntryLax (D : XD) (dec : View → Bool) (r0 file : ByteArray) : Who :=
  if D.ok then
    match readHead file with
    | none => .reader
    | some (r1, rest) =>
      match (laxWholeX (m := Id) _root_.Fmt.HF (D.atR r0 r1) rest).bind
          (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) with
      | none => .reader
      | some π => if VXK D dec r0 r1 π then .accepted else .verifier
  else .limits

end Run.PQ
