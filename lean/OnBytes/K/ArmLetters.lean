-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/ArmLetters.lean: three definitions for the tie of the entry file: which statements are
served, how a table is read as a record, and how the key file and the entry file are read as a
further table and a typed string; each with the law that ties it to a yes of the program.

The tie of the entry file (OnBytes/K/Parts.lean, `EntryPart`) has three
parameters: `Served`, `recOf` and the reading's `ent`. Here each is a definition, at a ground G of
the entry's link (OnBytes/Tie/EntryGround.lean: the parameter file's lines, the chain's parameters
as read, the rounds of the dry run) and at a description's three public files Z
(OnBytes/K/Served.lean, `Pub`).

 (a) `servedArm Z x` is `servedAt Z x`. It pins x's three public files to Z's (`servedArm_pins`);
     so if Z's parameter file says G's lines, x's does (`servedArm_lines`).
 (b) `recOfArm G Z x t` is the record of the table t: ITS SEEDS ARE THE PROGRAM'S OWN, drawn at the
     table's name under G's parameters at the digest of Z's files (`seedsUnder recordSeeds`); its
     answers are the table's, typed (`recOne`). It reads nothing of x. At a yes of the program on
     files pinned to Z it answers at both tables, with the seeds that the program drew, and the
     pair is the pair of records read off a converter's value (`recOfArm_port`).
 (c) `entArm G Z dec x key ent` reads the first table off the key file's head by the plain reader
     (`Tie.keyAt`), reads the entry file with the program's own reader (`Entry.read`), and types
     what was read of the chain (`assembleS`). It parses and does not search. At a yes of the
     program on files pinned to Z it returns the program's own further table and the typed string
     of what the program read (`entArm_port`).

The records' letters are G's own: G.q.link.table.v, .cubeBits, .answers.

Main definitions: `Pub.digest`, `servedArm`, `recOne`, `recOfArm`, `entArm`.
Main theorems: `servedArm_pins`, `servedArm_lines`, `recOfArm_port`, `entArm_port`.

Not claimed here: soundness or hiding. That the seeds' tests or Link say yes at these values. That
any statement is served. That `entArm` refuses what the program refuses: it leaves out the key
file's proofs, the decision on the entry's chain and the commitment ID. `Entry.read` and
`recordSeeds` hash by Lean's BLAKE2b: these are functions of the bytes under that one hash. For
proofs only; the program does not import this file.


-/
import OnBytes.K.Served
import OnBytes.K.Left.Conv
import OnBytes.K.Left.AsmAt
import OnBytes.K.Left.SibFit

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Tie OnBytes.Slice TypedOracleCompiler.Slice OnBytes.Flat
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)

/-- The digest of a description's three public files, the parameter file first. -/
def Pub.digest (Z : Pub) : ByteArray := Params.configurationDigest [Z.pol, Z.lay, Z.KL]

/-! ## Which statements are served -/

/-- The statements that are served at the public files Z. -/
def servedArm (Z : Pub) (x : UserStm) : Bool := servedAt Z x

/-- A served statement has Z's three public files. -/
theorem servedArm_pins {Z : Pub} {x : UserStm} (h : servedArm Z x = true) :
    x.pol = Z.pol ∧ x.lay = Z.lay ∧ x.KL = Z.KL := by
  unfold servedArm servedAt at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2⟩

/-- If Z's parameter file says G's lines, so does a served statement's. -/
theorem servedArm_lines (G : EntryGround) {Z : Pub} {x : UserStm} (hZ : G.SaysLines Z.pol)
    (h : servedArm Z x = true) : G.SaysLines x.pol := by
  rw [(servedArm_pins h).1]
  exact hZ

/-! ## A table as a record -/

/-- The record made of a table's answers and of seeds. -/
def recOne (v lg s : ℕ) (t : Params.TableName) (l : List (List E × E)) : RecP NZ v lg s :=
  (seedOfC lg s l, anT v s (t.answers.map E.triple))

/-- The two records read off a converter's value are these, table by table. -/
theorem recsOf_eq (v lg s : ℕ) (a : AskedE) :
    recsOf v lg s a = (recOne v lg s a.first a.l0, recOne v lg s a.further a.l1) := rfl

/-- **A table as a record: the program's own seeds at the table's name, and the table's answers.**
The statement is not read. -/
def recOfArm (G : EntryGround) (Z : Pub) (_x : UserStm) (t : Params.TableName) :
    Option (RecP NZ G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers) :=
  (seedsUnder recordSeeds (linkAtCfg G.q Z.digest) t).map
    (recOne G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers t)

/-- **At a yes of the program on files pinned to Z**: both tables are read as records, with the
seeds l0 and l1 that the program drew; and the pair is the pair of records read off a converter's
value with these tables and seeds, whatever it holds of the chain. -/
theorem recOfArm_port (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false) {Z : Pub}
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    (hp : F.pol = Z.pol) (hy : F.lay = Z.lay) (hk : F.KL = Z.KL) (x : UserStm) :
    ∃ (l0 l1 : List (List E × E))
      (c cj : RecP NZ G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers),
      seedsUnder recordSeeds (linkAtCfg G.q Z.digest) table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q Z.digest) further = some l1 ∧
      recOfArm G Z x table = some c ∧ recOfArm G Z x further = some cj ∧
      ∀ o : Fmt.ChainOut, (c, cj) =
        recsOf G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers
          ⟨table, further, l0, l1, o⟩ := by
  obtain ⟨zp, zl, zk⟩ := Z
  dsimp only at hp hy hk
  subst hp hy hk
  obtain ⟨-, l0, l1, -, -, a0, a1, -, -⟩ := Left.read_at G hA h hl
  refine ⟨l0, l1,
    recOne G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers table l0,
    recOne G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers further l1,
    a0, a1, ?_, ?_, fun _ => rfl⟩
  · show (seedsUnder recordSeeds _ table).map _ = _
    rw [show seedsUnder recordSeeds (linkAtCfg G.q (Pub.digest ⟨F.pol, F.lay, F.KL⟩)) table =
      some l0 from a0]
    rfl
  · show (seedsUnder recordSeeds _ further).map _ = _
    rw [show seedsUnder recordSeeds (linkAtCfg G.q (Pub.digest ⟨F.pol, F.lay, F.KL⟩)) further =
      some l1 from a1]
    rfl

/-! ## The key file and the entry file as a further table and a typed string -/

/-- **The reading of the entry file.** The first table comes off the key file's head by the plain
reader; the entry file is read by the program's own reader; what was read of the chain is typed.
`dec`: the decision of the written link, which the typed string's type names and no value here
reads. The statement is not read. -/
def entArm (G : EntryGround) (Z : Pub) {X : Type} (dec : X → _root_.Run.PQ.View → Bool)
    (_x : UserStm) (key ent : ByteArray) :
    Option (Params.TableName × OneProtocolProof 256 (PSXE (entryXD G Z.digest) dec).up) :=
  match Entry.read (linkAtCfg G.q Z.digest) (keyAt G.q.link.table Z.digest key).2.2 ent with
  | .ok r => (assembleS (entryXD G Z.digest) dec r.chain.out).map fun π => (r.further, π)
  | .error _ => none

/-- **At a yes of the program on files pinned to Z** the reading returns the program's own further
table, and the typed string of what the program's reader read of the entry's chain. -/
theorem entArm_port (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false) {Z : Pub}
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    (hp : F.pol = Z.pol) (hy : F.lay = Z.lay) (hk : F.KL = Z.KL)
    {X : Type} (dec : X → _root_.Run.PQ.View → Bool) (x : UserStm) :
    ∃ (r : Entry.EntryRead) (π : OneProtocolProof 256 (PSXE (entryXD G Z.digest) dec).up),
      Entry.read (linkAtCfg G.q Z.digest) table F.ent = .ok r ∧ r.further = further ∧
      assembleS (entryXD G Z.digest) dec r.chain.out = some π ∧
      entArm G Z dec x F.key F.ent = some (further, π) := by
  obtain ⟨zp, zl, zk⟩ := Z
  dsimp only at hp hy hk
  subst hp hy hk
  obtain ⟨r, -, -, hr, hf, -, -, -, -⟩ := Left.read_at G hA h hl
  obtain ⟨π, hπ⟩ := Left.asm G hA h hl hr dec
  have ht := Left.table_at G h hl (Params.configurationDigest [F.pol, F.lay, F.KL])
  refine ⟨r, π, hr, hf, hπ, ?_⟩
  unfold entArm
  rw [show (keyAt G.q.link.table (Pub.digest ⟨F.pol, F.lay, F.KL⟩) F.key).2.2 = table from ht,
    show Entry.read (linkAtCfg G.q (Pub.digest ⟨F.pol, F.lay, F.KL⟩)) table F.ent = .ok r from hr]
  show (assembleS (entryXD G (Pub.digest ⟨F.pol, F.lay, F.KL⟩)) dec r.chain.out).map _ = _
  rw [show assembleS (entryXD G (Pub.digest ⟨F.pol, F.lay, F.KL⟩)) dec r.chain.out = some π
    from hπ, hf]
  rfl

end OnBytes.K
