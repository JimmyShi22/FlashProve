-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/EntryInOf.lean: what the fast form of the verifier is handed for the entry file, read out
of an outside parser's form of that file (leaf-k.parsed.bin, magic FPENTC01, and the file of seeds
beside it). It hashes nothing and calls no reader that hashes.
`LeafP`, `rdLeaf`: the parsed file's fields, read as they stand by the format's readers that do not
hash; the text follows OnBytes/ShellOf/EntryParsed.lean. `chainOut`: the chain with what the file
says (the run's value; each round's items and nonce); the fields that only a hash makes are laid
empty, and the term reads none of them (`assembleW`, Johnson/RunOne/StrictLinkW.lean). `tabOwn`,
`tabStored`: the two tables, in the file's order. `laidOf`: the maker, general in the size's
numbers; c, the digest of the public configuration, is an argument and never comes out of the parsed
file. `entryInS`, `entryInD`: they refuse where a reader refuses and where a test in front says no.
Whose the bytes are: the prover's side's, through an outside tool that hashes. What the tool hashed,
the term makes again itself: it holds the rows against the places that the chain draws, hashes every
path to its root, and draws the copy's seed.
Not tested here: that a word is below the prime; a salt's or a column's length; two rows at one
leaf. Whether the term tests each of these is not shown here.
Through Johnson/Top/Fire/Code/VerifyVFastD.lean this file's imports reach modules of the program
`verify-on-bytes`; it calls none of that program's readers.

-/
import Johnson.Top.Fire.Code.VerifyVFastD
import Johnson.Top.Fire.Code.VerifyVFastDS
import OnBytes.Maker.Carrier
import OnBytes.K.ArmLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PV.EntryInOf
open OnBytes OnBytes.Maker OnBytes.Slice
open _root_.Iop (Dig)
open _root_.Run (bytesToDig)
open _root_.Fmt (Rd rdWord rdPair rdDigest rdText rdList ItemValue)

/-- (a tree's number | 0 | 1, a leaf) ↦ (column, the file's salt, the whole path): the table's
  type. -/
abbrev TabE : Type := Johnson.RunOne.StrictB.Tab

/-! ## The parsed leaf file, as it stands -/

def rdMap {α β : Type} (f : α → β) (r : Rd α) : Rd β := fun b i => (r b i).map fun x => (f x.1, x.2)
def rdT3 : Rd (UInt64 × UInt64 × UInt64) := rdPair rdWord (rdPair rdWord rdWord)
def rdNat : Rd Nat := rdMap (·.toNat) rdWord

/-- Item := kind, value. Kind 0: a root; 3: an element; 4: an answer. All others: refused. -/
def rdItem : Rd ItemValue := fun b i =>
  match rdWord b i with
  | some (k, j) =>
    if k == 0 then rdMap ItemValue.root rdDigest b j
    else if k == 3 then rdMap ItemValue.e rdT3 b j
    else if k == 4 then rdMap ItemValue.answer rdT3 b j
    else none
  | none => none

/-- Row := leaf, column, salt, path. -/
structure RowP where
  leaf : Nat
  col : List UInt64
  salt : ByteArray
  path : List ByteArray

def rdRow : Rd RowP :=
  rdMap (fun x => ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩)
    (rdPair rdNat (rdPair (rdList rdWord) (rdPair rdText (rdList rdDigest))))

/-- The ten fields but the magic. -/
structure LeafP where
  root0 : ByteArray
  answers0 : List (UInt64 × UInt64 × UInt64)
  root : ByteArray
  answers : List (UInt64 × UInt64 × UInt64)
  run : ByteArray
  rounds : List (List ItemValue × Nat)
  trees : List (Nat × List RowP)
  stored0 : List RowP
  stored1 : List RowP

/-- TreeRows := tree, chain, rows: the second is dropped. -/
def rdTree : Rd (Nat × List RowP) :=
  rdMap (fun x => (x.1, x.2.2)) (rdPair rdNat (rdPair rdNat (rdList rdRow)))

def magicLeaf : ByteArray := "FPENTC01".toUTF8

/-- The parsed leaf file: whole, or nothing. -/
def rdLeaf (b : ByteArray) : Option LeafP :=
  if b.extract 0 8 == magicLeaf then do
    let (root0, i) ← rdDigest b 8
    let (answers0, i) ← rdList rdT3 b i
    let (root, i) ← rdDigest b i
    let (answers, i) ← rdList rdT3 b i
    let (run, i) ← rdDigest b i
    let (rounds, i) ← rdList (rdPair (rdList rdItem) rdNat) b i
    let (trees, i) ← rdList rdTree b i
    let (stored0, i) ← rdList rdRow b i
    let (stored1, i) ← rdList rdRow b i
    if i == b.size then some ⟨root0, answers0, root, answers, run, rounds, trees, stored0, stored1⟩
    else none
  else none

/-! ## What the term is handed -/

/-- The chain with what the file says; what only a hash makes is laid empty. -/
def chainOut (L : LeafP) : _root_.Fmt.ChainOut where
  pd := ByteArray.empty
  run := some L.run
  rho0 := ByteArray.empty
  rho := ByteArray.empty
  seen := []
  rounds := (L.rounds.map fun r =>
    ({ msg := ByteArray.empty, vals := r.1, nonce := r.2, drawn := ⟨[], [], [], none⟩, list := [],
       opens := [] } : _root_.Fmt.RoundOut)).toArray

def rowsAt (n : Nat) (rows : List RowP) : TabE :=
  rows.map fun r => ((n, r.leaf), (r.col, r.salt, r.path.map bytesToDig))

/-- The own trees' table, in the file's order. -/
def tabOwn (L : LeafP) : TabE := L.trees.flatMap fun t => rowsAt t.1 t.2

/-- The two stored tables' table: the first table's rows under 0, the copy's under 1. -/
def tabStored (L : LeafP) : TabE := rowsAt 0 L.stored0 ++ rowsAt 1 L.stored1

/-- What is laid of a parsed leaf file and its seeds' file. -/
structure Laid (v lg s : ℕ) where
  L : LeafP
  /-- the copy's root -/
  cm' : Dig 256
  /-- the copy's record: the seeds of the file beside; the answers read as typed answers -/
  rcd' : RecP NZ v lg s
  /-- PUBLIC: laid by the caller -/
  cfg : ByteArray
  o : _root_.Fmt.ChainOut
  tab : TabE
  tx : TabE
  front : List (String × Bool)

def Laid.ok {v lg s : ℕ} (m : Laid v lg s) : Bool := m.front.all (·.2)
def Laid.firstNo {v lg s : ℕ} (m : Laid v lg s) : Option String := (m.front.find? fun x => !x.2).map
    (·.1)

/-- **The maker.** rounds: the number of the description's rounds. c: the public configuration's
  digest. -/
def laidOf (v lg s rounds : ℕ) (c leaf seeds : ByteArray) : Except String (Laid v lg s) :=
  match rdLeaf leaf, Carrier.readSeeds seeds with
  | none, _ => .error "entryIn: the parsed leaf file does not read (magic FPENTC01; ten fields; \
      nothing behind)"
  | _, .error w => .error s!"entryIn: the seeds' file beside it does not read: {w}"
  | some L, .ok sd =>
    let t : OnBytes.Params.TableName := ⟨L.root, L.answers.map E.ofTriple⟩
    .ok
      { L := L, cm' := bytesToDig L.root
        rcd' := OnBytes.K.recOne v lg s t (sd.map fun y => (y.1.map E.ofTriple, E.ofTriple y.2))
        cfg := c, o := chainOut L, tab := tabOwn L, tx := tabStored L
        front :=
          [("entryIn 1: five lengths: both roots, the run's value and the public digest have 32 \
              bytes; every digest of a path has",
              L.root0.size == 32 && L.root.size == 32 && L.run.size == 32 && c.size == 32 &&
                ((L.trees.flatMap (·.2)) ++ L.stored0 ++ L.stored1).all fun r => r.path.all (·.size
                    == 32)),
            ("entryIn 2: the copy has 2^v * s answers, and so has the leaf file's copy of the \
                first table",
              L.answers.length == 2 ^ v * s && L.answers0.length == 2 ^ v * s),
            ("entryIn 3: the seeds' file has s seeds of lg coordinates",
              sd.length == s && sd.all fun y => y.1.length == lg),
            ("entryIn 4: as many rounds as the description has", L.rounds.length == rounds)] }

def judged {v lg s : ℕ} (r : Except String (Laid v lg s)) : Except String (Laid v lg s) :=
  match r with
  | .error w => .error w
  | .ok m => match m.firstNo with
    | some n => .error s!"NO at: {n}"
    | none => .ok m

open VerifiableInference.OnPublicFiles in
def Laid.inDS (m : Laid srS.P.v 19 1) : SlotsBehindCutDS.EntryIn := ⟨m.cm', m.rcd', m.cfg, m.o,
    m.tab, m.tx⟩
open VerifiableInference.OnPublicFiles in
def Laid.inD (m : Laid frS.P.v 29 1) : SlotsBehindCutD.EntryIn := ⟨m.cm', m.rcd', m.cfg, m.o, m.tab,
    m.tx⟩

/-- The small size: 24 rounds. -/
def laidS (c leaf seeds : ByteArray) : Except String (Laid srS.P.v 19 1) :=
  judged (laidOf srS.P.v 19 1 OnBytes.Flat.dsSmall.length c leaf seeds)
/-- The full size: 41 rounds. -/
def laidD (c leaf seeds : ByteArray) : Except String (Laid frS.P.v 29 1) :=
  judged (laidOf frS.P.v 29 1 OnBytes.Flat.dsFull.length c leaf seeds)

open VerifiableInference.OnPublicFiles in
/-- **The shape for a run, the small size.** -/
def entryInS (c leaf seeds : ByteArray) : Except String SlotsBehindCutDS.EntryIn := (laidS c leaf
    seeds).map Laid.inDS
open VerifiableInference.OnPublicFiles in
/-- **The shape for a run, the full size.** -/
def entryInD (c leaf seeds : ByteArray) : Except String SlotsBehindCutD.EntryIn := (laidD c leaf
    seeds).map Laid.inD

end PV.EntryInOf
