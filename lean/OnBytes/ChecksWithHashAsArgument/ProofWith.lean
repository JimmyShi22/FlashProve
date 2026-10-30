-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/ProofWith.lean: a twin of the port's reading and check of a proof file (and of the
tail that a key file shares with it), with all that hashes as arguments; and its tie: at the port's
own four functions it is the port's text.
Why: the verifier of the theorem aimed at (VerifyB H …) types a proof file at every hash H; the
typing is made from a twin of the port's own strict reader. Proof.check has no hash among its
arguments: its chains run at the port's reader readIn, its place at Fmt.bindLeaf | Fmt.vertexB, its
record's seeds at recordSeeds. The entry file's twin has the same shapes (checkWith: the chain's
reader as a parameter; keyWith: the seeds' function as a parameter).
  HashFns  the four things that hash: rd (a chain's strict reader within a session), leafB (the
      binding tree's leaf), vertB (its vertex), sd (the seeds of a table's record)
  HashFns.port  the port's own: readIn, Fmt.bindLeaf, Fmt.vertexB, recordSeeds
  climbW, readPlaceW, tableKeyW, readNamedW, readTailW, readProofW, checkW  the port's text, by
      copy, with these in the places of the four
  climbW_port … checkW_port  at HashFns.port each is the port's function (by unfolding: if the
      port's text moves, these break: meant so)
The decision (proofRefusal | tailRefusal | judge) hashes nothing: it is the port's own term in
checkW.
A refusal's name is made as the port makes it (readerName: a second pass by the port's own hash): at
other functions the name of a reader's refusal means nothing; whether a file is accepted hangs on no
name.
Which text: this twin copies five files of the port: Proof/File, Tail, Place, Reading, and
Entry/Table. The ties by unfolding fail to build if that text moves: meant so. The twin made by
program over a monad (OnBytes.TwoPort.M) is the one by which the three typings ask; this file and
a file of this project that is not in this library stay as tools of the plain side.
  HashFns.at q h  the four at one hash: rd := the port's own general reader readChainK
      (Chain/Engine.lean) at (q, h); leafB | vertB := the library's bindLeafW | vertexBW at h; sd :=
      recordSeeds' text at q and the library's recordFirstW h
  HashFns.at_port  HashFns.at queryH formatHashFastForm = HashFns.port: not by unfolding: the port is of two
      makes: its chains run at queryH | formatHashFastForm, its place and its seeds at Fmt.formatHash | Fmt.Chain.query:
      by the port's own formatHashFastForm_eq_formatHash, queryH_eq_query
  checkW_at_port  checkW (HashFns.at queryH formatHashFastForm) … = Proof.check …
  checkW_accepted_iff  a yes is: the reading returns some r, and the decision on r refuses nothing
A statement "for all F : HashFns" is about nothing: nothing says that four loose functions come of
one hash: let every later statement go through HashFns.at; the record is the proof's tool.
"All that hashes" is said of the text, not of the data: three arguments of checkW are made by
hashing before the call, by the port's own hashes: cfg (the call 169, index 2), request (708 bytes
with five digests of the second hash function), the public tables' digests; the ID (179) is outside
too. The argument words (the fourth item of the first chain's statement: for a model's proof the
request file, whole) is made by no hash: it goes into the statement as it comes.
"The decision hashes nothing" rests on a search of the text (for a dozen words of hashing over 18
files of Iop/, Chain/Draws | Loops, Key/Ranges, Result, Walk), and links is an argument: Model/ was
not walked.
What is not said. HashFns.at at an oracle O (q, h made of O): it agrees with the port's only within
the hash's domain: that a yes is carried there is not shown in this library. A key file's check
(over readTailW). A Place
holds no salt and no sibling: the typing must cut them from the file again. Nothing on what a yes
means.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Proof.File
import OnBytes.Hash.HEq
import OnBytes.Hash.QueryEq

namespace OnBytes.TwoPort

open OnBytes OnBytes.Proof

/-- The four things that hash. -/
structure HashFns where
  /-- a chain's strict reader within a session -/
  rd : Fmt.SpecX → ByteArray → Nat → InSession ChainRead
  /-- the binding tree's leaf: depth, place, cfg, the seal, the salt -/
  leafB : Nat → Nat → ByteArray → ByteArray → ByteArray → ByteArray
  /-- the binding tree's vertex: cfg, left, right -/
  vertB : ByteArray → ByteArray → ByteArray → ByteArray
  /-- the seeds of a stored table's record: field, the table's name, bits, count -/
  sd : Fmt.Fld → ByteArray → Nat → Nat → Option (List (List E × E))

/-- the port's own -/
def HashFns.port : HashFns := ⟨readIn, Fmt.bindLeaf, Fmt.vertexB, recordSeeds⟩

variable (F : HashFns)

def climbW (cfg b : ByteArray) : (levels : Nat) → (x : ByteArray) → (p i : Nat) →
    Option (ByteArray × Nat)
  | 0, x, _, i => some (x, i)
  | levels + 1, x, p, i =>
    match Fmt.slice b i 32 with
    | none => none
    | some sib =>
      let up := if p % 2 == 1 then F.vertB cfg sib x else F.vertB cfg x sib
      climbW cfg b levels up (p / 2) (i + 32)

def readPlaceW (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : Nat) : Option Place :=
  if !bindingOk s then none
  else
    match Fmt.rdWord b i with
    | none => none
    | some (w, i1) =>
      if 2 ^ s.logLeaves ≤ w.toNat then none
      else
        match Fmt.slice b i1 s.saltBytes with
        | none => none
        | some salt =>
          (climbW F cfg b s.logLeaves (F.leafB s.logLeaves w.toNat cfg closing salt) w.toNat
            (i1 + s.saltBytes)).map fun x => ⟨w.toNat, x.1, 2 ^ s.logLeaves, x.2⟩

def tableKeyW (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape) (table : Params.TableName)
    (item : Nat) : Option TableKey := do
  let seeds ←
    F.sd f
      (Fmt.tableName table.root cfg s.code.logN s.code.ell s.code.r s.v s.answers s.saltBytes)
      s.cubeBits s.answers
  let key : TableKey :=
    { item := item, record := table.answers.toArray, seeds := seeds.map fun x => ⟨x.1, x.2⟩ }
  if key.fits s then some key else none

def readNamedW (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) : Reading ChainRead :=
  fun s =>
    match F.rd S b i s with
    | some y => .ok y
    | none => .error (readerName front S s.seen b i)

def readTailW (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray) :
    Reading TailRead := do
  let g := p.shared.given
  let seal1 ← need "first-chain-seal" first.seal
  let place ← need "place" (readPlaceW F p.binding g.cfg seal1 b first.next)
  let key ← need "table-record" (tableKeyW F g.plan.field g.cfg p.lin.fold.index p.table 0)
  let (rounds2, end2) ← need "shared-chain-parameters"
    ((sharedBlock p.lin key).dryRun (sharedStart p))
  let spec2 ← need "shared-chain-parameters" (p.shared.describe p.lab₂ p.table place.root rounds2)
  let shared ← readNamedW F "shared-chain-" spec2 b place.next
  let seal2 ← need "shared-chain-seal" shared.seal
  let rounds3 ← need "second-chain-parameters"
    ((secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first))
  let spec3 ← need "second-chain-parameters"
    (p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first))
  let second ← readNamedW F "second-chain-" spec3 b shared.next
  pure ⟨first, place, key, shared, second⟩

def readProofW (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Reading ProofRead := do
  let (madeOn, i) ←
    match readProofHead c.first.given.plan.field file with
    | .error e => throw e
    | .ok x => pure x
  if madeOn != copy then throw "made-on-another-stored-copy"
  if c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32 then
    throw "first-chain-parameters"
  let (rounds1, dry) ← need "first-chain-parameters" (block.dryRun (firstStart c.first))
  let spec1 ← need "first-chain-parameters" (c.first.describe table copy request words rounds1)
  let first ← readNamedW F "first-chain-" spec1 file i
  let r ← readTailW F (tailPublic c table) dry first file
  if r.next != file.size then throw "bytes-left-over"
  pure r

def checkW (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk LinksResult) (file : ByteArray) : Verdict :=
  let block := firstBlock c.first links reply
  match (readProofW F c table copy request words block file).fromStart with
  | .error why => .refused ⟨.proof, why⟩
  | .ok r =>
    match proofRefusal c table block r with
    | some why => .refused ⟨.proof, why⟩
    | none => .accepted

/-! ## The tie: at the port's own four functions -/

theorem climbW_port (cfg b : ByteArray) : ∀ (levels : Nat) (x : ByteArray) (p i : Nat),
    climbW HashFns.port cfg b levels x p i = climb cfg b levels x p i
  | 0, _, _, _ => rfl
  | levels + 1, x, p, i => by
    unfold climbW climb
    cases Fmt.slice b i 32 with
    | none => rfl
    | some sib => exact climbW_port cfg b levels _ (p / 2) (i + 32)

theorem readPlaceW_port (s : Params.LinBindingShape) (cfg closing b : ByteArray) (i : Nat) :
    readPlaceW HashFns.port s cfg closing b i = readPlace s cfg closing b i := by
  unfold readPlaceW readPlace
  simp only [climbW_port]
  rfl

theorem tableKeyW_port (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : Params.TableName) (item : Nat) :
    tableKeyW HashFns.port f cfg s table item = tableKey f cfg s table item := by
  unfold tableKeyW tableKey HashFns.port
  rfl

theorem readNamedW_port (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    readNamedW HashFns.port front S b i = readNamed front S b i := by
  unfold readNamedW readNamed HashFns.port
  rfl

theorem readTailW_port (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray) :
    readTailW HashFns.port p dry first b = readTail p dry first b := by
  unfold readTailW readTail
  simp only [readPlaceW_port, tableKeyW_port, readNamedW_port]

theorem readProofW_port (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    readProofW HashFns.port c table copy request words block file = readProof c table copy request
      words
        block file := by
  unfold readProofW readProof
  simp only [readTailW_port, readNamedW_port]
  rfl

/-- At the port's own four functions the twin is the port's check. -/
theorem checkW_port (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk LinksResult) (file : ByteArray) :
    checkW HashFns.port c table copy request words reply links file = check c table copy request
      words reply
        links file := by
  unfold checkW check
  simp only [readProofW_port]
  rfl

/-! ## The four at one hash -/

def rdAt (q : Fmt.Qry) (h : Fmt.Hash) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    InSession ChainRead := fun s =>
  match readChainK Keeper.indexed q h S s.seen b i with
  | none => none
  | some (o, j) => some (⟨o, viewOf S o, j⟩, ⟨o.seen⟩)

def leafAt (h : Fmt.Hash) (depth place : Nat) (cfg closing salt : ByteArray) : ByteArray :=
  Id.run (Fmt.bindLeafW (m := Id) h depth place cfg closing salt)

def vertAt (h : Fmt.Hash) (cfg l r : ByteArray) : ByteArray :=
    Id.run (Fmt.vertexBW (m := Id) h cfg l r)

def sdAt (q : Fmt.Qry) (h : Fmt.Hash) (f : Fmt.Fld) (name : ByteArray) (bits count : Nat) :
    Option (List (List E × E)) :=
  match q ⟨Fmt.recordLabel, Fmt.recordFirstW (m := Id) h name, 0⟩ ByteArray.empty .seeds 0 0
      (Fmt.blocksFor (count * (bits * 18 + 36))) with
  | none => none
  | some (_, vb) =>
    some ((timesT (Fmt.drawSeed f bits) count (Fmt.rowOf vb) 0).1.map fun x =>
      (x.1.map E.ofTriple, E.ofTriple x.2))

/-- The four at one hash: q the chain's step, h the hash. -/
def HashFns.at (q : Fmt.Qry) (h : Fmt.Hash) : HashFns := ⟨rdAt q h, leafAt h, vertAt h, sdAt q h⟩

theorem rdAt_port : rdAt queryH formatHashFastForm = readIn := by
  funext S b i s
  unfold rdAt readIn readChain
  rfl

theorem hId_eq : (Fmt.hId : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) = Fmt.formatHash := rfl

theorem leafAt_port : leafAt formatHashFastForm = Fmt.bindLeaf := by
  funext depth place cfg closing salt
  unfold leafAt Fmt.bindLeaf
  rw [formatHashFastForm_eq_formatHash, hId_eq]

theorem vertAt_port : vertAt formatHashFastForm = Fmt.vertexB := by
  funext cfg l r
  unfold vertAt Fmt.vertexB
  rw [formatHashFastForm_eq_formatHash, hId_eq]

/-- The first value of the seeds' chain at the format's own hash is the format's. -/
theorem recordFirstW_atH (name : ByteArray) :
    Fmt.recordFirstW (m := Id) Fmt.formatHash name = Fmt.recordFirst name := rfl

theorem sdAt_port : sdAt queryH formatHashFastForm = recordSeeds := by
  -- The port's `recordSeeds` is unfolded while it stands alone, without arguments; every further
  -- step is a rewriting by a named equation; a letter x stands for the round's value before the
  -- two texts are compared: written so that no checker need compute that value.
  delta recordSeeds
  funext f name bits count
  rw [sdAt, formatHashFastForm_eq_formatHash, queryH_eq_query, recordFirstW_atH]
  generalize Fmt.Chain.query _ _ _ _ _ _ = x
  cases x with
  | none => rfl
  | some p =>
    cases p
    rfl

/-- At the port's own step and hash the four are the port's. -/
theorem HashFns.at_port : HashFns.at queryH formatHashFastForm = HashFns.port := by
  unfold HashFns.at HashFns.port
  rw [rdAt_port, leafAt_port, vertAt_port, sdAt_port]

/-- The port's check IS the twin at the port's own step and hash. -/
theorem checkW_at_port (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk LinksResult) (file : ByteArray) :
    checkW (HashFns.at queryH formatHashFastForm) c table copy request words reply links file =
      check c table copy request words reply links file := by
  rw [HashFns.at_port, checkW_port]

/-- a yes: the reading returns, and the decision refuses nothing -/
theorem checkW_accepted_iff (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk LinksResult) (file : ByteArray) :
    checkW F c table copy request words reply links file = .accepted ↔
      ∃ r, (readProofW F c table copy request words (firstBlock c.first links reply) file).fromStart
        = .ok
          r ∧
        proofRefusal c table (firstBlock c.first links reply) r = none := by
  unfold checkW
  dsimp only
  cases (readProofW F c table copy request words (firstBlock c.first links reply) file).fromStart
    with
  | error e => exact ⟨fun h => (by cases h), fun ⟨r, h, _⟩ => (by cases h)⟩
  | ok r =>
    dsimp only
    cases hp : proofRefusal c table (firstBlock c.first links reply) r with
    | some why =>
        exact ⟨fun h => (by cases h), fun ⟨r', h, h'⟩ => (by cases h; rw [hp] at h'; cases h')⟩
    | none => exact ⟨fun _ => ⟨r, rfl, hp⟩, fun _ => rfl⟩

end OnBytes.TwoPort
