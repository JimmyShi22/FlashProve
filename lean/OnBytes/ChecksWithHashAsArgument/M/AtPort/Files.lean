-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/Files.lean: the twin over a monad, at the identity monad, the program's
hash and the second hash function's own function, is the port's own text. The checks of a
key file, an entry file and a proof file; the request's item; the two digests.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Reading
import OnBytes.ChecksWithHashAsArgument.M.Proof.File
import OnBytes.ChecksWithHashAsArgument.M.Proof.RequestItem
import OnBytes.ChecksWithHashAsArgument.M.Key.File
import OnBytes.ChecksWithHashAsArgument.M.Entry.File
import OnBytes.ChecksWithHashAsArgument.M.Params.Configure

set_option autoImplicit false

namespace OnBytes.TwoPort.M.AtPort

open OnBytes.Params (TableName IndexShape KeyChains ProofChains)

theorem relP_guard {β : Type} {c : Prop} [Decidable c] (e : String)
    {g : PUnit → M.Proof.Reading Id β} {g' : PUnit → OnBytes.Proof.Reading β}
    (hg : ∀ y, RelP (g y) (g' y)) :
    RelP (if c then throw e >>= g else pure PUnit.unit >>= g)
      (if c then throw e >>= g' else pure PUnit.unit >>= g') := by
  split
  · exact relP_bind (relP_throw _) hg
  · exact relP_bind (relP_pure _) hg

/-! ## The proof file -/

theorem relP_readProof (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (block : Blk OnBytes.Proof.FirstEnd) (file : ByteArray) :
    RelP (M.Proof.readProof (m := Id) formatHashFastForm c table copy request words block file)
      (OnBytes.Proof.readProof c table copy request words block file) := by
  unfold M.Proof.readProof OnBytes.Proof.readProof
  dsimp only
  cases OnBytes.Proof.readProofHead c.first.given.plan.field file <;> dsimp only <;>
    refine relP_bind (by first | exact relP_throw _ | exact relP_pure _) fun x => ?_
  all_goals
    obtain ⟨madeOn, i⟩ := x
    dsimp only
    refine relP_guard _ fun _ => ?_
    refine relP_guard _ fun _ => ?_
    refine relP_bind (relP_need _ _) fun x => ?_
    obtain ⟨rounds1, dry⟩ := x
    refine relP_bind (relP_need _ _) fun spec1 => ?_
    refine relP_bind (relP_readNamed _ _ _ _) fun first => ?_
    refine relP_bind (relP_readTail _ _ _ _) fun r => ?_
    exact relP_guard _ fun _ => relP_pure _

/-- The check of a proof file. -/
theorem proofCheck_port (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk OnBytes.Proof.LinksResult) (file : ByteArray) :
    M.Proof.check (m := Id) formatHashFastForm c table copy request words reply links file =
      OnBytes.Proof.check c table copy request words reply links file := by
  unfold M.Proof.check OnBytes.Proof.check
  dsimp only
  show (match M.Proof.Reading.fromStart (M.Proof.readProof (m := Id) formatHashFastForm c table copy request
      words (OnBytes.Proof.firstBlock c.first links reply) file) with
    | .error why => _
    | .ok r => _) = _
  rw [fromStart_port (relP_readProof _ _ _ _ _ _ _)]
  cases OnBytes.Proof.Reading.fromStart (OnBytes.Proof.readProof c table copy request words
      (OnBytes.Proof.firstBlock c.first links reply) file) with
  | error why => rfl
  | ok r =>
    dsimp only
    cases OnBytes.Proof.proofRefusal c table (OnBytes.Proof.firstBlock c.first links reply) r <;>
        rfl

/-- The request's item, the request file's digest being the second hash function's. -/
theorem requestItem_port (parameterFile scaleFile requestFile : ByteArray) :
    M.Proof.requestItem (m := Id) (fun b => secondHashFunctionTree b) parameterFile scaleFile requestFile =
      OnBytes.Proof.requestItem parameterFile scaleFile requestFile := rfl

/-! ## The key file -/

theorem relP_readKey (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat) :
    RelP (M.Key.readKey (m := Id) formatHashFastForm k table file j) (OnBytes.Key.readKey k table file j) := by
  unfold M.Key.readKey OnBytes.Key.readKey
  dsimp only
  refine relP_bind (relP_need _ _) fun x => ?_
  obtain ⟨rounds, dry⟩ := x
  refine relP_bind (relP_need _ _) fun spec => ?_
  refine relP_bind (relP_readNamed _ _ _ _) fun first => ?_
  refine relP_bind (relP_readTail _ _ _ _) fun r => ?_
  exact relP_guard _ fun _ => relP_pure _

/-- The check of a key file. -/
theorem keyCheck_port (k : KeyChains) (file : ByteArray) :
    M.Key.check (m := Id) formatHashFastForm k file = OnBytes.Key.check k file := by
  unfold M.Key.check OnBytes.Key.check
  dsimp only
  split
  · rfl
  · split
    · rfl
    · cases OnBytes.Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file with
      | error e => rfl
      | ok y =>
        obtain ⟨table, j⟩ := y
        dsimp only
        show (match M.Proof.Reading.fromStart (M.Key.readKey (m := Id) formatHashFastForm k table file j) with
          | .error why => _
          | .ok r => _) = _
        rw [fromStart_port (relP_readKey _ _ _ _)]
        cases OnBytes.Proof.Reading.fromStart (OnBytes.Key.readKey k table file j) with
        | error why => rfl
        | ok r =>
          dsimp only
          cases OnBytes.Key.keyRefusal k table r <;> rfl

/-! ## The entry file -/

attribute [local irreducible] M.tableKey in
theorem entryRead_port (p : Params.Link) (first : TableName) (file : ByteArray) :
    M.Entry.read (m := Id) formatHashFastForm p first file = OnBytes.Entry.read p first file := by
  unfold M.Entry.read OnBytes.Entry.read
  dsimp only
  cases OnBytes.Proof.readHead p.given.plan.field .entry file with
  | error e => rfl
  | ok i =>
    dsimp only
    split
    · rfl
    · cases readTable p.given.plan.field (p.link.table.rows * p.link.table.answers) file i with
      | error e => rfl
      | ok y =>
        obtain ⟨further, j⟩ := y
        dsimp only
        show (match M.tableKey (m := Id) formatHashFastForm p.given.plan.field p.given.cfg p.link.table first 0,
            M.tableKey (m := Id) formatHashFastForm p.given.plan.field p.given.cfg p.link.table further 1 with
          | some k0, some k1 => _
          | _, _ => _) = _
        rw [tableKey_port, tableKey_port]
        cases OnBytes.tableKey p.given.plan.field p.given.cfg p.link.table first 0 with
        | none => rfl
        | some k0 =>
          cases OnBytes.tableKey p.given.plan.field p.given.cfg p.link.table further 1 with
          | none => rfl
          | some k1 =>
            dsimp only
            cases ((linkVerify p.link k0 k1).rounds (OnBytes.Entry.start p)).bind
                (p.describe first further) with
            | none => rfl
            | some spec =>
              dsimp only
              show (match M.Proof.Reading.fromStart
                  (M.Proof.readNamed (m := Id) formatHashFastForm "" spec file j) with
                | .error e => _
                | .ok r => _) = _
              rw [fromStart_port (relP_readNamed _ _ _ _)]
              cases OnBytes.Proof.Reading.fromStart (OnBytes.Proof.readNamed "" spec file j) <;> rfl

/-- The check of an entry file. -/
theorem entryCheck_port (params : ByteArray) (first : TableName) (file : ByteArray) :
    M.Entry.check (m := Id) formatHashFastForm params first file = OnBytes.Entry.check params first file := by
  unfold M.Entry.check OnBytes.Entry.check
  cases Params.Link.read params with
  | none => rfl
  | some p =>
    dsimp only
    show (match M.Entry.read (m := Id) formatHashFastForm p first file with
      | .error e => _
      | .ok r => _) = _
    rw [entryRead_port]
    cases OnBytes.Entry.read p first file with
    | error e => rfl
    | ok r =>
      dsimp only
      cases OnBytes.Proof.judge "" r.block (OnBytes.Entry.start p) r.chain.view <;> rfl

/-! ## The two digests -/

theorem seedsOf_port (s : IndexShape) (cfg : ByteArray) (t : TableName) :
    M.Key.seedsOf (m := Id) formatHashFastForm s cfg t = OnBytes.Key.seedsOf s cfg t := by
  unfold M.Key.seedsOf OnBytes.Key.seedsOf
  exact recordSeeds_port _ _ _ _

theorem commitmentId_port (s : IndexShape) (cfg : ByteArray) (t : TableName) :
    M.Key.commitmentId (m := Id) formatHashFastForm s cfg t = OnBytes.Key.commitmentId s cfg t := by
  unfold M.Key.commitmentId OnBytes.Key.commitmentId
  show M.Key.commitmentIdAt (m := Id) formatHashFastForm s cfg [] t
      ((M.Key.seedsOf (m := Id) formatHashFastForm s cfg t).getD []) = _
  rw [seedsOf_port]
  unfold M.Key.commitmentIdAt OnBytes.Key.commitmentIdAt
  rw [formatHashFastForm_eq_formatHash]
  rfl

theorem configurationDigest_port (files : List ByteArray) :
    M.Params.configurationDigest (m := Id) formatHashFastForm files =
      OnBytes.Params.configurationDigest files := rfl

end OnBytes.TwoPort.M.AtPort
