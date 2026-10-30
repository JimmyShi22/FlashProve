-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ThreeRead.lean: what the verifier program's reading of a key file or of a proof file
has done if it returns: the three descriptions and the three readings, at the value r that the
caller holds.

Statements and proofs. OnBytes/TieK/Chains.lean lays the facts of a check that said yes side by side
(`ThreeChains`): facts of the reading and facts of the decision. Here the facts of the reading stand
alone (`ThreeRead`), with the same names and letters, and they are had from the reading's own
equation: no decision is asked. r is the caller's letter: the value of `Key.readKey` or of
`Proof.readProof`, run from the empty record of vertices.

Main names:
  `ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃`: the first chain's
    rounds come from a dry run of its block; it was read from the empty record; the place, the
    table's key; the shared chain's dry run, description and reading, from the record that the
    first chain left; the second chain's rounds, description and reading, from the record that the
    shared chain left; the three views; the two seals; no byte is left over.
  `ThreeChains.toRead`: the record of a check that said yes holds it.
  `threeRead_of`: from the first chain's reading and the tail's.
  `threeRead_of_readKey`, `threeRead_of_readProof`: at a value r of the program's two readers.
Under "there are" in the last two stand the rounds, the dry runs' values, the descriptions, the
seals and (for a proof file) the place of the first chain's first byte. Each is fixed by an equation
of `ThreeRead` or beside it: the dry runs, the describes, the seals' equations, the head's reading.
Limits: nothing on a decision. Nothing on what a chain proves. At a letter p the labels `p.lab₂` and
`p.lab₃` are any numbers: they are the format's at `Key.tailPublic` and `Proof.tailPublic` alone.
Nothing on soundness.


-/
import OnBytes.TieK.Chains

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)

/-- **The facts of the reading of a file's three chains.** p: what is public about the tail;
block1, start1: the first chain's block and what it starts from; S₁: the first chain's description;
i: the place of the first chain's first byte. -/
structure ThreeRead (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start) (file : ByteArray)
    (i : ℕ) (R₁ : Rounds) (dry : FirstEnd) (S₁ : Fmt.SpecX) (r : TailRead)
    (seal1 seal2 : ByteArray) (R₂ : Rounds) (dry2 : SharedEnd) (S₂ : Fmt.SpecX) (R₃ : Rounds)
    (S₃ : Fmt.SpecX) : Prop where
  first_dry : block1.dryRun start1 = some (R₁, dry)
  first_read : readChain S₁ [] file i = some (r.first.out, r.first.next)
  first_view : r.first.view = viewOf S₁ r.first.out
  first_seal : r.first.seal = some seal1
  place_read : readPlace p.binding p.shared.given.cfg seal1 file r.first.next = some r.place
  key_made :
    tableKey p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index p.table 0 = some r.key
  shared_dry : (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (R₂, dry2)
  shared_spec : p.shared.describe p.lab₂ p.table r.place.root R₂ = some S₂
  shared_read :
    readChain S₂ r.first.out.seen file r.place.next = some (r.shared.out, r.shared.next)
  shared_view : r.shared.view = viewOf S₂ r.shared.out
  shared_seal : r.shared.seal = some seal2
  second_rounds :
    (secondBlock p.lin dry.lin (dry2.goesOn r.shared)).rounds (secondStart p dry r.first) =
      some R₃
  second_spec : p.second.describe p.lab₃ seal1 seal2 R₃ (secondFirstTree r.first) = some S₃
  second_read :
    readChain S₃ r.shared.out.seen file r.shared.next = some (r.second.out, r.second.next)
  second_view : r.second.view = viewOf S₃ r.second.out
  whole : r.second.next = file.size

/-- The record of a check that said yes holds the facts of the reading. -/
theorem _root_.OnBytes.TieK.ThreeChains.toRead {p : TailPublic} {block1 : Blk FirstEnd}
    {start1 : Start} {file : ByteArray} {i : ℕ} {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX}
    {r : TailRead} {seal1 seal2 : ByteArray} {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX}
    {R₃ : Rounds} {S₃ : Fmt.SpecX} {real : FirstEnd} {real2 : SharedEnd}
    (T : ThreeChains p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃ real real2) :
    ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃ :=
  ⟨T.first_dry, T.first_read, T.first_view, T.first_seal, T.place_read, T.key_made, T.shared_dry,
    T.shared_spec, T.shared_read, T.shared_view, T.shared_seal, T.second_rounds, T.second_spec,
    T.second_read, T.second_view, T.whole⟩

/-- **From the first chain's reading and the tail's.** -/
theorem threeRead_of (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start) (file : ByteArray)
    (i : ℕ) (R₁ : Rounds) (dry : FirstEnd) (S₁ : Fmt.SpecX) (r : TailRead) (s1 s' : Session)
    (hdry : block1.dryRun start1 = some (R₁, dry))
    (hread : readIn S₁ file i Session.start = some (r.first, s1))
    (htail : readTail p dry r.first file s1 = .ok (r, s')) (hwhole : r.next = file.size) :
    ∃ seal1 seal2 R₂ dry2 S₂ R₃ S₃,
      ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃ := by
  obtain ⟨seal1, seal2, R₂, dry2, S₂, s2, R₃, S₃, f⟩ := readTail_open _ _ _ _ _ _ _ htail
  obtain ⟨a1, a2, a3⟩ := readIn_open _ _ _ _ _ _ hread
  obtain ⟨b1, b2, b3⟩ := readIn_open _ _ _ _ _ _ f.shared_read
  obtain ⟨c1, c2, _⟩ := readIn_open _ _ _ _ _ _ f.second_read
  rw [a3] at b1
  rw [b3] at c1
  exact ⟨seal1, seal2, R₂, dry2, S₂, R₃, S₃,
    ⟨hdry, a1, a2, f.seal_first, f.place_read, f.key_made, f.shared_dry, f.shared_spec, b1, b2,
      f.seal_shared, f.second_rounds, f.second_spec, c1, c2, hwhole⟩⟩

/-- A reading that returns from the empty record, as an equation with the record that it left. -/
theorem fromStart_returns {α : Type} {w : Reading α} {x : α} (h : w.fromStart = .ok x) :
    ∃ s', w Session.start = .ok (x, s') := by
  unfold Reading.fromStart at h
  cases hq : w Session.start with
  | error e => rw [hq] at h; cases h
  | ok y =>
    rw [hq] at h
    injection h with hy
    exact ⟨y.2, by rw [← hy]⟩

/-- **A key file, at the value r of the program's reader.** j: the place behind the table's
record. -/
theorem threeRead_of_readKey (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r) :
    ∃ R₁ dry S₁ seal1 seal2 R₂ dry2 S₂ R₃ S₃,
      k.oneTime.describe table R₁ = some S₁ ∧
      ThreeRead (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
        R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃ S₃ := by
  obtain ⟨s', hs'⟩ := fromStart_returns h
  obtain ⟨R₁, dry, S₁, s1, f⟩ := readKey_open _ _ _ _ _ _ _ hs'
  obtain ⟨seal1, seal2, R₂, dry2, S₂, R₃, S₃, t⟩ :=
    threeRead_of _ _ _ _ _ _ _ _ _ _ _ f.first_dry f.first_read f.tail_read f.whole
  exact ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃, S₃, f.first_spec, t⟩

/-- **A proof file, at the value r of the program's reader.** block: the first chain's block. -/
theorem threeRead_of_readProof (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
    (h : (readProof c table copy request words block file).fromStart = .ok r) :
    ∃ i R₁ dry S₁ seal1 seal2 R₂ dry2 S₂ R₃ S₃,
      readProofHead c.first.given.plan.field file = .ok (copy, i) ∧
      c.first.describe table copy request words R₁ = some S₁ ∧
      ThreeRead (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2 R₂
        dry2 S₂ R₃ S₃ := by
  obtain ⟨s', hs'⟩ := fromStart_returns h
  obtain ⟨i, R₁, dry, S₁, s1, f⟩ := readProof_open _ _ _ _ _ _ _ _ _ _ hs'
  obtain ⟨seal1, seal2, R₂, dry2, S₂, R₃, S₃, t⟩ :=
    threeRead_of _ _ _ _ _ _ _ _ _ _ _ f.first_dry f.first_read f.tail_read f.whole
  exact ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃, S₃, f.head_read, f.first_spec, t⟩

end OnBytes.Maker
