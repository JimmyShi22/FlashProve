-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/Chains.lean: if the program's check of a key file or of a proof file says yes: one flat
statement for each kind of file, at the program's own strict reader of a chain.

OnBytes/TieK/KeyOpen.lean, ProofOpen.lean and TailOpen.lean open the two checks step by step. This
file lays their facts side by side. Each of the three descriptions is named as the function of the
public values, of the file's earlier parts and of dry runs that the program's text makes it. Each
chain stands with the equation at `readChain` (OnBytes/Chain/Reader.lean), with the record of tree
vertices as it is carried from chain to chain: the first chain is read from the empty record, each
later chain from the record that the chain before it left. `readChain_eq`
(OnBytes/Chain/ReaderLaws.lean) turns such an equation into one at `Fmt.readChainX`.

`ThreeChains` holds what a key file and a proof file have in common, from the first chain's
description on. The second chain is cut at dry values and judged at real ones: its rounds come from
its block at `dry` and at the shared chain's dry end `dry2`; the run that decides is that of its
block at `real` and at the shared chain's real end `real2`. Both stand in the statement. That the
two blocks have the same rounds is not stated here.

Main definitions: `ThreeChains`.
Main theorems: `readIn_open`, `key_check_chains`, `proof_check_chains`.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.TieK.KeyOpen
import OnBytes.TieK.ProofOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof OnBytes.Tie

/-- What a reading step of a session has done if it returns. -/
theorem readIn_open (S : Fmt.SpecX) (b : ByteArray) (i : Nat) (s s' : Session) (r : ChainRead)
    (h : readIn S b i s = some (r, s')) :
    readChain S s.seen b i = some (r.out, r.next) ∧ r.view = viewOf S r.out ∧
      s'.seen = r.out.seen := by
  unfold readIn at h
  split at h
  · cases h
  · rename_i o j ho
    injection h with h'
    have e1 : (⟨o, viewOf S o, j⟩ : ChainRead) = r := congrArg (·.1) h'
    have e2 : (⟨o.seen⟩ : Session) = s' := congrArg (·.2) h'
    subst e1
    subst e2
    exact ⟨ho, rfl, rfl⟩

/-- What a key file and a proof file have in common if the program's check says yes. p: what is
public about the tail; block1, start1: the first chain's block and what it starts from; S1: the
first chain's description; i: the place of the first chain's first byte. -/
structure ThreeChains (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start) (file : ByteArray)
    (i : Nat) (rounds1 : Params.Rounds) (dry : FirstEnd) (S1 : Fmt.SpecX) (r : TailRead)
    (seal1 seal2 : ByteArray) (rounds2 : Params.Rounds) (dry2 : SharedEnd) (S2 : Fmt.SpecX)
    (rounds3 : Params.Rounds) (S3 : Fmt.SpecX) (real : FirstEnd) (real2 : SharedEnd) : Prop where
  /-- the first chain's rounds come from a dry run of its block -/
  first_dry : block1.dryRun start1 = some (rounds1, dry)
  /-- the first chain was read from the empty record of vertices -/
  first_read : readChain S1 [] file i = some (r.first.out, r.first.next)
  first_view : r.first.view = viewOf S1 r.first.out
  first_seal : r.first.seal = some seal1
  /-- the place in the binding tree was read behind the first chain, under its seal -/
  place_read : readPlace p.binding p.shared.given.cfg seal1 file r.first.next = some r.place
  key_made :
    tableKey p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index p.table 0 = some r.key
  /-- the shared chain's rounds come from a dry run of its block -/
  shared_dry : (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (rounds2, dry2)
  /-- its description holds the binding tree's root as read -/
  shared_spec : p.shared.describe p.lab₂ p.table r.place.root rounds2 = some S2
  /-- it was read from the record of vertices that the first chain left -/
  shared_read :
    readChain S2 r.first.out.seen file r.place.next = some (r.shared.out, r.shared.next)
  shared_view : r.shared.view = viewOf S2 r.shared.out
  shared_seal : r.shared.seal = some seal2
  /-- the second chain's rounds come from its block at the two dry ends -/
  second_rounds :
    (secondBlock p.lin dry.lin (dry2.goesOn r.shared)).rounds (secondStart p dry r.first) =
      some rounds3
  /-- its description holds both seals -/
  second_spec : p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree r.first) = some S3
  /-- it was read from the record of vertices that the shared chain left -/
  second_read :
    readChain S3 r.shared.out.seen file r.shared.next = some (r.second.out, r.second.next)
  second_view : r.second.view = viewOf S3 r.second.out
  /-- no byte is left over -/
  whole : r.second.next = file.size
  /-- the three blocks' runs on the three views, the second chain's at the two real ends -/
  first_yes : block1.runOn start1 r.first.view = .ok real
  shared_yes : (sharedBlock p.lin r.key).runOn (sharedStart p) r.shared.view = .ok real2
  second_yes :
    (secondBlock p.lin real.lin (real2.goesOn r.shared)).runOn (secondStart p real r.first)
      r.second.view = .ok ()

/-- The common part, from the facts of the steps. -/
theorem threeChains_of (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start) (file : ByteArray)
    (i : Nat) (rounds1 : Params.Rounds) (dry : FirstEnd) (S1 : Fmt.SpecX) (r : TailRead)
    (s1 s' : Session) (real : FirstEnd) (real2 : SharedEnd)
    (hdry : block1.dryRun start1 = some (rounds1, dry))
    (hread : readIn S1 file i Session.start = some (r.first, s1))
    (htail : readTail p dry r.first file s1 = .ok (r, s')) (hwhole : r.next = file.size)
    (hyes : block1.runOn start1 r.first.view = .ok real) (ht : TailYes p real r real2) :
    ∃ seal1 seal2 rounds2 dry2 S2 rounds3 S3,
      ThreeChains p block1 start1 file i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3
        real real2 := by
  obtain ⟨seal1, seal2, rounds2, dry2, S2, s2, rounds3, S3, f⟩ := readTail_open _ _ _ _ _ _ _ htail
  obtain ⟨a1, a2, a3⟩ := readIn_open _ _ _ _ _ _ hread
  obtain ⟨b1, b2, b3⟩ := readIn_open _ _ _ _ _ _ f.shared_read
  obtain ⟨c1, c2, _⟩ := readIn_open _ _ _ _ _ _ f.second_read
  rw [a3] at b1
  rw [b3] at c1
  exact ⟨seal1, seal2, rounds2, dry2, S2, rounds3, S3,
    ⟨hdry, a1, a2, f.seal_first, f.place_read, f.key_made, f.shared_dry, f.shared_spec, b1, b2,
      f.seal_shared, f.second_rounds, f.second_spec, c1, c2, hwhole, hyes, ht.shared_yes,
      ht.second_yes⟩⟩

/-- **A key file: if the program's check says yes.** The one-time chain's field and public values
have passed their tests; the table was read; the one-time chain's
description is made of its dry run's rounds and the table; then the three chains. -/
theorem key_check_chains (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName)
    (h : Key.check k file = .ok table) :
    ∃ j rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2,
      (k.oneTime.given.plan.field != .two) = false ∧ (!Key.admitted k.oneTime) = false ∧
      Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) ∧
      k.oneTime.describe table rounds1 = some S1 ∧
      ThreeChains (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
        rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2 := by
  obtain ⟨j, r, s', rounds1, dry, S1, s1, real, real2, f⟩ := key_check_open k file table h
  obtain ⟨seal1, seal2, rounds2, dry2, S2, rounds3, S3, t⟩ :=
    threeChains_of _ _ _ _ _ _ _ _ _ _ _ _ _ f.read.first_dry f.read.first_read f.read.tail_read
      f.read.whole f.first_yes f.tail_yes
  exact ⟨j, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2,
    f.field_two, f.admitted, f.table_read, f.read.first_spec, t⟩

/-- **A proof file: if the program's check says yes.** The head was read, with the number of the
stored copy that the caller holds; the first chain's field is the program's and its digest of the
public files is not 32 zero bytes; the first chain's description is made of its dry run's rounds,
the table, that number, the request's bytes and the request file's words; then the three chains. -/
theorem proof_check_chains (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (reply : E) (links : Blk LinksResult) (file : ByteArray)
    (h : check c table copy request words reply links file = .accepted) :
    ∃ i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2,
      readProofHead c.first.given.plan.field file = .ok (copy, i) ∧
      (c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32) = false ∧
      c.first.describe table copy request words rounds1 = some S1 ∧
      ThreeChains (tailPublic c table) (firstBlock c.first links reply) (firstStart c.first) file i
        rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2 := by
  obtain ⟨r, s', i, rounds1, dry, S1, s1, real, real2, f⟩ :=
    proof_check_open c table copy request words reply links file h
  obtain ⟨seal1, seal2, rounds2, dry2, S2, rounds3, S3, t⟩ :=
    threeChains_of _ _ _ _ _ _ _ _ _ _ _ _ _ f.read.first_dry f.read.first_read f.read.tail_read
      f.read.whole f.first_yes f.tail_yes
  exact ⟨i, rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, real, real2,
    f.read.head_read, f.read.params_ok, f.read.first_spec, t⟩

end OnBytes.TieK
