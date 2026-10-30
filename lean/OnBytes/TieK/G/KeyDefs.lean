-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/G/KeyDefs.lean: the reading of a key file's three chains with the hash as a letter h:
definitions.

Why. OnBytes/TieK/ says what holds where the Lean verifier program has read and judged a key file
(`ThreeChains`, `KeyOpened`, `KeyGood`; the fixed reading `readKeyChains`), at the program's own
hash. A statement that is to hold at every hash function needs these notions with the hash as a
letter. OnBytes/ChecksWithHashAsArgument/M/ has the program's readers written once more over a monad in which the
hash is asked. Here that monad is Id, so a hash is a plain function h.

 - `ThreeChainsG h`: `ThreeChains` (OnBytes/TieK/Chains.lean) with the five clauses that hash turned
   to the twins at h: the three chains (`M.readChain`), the place in the binding tree
   (`M.Proof.readPlace`), the table's key (`M.tableKey`). The fourteen other clauses are to the
   letter, made by program; none names a hash.
 - `readKeyChainsG h k file`: the table by the program's own reader of a table (it does not hash);
   the three chains by the twin's reader at h (`M.Key.readKey`); the rest of the data from these by
   `keyDataOf` (OnBytes/TieK/DataOf.lean), which calls no hash.
 - `KeyOpenedG h k file table`: `KeyOpened` (OnBytes/TieK/PortChains.lean)
   without its clauses on the planner's return, on the digests, on the chains' parameter bytes and
   on the file's size; k stands for the planner's chains of a key file.
 - `KeyGoodG h k d`: at some file, opened so, the reading returns d.

The letter's type is `M.HashM Id`; `Run.HId` (Run/LaxDom.lean) is the same type by unfolding two
abbreviations. It is written so here because this file is to stand on modules that can be linked
into a test program.

Not claimed. No law is here. Nothing on soundness. The program does not import this file.

-/
import OnBytes.ChecksWithHashAsArgument.M.Key.File
import OnBytes.TieK.DataOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.G

open OnBytes.Proof OnBytes.TwoPort

/-- What a key file and a proof file have in common if the check at the hash h says yes. The letters
are those of `ThreeChains`. -/
structure ThreeChainsG (h : M.HashM Id) (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start)
    (file : ByteArray) (i : Nat) (rounds1 : Params.Rounds) (dry : FirstEnd) (S1 : Fmt.SpecX)
    (r : TailRead) (seal1 seal2 : ByteArray) (rounds2 : Params.Rounds) (dry2 : SharedEnd)
    (S2 : Fmt.SpecX) (rounds3 : Params.Rounds) (S3 : Fmt.SpecX) (real : FirstEnd)
    (real2 : SharedEnd) : Prop where
  /-- the first chain's rounds come from a dry run of its block -/
  first_dry : block1.dryRun start1 = some (rounds1, dry)
  /-- the first chain was read from the empty record of vertices -/
  first_read : M.readChain (m := Id) h S1 [] file i =
    (some (r.first.out, r.first.next) : Option (Fmt.ChainOut × Nat))
  first_view : r.first.view = viewOf S1 r.first.out
  first_seal : r.first.seal = some seal1
  /-- the place in the binding tree was read behind the first chain, under its seal -/
  place_read : M.Proof.readPlace (m := Id) h p.binding p.shared.given.cfg seal1 file r.first.next =
    (some r.place : Option Place)
  key_made : M.tableKey (m := Id) h p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index
    p.table 0 = (some r.key : Option TableKey)
  /-- the shared chain's rounds come from a dry run of its block -/
  shared_dry : (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (rounds2, dry2)
  /-- its description holds the binding tree's root as read -/
  shared_spec : p.shared.describe p.lab₂ p.table r.place.root rounds2 = some S2
  /-- it was read from the record of vertices that the first chain left -/
  shared_read : M.readChain (m := Id) h S2 r.first.out.seen file r.place.next =
    (some (r.shared.out, r.shared.next) : Option (Fmt.ChainOut × Nat))
  shared_view : r.shared.view = viewOf S2 r.shared.out
  shared_seal : r.shared.seal = some seal2
  /-- the second chain's rounds come from its block at the two dry ends -/
  second_rounds :
    (secondBlock p.lin dry.lin (dry2.goesOn r.shared)).rounds (secondStart p dry r.first) =
      some rounds3
  /-- its description holds both seals -/
  second_spec : p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree r.first) = some S3
  /-- it was read from the record of vertices that the shared chain left -/
  second_read : M.readChain (m := Id) h S3 r.shared.out.seen file r.shared.next =
    (some (r.second.out, r.second.next) : Option (Fmt.ChainOut × Nat))
  second_view : r.second.view = viewOf S3 r.second.out
  /-- no byte is left over -/
  whole : r.second.next = file.size
  /-- the three blocks' runs on the three views, the second chain's at the two real ends -/
  first_yes : block1.runOn start1 r.first.view = .ok real
  shared_yes : (sharedBlock p.lin r.key).runOn (sharedStart p) r.shared.view = .ok real2
  second_yes :
    (secondBlock p.lin real.lin (real2.goesOn r.shared)).runOn (secondStart p real r.first)
      r.second.view = .ok ()

/-- **The reading of a key file at the hash h.** k: the parameters of a key file's three chains. -/
def readKeyChainsG (h : M.HashM Id) (k : Params.KeyChains) (file : ByteArray) :
    Option (Params.TableName × ChainsData) :=
  match Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file with
  | .error _ => none
  | .ok (table, j) =>
    match ((M.Key.readKey (m := Id) h k table file j).fromStart : Except String TailRead) with
    | .error _ => none
    | .ok r => (keyDataOf k table file r).map fun d => (table, d)

/-- The key file's three chains as read and judged at the hash h. table: what is kept of the key's
table. -/
def KeyOpenedG (h : M.HashM Id) (k : Params.KeyChains) (file : ByteArray)
    (table : Params.TableName) : Prop :=
  ∃ j rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2,
    (k.oneTime.given.plan.field != .two) = false ∧
    (!Key.admitted k.oneTime) = false ∧
    Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) ∧
    k.oneTime.describe table rounds1 = some S1 ∧
    ThreeChainsG h (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
      rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2

/-- A good reading of a key file at the hash h. -/
def KeyGoodG (h : M.HashM Id) (k : Params.KeyChains) (d : Params.TableName × ChainsData) : Prop :=
  ∃ file, KeyOpenedG h k file d.1 ∧ readKeyChainsG h k file = some d

end OnBytes.TieK.G
