-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/SameChains.lean: where the checks of a call said yes, the parameters of their chains
hold one digest, that of the call's three configuration files, and one shape of the stored tables.

A call forms the digest of its three configuration files, has the parameter bytes of seven chains
spelled under it, and reads these bytes back (`Verify.planned`). Each check, of the key file, the
entry file and the proof file, uses the digest and the tables' shape that its own chains hold as
read back. OnBytes/Model/VerifyDigest.lean and OnBytes/Model/VerifyShape.lean prove that these are
one digest and one shape, for parameter bytes that are fewer than 2^64. This file takes that bound
from a yes of the checks: a chain of which the program has made a description has at most 2^32 - 144
parameter bytes (`Fmt.Spec.small`), and each check that said yes has made one. Here "a chain in p"
is what the program has read back from that chain's parameter bytes (`Params.OneTime`, `Shared`,
`Second`, `Link`, `First`), not the chain in a file.

Main definition. `SameChains p d`: the digest in p and the digest that each of the seven chains in p
holds are d; and the tables' shape in the key's one-time chain, in the key's shared chain, in the
proof's first chain and in the proof's shared chain is the tables' shape in the entry's chain; and
the entry's chain in p is what `Params.Link.read` reads from the parameter bytes of the entry's
chain in p, which `Entry.check` is given and reads itself. The two second chains hold no shape:
`Params.Second` has no field but what `Params.Given.read` returns, and `Params.Second.read` refuses
parameter bytes with a further item. Main theorems.
- `entry_yes_cfg`, `key_yes_cfg`, `proof_yes_cfg`: the digest, for one check that said yes.
- `tableShape_oneTime`: the tables' shape that enters the commitment ID is the one in the key's
  one-time chain.
- `checks_same`: if `Verify.planned` returned p on three configuration files, and `Key.check`,
  `Entry.check` and `Proof.check` said yes under the chains in p, then `SameChains` holds of p and
  the digest of the three files.
`main_zero_same`, which says `SameChains` of a run that returned 0, stands in
OnBytes/Tie/ZeroNamed.lean.

What is not claimed. Nothing on soundness. `SameChains` speaks of the chains that `Verify.planned`
returns and the checks are given, not of bytes in the key file, the entry file or the proof file:
whether each check binds its file to the digest that its chains hold can only be read off the code
and is no theorem. `SameChains p d` is a property of the three configuration files alone: of the
checks' yes the proofs use only that the parameter bytes are few. That the shape which the chains
hold is the shape that the planner made is not stated: a number from 2^64 on is spelled modulo 2^64;
stated is that the chains hold the same shape. The tables' shape is `Params.IndexShape`, six
numbers: the three of the rows' code, the logarithm of the number of rows, the number of answers
that are stored for each row, and the bytes of a leaf's salt. How the matrix lies in a table (`kLo`,
`matrixRows` of `Params.LinShape`) is no part of it: that the key's and the proof's chains hold the
same two numbers is not stated. Nothing on the other values that are read back: plans, codes, the
other fields of the shapes. That the plans which the checks follow, as read back, are the plans
whose errors the stages account for, as made, is not stated. Nothing is proved of the hash in the
digest. That the checks take the digest of the three configuration files, and the shape of the
tables, from nowhere but their chains is read off the code and is no theorem. The item that
`Proof.requestItem` forms holds further digests, of the scale file, of lines of the parameter file
and of the request, by another hash, and four of public tables, copied from the parameter file's
lines: nothing is said of them here. No theorem here starts from a call on one file alone:
`entry_yes_cfg`, `key_yes_cfg` and `proof_yes_cfg` start from `Verify.planned` and one check's yes
and give the digest in p; on the tables' shape in the other checks' chains they say nothing. The
limits in the head of OnBytes/Shell/AtWholeId.lean, with those of OnBytes/Shell/AtWhole.lean that it
keeps, hold here too, but for two that are lifted here: that the chains under which the three checks
ran hold the same shape of the stored tables and the same digest, and that the digest in p, which
enters the commitment ID, is the digest that these chains hold. The program is the Lean port built
from OnBytes/; nothing here is said of the C++ program `cp_verify` or of how its results compare.
For proofs only; the program does not import this file.
-/
import OnBytes.Model.VerifyShape
import OnBytes.Tie.SpecXBase
import OnBytes.Tie.KeyFile

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Proof

/-- A chain of which the program has made a description has at most 2^32 - 144 parameter bytes. -/
theorem described_small {g : Params.Given} {label : ℕ} {statement : ByteArray} {rand : Fmt.Rand}
    {rounds : List Fmt.Round} {stored : List (List Fmt.Stored)} {firstTree : ℕ} {S : Fmt.SpecX}
    (h : g.describe label statement rand rounds stored firstTree = some S) :
    g.bytes.size ≤ 2 ^ 32 - 144 := by
  have hok := specX_base S (Params.Given.describe_ok h)
  have hs := Fmt.ok_small hok
  have he := Params.Given.describe_eq h
  unfold Fmt.Spec.small at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  have h1 := hs.1.1.1.1
  rw [he] at h1
  exact h1

/-- If a reading that stops on a condition, with the steps that follow it, returns a value, the
steps that follow have returned it from the same session. -/
theorem reading_guard {β : Type} {c : Prop} [Decidable c] {e : String}
    {next : PUnit → Reading β} {s s' : Session} {b : β}
    (h : (if c then (throw e : Reading PUnit) >>= next else pure PUnit.unit >>= next) s =
      .ok (b, s')) : next PUnit.unit s = .ok (b, s') := by
  split at h
  · obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ h
    cases hth
  · obtain ⟨_, _, hp, h2⟩ := bind_ok _ _ _ _ _ h
    cases hp
    exact h2

/-- If the check of a proof file says `accepted`, there are rounds on which `First.describe` returns
a description of the proof's first chain `c.first` and the table, copy, request and request file's
words that the check was given. -/
theorem proof_check_described {c : Params.ProofChains} {table : Params.TableName} {copy : ℕ}
    {request words : ByteArray} {reply : E} {links : Blk LinksResult} {file : ByteArray}
    (h : Proof.check c table copy request words reply links file = .accepted) :
    ∃ rounds S, c.first.describe table copy request words rounds = some S := by
  unfold Proof.check at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    have hrun : ∃ s', readProof c table copy request words (firstBlock c.first links reply) file
        Session.start = .ok (r, s') := by
      unfold Reading.fromStart at hr
      cases hq : readProof c table copy request words (firstBlock c.first links reply) file
          Session.start with
      | error e => rw [hq] at hr; cases hr
      | ok y =>
        rw [hq] at hr
        injection hr with hy
        exact ⟨y.2, by rw [← hy]⟩
    obtain ⟨s', hs'⟩ := hrun
    unfold readProof at hs'
    cases hh : readProofHead c.first.given.plan.field file with
    | error e =>
      rw [hh] at hs'
      obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ hs'
      cases hth
    | ok x =>
      rw [hh] at hs'
      obtain ⟨⟨madeOn, i⟩, s1, _, h1⟩ := bind_ok _ _ _ _ _ hs'
      replace h1 := reading_guard h1
      replace h1 := reading_guard h1
      obtain ⟨⟨rounds1, dry⟩, s2, _, h1⟩ := bind_ok _ _ _ _ _ h1
      obtain ⟨spec1, s3, h2, _⟩ := bind_ok _ _ _ _ _ h1
      exact ⟨rounds1, spec1, (need_ok _ _ _ _ _ h2).1⟩

/-- Where `Entry.check` said yes under the parameter bytes of the entry's chain in p, these are at
most 2^32 - 144 bytes. -/
theorem entry_yes_small {p : Model.Verify.Planned} {first further : Params.TableName}
    {ent : ByteArray} (h : Entry.check (p.chains.bytes .link) first ent = .ok further) :
    (p.chains.bytes .link).size ≤ 2 ^ 32 - 144 := by
  obtain ⟨q, block, S, _, _, _, hq, hS, _, _⟩ := entry_check_compiled _ _ _ _ h
  have hb : q.given.bytes.size ≤ 2 ^ 32 - 144 := by
    unfold entrySpec at hS
    split at hS
    · obtain ⟨S', hS', _⟩ := Option.map_eq_some_iff.1 hS
      obtain ⟨rs, _, hd⟩ := Option.bind_eq_some_iff.1 hS'
      exact described_small hd
    · cases hS
  rw [Params.Given.read_bytes (Params.Link.read_given hq)] at hb
  exact hb

/-- Where `Key.check` said yes under the key's three chains in p, the one-time chain has at most
2^32 - 144 parameter bytes. -/
theorem key_yes_small {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} {table : Params.TableName} {kb : ByteArray}
    (hp : Model.Verify.planned pol KL layout = .ok p)
    (h : Key.check p.chains.key kb = .ok table) :
    (p.chains.bytes .keyOneTime).size ≤ 2 ^ 32 - 144 := by
  obtain ⟨_, _, _, S, _, _, _, _, hd, _, _⟩ := key_check_oneTime _ _ _ h
  have hb := described_small hd
  rw [Params.Given.read_bytes (Params.OneTime.read_given
    (Params.KeyChains.read_parts (Model.Verify.planned_read hp).1).1)] at hb
  exact hb

/-- Where `Proof.check` said `accepted` under the proof's three chains in p, the first chain has at
most 2^32 - 144 parameter bytes. -/
theorem proof_yes_small {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} {table : Params.TableName} {copy : ℕ} {request words : ByteArray}
    {reply : E} {links : Blk LinksResult} {file : ByteArray}
    (hp : Model.Verify.planned pol KL layout = .ok p)
    (h : Proof.check p.chains.proof table copy request words reply links file = .accepted) :
    (p.chains.bytes .proofFirst).size ≤ 2 ^ 32 - 144 := by
  obtain ⟨_, S, hd⟩ := proof_check_described h
  have hb := described_small hd
  rw [Params.Given.read_bytes (Params.First.read_given
    (Params.ProofChains.read_parts (Model.Verify.planned_read hp).2.2).1)] at hb
  exact hb

/-- Where `Entry.check` said yes under the parameter bytes of the entry's chain in p, the digest
that this chain holds as read back is the digest in p. -/
theorem entry_yes_cfg {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} {first further : Params.TableName} {ent : ByteArray}
    (hp : Model.Verify.planned pol KL layout = .ok p)
    (h : Entry.check (p.chains.bytes .link) first ent = .ok further) :
    p.chains.link.given.cfg = p.cfg := by
  have := entry_yes_small h
  exact Model.Verify.planned_link_cfg hp (by omega)

/-- Where `Key.check` said yes under the key's three chains in p, the digest that each of them holds
as read back is the digest in p. -/
theorem key_yes_cfg {pol KL : ByteArray} {layout : Option ByteArray} {p : Model.Verify.Planned}
    {table : Params.TableName} {kb : ByteArray}
    (hp : Model.Verify.planned pol KL layout = .ok p)
    (h : Key.check p.chains.key kb = .ok table) :
    p.chains.key.oneTime.given.cfg = p.cfg ∧ p.chains.key.shared.given.cfg = p.cfg ∧
      p.chains.key.second.given.cfg = p.cfg := by
  have := key_yes_small hp h
  exact Model.Verify.planned_key_cfg hp (by omega)

/-- Where `Proof.check` said `accepted` under the proof's three chains in p, the digest that each of
them holds as read back is the digest in p. -/
theorem proof_yes_cfg {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} {table : Params.TableName} {copy : ℕ} {request words : ByteArray}
    {reply : E} {links : Blk LinksResult} {file : ByteArray}
    (hp : Model.Verify.planned pol KL layout = .ok p)
    (h : Proof.check p.chains.proof table copy request words reply links file = .accepted) :
    p.chains.proof.first.given.cfg = p.cfg ∧ p.chains.proof.shared.given.cfg = p.cfg ∧
      p.chains.proof.second.given.cfg = p.cfg := by
  have := proof_yes_small hp h
  exact Model.Verify.planned_proof_cfg hp (by omega)

/-- The digest in p and the digest that each of the seven chains in p holds are d; the four chains
of the key and of the proof that hold a shape of the stored tables hold the one that the entry's
chain holds (the two second chains hold none, by the code); and the entry's chain in p is read from
the parameter bytes of the entry's chain in p, the bytes that `Entry.check` is given and reads
itself (by the code).
-/
def SameChains (p : Model.Verify.Planned) (d : ByteArray) : Prop :=
  (p.cfg = d ∧ p.chains.key.oneTime.given.cfg = d ∧ p.chains.key.shared.given.cfg = d ∧
    p.chains.key.second.given.cfg = d ∧ p.chains.link.given.cfg = d ∧
    p.chains.proof.first.given.cfg = d ∧ p.chains.proof.shared.given.cfg = d ∧
    p.chains.proof.second.given.cfg = d) ∧
  (p.chains.key.oneTime.lin.fold.index = p.chains.link.link.table ∧
    p.chains.key.shared.lin.fold.index = p.chains.link.link.table ∧
    p.chains.proof.first.lin.fold.index = p.chains.link.link.table ∧
    p.chains.proof.shared.lin.fold.index = p.chains.link.link.table) ∧
  Params.Link.read (p.chains.bytes .link) = some p.chains.link

/-- The tables' shape that enters the commitment ID is the one in the key's one-time chain. -/
theorem tableShape_oneTime (c : Model.Verify.Chains) :
    c.tableShape = c.key.oneTime.lin.fold.index := rfl

/-- Where the three checks said yes under the chains in p, these chains hold the digest of the three
configuration files on which `Verify.planned` returned p, and one shape of the stored tables; and
the entry's chain in p is read from the bytes that `Entry.check` was given. Of the three yeses the
proof uses only that the parameter bytes of three chains are few: at most 2^32 - 144
(`entry_yes_small`, `key_yes_small`, `proof_yes_small`). -/
theorem checks_same {pol KL lay : ByteArray} {p : Model.Verify.Planned}
    {table first further tbl : Params.TableName} {kb ent : ByteArray} {copy : ℕ}
    {request words : ByteArray} {reply : E} {links : Blk LinksResult} {file : ByteArray}
    (hp : Model.Verify.planned pol KL (some lay) = .ok p)
    (hk : Key.check p.chains.key kb = .ok table)
    (he : Entry.check (p.chains.bytes .link) first ent = .ok further)
    (hf : Proof.check p.chains.proof tbl copy request words reply links file = .accepted) :
    SameChains p (Params.configurationDigest [pol, lay, KL]) := by
  obtain ⟨_, _, _, hc, _⟩ := Model.Verify.planned_entry hp
  obtain ⟨k1, k2, k3⟩ := key_yes_cfg hp hk
  have e1 := entry_yes_cfg hp he
  obtain ⟨f1, f2, f3⟩ := proof_yes_cfg hp hf
  rw [hc] at k1 k2 k3 e1 f1 f2 f3
  have b1 := key_yes_small hp hk
  have b2 := entry_yes_small he
  have b3 := proof_yes_small hp hf
  obtain ⟨s1, s3⟩ := Model.Verify.planned_shapes hp (by omega) (by omega) (by omega)
  obtain ⟨r1, r2, r3⟩ := Model.Verify.planned_read hp
  have s2 := Params.KeyChains.read_lin r1
  have s4 := Params.ProofChains.read_lin r3
  exact ⟨⟨hc, k1, k2, k3, e1, f1, f2, f3⟩, ⟨s1, by rw [s2]; exact s1, s3, by rw [s4]; exact s3⟩,
    r2⟩

end OnBytes.Tie

#print axioms OnBytes.Tie.checks_same
