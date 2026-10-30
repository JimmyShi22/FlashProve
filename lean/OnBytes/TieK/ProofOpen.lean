-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/ProofOpen.lean: what the program has done with a proof file if its check says yes:
every step of `Proof.check`, `Proof.readProof` and `Proof.proofRefusal` as a named fact, for all
three chains.

`Proof.check` (OnBytes/Proof/File.lean) is the function that the program `verify-on-bytes` runs on a
proof file. This file proves no more than what its text says, as one statement, so that a tie from
the program's yes to another verifier's yes can begin at named facts.

`ProofFacts` lists them:
  - the head was read; the proof was made on the stored copy whose number the caller holds;
  - the first chain's field is the one in which the program computes, and its digest of the public
    files is not 32 zero bytes;
  - the first chain's rounds come from a dry run of its block; its description is made of them, the
    table, the copy's number, the request's bytes and the request file's words;
  - the strict reader has read the first chain under that description, behind the head, from the
    empty record of vertices;
  - the tail was read at what that dry run has returned (`readTail_open` opens it);
  - no byte is left over;
  - the first chain's block accepts the first chain's view and returns an end, `real`;
  - the tail's yes (`TailYes`), at `real`.
The descriptions come from dry runs, the decisions from the same blocks' runs on the views: the
second chain's description is made at `dry` and at the shared chain's dry end, its decision at
`real` and at the shared chain's real end. That the two give the same rounds is not stated here.

Main definition: `ProofFacts`.
Main theorems: `readProof_open`, `proof_check_open`.
It claims nothing on soundness. The program does not import this file.

-/
import OnBytes.TieK.TailOpen
import OnBytes.Proof.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof OnBytes.Tie

/-- The facts of a proof file's reading that has returned r, from the session s to s'. -/
structure ReadFacts (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (s s' : Session)
    (r : ProofRead) (i : Nat) (rounds1 : Params.Rounds) (dry : FirstEnd) (spec1 : Fmt.SpecX)
    (s1 : Session) : Prop where
  head_read : readProofHead c.first.given.plan.field file = .ok (copy, i)
  /-- the first chain's field is the one in which the program computes, and the digest of the
  public files is not 32 zero bytes -/
  params_ok :
    (c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32) = false
  first_dry : block.dryRun (firstStart c.first) = some (rounds1, dry)
  first_spec : c.first.describe table copy request words rounds1 = some spec1
  first_read : readIn spec1 file i s = some (r.first, s1)
  tail_read : readTail (tailPublic c table) dry r.first file s1 = .ok (r, s')
  whole : r.next = file.size

/-- **What `readProof` has done if it returns.** -/
theorem readProof_open (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (s s' : Session)
    (r : ProofRead) (h : readProof c table copy request words block file s = .ok (r, s')) :
    ∃ i rounds1 dry spec1 s1,
      ReadFacts c table copy request words block file s s' r i rounds1 dry spec1 s1 := by
  unfold readProof at h
  cases hx : readProofHead c.first.given.plan.field file with
  | error e =>
    rw [hx] at h
    obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ h
    cases hth
  | ok x =>
    rw [hx] at h
    obtain ⟨y, t0, h0, g0⟩ := bind_ok _ _ _ _ _ h
    injection h0 with h0'
    have ey : x = y := congrArg (·.1) h0'
    have et0 : s = t0 := congrArg (·.2) h0'
    subst ey
    subst et0
    obtain ⟨madeOn, i⟩ := x
    dsimp only at g0
    split at g0
    · obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ g0
      cases hth
    · rename_i hcopy
      obtain ⟨u1, t1, h1, g1⟩ := bind_ok _ _ _ _ _ g0
      injection h1 with h1'
      have et1 : s = t1 := congrArg (·.2) h1'
      subst et1
      split at g1
      · obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ g1
        cases hth
      · rename_i hpar
        obtain ⟨u2, t2, h2, g2⟩ := bind_ok _ _ _ _ _ g1
        injection h2 with h2'
        have et2 : s = t2 := congrArg (·.2) h2'
        subst et2
        obtain ⟨⟨rounds1, dry⟩, t3, h3, g3⟩ := bind_ok _ _ _ _ _ g2
        obtain ⟨e3, et3⟩ := need_ok _ _ _ _ _ h3
        subst et3
        dsimp only at g3
        obtain ⟨spec1, t4, h4, g4⟩ := bind_ok _ _ _ _ _ g3
        obtain ⟨e4, et4⟩ := need_ok _ _ _ _ _ h4
        subst et4
        obtain ⟨first, s1, h5, g5⟩ := bind_ok _ _ _ _ _ g4
        have e5 := readNamed_ok _ _ _ _ _ _ _ h5
        obtain ⟨r', t6, h6, g6⟩ := bind_ok _ _ _ _ _ g5
        split at g6
        · obtain ⟨_, _, hth, _⟩ := bind_ok _ _ _ _ _ g6
          cases hth
        · rename_i hsize
          obtain ⟨u7, t7, h7, g7⟩ := bind_ok _ _ _ _ _ g6
          injection h7 with h7'
          have et7 : t6 = t7 := congrArg (·.2) h7'
          subst et7
          injection g7 with hr
          have er : r' = r := congrArg (·.1) hr
          have es : t6 = s' := congrArg (·.2) hr
          subst er
          subst es
          have ef : r'.first = first := readTail_first _ _ _ _ _ _ _ h6
          have ecopy : madeOn = copy := by
            simpa using hcopy
          have esize : r'.next = file.size := by
            simpa using hsize
          subst ecopy
          subst ef
          exact ⟨_, _, _, _, _, ⟨hx, eq_false_of_ne_true hpar, e3, e4, e5, h6, esize⟩⟩

/-- The facts of a check of a proof file that said yes. -/
structure ProofFacts (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : ProofRead)
    (s' : Session) (i : Nat) (rounds1 : Params.Rounds) (dry : FirstEnd) (spec1 : Fmt.SpecX)
    (s1 : Session) (real : FirstEnd) (end2 : SharedEnd) : Prop where
  read : ReadFacts c table copy request words block file Session.start s' r i rounds1 dry spec1 s1
  first_yes : block.runOn (firstStart c.first) r.first.view = .ok real
  tail_yes : TailYes (tailPublic c table) real r end2

/-- **What the program has done with a proof file if its check says yes.** -/
theorem proof_check_open (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (reply : E) (links : Blk LinksResult) (file : ByteArray)
    (h : check c table copy request words reply links file = .accepted) :
    ∃ r s' i rounds1 dry spec1 s1 real end2,
      ProofFacts c table copy request words (firstBlock c.first links reply) file r s' i rounds1 dry
        spec1 s1 real end2 := by
  unfold check at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · rename_i hno
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
      obtain ⟨i, rounds1, dry, spec1, s1, hf⟩ := readProof_open _ _ _ _ _ _ _ _ _ _ hs'
      rw [proofRefusal_eq] at hno
      split at hno
      · cases hno
      · rename_i real hj
        obtain ⟨end2, hy⟩ := tailRefusal_open _ _ _ hno
        exact ⟨r, s', i, rounds1, dry, spec1, s1, real, end2, ⟨hf, judge_ok _ _ _ _ _ hj, hy⟩⟩

end OnBytes.TieK
