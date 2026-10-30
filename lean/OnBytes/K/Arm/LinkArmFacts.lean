-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LinkArmFacts.lean: what `link_arm2_read` (OnBytes/K/Arm/LinkArmRead.lean) asks of
the description and of the statement, as one record at an entry's ground, with its proof.

`link_arm2_read` says that the lax compiled verifier of an entry's link says yes over a second
interface. Beside the reading, the typed string and the second interface's data it asks twelve
things that hang on the typed description D and the statement st alone. Here D is `entryXD G c`
(OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean), st is the program's statement on two tables, and the twelve are
the fields of one record, in that theorem's own words. For proofs only; the program does not
import this file.

Main definition.
 `GroundFacts G c first further`   the digest has 32 bytes; the rounds' data fit (`FitsE`); K + 1 is
    below 2^48; the description passes the test of limits `PQ.ok`, at its own empty statement
    (`hok`) and at the statement on the two tables (`hokb`); the chain has random bytes; no round
    has more than 64 bits of work; the stored openings are in order; all stored tables have the
    depth `D.a`, the plan's length of salts and the item 0 or 1; each table is opened at most
    once; the statement's items hold the two tables' roots.
Main theorems.
 `groundFacts_of`      the record at any ground G and any digest c of 32 bytes. Asked of G: its
    description at an empty statement is in order; no round is sealed; the rounds' number and K
    are small. Asked of the reading: the strict reader, at any hash, has read something under the
    program's description at the two tables. Asked of the statement: the field `hit` itself.
 `groundFacts_full`, `groundFacts_small`   at the two grounds with a record: what is asked of G is
    shown.

What is not claimed. The field `hit` is handed through: `ground` (OnBytes/K/Left/LaxGround.lean) has
it from the exit code 0. That any file is read. Nothing on the second interface. Nothing on
soundness.


-/
import OnBytes.K.Left.LaxChain
import OnBytes.K.Left.LaxRowsAt

set_option autoImplicit false

namespace OnBytes.K.Arm
open OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Run.RowsE2

/-- **What `link_arm2_read` asks of the description and of the statement**, at an entry's ground,
a digest c and two tables. -/
structure GroundFacts (G : EntryGround) (c : ByteArray) (first further : Params.TableName) :
    Prop where
  /-- the digest has 32 bytes -/
  hcfg : (entryXD G c).base.cfg.size = 32
  /-- the rounds' data fit -/
  fits : FitsE (entryXD G c)
  /-- the blocks of a challenge are few -/
  hK : (entryXD G c).K + 1 < 2 ^ 48
  /-- it passes the test of limits `PQ.ok`, at the description's own empty statement -/
  hok : PQ.ok (entryXD G c).base = true
  /-- and at the statement on the two tables -/
  hokb : PQ.ok (PQ.inFile ({ (entryXD G c).base with
    statement := Params.Link.statement first further } : Fmt.Spec)) = true
  /-- the chain has random bytes -/
  hn : (entryXD G c).base.rand.isNone = false
  /-- no round has more than 64 bits of work -/
  work : ∀ r ∈ (entryXD G c).ds, r.entry.work ≤ 64
  /-- the stored openings are in order -/
  okx : PQ.okX (entryXD G c).ds (entryXD G c).a (entryXD G c).xs = true
  /-- all stored tables have one depth and the item 0 or 1 -/
  hD : ∀ t ∈ (entryXD G c).stored.flatten, t.sh.a = (entryXD G c).a ∧ t.item ≤ 1
  /-- each table is opened at most once -/
  honce : ((entryXD G c).stored.flatten.map (·.item == 1)).Nodup
  /-- all stored tables have one depth and the plan's length of salts -/
  hsame : ∀ t ∈ (entryXD G c).stored.flatten,
    t.sh.a = (entryXD G c).a ∧ t.salt = (entryXD G c).base.plan.salt
  /-- the statement's items hold the two tables' roots -/
  hit : ∀ t ∈ (entryXD G c).stored.flatten,
    Fmt.itemRoot (Params.Link.statement first further) t.item =
      some (if t.item == 1 then further.root else first.root)

/-- **The record at a ground.** -/
theorem groundFacts_of (G : EntryGround)
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (hseal : (G.rs.all fun r => decide (r.1.kind ≠ .sealed)) = true)
    (hlen : G.rs.length + 1 < 2 ^ 64) (c : ByteArray) (hc : c.size = 32)
    (hK : (entryXD G c).K + 1 < 2 ^ 48) (first further : Params.TableName) (h : _root_.Run.HId)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (x : Fmt.ChainOut × ℕ)
    (e : Fmt.readChainX (m := Id) h (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement first further)) seen b i = some x)
    (hit : ∀ t ∈ (entryXD G c).stored.flatten,
      Fmt.itemRoot (Params.Link.statement first further) t.item =
        some (if t.item == 1 then further.root else first.root)) :
    GroundFacts G c first further := by
  have hw := within_of G hb c hc
  have hok := entryXD_ok G hb c hc
  have hs := hw
  unfold withinX at hs
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hs
  have hx : (entryXD G c).ok = true :=
    ok_asTypedCompilerDescription (OnBytes.Tie.xdOf (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty)
                           fun r0 r1 => Params.Link.statement ⟨r0, []⟩ ⟨r1, []⟩) (OnBytes.Slice.within_ok _ _ hw)
  simp only [PQ.XD.ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at hx
  exact
    { hcfg := hc
      fits := fitsE_of G c hw hok hseal hlen
      hK := hK
      hok := hok
      hokb := okb_at G c first further hok (readX_ok h _ seen b i x e)
      hn := hs.1.2
      work := (descr_of G c hw).1
      okx := (descr_of G c hw).2
      hD := fun t ht => ⟨(hx.2 t ht).1.1, (hx.2 t ht).2⟩
      honce := hs.2
      hsame := fun t ht => ⟨(hx.2 t ht).1.1, (hx.2 t ht).1.2⟩
      hit := hit }

section
variable (c : ByteArray) (hc : c.size = 32) (first further : Params.TableName)
  (h : _root_.Run.HId) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (x : Fmt.ChainOut × ℕ)

include hc in
/-- **At the full size.** -/
theorem groundFacts_full
    (e : Fmt.readChainX (m := Id) h (Params.entrySpecOf (linkAtCfg recordGround.q c)
      recordGround.rs (Params.Link.statement first further)) seen b i = some x)
    (hit : ∀ t ∈ (entryXD recordGround c).stored.flatten,
      Fmt.itemRoot (Params.Link.statement first further) t.item =
        some (if t.item == 1 then further.root else first.root)) :
    GroundFacts recordGround c first further :=
  groundFacts_of recordGround full_base_ok Params.record_no_seal.1
    (by
      show Params.recordRounds.length + 1 < 2 ^ 64
      rw [Params.record_rounds_length]
      decide)
    c hc (by rw [full_K]; decide) first further h seen b i x e hit

include hc in
/-- **At the small example.** -/
theorem groundFacts_small
    (e : Fmt.readChainX (m := Id) h (Params.entrySpecOf (linkAtCfg smallRecordGround.q c)
      smallRecordGround.rs (Params.Link.statement first further)) seen b i = some x)
    (hit : ∀ t ∈ (entryXD smallRecordGround c).stored.flatten,
      Fmt.itemRoot (Params.Link.statement first further) t.item =
        some (if t.item == 1 then further.root else first.root)) :
    GroundFacts smallRecordGround c first further :=
  groundFacts_of smallRecordGround small_base_ok Params.record_no_seal.2
    (by
      show Params.smallRecordRounds.length + 1 < 2 ^ 64
      rw [Params.small_record_rounds_length]
      decide)
    c hc (by rw [small_K]; decide) first further h seen b i x e hit

end

end OnBytes.K.Arm
