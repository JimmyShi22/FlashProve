-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ArmFacts.lean: from the program's yes to all that the yes of the lax verifier of an
entry's link over a second interface asks of the file and of the description, at a ground.

The theorem on that verifier (OnBytes/K/Arm/LinkArm2.lean, with the walks paid in
OnBytes/K/Arm/LinkArmRead.lean) asks, of one reading: the line's record `EntryRead`
(OnBytes/TypedOracleCompiler/Slice/EntryChain.lean); the typing's yes; the decision's yes on the reader's view; and
twelve tests on the description and the statement (`GroundFacts`,
OnBytes/K/Arm/LinkArmFacts.lean). OnBytes/K/Left/ has each of the first three from the program's yes
(`PortYesAt`) at a ground whose lines the parameter file says: LaxKeys.lean (`dec_yes`),
LaxGround.lean (`ground`, `ground_bounds`), AsmAt.lean (`asm`), Asm.lean (`run_of_read`),
LaxChain.lean (`entryRead_of`). Here all are put together at one reading. No second interface, no
encoding and no second protocol is named. For proofs only; the program does not import this file.

Main names.
 `ArmFacts G c table further l0 l1 o π`: the record: `read` (`EntryRead` at `entryXD G c`, the
   oracle `oBits`, the two tables and their roots as digests, for some run value and typed plain
   parts), `typed`, `dec`, `ground`.
 `armFacts_of`: there are r, l0, l1 and π with: `Entry.read` returned r, with the program's further
   table; the program's seeds at both names are l0, l1; `ArmFacts` at what r's chain read. c is the
   digest of the three public files (`ec`).
 `armFacts_full`, `armFacts_small`: that at the two grounds. Hypotheses: `PortYesAt`,
   `G.SaysLines F.pol`, `ec`; no other.

What is not claimed. That a served statement's parameter file says a ground's lines. Nothing on a
second interface, an encoding or the walks. Nothing on soundness.


-/
import OnBytes.K.Left.LaxFrom
import OnBytes.K.Arm.LinkArmFacts

set_option autoImplicit false

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom OnBytes.Tie TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Slice.EntryChain
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)

/-- What is asked of the file and of the description, at a ground G, a digest c, two tables, the
program's seeds at both names, what was read (o) and the typed string π. -/
structure ArmFacts (G : EntryGround) (c : ByteArray) (table further : Params.TableName)
    (l0 l1 : List (List E × E)) (o : Fmt.ChainOut)
    (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up) : Prop where
  /-- the line's record of one reading, at the hash over the realised oracle -/
  read : ∃ (run : ByteArray) (pls : Plains (PQ.uL (entryXD G c).C (entryXD G c).ds)),
    EntryRead (entryXD G c) (EntryRunTop.pdOf (entryXD G c)) oBits table further
      (bytesToDig table.root) (bytesToDig further.root)
      ⟨{ (entryXD G c).base with statement := Params.Link.statement table further },
        (entryXD G c).stored⟩ o run pls
  /-- the typing's yes -/
  typed : assembleS (entryXD G c) (decAt G c) o = some π
  /-- the decision of a run at the typed instance says yes on the reader's view -/
  dec : decAt G c (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩)
    (Fmt.viewX ⟨{ (entryXD G c).base with statement := Params.Link.statement table further },
        (entryXD G c).stored⟩ o) = true
  /-- the tests on the description and the statement -/
  ground : GroundFacts G c table further

/-- From the program's yes, at a ground. -/
theorem armFacts_of (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two) (hrs : G.rs ≠ [])
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (hseal : (G.rs.all fun r => decide (r.1.kind ≠ .sealed)) = true)
    (hlen : G.rs.length + 1 < 2 ^ 64)
    (hK : ∀ c : ByteArray, (entryXD G c).K + 1 < 2 ^ 48)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) (c : ByteArray)
    (ec : Params.configurationDigest [F.pol, F.lay, F.KL] = c) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
      (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up),
      Entry.read (linkAtCfg G.q c) table F.ent = .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg G.q c) table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q c) further = some l1 ∧
      ArmFacts G c table further l0 l1 r.chain.out π := by
  subst ec
  obtain ⟨r, l0, l1, i, hr, hf, a0, a1, e, hd⟩ := dec_yes G hA hF rfl rfl rfl h hl
  obtain ⟨-, -, -, -, -, -, -, -, h0, h1, -, -, hit⟩ := ground G hA h hl
  obtain ⟨hd169, f0, f1, -⟩ := ground_bounds G hA h hl
  obtain ⟨π, hπ⟩ := asm G hA h hl hr (decAt G _)
  rw [specAt_with] at e hd
  obtain ⟨run, pls, -, -, hrun, hpl, -⟩ := assembleS_some _ _ hπ
  have h32 : run.size = 32 := by
    obtain ⟨run', g1, g2⟩ := run_of_read (_root_.Run.PQ.size_HO Fmt.oracle Fmt.size_oracle) e
      (fun h => by cases h)
    obtain rfl : run' = run := Option.some.inj (g1.symm.trans hrun)
    exact g2
  have H : GroundFacts G _ table further :=
    groundFacts_of G hb hseal hlen _ (Params.configurationDigest_size _) (hK _) table further _ _
      F.ent i _ e hit
  exact ⟨r, l0, l1, π, hr, hf, a0, a1,
    ⟨run, pls, entryRead_of G _ H.hok table further h0 h1 hrs hd169 _ F.ent i _ r.chain.out e run
      hrun h32 pls hpl f0 f1⟩, hπ, hd, H⟩

/-- At the full size. -/
theorem armFacts_full {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : recordGround.SaysLines F.pol) (c : ByteArray)
    (ec : Params.configurationDigest [F.pol, F.lay, F.KL] = c) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
      (π : OneProtocolProof 256 (PSXE (entryXD recordGround c) (decAt recordGround c)).up),
      Entry.read (linkAtCfg recordGround.q c) table F.ent = .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg recordGround.q c) table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg recordGround.q c) further = some l1 ∧
      ArmFacts recordGround c table further l0 l1 r.chain.out π :=
  armFacts_of recordGround record_answers record_field
    (fun h => by
      have h2 := Params.record_rounds_length
      rw [show Params.recordRounds = [] from h] at h2
      cases h2)
    full_base_ok Params.record_no_seal.1
    (by
      show Params.recordRounds.length + 1 < 2 ^ 64
      rw [Params.record_rounds_length]
      decide)
    (fun c => by rw [full_K]; decide) h hl c ec

/-- At the small example. -/
theorem armFacts_small {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : smallRecordGround.SaysLines F.pol) (c : ByteArray)
    (ec : Params.configurationDigest [F.pol, F.lay, F.KL] = c) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
      (π : OneProtocolProof 256 (PSXE (entryXD smallRecordGround c) (decAt smallRecordGround c)).up),
      Entry.read (linkAtCfg smallRecordGround.q c) table F.ent = .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg smallRecordGround.q c) table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg smallRecordGround.q c) further = some l1 ∧
      ArmFacts smallRecordGround c table further l0 l1 r.chain.out π :=
  armFacts_of smallRecordGround small_record_answers small_record_field
    (fun h => by
      have h2 := Params.small_record_rounds_length
      rw [show Params.smallRecordRounds = [] from h] at h2
      cases h2)
    small_base_ok Params.record_no_seal.2
    (by
      show Params.smallRecordRounds.length + 1 < 2 ^ 64
      rw [Params.small_record_rounds_length]
      decide)
    (fun c => by rw [small_K]; decide) h hl c ec

end OnBytes.K.Arm
