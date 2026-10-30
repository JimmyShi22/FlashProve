-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Top.lean: from the yes of the Lean program `verify-on-bytes` (OnBytes/Main.lean; "the
program" below) on a call's files to the yes of the entry's verifier of a call, `verifyE`
(OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean).

`K.PortYesAt F id table further` (OnBytes/K/Top.lean) is what exit code 0 of the program says of the
bytes F of a whole call, at the two tables that the program hands on. `verifyE G hok x a` is the
verifier of an entry file at a ground G: on a statement x (the commitment ID in its normal form and
the digest of the three public files) and on what a converter has made of the files.

Main definitions. `LaxAt`: the one step that this file takes as a hypothesis: at what the program's
own reader has read of the entry file, the lax verifier's evaluable form `laxE` says yes.
Main theorem. `entry_left`: if the program's yes holds, and the parameter file's lines are the
ground's, then the strict converter (`prepE` with lax := false,
OnBytes/TypedOracleCompiler/Slice/EntryRunBytes.lean) returns on these very files a value a with the program's two
tables, and `verifyE` says yes on a, at the user's ID in its normal form and at the public files'
digest. So a is a function of the files' bytes, by a converter that parses and does not search.
It puts together: the standard form (Std.lean), the converter's value (Conv.lean), the pins
(Pins.lean), the typed string (AsmAt.lean), the comparison of the seeds (SeedsAt.lean), the ID
(Id.lean), the reading (LaxGround.lean), and `LaxAt`.

What is not claimed. `LaxAt` is a hypothesis here (see OnBytes/K/Left/Lax.lean). It is
proved at both grounds in OnBytes/K/Left/LaxDone.lean (`restAll_full`, `restAll_small`, with
`laxAt_of` of OnBytes/K/Left/LaxEnd.lean). Nothing on soundness: what a yes of `verifyE` means is
OnBytes/TypedOracleCompiler/Slice/EntryVerdict.lean's and the files' behind it. The key file and the proof file of
the call are not spoken of. The conditions on the ground (`hA`, `SeedsFit`, the pins) are shown at
the two grounds in their own files. For proofs only; the program does not import
this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.AsmAt
import OnBytes.K.Left.SeedsAt
import OnBytes.K.Left.Id
import OnBytes.K.Left.Pins
import OnBytes.K.Left.Std
import OnBytes.TypedOracleCompiler.Slice.EntryVerdict

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left

open OnBytes.Tie
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PQ (bodyS)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig)

variable (G : EntryGround)
  (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)

/-- The lax verifier's yes at what the program's reader has read of the entry file ent against the
first table, at the digest c. -/
def LaxAt (c : ByteArray) (hc : c.size = 32) (table further : Params.TableName)
    (ent : ByteArray) : Prop :=
  ∀ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
    (π : OneProtocolProof 256 (PSXE (entryXD G c) (decRun (linkAtCfg G.q c) G.q.link.table.v
                  G.q.link.table.cubeBits G.q.link.table.answers)).up),
    Entry.read (linkAtCfg G.q c) table ent = .ok r → r.further = further →
    seedsUnder recordSeeds (linkAtCfg G.q c) table = some l0 →
    seedsUnder recordSeeds (linkAtCfg G.q c) further = some l1 →
    assembleS (entryXD G c) (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits
      G.q.link.table.answers) r.chain.out = some π →
    laxE (entryXD G c) (decRun (linkAtCfg G.q c) G.q.link.table.v G.q.link.table.cubeBits
        G.q.link.table.answers) (bodyS (entryXD G c).a (entryXD G c).base.plan.salt)
      (ownES (entryXD G c) (hok c hc)) (earlyTwo (d1Run _ _))
      (fun _ => TSE (entryXD G c) (seedEntry _ _))
      (EntryRunTop.famOf (entryXD G c) hc (d1Run _ _) G.q.link.table)
      [bytesToDig table.root, bytesToDig further.root]
      (xOfAskedC _ _ ⟨table, further, l0, l1, r.chain.out⟩) π = true

/-- From the program's yes to the yes of the entry's verifier of a call, under `LaxAt`. -/
theorem entry_left (hA : (G.q.link.table.answers == 0) = false) (S : SeedsFit G)
    (hp : ∀ c, pinsFit (entryXD G c) G.q.link.table = true)
    (z : Params.StdSize) (hz : z.lines = G.lines)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    (hlax : LaxAt G hok (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) table further F.ent) :
    ∃ (a : AskedE) (nid : String), Model.Verify.idAsked id = some nid ∧ a.first = table ∧
      a.further = further ∧
      prepE G z false F.pol F.lay F.KL F.key F.ent =
        .ok ⟨Params.configurationDigest [F.pol, F.lay, F.KL], Params.configurationDigest_size _,
          linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]), a⟩ ∧
      verifyE G hok ⟨nid, Params.configurationDigest [F.pol, F.lay, F.KL],
        Params.configurationDigest_size _⟩ a = true := by
  obtain ⟨r, l0, l1, i, hr, hf, e0, e1, h0, h1, -⟩ := ground G hA h hl
  have hsz : F.pol.size ≤ Shell.textLimit ∧ F.lay.size ≤ Shell.textLimit ∧
      F.KL.size ≤ Shell.fileLimit := by
    obtain ⟨_, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, a1, a2, a3,
      -⟩ := h
    exact ⟨a1, a2, a3⟩
  obtain ⟨r', l0', l1', hr', -, e0', e1', -, -, hprep⟩ :=
    conv G hA z h hl (std_of_limits G z hz hl hsz.1 hsz.2.1 hsz.2.2)
  obtain rfl : r = r' := Except.ok.inj (hr.symm.trans hr')
  obtain rfl : l0 = l0' := Option.some.inj (e0.symm.trans e0')
  obtain rfl : l1 = l1' := Option.some.inj (e1.symm.trans e1')
  obtain ⟨π, hπ⟩ := asm G hA h hl hr (decRun
    (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) G.q.link.table.v
    G.q.link.table.cubeBits G.q.link.table.answers)
  refine ⟨⟨table, further, l0, l1, r.chain.out⟩, _,
    id_left G h hl ⟨table, further, l0, l1, r.chain.out⟩ rfl S.field hA e0, rfl, rfl, hprep, ?_⟩
  unfold verifyE
  dsimp only
  rw [hp, hπ]
  dsimp only
  rw [Bool.true_and, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  refine ⟨(whyOutE_yes _ _ _ _ _ _ _ _).2 ⟨rfl, ?_, hlax r l0 l1 π hr hf e0 e1 hπ⟩, rfl⟩
  exact cmp_left G hok S _ (Params.configurationDigest_size _) table further h0 h1 l0 l1 e0 e1
    r.chain.out

end OnBytes.K.Left
