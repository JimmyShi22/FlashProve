-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SeedsAt.lean: the comparison of the seeds in the entry's checker says yes at what the
strict converter makes of an entry file, at a ground and at the two grounds "record with work".

OnBytes/K/Left/Seeds.lean shows `cmpE` true at the program's own seeds, for a description D under
five conditions. This file lays D at `entryXD G c`, the description of an entry's chain at the
ground G and the configuration digest c, and the seeds at those that the converter (`convE`,
OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) draws by `seedsUnder recordSeeds` at the two tables' names.

Main definitions. `SeedsFit G`: four conditions on the ground alone: the field is the second one;
there is at least one seed; the seeds' round fits into the blocks of a verifier's message, at every
digest; of these blocks there are fewer than 2 ^ 48.
Main theorems.
 `cmp_left`     under `SeedsFit G`, at a digest and two roots of 32 bytes: `cmpE`, at the page's
                family, under the two roots, at the seeds in the instance `xOfAskedC` of the
                converter's value, is true.
 `record_fit`, `small_record_fit`   `SeedsFit` holds at `recordGround` and at `smallRecordGround`.

What is not claimed. Nothing on soundness. That a call's files give this value of the converter is
OnBytes/K/Left/Conv.lean's statement. All that the head of OnBytes/K/Left/Seeds.lean does not claim.
For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Seeds
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain
import OnBytes.TypedOracleCompiler.Slice.EntryHomeFull
import OnBytes.TypedOracleCompiler.Slice.EntryHomeSmall

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Left

open OnBytes.Tie (EntryGround AskedE seedsUnder linkAtCfg recordGround smallRecordGround)
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Slice.EntryRunTop
open OnBytes.Slice (seedEntry seedOfDrawnC seedOf seedBS)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

/-- Four conditions on a ground, for the seeds' comparison. -/
structure SeedsFit (G : EntryGround) : Prop where
  /-- the plan is over the second field -/
  field : G.q.given.plan.field = .two
  /-- the shape's number of answers, which is also the number of seeds, is at least one -/
  pos : 0 < G.q.link.table.answers
  /-- the seed's draw needs no more blocks than a verifier message has, at every digest -/
  room : ∀ c, (seedBS G.q.link.table.cubeBits G.q.link.table.answers).b ≤ (entryXD G c).K
  /-- the number of blocks is below 2^48, at every digest -/
  few : ∀ c, (entryXD G c).K + 1 < 2 ^ 48

/-- What stands behind a root in a table's name has 48 bytes more than the digest. -/
theorem restAt_size (D : TypedOracleCompiler.Run.PQ.XD) (sh : OnBytes.Params.IndexShape) :
    (restAt D sh).size = D.base.cfg.size + 48 := by
  unfold restAt FirstName.restOf
  simp only [ByteArray.size_append, FirstAnswers.size_u64n]

/-- The comparison of the seeds says yes at the strict converter's value. -/
theorem cmp_left (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    [DecidableEq (Sd1 G.q.link.table.cubeBits G.q.link.table.answers)]
    (S : SeedsFit G) (c : ByteArray) (hc : c.size = 32) (table further : OnBytes.Params.TableName)
    (h₀ : table.root.size = 32) (h₁ : further.root.size = 32) (l0 l1 : List (List E × E))
    (e₀ : seedsUnder recordSeeds (linkAtCfg G.q c) table = some l0)
    (e₁ : seedsUnder recordSeeds (linkAtCfg G.q c) further = some l1) (out : Fmt.ChainOut) :
    cmpE (entryXD G c) (earlyTwo (A := AnsT × AnsT) (d1Run _ _))
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)
      (seedOfDrawnC G.q.link.table.cubeBits G.q.link.table.answers)
      (famOf (entryXD G c) hc (d1Run _ _) G.q.link.table)
      [bytesToDig table.root, bytesToDig further.root] 0
      (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers
        ⟨table, further, l0, l1, out⟩).2 = true := by
  have hx : (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers
      ⟨table, further, l0, l1, out⟩).2 =
      (seedOf G.q.link.table.cubeBits G.q.link.table.answers l0,
        seedOf G.q.link.table.cubeBits G.q.link.table.answers l1) := by
    rw [xOfAskedC_eq]
    rfl
  rw [hx]
  have hr : (restAt (entryXD G c) G.q.link.table).size < 2 ^ 32 := by
    rw [restAt_size]
    show c.size + 48 < 2 ^ 32
    rw [hc]
    norm_num
  -- f₀, f₁: by the named equation, not by unfolding: see `Tie.seedsUnder_eq`
  have f₀ : recordSeeds .two (OnBytes.Key.nameOf G.q.link.table (entryXD G c).base.cfg table)
      G.q.link.table.cubeBits G.q.link.table.answers = some l0 := by
    rw [← S.field]
    exact (OnBytes.Tie.seedsUnder_eq recordSeeds (linkAtCfg G.q c) table).symm.trans e₀
  have f₁ : recordSeeds .two (OnBytes.Key.nameOf G.q.link.table (entryXD G c).base.cfg further)
      G.q.link.table.cubeBits G.q.link.table.answers = some l1 := by
    rw [← S.field]
    exact (OnBytes.Tie.seedsUnder_eq recordSeeds (linkAtCfg G.q c) further).symm.trans e₁
  exact cmpE_program (entryXD G c) (hok c hc) hc (d1Run _ _) G.q.link.table (fun _ _ => true)
    S.field S.pos (S.room c) (S.few c) table further h₀ h₁ hr l0 l1 f₀ f₁

/-- The four conditions at the full size. -/
theorem record_fit : SeedsFit recordGround where
  field := full_field ByteArray.empty
  pos := by decide +kernel
  room := fun c => full_enough c
  few := fun c => by rw [full_K]; norm_num

/-- The four conditions at the small size. -/
theorem small_record_fit : SeedsFit smallRecordGround where
  field := small_field ByteArray.empty
  pos := by decide +kernel
  room := fun c => small_enough c
  few := fun c => by rw [small_K]; norm_num

end OnBytes.K.Left
