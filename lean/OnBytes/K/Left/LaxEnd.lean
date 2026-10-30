-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxEnd.lean: the one hypothesis of `entry_left` (`LaxAt`, OnBytes/K/Left/Top.lean)
from the exit code 0 and from the five fields that are still owed (`LaxRest`,
OnBytes/K/Left/LaxAt.lean); and `entry_left` at both grounds with these five fields in its place.

Main names:
  `RestAt G hok F table further`: `LaxRest` at every r, l0, l1 and π that meet the four equations of
    `LaxAt`: what `Entry.read` returned, the program's seeds at both names, the typed string.
  `laxAt_of`: `FromPort` (OnBytes/K/Left/LaxFrom.lean) and `RestAt` give `LaxAt`. The values that
    `FromPort` names are those of `LaxAt`: each is the value of a function.
  `entry_left_full`, `entry_left_small`: from the program's yes to the yes of the entry's verifier
    of a call, at the two grounds. Hypotheses: `PortYesAt`, `G.SaysLines F.pol`, `RestAt`.
  `RestAll G hok`: `RestAt` at every yes of the program whose parameter file has the ground's lines.
  `leftAt_full`, `leftAt_small`: `RestAll` gives `EntryLeftAt` (OnBytes/K/Left/TopAt.lean) at the
    two grounds.

Limits: `RestAt` is a hypothesis here. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxFrom
import OnBytes.K.Left.TopAt

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open TypedOracleCompiler.Slice
open TypedOracleCompiler.Compile.Batch (OneProtocolProof)

/-- The five fields that are still owed, at every r, l0, l1 and π that meet the four equations. -/
def RestAt (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    (F : Files) (table further : Params.TableName) : Prop :=
  ∀ (r : Entry.EntryRead) (l0 l1 : List (List E × E))
    (π : OneProtocolProof 256 (PSXE (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
                  (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL]))).up),
    Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
      .ok r → r.further = further →
    seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
      table = some l0 →
    seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
      further = some l1 →
    assembleS (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL]))
      (decAt G (Params.configurationDigest [F.pol, F.lay, F.KL])) r.chain.out = some π →
    LaxRest G (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) (hok _ (Params.configurationDigest_size _))
      ⟨table, further, l0, l1, r.chain.out⟩ π

/-- The lax verifier's yes at what the program's reader has read, from `FromPort` and the five
fields. -/
theorem laxAt_of (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true)
    {F : Files} {table further : Params.TableName} (hfp : FromPort G F table further)
    (hR : RestAt G hok F table further) :
    LaxAt G hok (Params.configurationDigest [F.pol, F.lay, F.KL])
      (Params.configurationDigest_size _) table further F.ent := by
  intro r l0 l1 π hr hf a0 a1 hπ
  obtain ⟨r', l0', l1', π', hconv, hπ', hch, hd, -⟩ := hfp
  have e := Option.some.inj (hconv.symm.trans (conv_eq hr hf a0 a1))
  obtain ⟨-, -, e0, e1, eo⟩ := AskedE.mk.inj e
  subst e0 e1
  rw [eo] at hπ' hch
  obtain rfl : π' = π := Option.some.inj (hπ'.symm.trans hπ)
  exact lax_at G _ _ (hok _ (Params.configurationDigest_size _))
    ⟨table, further, l0', l1', r.chain.out⟩ π' hπ hch hd (hR r l0' l1' π' hr hf a0 a1 hπ)

/-- From the program's yes to the yes of the entry's verifier of a call, at the full size. -/
theorem entry_left_full {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : recordGround.SaysLines F.pol)
    (hR : RestAt recordGround record_ok F table further) :
    ∃ (a : AskedE) (nid : String), Model.Verify.idAsked id = some nid ∧ a.first = table ∧
      a.further = further ∧
      prepE recordGround Params.stdFull false F.pol F.lay F.KL F.key F.ent =
        .ok ⟨Params.configurationDigest [F.pol, F.lay, F.KL], Params.configurationDigest_size _,
          linkAtCfg recordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL]), a⟩ ∧
      verifyE recordGround record_ok ⟨nid, Params.configurationDigest [F.pol, F.lay, F.KL],
        Params.configurationDigest_size _⟩ a = true :=
  entry_left recordGround record_ok record_answers record_fit record_pins Params.stdFull rfl h hl
    (laxAt_of recordGround record_ok (from_port_full h hl) hR)

/-- The same at the small example. -/
theorem entry_left_small {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : smallRecordGround.SaysLines F.pol)
    (hR : RestAt smallRecordGround small_record_ok F table further) :
    ∃ (a : AskedE) (nid : String), Model.Verify.idAsked id = some nid ∧ a.first = table ∧
      a.further = further ∧
      prepE smallRecordGround Params.stdSmall false F.pol F.lay F.KL F.key F.ent =
        .ok ⟨Params.configurationDigest [F.pol, F.lay, F.KL], Params.configurationDigest_size _,
          linkAtCfg smallRecordGround.q (Params.configurationDigest [F.pol, F.lay, F.KL]), a⟩ ∧
      verifyE smallRecordGround small_record_ok
        ⟨nid, Params.configurationDigest [F.pol, F.lay, F.KL],
          Params.configurationDigest_size _⟩ a = true :=
  entry_left smallRecordGround small_record_ok small_record_answers small_record_fit
    small_record_pins Params.stdSmall rfl h hl
    (laxAt_of smallRecordGround small_record_ok (from_port_small h hl) hR)

/-- `RestAt` at every yes of the program whose parameter file has the ground's lines. -/
def RestAll (G : EntryGround)
    (hok : ∀ c : ByteArray, c.size = 32 → TypedOracleCompiler.Run.PQ.ok (entryXD G c).base = true) : Prop :=
  ∀ (F : Files) (id : String) (table further : Params.TableName),
    PortYesAt F id table further → G.SaysLines F.pol → RestAt G hok F table further

/-- At the full size: the five fields give the left half. -/
theorem leftAt_full (hR : RestAll recordGround record_ok) :
    EntryLeftAt recordGround record_ok Params.stdFull := fun F id table further h hl =>
  entry_left_full h hl (hR F id table further h hl)

/-- At the small example. -/
theorem leftAt_small (hR : RestAll smallRecordGround small_record_ok) :
    EntryLeftAt smallRecordGround small_record_ok Params.stdSmall := fun F id table further h hl =>
  entry_left_small h hl (hR F id table further h hl)

end OnBytes.K.Left
