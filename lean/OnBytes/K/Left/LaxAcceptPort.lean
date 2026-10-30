-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxAcceptPort.lean: the field `accept` at every yes of the program: the premise `hAc`
of `restAll_of` (OnBytes/K/Left/LaxRestAll.lean), general in the ground under tests on the ground,
and at the two grounds.

Under `PortYesAt` and `G.SaysLines`, `dec_yes` (OnBytes/K/Left/LaxKeys.lean) gives a reading of the
entry file, the program's seeds at both tables' names, the strict reader's equation, and the yes of
a run's decision on the reader's view. Readings and seeds are values of functions, so they are the
ones that the premise names. `accept_rest` (OnBytes/K/Left/LaxAcceptAt.lean) does the rest.

Main names:
  `AcceptAll G`: the premise, as a statement.
  `accept_port`: it holds, if the ground's tables have a record, its field is the second, its
    description is within the limits of OnBytes/TypedOracleCompiler at every digest of 32 bytes and in order at an
    empty statement, and among its openings of stored tables at most one names the statement's item
    1 and at most one another item.
  `accept_port_full`, `accept_port_small`: at the two grounds nothing is assumed.

Limits: values alone. Nothing on soundness; no probability. That some files meet `PortYesAt` is not
shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxAcceptAt
import OnBytes.K.Left.LaxKeys
import OnBytes.K.Left.LaxRestAll
import OnBytes.K.Left.LaxReal

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop

/-- The field `accept` at every yes of the program whose parameter file has the ground's lines: for
every reading r that the program's reader returns, the program's seeds l0, l1 and the typed string
π. -/
def AcceptAll (G : EntryGround) : Prop :=
  ∀ (F : Files) (id : String) (table further : Params.TableName),
    PortYesAt F id table further → G.SaysLines F.pol →
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
      AcceptAt G (Params.configurationDigest [F.pol, F.lay, F.KL])
        ⟨table, further, l0, l1, r.chain.out⟩ π

/-- The field `accept` at every yes of the program. -/
theorem accept_port (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two)
    (hok : ∀ c : ByteArray, c.size = 32 → PQ.ok (entryXD G c).base = true)
    (hb : (Params.entrySpecOf G.q G.rs ByteArray.empty).base.ok = true)
    (honce : ∀ c, ((entryXD G c).stored.flatten.map (·.item == 1)).Nodup) : AcceptAll G := by
  intro F id table further h hl r l0 l1 π hr _ e0 e1 hπ ρ hd hpass
  obtain ⟨r', l0', l1', i, hr', -, a0, a1, e, hdec⟩ := dec_yes G hA hF rfl rfl rfl h hl
  obtain rfl : r' = r := Except.ok.inj (hr'.symm.trans hr)
  obtain rfl : l0' = l0 := Option.some.inj (a0.symm.trans e0)
  obtain rfl : l1' = l1 := Option.some.inj (a1.symm.trans e1)
  exact accept_rest G _ (hok _ (Params.configurationDigest_size _))
    (within_of G hb _ (Params.configurationDigest_size _)) (honce _)
    ⟨table, further, l0', l1', r'.chain.out⟩ _ F.ent i _ e π hπ hdec ρ hd hpass

/-- At the full size. -/
theorem accept_port_full : AcceptAll recordGround :=
  accept_port recordGround record_answers record_field record_ok full_base_ok real_once_full

/-- At the small example. -/
theorem accept_port_small : AcceptAll smallRecordGround :=
  accept_port smallRecordGround small_record_answers small_record_field small_record_ok
    small_base_ok real_once_small

end OnBytes.K.Left
