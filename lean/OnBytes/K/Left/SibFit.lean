-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/SibFit.lean: at every yes of the program, the instance on which the entry's verifier
on plain data runs (`xOfAskedC` of the converter's value) is the instance made of two records
(`recX`, OnBytes/Flat/LinkSib.lean): of the records read off that value
(`recsOf`, OnBytes/Flat/LinkSibFit.lean).

Main names:
  `answers_at`: under `PortYesAt` and `G.SaysLines`: both tables have 2 ^ v * s answers, each with
    words below the prime; v, s: the ground's numbers of row variables and of answers.
  `recX_port`: so `recX (recsOf …) = xOfAskedC …` at the value made of the two tables, any seeds and
    anything read.

Hypotheses: `PortYesAt`; `G.SaysLines F.pol`; the ground's tables have a record; its field is the
one in which the program computes.

Limits: values alone. That some files meet `PortYesAt` is not shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxKeys
import OnBytes.Flat.LinkSibFit

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie OnBytes.Slice TypedOracleCompiler.Slice OnBytes.Flat

/-- The answers of a table of which `tableKey` makes a key are as many as the shape says. -/
theorem answers_length {cfg : ByteArray} {sh : Params.IndexShape} {t : Params.TableName}
    {item : ℕ} {k : TableKey} (hk : tableKey .two cfg sh t item = some k) :
    t.answers.length = 2 ^ sh.v * sh.answers := by
  have hfit := (Params.tableKey_fits hk).1
  rw [TableKey.fits, Params.tableKey_record hk] at hfit
  simp only [Bool.and_eq_true, beq_iff_eq, List.size_toArray] at hfit
  exact hfit.1.1

/-- Both tables' answers, at every yes of the program. -/
theorem answers_at (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    table.answers.length = 2 ^ G.q.link.table.v * G.q.link.table.answers ∧
      further.answers.length = 2 ^ G.q.link.table.v * G.q.link.table.answers ∧
      (∀ a ∈ table.answers, okE a = true) ∧ ∀ a ∈ further.answers, okE a = true := by
  obtain ⟨p, -, hk, -, -, -, -⟩ := entry_facts h
  obtain ⟨j, hj⟩ := Model.Verify.keyCheck_table hk
  obtain ⟨r, -, -, hr, hf, -, -, -, -⟩ := read_at G hA h hl
  have hF' : (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])).given.plan.field =
      .two := hF
  have ans0 := key_answers hj
  have ans1 := entry_answers hF' hr
  rw [hf] at ans1
  obtain ⟨_, S, _, hS, -, -⟩ := entry_read_spec _ table F.ent r hr
  obtain ⟨⟨k0, k1, hk0, hk1, -⟩, -⟩ := Params.entrySpec_eq_all hS
  rw [hf] at hk1
  rw [hF'] at hk0 hk1
  exact ⟨answers_length hk0, answers_length hk1, ans0, ans1⟩

/-- The instance of a run is the instance made of the two records. -/
theorem recX_port (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    (hF : G.q.given.plan.field = .two)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol)
    (l0 l1 : List (List E × E)) (o : Fmt.ChainOut) :
    recX (recsOf G.q.link.table.v G.q.link.table.cubeBits G.q.link.table.answers
        ⟨table, further, l0, l1, o⟩) =
      xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers ⟨table, further, l0, l1, o⟩ := by
  obtain ⟨h0, h1, k0, k1⟩ := answers_at G hA hF h hl
  exact recX_recsOf _ _ _ _ h0 h1 k0 k1

end OnBytes.K.Left
