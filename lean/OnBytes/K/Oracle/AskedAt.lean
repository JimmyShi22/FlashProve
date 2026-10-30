-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/AskedAt.lean: where the exit code 0 holds of a call's files, the reader of the
entry file that asks an oracle for every hash (`askedE`, OnBytes/Tie/EntryAsked.lean), run at the
oracle that is made from the format's hash, returns what the program itself read and drew.

`askedE q first ent` is the twin of the program's `Entry.read` over a monad, with the hash asked of
an oracle, and then both tables' seeds, asked. OnBytes/Tie/EntryAsked.lean shows the statement below
from `ZeroFacts`; here it is shown from `PortYesAt` (OnBytes/K/Top.lean), by the same steps.

Main names:
  `asked_port`: under `PortYesAt` and `G.SaysLines`: `(askedE q table F.ent).det (Run.oBits ())` is
    the two tables that the program hands on, the program's seeds at both names, and what
    `Entry.read` read of the chain. q: G's parameters with the three public files' digest.
  `asked_value`: so it is the value of the strict converter `convE`
    (OnBytes/TypedOracleCompiler/Slice/EntryConv.lean) on these files, and that is some value with the two tables.
  `asked_conv`: the same as one equation between plain functions: `askedAt`, the asking half's value
    at a function in the hash's place, at the function that `Run.oBits` induces, is `convE`.

Hypotheses: `PortYesAt`; `G.SaysLines F.pol`; the ground's tables have a record (a test on G).

What is not claimed. One fixed oracle: nothing on a drawn oracle, on soundness or on any
probability. Values alone: of what is asked nothing is said here (OnBytes/Tie/EntryAskedCost.lean
counts it). That some files meet `PortYesAt` is not shown here. The program does not call `askedE`.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxGround
import OnBytes.K.Left.LaxFrom
import OnBytes.Tie.EntryAsked

set_option autoImplicit false

namespace OnBytes.K.Oracle
open OnBytes.Tie TypedOracleCompiler.Slice OnBytes.K.Left

/-- At the oracle made from the format's hash, the reader that asks returns what the program read
and drew. -/
theorem asked_port (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    ∃ (r : Entry.EntryRead) (l0 l1 : List (List E × E)),
      Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
        .ok r ∧ r.further = further ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        table = some l0 ∧
      seedsUnder recordSeeds (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL]))
        further = some l1 ∧
      (askedE (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent).det
        (_root_.Run.oBits ()) = some ⟨table, further, l0, l1, r.chain.out⟩ := by
  obtain ⟨-, -, -, -, -, h0, hb⟩ := entry_facts h
  obtain ⟨r, l0, l1, -, hr, hf, a0, a1, -, h32, -⟩ := ground G hA h hl
  have hc32 := Params.configurationDigest_size [F.pol, F.lay, F.KL]
  generalize Params.configurationDigest [F.pol, F.lay, F.KL] = c at hc32 hr a0 a1 ⊢
  have hsm : ∀ P, entryPlaceR recordSeeds (linkAtCfg G.q c) table F.ent = some P →
      P.spec.ok = true → smallFX P.spec F.ent = true := by
    intro P hP hokP
    obtain ⟨_, ⟨rs2, h2, eP⟩, _⟩ := entryPlaceR_spec_any hP
    obtain rfl : G.rs = rs2 := Option.some.inj ((G.rounds_at c).symm.trans h2)
    rw [eP] at hokP ⊢
    exact smallFX_of_withinX _ hokP (G.within_at c hc32 _ (specX_base _ hokP)) F.ent hb
  have key := (readWithR_reader (q := linkAtCfg G.q c) (first := table) (file := F.ent)
    (readInAt Fmt.oracle) (fun S i hs => readInAt_oracle S F.ent i Session.start hs)
    (fun S i y hx => readX_ok _ _ _ F.ent i _ (readInAt_read _ _ _ _ _ y.2 y.1 hx).1) hc32
    h0 hsm r).2 hr
  have H := seedsSame_oracle (linkAtCfg G.q c) hc32
  refine ⟨r, l0, l1, hr, hf, a0, a1, ?_⟩
  -- b0, b1 and the end: by named equations, not by unfolding: see `Tie.seedsUnder_eq`
  have b0 : seedsUnder (seedsAt Fmt.oracle) (linkAtCfg G.q c) table = some l0 :=
    (seedsUnder_eq _ _ _).trans
      ((H table.root h0).trans ((seedsUnder_eq _ _ _).symm.trans a0))
  have b1 : seedsUnder (seedsAt Fmt.oracle) (linkAtCfg G.q c) further = some l1 :=
    (seedsUnder_eq _ _ _).trans
      ((H further.root h32).trans ((seedsUnder_eq _ _ _).symm.trans a1))
  rw [askedE_det, askedAt_oBits, askedAt, key, Option.bind_some, b0, Option.bind_some, hf, b1,
    Option.map_some]

/-- So it is the strict converter's value on these files, and that is some value. -/
theorem asked_value (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    ∃ a : AskedE, a.first = table ∧ a.further = further ∧
      convE (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
        some a ∧
      (askedE (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent).det
        (_root_.Run.oBits ()) = some a := by
  obtain ⟨r, l0, l1, hr, hf, a0, a1, e⟩ := asked_port G hA h hl
  exact ⟨_, rfl, rfl, conv_eq hr hf a0 a1, e⟩

/-- The asking half's value at the function that the oracle made from the format's hash induces is
the strict converter's value on these files. -/
theorem asked_conv (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) :
    askedAt (_root_.Run.oB (_root_.Run.oBits ()))
        (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent =
      convE (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table F.ent := by
  obtain ⟨a, -, -, hc, ha⟩ := asked_value G hA h hl
  rw [hc, ← askedE_det, ha]

end OnBytes.K.Oracle
