-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieArmServed.lean: the tie of Johnson/Top/TieArm.lean for the entry's arm with the lax
Link, with "served" paid from the exit code.

Main theorem. `exit_arm_served`: let r be an `ArmIn` that serves every statement which passes the
test `servedAt Z` (OnBytes/K/Served.lean), and let `EntryPart` hold at r's shape. For every run of
the Lean program `verify-on-bytes` (OnBytes/Main.lean) that ends in 0 there are the files F that
this run has read, the ID among its arguments, and the program's own two tables (`PortYesAt`), such
that: if the three public files as read are Z's, byte for byte, and the call names neither -policy
nor -no-proof-of-work, then the two tables are read as records, the fixed reading gives the further
table and Link's typed string off the key file and the entry file, and the run of `armL`, at what
`r.m` reads out of Lean's BLAKE2b, says yes. By `served_any` (OnBytes/K/ServedAny.lean).

What is not claimed. All that the heads of Johnson/Top/TieArm.lean, OnBytes/K/Served.lean and
OnBytes/K/ServedAny.lean do not claim. `EntryPart` stays a hypothesis here, with `r.Served` inside
its three fields. A call that names -policy is not spoken of. Z, r and the reading R are
parameters. For proofs only; the program does not import this file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.TieArm
import OnBytes.K.ServedAny

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig oBits)

/-- The tie for the entry file at the arm with the lax Link, with "served" paid from the exit code
but for three pins and two options. -/
theorem exit_arm_served (r : ArmIn) (Z : Pub) (hZ : ∀ x, servedAt Z x = true → r.Served x)
    (R : Reading5 r.shape) (A : EntryPart r.shape R)
    {args : List String} {s s' : World} (h : Shell.Run (_root_.main args) s 0 s') :
    ∃ (config ivk request y proof : String) (a : Asked) (F : Files) (t : List Event) (id : String)
      (pre post : List String),
      args = "verify" :: config :: ivk :: request :: y :: proof ::
        (pre ++ "-id" :: id :: post) ∧
      kindOf args = .whole config ivk request y proof a ∧
      Steps opsIO (wholeReads config ivk request y proof F.entry (.bytes F.pol) (.bytes F.KL)
        (.bytes F.lay) (.bytes F.key) (.bytes F.request) (.bytes F.y) (.bytes F.proof)
        (.bytes F.ent) ++ t) s s' ∧
      a.options.id = some id ∧ a.options.bits = 128 ∧
      ∃ (table further : OnBytes.Params.TableName), PortYesAt F id table further ∧
        (F.pol = Z.pol → F.lay = Z.lay → F.KL = Z.KL → a.options.policy = none →
          a.options.noProofOfWork = false →
          ∃ (c cj : r.L.Rec) (πL : OneProtocolProof 256 (batLC r.L r.aL)),
            r.recOf (stmOf F a.options) table = some c ∧
            r.recOf (stmOf F a.options) further = some cj ∧
            R.ent (stmOf F a.options) F.key F.ent = some (further, πL) ∧
            (runA r.W (armL r.W r.Sd r.cA) (readBlocks r.m oBits)
              (bytesToDig table.root, bytesToDig further.root, c, cj, πL)).1 = true) := by
  obtain ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table, further,
    hp, hs⟩ := exit_arm r R A h
  refine ⟨config, ivk, request, y, proof, a, F, t, id, pre, post, e, h1, h2, hi, hb, table,
    further, hp, fun p1 p2 p3 o1 o2 => hs (hZ _ ?_)⟩
  have hq := served_any h config ivk request y proof a F t h1 h2 o1 o2
  have eZ : (⟨F.pol, F.lay, F.KL⟩ : Pub) = Z := by
    cases Z
    simp only [Pub.mk.injEq]
    exact ⟨p1, p2, p3⟩
  rw [eZ] at hq
  exact hq

end OnBytes.K
