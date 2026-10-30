-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieSeedRec.lean: the reading of a table as a record `recOfArm` and the test `servedArm`
(OnBytes/K/ArmLetters.lean) are as the seeds' fields ask (`RecIsProgram`,
Johnson/Top/TieSeedArm.lean).

`recOfArm G Z x t` is made of what the program's own `recordSeeds` returns at the table's name,
under the parameters of a ground G of the entry's link at the digest of three public files Z, and
of the table's answers. `RecIsProgram` asks: where the program says yes on a served statement, both
tables are read as records, and each record's seed is the typed form of what `recordSeeds` returns
at the table's name.

Main theorem.
 `recIsProgram_arm`   `RecIsProgram` at the field of G's parameters, the digest of Z, the shape of
                      G's tables, `seedOfC` (OnBytes/TypedOracleCompiler/Slice/EntryConv.lean), `servedArm Z` and
                      `recOfArm G Z`. By `recOfArm_port`.

Asked: the tables of G have answers; Z's parameter file says G's lines.

Limits: nothing on the seeds' tests themselves. `recordSeeds`, the digest of Z, `PortYesAt`
(OnBytes/K/Top.lean; it is "the program says yes" of this head) and `servedArm` hash by the format's
hash at Lean's BLAKE2b, as one fixed function (`Fmt.formatHash`; `formatHashFastForm_eq_formatHash`, OnBytes/Hash/HEq.lean;
`queryH_eq_query`, OnBytes/Hash/QueryEq.lean), and `PortYesAt` and `servedArm` by the second hash
function too, fixed likewise (OnBytes/Hash/SecondHashFunction.lean). So the test that says which statements are
served calls both functions too. No hash function is a variable of this theorem, and nothing here is
said at another function in the hash's place. That any files meet `PortYesAt` with a served
statement is not shown here. Nothing on soundness.

Terms: lean/GLOSSARY.md.


-/
import Johnson.Top.TieSeedArm
import OnBytes.K.ArmLetters

set_option autoImplicit false

namespace OnBytes.K

open OnBytes.Tie OnBytes.Slice TypedOracleCompiler.Slice

/-- **`recOfArm` is made of the program's own seeds.** -/
theorem recIsProgram_arm (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false) (Z : Pub)
    (hZ : G.SaysLines Z.pol) :
    RecIsProgram G.q.given.plan.field Z.digest G.q.link.table
      (seedOfC G.q.link.table.cubeBits G.q.link.table.answers) (fun x => servedArm Z x = true)
      (recOfArm G Z) := by
  intro Fl o id table further hp hs
  obtain ⟨e1, e2, e3⟩ := servedArm_pins hs
  obtain ⟨l0, l1, c, cj, a0, a1, r0, r1, -⟩ :=
    recOfArm_port G hA hp (servedArm_lines G hZ hs) e1 e2 e3 (stmOf Fl o)
  -- by named equations, not by unfolding: see `Tie.seedsUnder_eq`
  refine ⟨l0, l1, c, cj,
    (seedsUnder_eq recordSeeds (linkAtCfg G.q Z.digest) table).symm.trans a0,
    (seedsUnder_eq recordSeeds (linkAtCfg G.q Z.digest) further).symm.trans a1, r0, r1, ?_, ?_⟩
  · have h := r0
    rw [recOfArm, a0, Option.map_some] at h
    rw [← Option.some.inj h]
    rfl
  · have h := r1
    rw [recOfArm, a1, Option.map_some] at h
    rw [← Option.some.inj h]
    rfl

end OnBytes.K
