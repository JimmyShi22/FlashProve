-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxRowsAt.lean: the field `rows` of OnBytes/K/Left/Lax.lean's list at a ground: round
by round and tree by tree of the chain's own, "the written link's verifier reads this position"
means "the file's opening of that tree lists it", at `entryXD G c` and at what the strict reader
read under the program's own description at two tables.

`rowsL_read` (OnBytes/K/Left/LaxOwn.lean) shows it for a description S with stored tables and a
typed description D, from three conditions that tie D to S. This file pays the three at a ground.

Main names:
  `ds_at`: the typed rounds' data are those of the program's description: they do not read the
    statement.
  `okb_at`: the program's description at two tables is within the limits of OnBytes/TypedOracleCompiler, if
    `entryXD G c` is and the description is in order (which the reader's yes says).
  `rows_at`: the field, for verifier messages ρ whose typed draws are the reader's.

Limits: values alone. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxOwn
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Run.AllRoots
import OnBytes.Tie.OneChain

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie (EntryGround linkAtCfg)
open TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View)

section
variable (G : EntryGround) (c : ByteArray) (first further : Params.TableName)

/-- The typed rounds' data are those of the program's description at two tables. -/
theorem ds_at : (entryXD G c).ds =
    PQ.rds (PQ.inFile (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement first further)).base) :=
  PQ.rds_congr _ _ rfl rfl

/-- The program's description at two tables is within the limits of OnBytes/TypedOracleCompiler. -/
theorem okb_at (hok : PQ.ok (entryXD G c).base = true)
    (hS : (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement first further)).ok = true) :
    PQ.ok (PQ.inFile (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement first further)).base) = true := by
  have hb : (Params.entrySpecOf (linkAtCfg G.q c) G.rs
      (Params.Link.statement first further)).base.ok = true := by
    unfold Fmt.SpecX.ok at hS
    simp only [Bool.and_eq_true] at hS
    exact hS.1.1
  simp only [PQ.ok, Bool.and_eq_true, and_assoc] at hok ⊢
  exact ⟨hb, hok.2⟩

/-- The field `rows` at a ground. -/
theorem rows_at {X : Type} (dec : X → View → Bool) (hok : PQ.ok (entryXD G c).base = true)
    (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : Fmt.ChainOut)
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) seen b i =
        some (o, j))
    (x : X) (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds)))
    (hd : PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = o.rounds.toList.map (·.drawn))
    (pls : Plains (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds))) :
    PQ.RowsL (entryXD G c).C (tblOf ((opsOf 1 o).filter fun op => !op.sh.stored))
      (entryXD G c).base.plan.salt (entryXD G c).ds o.rounds.toList fun q =>
        (haveI := (wqXE (entryXD G c) dec).decO
         decide (Sum.inr q ∈ (PSXE (entryXD G c) dec).up.loc.reads x ρ pls)) :=
  rowsL_read (entryXD G c) dec _ Fmt.oracle (ds_at G c first further)
    (okb_at G c first further hok (OnBytes.Tie.readX_ok _ _ seen b i _ e)) rfl seen b i o j e x ρ
    hd pls

end

end OnBytes.K.Left
