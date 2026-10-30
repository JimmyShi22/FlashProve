-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/LaxRestAt.lean: three fields of what OnBytes/K/Left/LaxAt.lean lists as still owed at
a ground (`LaxRest`): `rows`, `cols`, `listed`, at `entryXD G c` and at what the strict reader read
under the program's own description at the two tables of a converter's value.

The three are shown for any description with stored tables in OnBytes/K/Left/LaxOwn.lean
(`rowsL_read`), OnBytes/K/OpenedCols.lean (`colsFit_read`) and OnBytes/K/Left/LaxExt.lean
(`listed_read`). Here their conditions on the description are paid at a ground.

Main names:
  `xdok_of`: `entryXD G c` is within the limits of OnBytes/TypedOracleCompiler on a description with stored tables,
    from the line's limits test; `depth_of`: so all stored tables have its depth.
  `cols_at`, `listed_at`: the two fields for any decision and instance (`rows_at`:
    OnBytes/K/Left/LaxRowsAt.lean).
  `rows_rest`, `cols_rest`, `listed_rest`: the three in the letters of `LaxRest`.

Hypotheses: the limits of OnBytes/TypedOracleCompiler at `entryXD G c`; the line's limits test at the empty
statement; the reader's equation.

Limits: values alone. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.LaxAt
import OnBytes.K.Left.LaxRowsAt
import OnBytes.K.Left.LaxExt
import OnBytes.K.OpenedCols

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie (EntryGround linkAtCfg AskedE withinX)
open TypedOracleCompiler.Slice TypedOracleCompiler.Run TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.PQ (View)

section
variable (G : EntryGround) (c : ByteArray)
  (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)

include hw in
/-- The description with its stored tables is within the limits of OnBytes/TypedOracleCompiler. -/
theorem xdok_of : (entryXD G c).ok = true :=
  ok_asTypedCompilerDescription (OnBytes.Tie.xdOf (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty)
                         fun r0 r1 => Params.Link.statement ⟨r0, []⟩ ⟨r1, []⟩) (OnBytes.Slice.within_ok _ _ hw)

include hw in
/-- All stored tables have the description's depth. -/
theorem depth_of : ∀ t ∈ (entryXD G c).stored.flatten, t.sh.a = (entryXD G c).a := by
  intro t ht
  have hD := xdok_of G c hw
  simp only [PQ.XD.ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hD
  exact (hD.2 t ht).1.1

end

section
variable (G : EntryGround) (c : ByteArray) (first further : Params.TableName)
  (hok : PQ.ok (entryXD G c).base = true)
  (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ) (o : Fmt.ChainOut)
  (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
    (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement first further)) seen b i =
      some (o, j))

include hok e in
/-- The field `cols` at a ground. -/
theorem cols_at : ColsFit ((opsOf 1 o).filter fun op => !op.sh.stored) :=
  colsFit_read _ _ (okb_at G c first further hok (OnBytes.Tie.readX_ok _ _ seen b i _ e)) seen b i
    o j e

include hok e in
/-- The field `listed` at a ground. -/
theorem listed_at
    (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)
    {X : Type} (dec : X → View → Bool) (x : X)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds)))
    (hd : PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = o.rounds.toList.map (·.drawn)) :
    ListedX (entryXD G c) (entryXD G c).a ((opsOf 1 o).filter fun op => op.sh.stored) fun p =>
      (haveI := (wqXE (entryXD G c) dec).ext.dec
       decide (p ∈ (PSXE (entryXD G c) dec).up.loc.extReads x ρ)) :=
  listed_read (entryXD G c) dec _ Fmt.oracle rfl (ds_at G c first further).symm
    (okb_at G c first further hok (OnBytes.Tie.readX_ok _ _ seen b i _ e)) rfl (depth_of G c hw)
    seen b i o j e x ρ hd

end

/-! ## In the letters of `LaxRest` -/

section
variable (G : EntryGround) (c : ByteArray) (hok : PQ.ok (entryXD G c).base = true) (a : AskedE)
  (seen : Fmt.Seen) (b : ByteArray) (i j : ℕ)
  (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
    (Params.entrySpecOf (linkAtCfg G.q c) G.rs (Params.Link.statement a.first a.further)) seen b
      i = some (a.out, j))

include hok e in
/-- `LaxRest.rows`. -/
theorem rows_rest (π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds)))
    (hd : PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn)) :
    ∃ sb, PQ.RowsL (entryXD G c).C (tblOf (ownOps a.out)) sb (entryXD G c).ds
      a.out.rounds.toList fun q => (haveI := (wqXE (entryXD G c) (decAt G c)).decO
        decide (Sum.inr q ∈ (PSXE (entryXD G c) (decAt G c)).up.loc.reads (xOfAskedC _ _ a) ρ
          (effPlains (PSXE (entryXD G c) (decAt G c)).up.loc.shape
            (PSXE (entryXD G c) (decAt G c)).up.ann (rtsAt G c a.out) π.plains))) :=
  ⟨_, rows_at G c a.first a.further (decAt G c) hok seen b i j a.out e _ ρ hd _⟩

include hok e in
/-- `LaxRest.cols`. -/
theorem cols_rest : ColsFit (ownOps a.out) :=
  cols_at G c a.first a.further hok seen b i j a.out e

include hok e in
/-- `LaxRest.listed`. -/
theorem listed_rest
    (hw : withinX (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) = true)
    (ρ : Rho (_root_.Run.Twin.up (PQ.SOf (entryXD G c).C (entryXD G c).ds)))
    (hd : PQ.drawnSL (entryXD G c).C (entryXD G c).ds ρ.2 = a.out.rounds.toList.map (·.drawn)) :
    ListedX (entryXD G c) (entryXD G c).a (stoOps a.out) fun p =>
      (haveI := (wqXE (entryXD G c) (decAt G c)).ext.dec
       decide (p ∈ (PSXE (entryXD G c) (decAt G c)).up.loc.extReads (xOfAskedC _ _ a) ρ)) :=
  listed_at G c a.first a.further hok seen b i j a.out e hw (decAt G c) _ ρ hd

end

end OnBytes.K.Left
