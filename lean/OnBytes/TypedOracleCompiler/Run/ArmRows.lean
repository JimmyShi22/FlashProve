-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmRows.lean: the row law of an entry's written rounds, at the typed oracle
functions that the encoding over a second interface (`ArmRounds.implAt`) reads out of an oracle.

OnBytes/TypedOracleCompiler/Run/ChainERead.lean's `chain_one_read` recomputes a chain over any interface and any
typed oracle functions from two laws: the row law of the written rounds (`PQ.RowEnd`) and the law of
the first query. At the entry's own page the first is `rowEndE` (OnBytes/TypedOracleCompiler/Run/RowsE2.lean). Here
it is shown over the second interface L2, as there: from the strings (`ArmRounds.e162_put`, through
`armD_code_round`, OnBytes/TypedOracleCompiler/Run/ArmCodes.lean) to the values by `row_of_codes`
(OnBytes/TypedOracleCompiler/Run/RowsG.lean). No page over the first interface enters.

Main theorems.
 `rowAt_arm`     `PQ.RowAt` at the written round k, over L2; the way of the round's own plain part
                 is the page's `inE`, then `pbF.symm`.
 `rowEnd_arm`    `PQ.RowEnd` over L2, at the pins' label, from the typed round 1 and the format's
                 index 1 on, through `wayE`, then `pbF.symm`. Asked: `FitsE D`; K + 1 below 2 ^ 48.

Not claimed. The first query's law over L2. That any chain is recomputed. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.ArmRounds
import OnBytes.TypedOracleCompiler.Run.ArmCodes
import OnBytes.TypedOracleCompiler.Run.RowsE2

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.ArmRows
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Run.RowsE TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.PlainIn
open TypedOracleCompiler.Run.ArmRounds TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Run.LinkAlongM
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (K : ℕ) (V : Leaves (Le D early e))
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Le D early e) .link) (annOf (Le D early e) .link))
  (bd : L2.Bd ≃ (Le D early e).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 P.l s)
  (back : StrCode (AllPts 256 (K + 1) L2)) (g : Fam (rom 256))

/-- **The row law at one written round, over L2.** -/
theorem rowAt_arm (hK : K + 1 < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256)
    (hs : (D.ds.get k).entry.work ≠ 0 ∨ (D.ds.get k).kind ≠ .sealed)
    (hr : (D.ds.get k).trees.length = _root_.Fmt.countItem .root (D.ds.get k).items) :
    PQ.RowAt (fun _ : Unit => L2) D.C K
      (readBlocks (implAt P (K + 1) V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest f0 h0 back) g)
      .link (oB (g ())) P.l (fun ρ => .f2 none ρ) (D.ds.get k)
      (fun pl => pbF.symm (inE D early e k pl)) (k.val + 1) (k.val + 1) :=
  fun ρ rt pl hρ hrt hno =>
    row_of_codes (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest (K + 1) P.l P.hlt P.hR f0 h0
      (laterM (Le D early e) L2 pbF) (e162 P (K + 1)) (e162_is P (K + 1))
      (leafM (Le D early e) L2 bd) V P.cfg P.hcfg back) g .link _ P.l _ _ _ _ _ _ fun j => by
      rw [blockNo_eq _ (K + 1) j (Or.inl (Nat.succ_pos K)), ← ordOf_plain _ hs]
      exact armD_code_round L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest (K + 1) P.l P.hlt P.hR f0 h0 _
        (e162 P (K + 1)) (e162_is P (K + 1)) _ V P.cfg P.hcfg back _ (Nat.succ_ne_zero _) _
        (sel_round L2 pbF k ρ rt pl) j _
        (e162_put P (K + 1) hK k hi hw ρ hρ rt pl (okRound_true _ _ _ _ (hrt.trans hr) hno) j)

/-- **The row law of the entry's written rounds, over L2.** -/
theorem rowEnd_arm (F : FitsE D) (hK : K + 1 < 2 ^ 48) :
    PQ.RowEnd (fun _ : Unit => L2) D.C K
      (readBlocks (implAt P (K + 1) V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest f0 h0 back) g)
      .link (oB (g ())) P.l D.ds (fun z => pbF.symm (wayE D early e (.inr z))) 1 1 :=
  rowEnd_of_get _ D.C K _ .link _ P.l D.ds _ 1 1 fun k => by
    have hm : D.ds.get k ∈ D.ds := List.get_mem D.ds k
    have h := rowAt_arm P K V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest f0 h0 back g hK k
      (by have := k.isLt; have := F.few; omega)
      (Nat.lt_of_le_of_lt (F.work _ hm) (by omega)) (F.plain _ hm) (F.roots _ hm)
    have ee : (fun pl => pbF.symm (wayE D early e (.inr (inA D.C D.ds k pl)))) =
        fun pl => pbF.symm (inE D early e k pl) :=
      funext fun pl => congrArg (fun z => pbF.symm (Sum.inr z)) (toL_inA D.C D.ds k pl)
    rw [ee, Nat.add_comm 1 k.val]
    exact h

end TypedOracleCompiler.Run.ArmRows
