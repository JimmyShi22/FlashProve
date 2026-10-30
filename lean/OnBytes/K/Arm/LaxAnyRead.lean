-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LaxAnyRead.lean: the record `LaxDebtsAny` (OnBytes/K/Arm/LaxAny.lean) from one yes
of the strict reader, the decision's yes on the reader's view, and the two fields that name the
carrier.

Of the nine fields four are paid here by the lemmas on a reading: `rows`
(OnBytes/K/Left/LaxOwn.lean), `cols` (OnBytes/K/OpenedCols.lean), `listed`
(OnBytes/K/Left/LaxExt.lean), `accept` (OnBytes/K/Left/LaxAccept.lean). None of the four names the
carrier, the oracle functions or the list of outer roots. The typed description D and the reader's
statement st stand apart. For proofs only; the program does not import this file.

Main theorem.
 `debtsAny_read`  the record. Asked: of the description: the test `PQ.ok`
                  (OnBytes/TypedOracleCompiler/Run/PlanQTypes.lean) at D's own part, and with st put in; random
                  bytes; all stored tables have the depth D.a and items 0 or 1; each is opened at
                  most once; `work`, `okx`. Of the reading: the reader's yes under D's own part with
                  st put in; the typing's yes; the decision's yes on the reader's view. Of the
                  carrier: `chain`, with "it draws what the reader drew" and "all tests of work
                  pass" beside it; `walks`. With `lax_any` the lax verifier at the skeleton then
                  says yes over that carrier.

What is not claimed. That any of these holds at a file or at any oracle functions. Nothing on
soundness.


-/
import OnBytes.K.Arm.LaxAny
import OnBytes.K.Left.LaxOwn
import OnBytes.K.Left.LaxExt
import OnBytes.K.Left.LaxAccept
import OnBytes.K.OpenedCols

set_option autoImplicit false

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Slice
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ (XD SOf RowsL inFile rds_congr)
open _root_.Run.PQ (View SgX)

variable {I X' X : Type} {L : BatchProtocolWithLeafBody I X'} (D : XD) (dec : X → View → Bool)
  (g : Fam (typedOracleFamily 256 (D.K + 1) L))
  (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
    OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
  (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
    PlainPart (shapeOf L .link) (annOf L .link))
  (xin : X → Option X') (embE : SgX → Body L) (cms : List (Dig 256))

/-- **The record, from one yes of the strict reader.** -/
theorem debtsAny_read (hok : PQ.ok D.base = true) (st : ByteArray) (O : ByteArray → ByteArray)
    (hokb : PQ.ok (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
      ⟨{ D.base with statement := st }, D.stored⟩ seen b i = some (o, j))
    (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) (hπ : assembleS D dec o = some π)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits)
    (chain : (recomputeChainOfProof (L := L) .link (PSXE D dec).up (wqXE D dec) embP xin cms x π).det g =
      some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList), Phase.loc v))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : PQ.passSL D.C D.ds ρ.2 = true)
    (work : ∀ r ∈ D.ds, r.entry.work ≤ 64) (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (walks : ArmWalks.Walks D g embS embE cms o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true) :
    LaxDebtsAny D dec g embS embP xin embE cms x o π ρ v := by
  have hds : D.ds = PQ.rds (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) :=
    rds_congr _ _ rfl rfl
  have listed := listed_read D dec ⟨{ D.base with statement := st }, D.stored⟩ O rfl hds.symm hokb
    hn (fun s hs => (hD s hs).1) seen b i o j e x ρ hd
  exact
    { str := hπ
      chain := chain
      work := work
      okx := okx
      rows := ⟨_, rowsL_read D dec ⟨{ D.base with statement := st }, D.stored⟩ O hds hokb hn seen b
        i o j e x ρ hd _⟩
      cols := colsFit_read (_root_.Fmt.HO O) ⟨{ D.base with statement := st }, D.stored⟩ hokb seen
        b i o j e
      listed := listed
      walks := walks
      accept := accept_read D hok st O hokb hn seen b i o j e dec x π hπ ρ hd hpass hD honce okx
        listed ⟨{ D.base with statement := st }, D.stored⟩ rfl rfl hdec }

end OnBytes.K.Arm
