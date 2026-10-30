-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LinkArmK.lean: the lax compiled verifier of an entry's link says yes over a second
interface, at the written encoding with K + 1 blocks, for every K that is at least the description's
own number of blocks: from one reading.

OnBytes/K/Arm/LinkArm2.lean has this at `D.K + 1` blocks: its `hK` asks that the second protocol's
wiring has that number. Here the skeleton is wired with K blocks in a verifier's message
(`wqXK D dec K chal`, OnBytes/K/Arm/WireK.lean), and the pieces are those at K: the record and the
join (OnBytes/K/Arm/LaxAnyK.lean), the decision's clause and the chain
(OnBytes/K/Arm/AcceptK.lean). The four fields that name no wiring's number are as before
(OnBytes/K/Left/LaxOwn.lean, LaxExt.lean, OnBytes/K/OpenedCols.lean). For proofs only; the program
does not import this file.

Main theorems.
 `debtsAnyK_read`   the record `LaxDebtsAnyK` from one yes of the strict reader, the chain and the
                    walks.
 `lax_twoK`         under `LaxDebtsAnyK`: the lax verifier at another protocol Q2 over E', with a
                    wiring of K + 1 blocks, says yes, if E' is the skeleton's kind of external
                    strings, `SameRun2` holds once both instances are fixed, the maps of external
                    symbols agree, and the two chains are handed the same in the field x.
 `link_debtsK`      from one reading: the record at the skeleton, over L2, at the written encoding
                    with K + 1 blocks.
 `link_armK`        so the yes at Q2, wq2, x2, π2.

What is asked beside what `link_arm2` asks: `D.K ≤ K`; K + 1 is below 2 ^ 48; chal fits the field's
data (`hkit`); the rounds' wires at K and chal obey the sibling's laws (`wires`). What is asked no
more: that the second wiring's number of blocks is `D.K + 1`; that no round has more than 64 bits of
work (it served for `wires`).

What is not claimed. That any of the premises holds at a file. That any object's Link has `SameRun2`
with the skeleton. The walks over L2 are a premise. The seeds' two tests. Nothing on soundness.


-/
import OnBytes.K.Arm.LaxAnyK
import OnBytes.K.Arm.AcceptK
import OnBytes.K.Left.LaxOwn
import OnBytes.K.Left.LaxExt
import OnBytes.K.OpenedCols
import OnBytes.K.TwoCarrySame2

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Compile.Batch.Carry
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf inFile rds_congr)
open OnBytes.Slice (seedEntry)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX)

section
variable {I X' X : Type} {L : BatchProtocolWithLeafBody I X'} (D : XD) (dec : X → View → Bool) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k) (g : Fam (typedOracleFamily 256 (K + 1) L))
  (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
    OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L)
  (embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
    PlainPart (shapeOf L .link) (annOf L .link))
  (xin : X → Option X') (embE : SgX → Body L) (cms : List (Dig 256))

/-- The record, from one yes of the strict reader. -/
theorem debtsAnyK_read (hok : TypedOracleCompiler.Run.PQ.ok D.base = true) (st : ByteArray)
    (O : ByteArray → ByteArray)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
      ⟨{ D.base with statement := st }, D.stored⟩ seen b i = some (o, j))
    (x : X) (π : OneProtocolProof 256 (PSXE D dec).up) (hπ : assembleS D dec o = some π)
    (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits)
    (chain : (recomputeChainOfProof (L := L) .link (PSXE D dec).up (wqXK D dec K chal) embP xin cms x π).det g =
      some (ρ, ((none, some []), PQ.rtSL D.C D.ds o.rounds.toList), Phase.loc v))
    (hd : PQ.drawnSL D.C D.ds ρ.2 = o.rounds.toList.map (·.drawn))
    (hpass : PQ.passSL D.C D.ds ρ.2 = true)
    (wires : (PQ.wqS D.C K chal D.ds fun _ => true).OKG) (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a ∧ s.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (walks : ArmWalks.Walks D g embS embE cms o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true) :
    LaxDebtsAnyK D dec K chal g embS embP xin embE cms x o π ρ v := by
  have hds : D.ds =
      TypedOracleCompiler.Run.PQ.rds (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) :=
    rds_congr _ _ rfl rfl
  have listed := listed_read D dec ⟨{ D.base with statement := st }, D.stored⟩ O rfl hds.symm hokb
    hn (fun s hs => (hD s hs).1) seen b i o j e x ρ hd
  exact
    { str := hπ
      chain := chain
      wires := wires
      okx := okx
      rows := ⟨_, rowsL_read D dec ⟨{ D.base with statement := st }, D.stored⟩ O hds hokb hn seen b
        i o j e x ρ hd _⟩
      cols := colsFit_read (_root_.Fmt.HO O) ⟨{ D.base with statement := st }, D.stored⟩ hokb seen
        b i o j e
      listed := listed
      walks := walks
      accept := accept_readK D dec K chal hok st O hokb hn seen b i o j e x π hπ ρ hd hpass hD honce
        okx listed ⟨{ D.base with statement := st }, D.stored⟩ rfl rfl hdec }

variable {D dec K chal g embS embP xin embE cms}

/-- The yes at another protocol, on another term for the kind of external strings. -/
theorem lax_twoK {x : X} {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    {ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))} {v : Bits}
    (h : LaxDebtsAnyK D dec K chal g embS embP xin embE cms x o π ρ v) {E' : ExtSpec}
    (hE : E' = twoExternalStrings (2 ^ D.a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 (K + 1) Q2)
    (embS2 : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L .link) (annOf L .link))
    (xin2 : Y2 → Option X') (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = xin x)
    (embE2 : E'.Sym → Body L) (hemb : HEq embE2 embE)
    (hs : SameRun2 (L := L) (t := .link) (fixB Q2 x2) (fixB (PSXE D dec).up x) (fixW wq2 x2)
      (fixW (wqXK D dec K chal) x) embS2 embS embP2 embP (fixP π2 x2) (fixP π x))
    (depthReq : ℕ) :
    (verifyB (L := L) .link Q2 wq2 embS2 embP2 xin2 embE2 depthReq cms x2 π2).det g = true := by
  have h1 := verifyB_fix (L := L) .link Q2 wq2 embS2 embP2 xin2 embE2 depthReq cms x2 π2
  rw [← h1, hx, verifyB_same2 hE rfl hs (fun _ => xin x) embE2 embE hemb depthReq cms () g g
    HEq.rfl]
  exact lax_anyK_fix h depthReq

end

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁)) (K : ℕ)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (bd : L2.Bd ≃ (Ls D d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (back : StrCode (AllPts 256 (K + 1) L2)) (g : Fam (rom 256))
  (chal : ∀ e k, (Fin K → Dig 256) → D.C.Ch e k)

/-- The record at the skeleton wired with K blocks, over L2, from one reading. -/
theorem link_debtsK {X : Type} (dec : X → View → Bool) (x : X) (F : FitsE D) (hDK : D.K ≤ K)
    (hK0 : K + 1 < 2 ^ 48) (hkit : _root_.Run.PQ.KitFits D.base.plan.field D.C K chal)
    (wires : (PQ.wqS D.C K chal D.ds fun _ => true).OKG)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (an an' : An) (a₀ : tr an = first.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L2) (embE : SgX → Body L2)
    (walks : ArmWalks.Walks D
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
        rest isPL hpL cA tr hinj hlen htr (K + 1) back) g) embS embE
      (c₀ :: c₁ :: (cA an ++ cA an')) o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits),
      LaxDebtsAnyK D dec K chal
        (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
        rest isPL hpL cA tr hinj hlen htr (K + 1) back) g) embS
        (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
        (fun _ => none) embE (c₀ :: c₁ :: (cA an ++ cA an')) x o π ρ v := by
  obtain ⟨seen, b, i, j, e⟩ := A.read
  obtain ⟨run', pl, tab, tx, h1, h2, -, -, hsalt, hroots, hpl, -⟩ := assembleS_some D dec hπ
  obtain rfl : run' = run := Option.some.inj (h1.symm.trans A.runIs)
  obtain rfl : pl = pls := Option.some.inj (h2.symm.trans A.plains)
  obtain ⟨ρ, v, hc, hd, hp⟩ := chain_armK D d₁ cfg hcfg pd rest1 V K L2 pbF bd p0 p1 isP0 isP1
    cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr back g dec (fun _ => none) x rfl F hDK hK0
    first further c₀ c₁ _ o run' pl A an an' a₀ a₁ chal hkit π [] hsalt
    (by rw [hroots, List.append_nil]) hpl
  exact ⟨ρ, v, debtsAnyK_read D dec K chal _ embS _ (fun _ => none) embE _ hok st (oB (g ())) hokb
    hn seen b i o j e x π hπ ρ v hc hd hp wires okx hD honce walks hdec⟩

/-- The yes from one reading, at the written encoding with K + 1 blocks, at every depth of the
request tree. -/
theorem link_armK {X : Type} (dec : X → View → Bool) (x : X) (F : FitsE D) (hDK : D.K ≤ K)
    (hK0 : K + 1 < 2 ^ 48) (hkit : _root_.Run.PQ.KitFits D.base.plan.field D.C K chal)
    (wires : (PQ.wqS D.C K chal D.ds fun _ => true).OKG)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (an an' : An) (a₀ : tr an = first.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L2) (embE : SgX → Body L2)
    (walks : ArmWalks.Walks D
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
        rest isPL hpL cA tr hinj hlen htr (K + 1) back) g) embS embE
      (c₀ :: c₁ :: (cA an ++ cA an')) o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true)
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ D.a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 (K + 1) Q2)
    (embS2 : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE2 : E'.Sym → Body L2) (hemb : HEq embE2 embE)
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2) (fixB (PSXE D dec).up x) (fixW wq2 x2)
      (fixW (wqXK D dec K chal) x) embS2 embS embP2
      (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
      (fixP π2 x2) (fixP π x)) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS2 embP2 xin2 embE2 depthReq
      (c₀ :: c₁ :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
        rest isPL hpL cA tr hinj hlen htr (K + 1) back) g) = true := by
  obtain ⟨ρ, v, h⟩ := link_debtsK D d₁ cfg hcfg pd rest1 V K L2 pbF bd p0 p1 isP0 isP1 cfgL sh
    hp0 hp1 rest isPL hpL cA tr hinj hlen htr back g chal dec x F hDK hK0 hkit wires first further
    c₀ c₁ st o run pls A an an' a₀ a₁ π hπ hok hokb hn okx hD honce embS embE walks hdec
  exact lax_twoK h hE Q2 wq2 embS2 embP2 xin2 x2 π2 hx embE2 hemb hs depthReq

end OnBytes.K.Arm
