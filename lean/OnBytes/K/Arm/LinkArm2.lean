-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LinkArm2.lean: the lax compiled verifier of an entry's link says yes over a second
interface L2, whose first query holds both tables' roots and answers in its list of digests, at the
typed oracle functions that the written encoding `ArmRead.implL2` reads out of an oracle g: from one
reading of the entry's chain at the hash over g.

What it is for: the same compiled verifier's entry arm (the two seeds' tests and the lax Link), run
at an object whose link is written at the shape at which the program's reader is tied; it is not yet
the object of the top's description. Here stands the lax Link alone.

The pieces. The chain over L2: OnBytes/TypedOracleCompiler/Slice/ArmRead.lean (`chain_arm`). The four fields that
name no interface: OnBytes/K/Arm/LaxAnyRead.lean (`debtsAny_read`). The join:
OnBytes/K/Arm/LaxAny.lean (`lax_any_fix`). The step to a protocol that the verifier cannot tell
from the skeleton: OnBytes/K/TwoCarrySame2.lean (`verifyB_same2`). A written object has its own
terms for the depth of the stored tables and for the number of blocks of an answer: at the sizes in
use they are equal to the description's D.a and D.K + 1 by theorems, not by unfolding, and both
stand in types. So the kind E' of external strings and the number K' of blocks of the second
protocol are letters, with equations. For proofs only; the program does not import this file.

What the letters pin. K' is the one number of blocks of all of L2's typed oracles, for Test, Link
and the session alike: it must be D.K + 1, the count of the entry's own description. bd asks that
the one type of leaves' bodies of L2 is, up to a bijection, the strings of bits. The letter `back`
is a one-to-one writing of all of L2's typed queries, so it asks that these are countable. pbF is no
free choice: `SameRun2` asks that "the way `wayE` of plain parts (OnBytes/TypedOracleCompiler/Run/RowsE2.lean), then
back along pbF" agrees with the second verifier's own way of writing plain parts. `walks` is shown
so far at cfg := D.base.cfg and V := `KeyLeaves.leavesAt` alone. The encoding itself holds two
digests, cfg and pd. At a configuration's own they are values of the very hash function at which the
verifier is run: so the encoding is fixed before a run, but not before the hash function.

Main theorems.
 `lax_two2`       under `LaxDebtsAny` at the skeleton: the lax verifier at Q2 over E', wq2 with K'
                  blocks, x2, π2 says yes at oracle functions g2 that agree with g, if E' and K' are
                  the skeleton's, `SameRun2` holds once both instances are fixed, the maps of
                  external symbols agree, and the two chains are handed the same in the field x.
 `link_debts`     from one reading: the record `LaxDebtsAny` at the skeleton, over L2, at the
                  written encoding. What is asked is listed there.
 `link_arm2`      so the yes at Q2, wq2, x2, π2, at the written encoding with K' blocks.

What is not claimed. That any of the premises holds at a file. That any object's Link has `SameRun2`
with the skeleton. The walks over L2 are a premise. The seeds' two tests: they are owed at this same
encoding. Nothing on soundness.


-/
import OnBytes.K.Arm.LaxAnyRead
import OnBytes.K.TwoCarrySame2
import OnBytes.TypedOracleCompiler.Slice.ArmRead

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsE2 TypedOracleCompiler.Run.EntryFb
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.EntryChain TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Compile.Batch.Carry
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf inFile)
open OnBytes.Slice (seedEntry)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX)

/-- **The yes at another protocol, on another term for the kind of external strings and with another
term for the number of blocks.** -/
theorem lax_two2 {I X' X : Type} {L : BatchProtocolWithLeafBody I X'} {D : XD} {dec : X → View → Bool}
    {g : Fam (typedOracleFamily 256 (D.K + 1) L)}
    {embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L}
    {embP : PlainPart (_root_.Run.Twin.up (SOf D.C D.ds)) (_root_.Run.Twin.allLo (SOf D.C D.ds)) →
      PlainPart (shapeOf L .link) (annOf L .link)}
    {xin : X → Option X'} {embE : SgX → Body L} {cms : List (Dig 256)} {x : X}
    {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE D dec).up}
    {ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))} {v : Bits}
    (h : LaxDebtsAny D dec g embS embP xin embE cms x o π ρ v) {E' : ExtSpec}
    (hE : E' = twoExternalStrings (2 ^ D.a) SgX) {K' : ℕ} (hK : K' = D.K + 1) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 K' Q2)
    (embS2 : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L .link) (annOf L .link))
    (xin2 : Y2 → Option X') (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = xin x)
    (embE2 : E'.Sym → Body L) (hemb : HEq embE2 embE)
    (hs : SameRun2 (L := L) (t := .link) (fixB Q2 x2) (fixB (PSXE D dec).up x) (fixW wq2 x2)
      (fixW (wqXE D dec) x) embS2 embS embP2 embP (fixP π2 x2) (fixP π x))
    (g2 : Fam (typedOracleFamily 256 K' L)) (hg : HEq g2 g) (depthReq : ℕ) :
    (verifyB (L := L) .link Q2 wq2 embS2 embP2 xin2 embE2 depthReq cms x2 π2).det g2 = true := by
  have h1 := verifyB_fix (L := L) .link Q2 wq2 embS2 embP2 xin2 embE2 depthReq cms x2 π2
  rw [← h1, hx, verifyB_same2 hE hK hs (fun _ => xin x) embE2 embE hemb depthReq cms () g2 g hg]
  exact lax_any_fix h depthReq

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (V : Leaves (Ls D d₁))
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
  (g : Fam (rom 256))

/-- **The record at the skeleton, over L2, from one reading.** Asked.
Of the description D: `FitsE D`; D.K + 1 below 2 ^ 48; the test `PQ.ok` at D's own part (`hok`), and
with the statement st put in (`hokb`); random bytes (`hn`); `work`; `okx`; all stored tables have
the depth D.a and items 0 or 1 (`hD`); each is opened at most once (`honce`).
Of the reading: `EntryRead` under D's own part with st put in (`A`); the typing's yes (`hπ`); the
decision's yes on the reader's view (`hdec`).
Of the typed answers: tr writes an, an' as the two tables' answers' triples (`a₀`, `a₁`).
Of the oracle functions over L2: the walks (`walks`). -/
theorem link_debts (back : StrCode (AllPts 256 (D.K + 1) L2))
    {X : Type} (dec : X → View → Bool) (x : X) (F : FitsE D) (hK0 : D.K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (an an' : An) (a₀ : tr an = first.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (work : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L2) (embE : SgX → Body L2)
    (walks : ArmWalks.Walks D
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr (D.K + 1) back) g) embS embE (c₀ :: c₁ :: (cA an ++ cA an')) o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true) :
    ∃ (ρ : Rho (_root_.Run.Twin.up (SOf D.C D.ds))) (v : Bits),
      LaxDebtsAny D dec
        (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr (D.K + 1) back) g) embS
        (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
        (fun _ => none) embE (c₀ :: c₁ :: (cA an ++ cA an')) x o π ρ v := by
  obtain ⟨seen, b, i, j, e⟩ := A.read
  obtain ⟨run', pl, tab, tx, h1, h2, -, -, hsalt, hroots, hpl, -⟩ := assembleS_some D dec hπ
  obtain rfl : run' = run := Option.some.inj (h1.symm.trans A.runIs)
  obtain rfl : pl = pls := Option.some.inj (h2.symm.trans A.plains)
  obtain ⟨ρ, v, hc, hd, hp⟩ := chain_arm D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1
    cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr g back dec (fun _ => none) x rfl F hK0
    first further c₀ c₁ _ o run' pl A an an' a₀ a₁ π [] hsalt
    (by rw [hroots, List.append_nil]) hpl
  exact ⟨ρ, v, debtsAny_read D dec _ embS _ (fun _ => none) embE _ hok st (oB (g ())) hokb hn seen b
    i o j e x π hπ ρ v hc hd hp work okx hD honce walks hdec⟩

/-- **The yes from one reading, at the written encoding with K' blocks**, at every depth of the
request tree. Asked beside what `link_debts` asks: E' and K' are the skeleton's (`hE`, `hK`); the
second chain is handed nothing in the field x (`hx`); the maps of external symbols agree (`hemb`);
`SameRun2` once both instances are fixed (`hs`). `walks` is asked at the encoding with D.K + 1
blocks and `back` carried along `hK`. -/
theorem link_arm2 {K' : ℕ} (hK : K' = D.K + 1) (back : StrCode (AllPts 256 K' L2))
    {X : Type} (dec : X → View → Bool) (x : X) (F : FitsE D) (hK0 : D.K + 1 < 2 ^ 48)
    (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (st : ByteArray)
    (o : _root_.Fmt.ChainOut) (run : ByteArray) (pls : Plains (PQ.uL D.C D.ds))
    (A : EntryRead D pd g first further c₀ c₁ ⟨{ D.base with statement := st }, D.stored⟩ o run
      pls)
    (an an' : An) (a₀ : tr an = first.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (π : OneProtocolProof 256 (PSXE D dec).up)
    (hπ : assembleS D dec o = some π) (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hokb : TypedOracleCompiler.Run.PQ.ok
      (inFile ({ D.base with statement := st } : _root_.Fmt.Spec)) = true)
    (hn : D.base.rand.isNone = false) (work : ∀ r ∈ D.ds, r.entry.work ≤ 64)
    (okx : PQ.okX D.ds D.a D.xs = true)
    (hD : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.item ≤ 1)
    (honce : (D.stored.flatten.map (·.item == 1)).Nodup)
    (embS : (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds))) →
      OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p → Body L2) (embE : SgX → Body L2)
    (walks : ArmWalks.Walks D
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr (D.K + 1) (hK ▸ back)) g) embS embE
      (c₀ :: c₁ :: (cA an ++ cA an')) o)
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true)
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ D.a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 K' Q2)
    (embS2 : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE2 : E'.Sym → Body L2) (hemb : HEq embE2 embE)
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2) (fixB (PSXE D dec).up x) (fixW wq2 x2)
      (fixW (wqXE D dec) x) embS2 embS embP2
      (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
      (fixP π2 x2) (fixP π x)) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS2 embP2 xin2 embE2 depthReq
      (c₀ :: c₁ :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr K' back) g) = true := by
  subst hK
  obtain ⟨ρ, v, h⟩ := link_debts D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh
    hp0 hp1 rest isPL hpL cA tr hinj hlen htr g back dec x F hK0 first further c₀ c₁ st o run
    pls A an an' a₀ a₁ π hπ hok hokb hn work okx hD honce embS embE walks hdec
  exact lax_two2 h hE rfl Q2 wq2 embS2 embP2 xin2 x2 π2 hx embE2 hemb hs _ HEq.rfl depthReq

end OnBytes.K.Arm
