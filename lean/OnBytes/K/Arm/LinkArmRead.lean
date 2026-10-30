-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LinkArmRead.lean: the lax compiled verifier of an entry's link says yes over a second
interface, at the written encoding `ArmRead.implL2` and the written bodies, from one reading: the
theorem `link_arm2` (OnBytes/K/Arm/LinkArm2.lean) with its premise on the walks paid.

`link_arm2` takes the walks over the second interface L2 as a premise. `walks_arm_read`
(OnBytes/K/Arm/ArmWalksL2.lean) has them from the strict reader's yes, which `EntryRead` holds, at
the page's digest `D.base.cfg`, the line's code of leaves for salts of nb bits, and the bodies
`embS2`, `embE2`. For proofs only; the program does not import this file.

Main name.
 `link_arm2_read`: `(verifyB .link Q2 wq2 embS' embP2 xin2 embE' depthReq
   (c₀ :: c₁ :: (cA an ++ cA an')) x2 π2).det (readBlocks (implL2 … K' back) g) = true`.

What is asked: what `link_arm2` asks but for the walks, at the bodies `embS2`, `embE2`; and, for the
walks: all stored tables have the plan's length of salts beside the depth `D.a` (`hsame`); the
statement's items hold the two tables' roots (`hit`); nb is eight times the plan's length of salts
(`hnb`).

What is not claimed. That any of it holds at a file. That any object's Link has `SameRun2` with the
skeleton at these bodies. Nothing on soundness.


-/
import OnBytes.K.Arm.LinkArm2
import OnBytes.K.Arm.ArmWalksL2

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

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (hcfg : D.base.cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (nb : ℕ)
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

/-- The yes over the second interface, with the walks paid from the reading. -/
theorem link_arm2_read {K' : ℕ} (hK : K' = D.K + 1) (back : StrCode (AllPts 256 K' L2))
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
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hnb : nb = 8 * D.base.plan.salt)
    (hit : ∀ t ∈ D.stored.flatten, _root_.Fmt.itemRoot st t.item =
      some (if t.item == 1 then further.root else first.root))
    (c : StrCode (ℕ × List UInt64))
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true)
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ D.a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 K' Q2)
    (embS' : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE' : E'.Sym → Body L2) (hemb : HEq embE' (embE2 D d₁ L2 bd c))
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2) (fixB (PSXE D dec).up x) (fixW wq2 x2)
      (fixW (wqXE D dec) x) embS' (embS2 D d₁ L2 bd hok) embP2
      (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
      (fixP π2 x2) (fixP π x)) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS' embP2 xin2 embE' depthReq
      (c₀ :: c₁ :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 D d₁ D.base.cfg hcfg pd rest1
        (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr K' back) g) = true := by
  obtain ⟨seen, b, i, j, e⟩ := A.read
  have hit' : ∀ t ∈ D.stored.flatten, _root_.Fmt.itemRoot st t.item =
      some (if t.item == 1 then digToBytes c₁ else digToBytes c₀) := by
    intro t ht
    rw [hit t ht, A.root₀, A.root₁]
  exact link_arm2 D d₁ D.base.cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) L2
    pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr g hK back dec x F hK0
    first further c₀ c₁ st o run pls A an an' a₀ a₁ π hπ hok hokb hn work okx hD honce
    (embS2 D d₁ L2 bd hok) (embE2 D d₁ L2 bd c)
    (walks_arm_read D d₁ hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA
      tr hinj hlen htr (D.K + 1) (hK ▸ back) g hok hsame hnb e c₀ c₁ hit' c (cA an ++ cA an'))
    hdec hE Q2 wq2 embS' embP2 xin2 x2 π2 hx embE' hemb hs depthReq

end OnBytes.K.Arm
