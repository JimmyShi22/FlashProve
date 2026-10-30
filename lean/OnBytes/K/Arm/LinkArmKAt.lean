-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LinkArmKAt.lean: the lax compiled verifier of an entry's link says yes over a second
interface, at the written encoding with K + 1 blocks and the written bodies, for every K that is at
least the description's own number of blocks: with the walks paid from the reading; and at a ground,
from the record `ArmFacts`.

As OnBytes/K/Arm/LinkArmRead.lean and LinkArmAt.lean, over `link_armK` (OnBytes/K/Arm/LinkArmK.lean)
in the place of `link_arm2`. `walks_arm_read` (OnBytes/K/Arm/ArmWalksL2.lean) holds at every number
of blocks. For proofs only; the program does not import this file.

Main theorems.
 `link_armK_read`   `link_armK` with its premise on the walks paid, at the page's digest
                    `D.base.cfg`, the line's code of leaves for salts of nb bits and the bodies
                    `embS2`, `embE2`.
 `link_armK_at`     that under `ArmFacts`, at `entryXD G c`, the statement on the two tables, the
                    realised oracle `oBits`, the decision and the typed instance of a run.
 `link_armK_atP`    that at the library's way `chalP` of making a message of K blocks: `hkit` and
                    `wires` are shown.

What is left in `link_armK_atP`. Of K: `D.K ≤ K`, K + 1 below 2 ^ 48. Of the written encoding: nb is
eight times the plan's length of salts. Of the typed answers: tr writes an, an' as the two tables'
answers' triples; cA and tr are one to one, cA with one number of digests. Of the second protocol:
its kind of external strings is the skeleton's; its chain is handed nothing in the field x; its map
of external symbols is `embE2`; `SameRun2` with the skeleton wired at K, at `embS2`.

What is not claimed. That any object's Link meets what is asked of the second protocol. Nothing on
the seeds' two tests. Nothing on soundness.


-/
import OnBytes.K.Arm.LinkArmK
import OnBytes.K.Arm.ArmWalksL2
import OnBytes.K.Arm.ArmFacts

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
open OnBytes.Tie (EntryGround linkAtCfg)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX)

section
variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (hcfg : D.base.cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray) (nb : ℕ) (K : ℕ)
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

/-- The yes over the second interface at K + 1 blocks, with the walks paid from the reading. -/
theorem link_armK_read {X : Type} (dec : X → View → Bool) (x : X) (F : FitsE D) (hDK : D.K ≤ K)
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
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hnb : nb = 8 * D.base.plan.salt)
    (hit : ∀ t ∈ D.stored.flatten, _root_.Fmt.itemRoot st t.item =
      some (if t.item == 1 then further.root else first.root))
    (c : StrCode (ℕ × List UInt64))
    (hdec : dec x (_root_.Fmt.viewX ⟨{ D.base with statement := st }, D.stored⟩ o) = true)
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ D.a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 (K + 1) Q2)
    (embS' : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE' : E'.Sym → Body L2) (hemb : HEq embE' (embE2 D d₁ L2 bd c))
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2) (fixB (PSXE D dec).up x) (fixW wq2 x2)
      (fixW (wqXK D dec K chal) x) embS' (embS2 D d₁ L2 bd hok) embP2
      (fun z => pbF.symm (wayE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) z))
      (fixP π2 x2) (fixP π x)) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS' embP2 xin2 embE' depthReq
      (c₀ :: c₁ :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 D d₁ D.base.cfg hcfg pd rest1
        (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
        isPL hpL cA tr hinj hlen htr (K + 1) back) g) = true := by
  obtain ⟨seen, b, i, j, e⟩ := A.read
  have hit' : ∀ t ∈ D.stored.flatten, _root_.Fmt.itemRoot st t.item =
      some (if t.item == 1 then digToBytes c₁ else digToBytes c₀) := by
    intro t ht
    rw [hit t ht, A.root₀, A.root₁]
  exact link_armK D d₁ D.base.cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) K L2
    pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr back g chal dec x F hDK
    hK0 hkit wires first further c₀ c₁ st o run pls A an an' a₀ a₁ π hπ hok hokb hn okx hD honce
    (embS2 D d₁ L2 bd hok) (embE2 D d₁ L2 bd c)
    (walks_arm_read D d₁ hcfg pd rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA
      tr hinj hlen htr (K + 1) back g hok hsame hnb e c₀ c₁ hit' c (cA an ++ cA an'))
    hdec hE Q2 wq2 embS' embP2 xin2 x2 π2 hx embE' hemb hs depthReq

end

variable (G : EntryGround) (c : ByteArray)
  (d₁ : Sd1 G.q.link.table.cubeBits G.q.link.table.answers) (rest1 : ByteArray) (nb : ℕ)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls (entryXD G c) d₁) .link) (annOf (Ls (entryXD G c) d₁) .link))
  (bd : L2.Bd ≃ (Ls (entryXD G c) d₁).Bd)
  (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
      (seedEntry G.q.link.table.cubeBits G.q.link.table.answers)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr)
  (K : ℕ) (back : StrCode (AllPts 256 (K + 1) L2))

/-- The same at a ground, under `ArmFacts`. -/
theorem link_armK_at (chal : ∀ e k, (Fin K → Dig 256) → (entryXD G c).C.Ch e k)
    {table further : Params.TableName} {l0 l1 : List (List E × E)}
    {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up}
    (A : ArmFacts G c table further l0 l1 o π) (hDK : (entryXD G c).K ≤ K) (hK0 : K + 1 < 2 ^ 48)
    (hkit : _root_.Run.PQ.KitFits (entryXD G c).base.plan.field (entryXD G c).C K chal)
    (wires : (PQ.wqS (entryXD G c).C K chal (entryXD G c).ds fun _ => true).OKG)
    (hnb : nb = 8 * (entryXD G c).base.plan.salt)
    (an an' : An) (a₀ : tr an = table.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (cc : StrCode (ℕ × List UInt64))
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ (entryXD G c).a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 (K + 1) Q2)
    (embS' : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE' : E'.Sym → Body L2) (hemb : HEq embE' (embE2 (entryXD G c) d₁ L2 bd cc))
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2)
      (fixB (PSXE (entryXD G c) (decAt G c)).up (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))
      (fixW wq2 x2)
      (fixW (wqXK (entryXD G c) (decAt G c) K chal) (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))
      embS' (embS2 (entryXD G c) d₁ L2 bd A.ground.hok) embP2
      (fun z => pbF.symm (wayE (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
        (seedEntry G.q.link.table.cubeBits G.q.link.table.answers) z))
      (fixP π2 x2) (fixP π (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS' embP2 xin2 embE' depthReq
      (bytesToDig table.root :: bytesToDig further.root :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 (entryXD G c) d₁ (entryXD G c).base.cfg A.ground.hcfg
        (EntryRunTop.pdOf (entryXD G c)) rest1
        (KeyLeaves.leavesAt (L0 (entryXD G c) d₁) nb (entryXD G c).base.cfg) L2 pbF bd p0 p1 isP0
        isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr (K + 1) back) oBits) = true := by
  obtain ⟨run, pls, R⟩ := A.read
  exact link_armK_read (entryXD G c) d₁ A.ground.hcfg (EntryRunTop.pdOf (entryXD G c)) rest1 nb K L2
    pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr back oBits chal
    (decAt G c) (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩) A.ground.fits hDK hK0 hkit wires
    table further _ _ (Params.Link.statement table further) o run pls R an an' a₀ a₁ π A.typed
    A.ground.hok A.ground.hokb A.ground.hn A.ground.okx A.ground.hD A.ground.honce A.ground.hsame
    hnb A.ground.hit cc A.dec hE Q2 wq2 embS' embP2 xin2 x2 π2 hx embE' hemb hs depthReq

/-- The same at the library's way of making a message of K blocks. -/
theorem link_armK_atP {table further : Params.TableName} {l0 l1 : List (List E × E)}
    {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up}
    (A : ArmFacts G c table further l0 l1 o π) (hDK : (entryXD G c).K ≤ K) (hK0 : K + 1 < 2 ^ 48)
    (hnb : nb = 8 * (entryXD G c).base.plan.salt)
    (an an' : An) (a₀ : tr an = table.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (cc : StrCode (ℕ × List UInt64))
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ (entryXD G c).a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 (K + 1) Q2)
    (embS' : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE' : E'.Sym → Body L2) (hemb : HEq embE' (embE2 (entryXD G c) d₁ L2 bd cc))
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2)
      (fixB (PSXE (entryXD G c) (decAt G c)).up (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))
      (fixW wq2 x2)
      (fixW (wqXK (entryXD G c) (decAt G c) K (chalP (entryXD G c).base.plan.field K))
        (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))
      embS' (embS2 (entryXD G c) d₁ L2 bd A.ground.hok) embP2
      (fun z => pbF.symm (wayE (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
        (seedEntry G.q.link.table.cubeBits G.q.link.table.answers) z))
      (fixP π2 x2) (fixP π (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS' embP2 xin2 embE' depthReq
      (bytesToDig table.root :: bytesToDig further.root :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 (entryXD G c) d₁ (entryXD G c).base.cfg A.ground.hcfg
        (EntryRunTop.pdOf (entryXD G c)) rest1
        (KeyLeaves.leavesAt (L0 (entryXD G c) d₁) nb (entryXD G c).base.cfg) L2 pbF bd p0 p1 isP0
        isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr (K + 1) back) oBits) = true :=
  link_armK_at G c d₁ rest1 nb L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj
    hlen htr K back (chalP (entryXD G c).base.plan.field K) A hDK hK0
    (_root_.Run.PQ.kit_pull (entryXD G c).base.plan.field K)
    (wqS_okgP (entryXD G c) K hDK A.ground.work) hnb an an' a₀ a₁ cc hE Q2 wq2 embS' embP2 xin2 x2
    π2 hx embE' hemb hs depthReq

end OnBytes.K.Arm
