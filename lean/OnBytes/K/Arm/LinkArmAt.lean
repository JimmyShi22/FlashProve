-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/LinkArmAt.lean: the lax compiled verifier of an entry's link says yes over a second
interface, at the written encoding and the written bodies, at a ground: from the record
`ArmFacts`.

`link_arm2_read` (OnBytes/K/Arm/LinkArmRead.lean) asks, of the file and of the description, what
`ArmFacts` (OnBytes/K/Arm/ArmFacts.lean) holds. `armFacts_of`, `armFacts_full` and
`armFacts_small` there have that record from the program's yes, at a ground whose lines the
parameter file says. Here `link_arm2_read` is said under the record: at the description
`entryXD G c`, the statement on the two tables, the realised oracle `oBits`, the decision of a run
and the typed instance of a run. For proofs only; the program does not import this file.

Main name.
 `link_arm_at`: under `ArmFacts`: the yes at any Q2, wq2, x2, π2 that have `SameRun2` with the
   skeleton once both instances are fixed.

What is asked beside `ArmFacts`. Of the written encoding: nb is eight times the plan's length of
salts. Of the typed answers: tr writes an, an' as the two tables' answers' triples; cA and tr are
one to one, cA with one number of digests. Of the second protocol: its kind of external strings and
its number of blocks are the skeleton's; its chain is handed nothing in the field x; its map of
external symbols is `embE2`; `SameRun2` at `embS2`. Of the second interface: the letter `back`, a
one-to-one writing of ALL its typed queries with a parser: the theorem speaks only where there is
one. The letter cc in `embE2` is no free choice at an object whose map of external symbols is
`(bodyS a salt).embE`: the two meet at cc := `Strings.cX` and bd the identity alone
(`embE_sib`, OnBytes/K/Arm/SibMaps.lean).

Johnson/Top/ArmLinkAt.lean (`link_field`) does not go by this theorem: it takes `ArmFacts` from here
and goes by `link_arm2_read`.

What is not claimed. That any object's Link meets what is asked of the second protocol. That a
served statement's parameter file says a ground's lines. Nothing on the seeds' two tests. Nothing on
soundness.


-/
import OnBytes.K.Arm.LinkArmRead
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
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.Slice (seedEntry)
open OnBytes.Tie (EntryGround linkAtCfg)
open OnBytes.K (fixB fixW fixP)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (View SgX)

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

/-- The yes over the second interface, at a ground, under `ArmFacts`. -/
theorem link_arm_at {table further : Params.TableName} {l0 l1 : List (List E × E)}
    {o : _root_.Fmt.ChainOut} {π : OneProtocolProof 256 (PSXE (entryXD G c) (decAt G c)).up}
    (A : ArmFacts G c table further l0 l1 o π) {K' : ℕ} (hK : K' = (entryXD G c).K + 1)
    (back : StrCode (AllPts 256 K' L2)) (hnb : nb = 8 * (entryXD G c).base.plan.salt)
    (an an' : An) (a₀ : tr an = table.answers.map E.triple)
    (a₁ : tr an' = further.answers.map E.triple) (cc : StrCode (ℕ × List UInt64))
    {E' : ExtSpec} (hE : E' = twoExternalStrings (2 ^ (entryXD G c).a) SgX) {Y2 : Type}
    (Q2 : BatchInteractiveOracleProof Y2 E') (wq2 : ProtocolQueryLayout 256 K' Q2)
    (embS' : (p : OPos Q2.loc.shape) → OSym Q2.loc.shape p → Body L2)
    (embP2 : PlainPart Q2.loc.shape Q2.ann → PlainPart (shapeOf L2 .link) (annOf L2 .link))
    (xin2 : Y2 → Option X2) (x2 : Y2) (π2 : OneProtocolProof 256 Q2) (hx : xin2 x2 = none)
    (embE' : E'.Sym → Body L2) (hemb : HEq embE' (embE2 (entryXD G c) d₁ L2 bd cc))
    (hs : SameRun2 (L := L2) (t := .link) (fixB Q2 x2)
      (fixB (PSXE (entryXD G c) (decAt G c)).up (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))
      (fixW wq2 x2)
      (fixW (wqXE (entryXD G c) (decAt G c)) (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩)) embS'
      (embS2 (entryXD G c) d₁ L2 bd A.ground.hok) embP2
      (fun z => pbF.symm (wayE (entryXD G c) (earlyTwo (A := List T3 × List T3) d₁)
        (seedEntry G.q.link.table.cubeBits G.q.link.table.answers) z))
      (fixP π2 x2) (fixP π (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩))) (depthReq : ℕ) :
    (verifyB (L := L2) .link Q2 wq2 embS' embP2 xin2 embE' depthReq
      (bytesToDig table.root :: bytesToDig further.root :: (cA an ++ cA an')) x2 π2).det
      (readBlocks (implL2 (entryXD G c) d₁ (entryXD G c).base.cfg A.ground.hcfg
        (EntryRunTop.pdOf (entryXD G c)) rest1
        (KeyLeaves.leavesAt (L0 (entryXD G c) d₁) nb (entryXD G c).base.cfg) L2 pbF bd p0 p1 isP0
        isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr K' back) oBits) = true := by
  obtain ⟨run, pls, R⟩ := A.read
  exact link_arm2_read (entryXD G c) d₁ A.ground.hcfg (EntryRunTop.pdOf (entryXD G c)) rest1 nb L2
    pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr oBits hK back
    (decAt G c)
    (xOfAskedC _ _ ⟨table, further, l0, l1, o⟩) A.ground.fits A.ground.hK table further _ _
    (Params.Link.statement table further) o run pls R an an' a₀ a₁ π A.typed A.ground.hok
    A.ground.hokb A.ground.hn A.ground.work A.ground.okx A.ground.hD A.ground.honce A.ground.hsame
    hnb A.ground.hit cc A.dec hE Q2 wq2 embS' embP2 xin2 x2 π2 hx embE' hemb hs depthReq

end OnBytes.K.Arm
