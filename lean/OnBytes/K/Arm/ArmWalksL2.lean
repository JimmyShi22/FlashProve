-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/ArmWalksL2.lean: what the lax verifier's clause on the walks asks at an entry's typed
string, at the typed oracle functions that the written encoding `ArmRead.implL2` reads out of an
oracle g, with written bodies over the second interface: from one yes of the strict reader.

`link_arm2` (OnBytes/K/Arm/LinkArm2.lean) takes the walks over the second interface L2 as a
premise, at the family `readBlocks (implL2 …) g`. `walks_armD_read`
(OnBytes/K/Arm/ArmWalksRead.lean) has them at `famG (pageArmD …) g`, for letters of that page. Here
the letters are `implL2`'s own, where the two families are one by unfolding, and the bodies are
those of OnBytes/TypedOracleCompiler/Run/ArmLeafId.lean. For proofs only; the program does not import this file.

Main names.
 `embS2`, `embE2`: the bodies over L2: what the correspondence bd of bodies reads as the entry's own
   body of a symbol of the chain's own trees (`ownES D hok`), and as the line's body of a stored
   symbol.
 `fam_L2`: at the page's digest `D.base.cfg`, the line's code of leaves for salts of nb bits and
   any number Kb of blocks: `famG (pageArmD …) g = readBlocks (implL2 …) g`.
 `walks_arm_read`: `Walks D (readBlocks (implL2 …) g) (embS2 …) (embE2 …) (c₀ :: c₁ :: more) o`.

What is asked. The strict reader's yes at the hash made of g, under D's description with a statement
st; the sibling's limits at D's own part; all stored tables have the depth `D.a` and the plan's
length of salts; the statement's items hold the two roots' bytes; nb is eight times the plan's
length of salts.

What is not claimed. That there is a correspondence bd or pbF at any interface. That a compiled
verifier's wire over L2 writes these bodies. Nothing on the chain's queries. Nothing on soundness.


-/
import OnBytes.K.Arm.ArmWalksRead
import OnBytes.TypedOracleCompiler.Run.ArmLeafId
import OnBytes.TypedOracleCompiler.Slice.ArmRead

set_option autoImplicit false

noncomputable section

namespace OnBytes.K.Arm
open OnBytes.K.Left
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.RowsG TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage
open TypedOracleCompiler.Slice.EntryFill TypedOracleCompiler.Slice.ArmRead TypedOracleCompiler.Slice.ArmWalks
open TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Run.ArmRounds TypedOracleCompiler.Run.ArmLeafId
open TypedOracleCompiler.Run.LinkAlongM TypedOracleCompiler.Run.LinkFirstAns
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD SOf)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run
open _root_.Run.PQ (SgX)

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
  (Kb : ℕ) (back : StrCode (AllPts 256 Kb L2)) (g : Fam (rom 256))

/-- The body over L2 of a symbol of the chain's own trees. -/
def embS2 (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (p : OPos (_root_.Run.Twin.up (SOf D.C D.ds)))
    (a : OSym (_root_.Run.Twin.up (SOf D.C D.ds)) p) : Body L2 :=
  bd.symm ((ownES D hok).emb p a)

/-- The body over L2 of a stored symbol. -/
def embE2 (c : StrCode (ℕ × List UInt64)) : SgX → Body L2 :=
  stoAt (L0 D d₁) L2 bd D.a D.base.plan.salt c

/-- The two families are one. -/
theorem fam_L2 :
    famG (pageArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Kb OnBytes.Params.labelLink
      (pinsE D d₁ D.base.cfg hcfg pd rest1).hlt (pinsE D d₁ D.base.cfg hcfg pd rest1).hR
      (lf0 L2 .link (pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))) isPL
        pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
      (lf0_is L2 .link _ isPL pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
      (laterM (Ls D d₁) L2 pbF) (e162 (pinsE D d₁ D.base.cfg hcfg pd rest1) Kb)
      (e162_is (pinsE D d₁ D.base.cfg hcfg pd rest1) Kb) (leafM (Ls D d₁) L2 bd)
      (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) D.base.cfg hcfg back) g =
    readBlocks (implL2 D d₁ D.base.cfg hcfg pd rest1 (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) L2
      pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr hinj hlen htr Kb back) g := rfl

/-- The clause on the walks at `implL2`'s family and the written bodies, from one yes of the strict
reader. -/
theorem walks_arm_read (hok : TypedOracleCompiler.Run.PQ.ok D.base = true)
    (hsame : ∀ t ∈ D.stored.flatten, t.sh.a = D.a ∧ t.salt = D.base.plan.salt)
    (hn : nb = 8 * D.base.plan.salt) {st : ByteArray} {seen : _root_.Fmt.Seen} {b : ByteArray}
    {i : ℕ} {o : _root_.Fmt.ChainOut} {j : ℕ}
    (e : _root_.Fmt.readChainX (m := Id) (hOfG g) (specOf D st) seen b i = some (o, j))
    (c₀ c₁ : Dig 256)
    (hit : ∀ t ∈ D.stored.flatten, _root_.Fmt.itemRoot st t.item =
      some (if t.item == 1 then digToBytes c₁ else digToBytes c₀))
    (c : StrCode (ℕ × List UInt64)) (more : List (Dig 256)) :
    Walks D (readBlocks (implL2 D d₁ D.base.cfg hcfg pd rest1
      (KeyLeaves.leavesAt (L0 D d₁) nb D.base.cfg) L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
      isPL hpL cA tr hinj hlen htr Kb back) g) (embS2 D d₁ L2 bd hok) (embE2 D d₁ L2 bd c)
      (c₀ :: c₁ :: more) o := by
  have W := walks_armD_read (L0 D d₁) L2 D p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest
    OnBytes.Params.labelLink (pinsE D d₁ D.base.cfg hcfg pd rest1).hlt
    (pinsE D d₁ D.base.cfg hcfg pd rest1).hR
    (lf0 L2 .link (pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))) isPL
      pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
    (lf0_is L2 .link _ isPL pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink) Kb
    (laterM (Ls D d₁) L2 pbF) (e162 (pinsE D d₁ D.base.cfg hcfg pd rest1) Kb)
    (e162_is (pinsE D d₁ D.base.cfg hcfg pd rest1) Kb) (leafM (Ls D d₁) L2 bd) nb hcfg back
    g hok hsame hn e (digToBytes c₀) (digToBytes c₁) hit
    (embS := embS2 D d₁ L2 bd hok) (e2 := ownAt (L0 D d₁) L2 bd (ownEnc D.base.plan.salt))
    (fun q a => ali_emb (fun z : List Bool => bd.symm z) (ownEnc D.base.plan.salt) D.C D.ds
      (ownES D hok).emb (own_emb D hok) q a)
    (embE2 := embE2 D d₁ L2 bd c) c
    (fun s x sym z => ali_selO (L0 D d₁) L2 bd (ownEnc D.base.plan.salt) s x sym z)
    (fun y z => ali_selS (L0 D d₁) L2 bd D.a D.base.plan.salt c y z) more
  rw [_root_.Run.TieTree.bytes_dig, _root_.Run.TieTree.bytes_dig] at W
  exact W

end OnBytes.K.Arm
