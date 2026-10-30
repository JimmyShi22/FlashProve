-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ArmLinkCode.lean: the code of the link's chain queries inside the encoding
`ArmRead.implL2`, under a name of its own, with what it writes.

`implL2` (OnBytes/TypedOracleCompiler/Slice/ArmRead.lean) is an encoding of typed oracles over a second interface L2
into one hash function. It is made of a code of the seeds' two queries, a code of the link's chain
queries, a code of leaves and a total code behind an escape (OnBytes/TypedOracleCompiler/Run/SeedPage.lean:
`implS`). The code of the link's chain queries stands in it as a term. Here that term has a name,
and the strings that it writes are said of the code itself, not of the encoding. For proofs only;
the program does not import this file.

Main definition.
 `linkAt`         a `SeedPage.LinkCode L2 K`: `ArmDirect.linkD` at the label of a link's chain; the
                 first query by `LinkFirstAns.lf0`; the later queries by the code `e162` of the
                 written rounds of an entry's page at the pins `pinsE`, carried along the pair
                 `LinkAlongM.laterM` at a one-to-one correspondence pbF of plain parts.
Main theorems.
 `implL2_linkAt`  `implL2` is `implS` at `linkAt`, by unfolding.
 `linkAt_first`   at the first query (round 0: both roots, then both tables' typed answers as
                 digests; no instance; the fixed plain part of the round in front, carried) and the
                 LAST block it writes the bits of the format's string of the call 160 under the
                 link's label, on the program's statement of a link's chain.
 `linkAt_round`   at the query of the written round k (round k + 1; the round's own plain part,
                 carried) and EVERY block j it writes the bits of the format's string of the call
                 162 of that block.

Not claimed. That the code writes at any other query, or at another block of the first query. That a
verifier over L2 asks these queries alone. That there is a pbF at any interface. Nothing on the
seeds' queries, on leaves or on vertices. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Slice.ArmRead

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice.ArmLinkCode
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.SeedPage TypedOracleCompiler.Run.LinkOf
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Slice.EntryFill
open TypedOracleCompiler.Run.PlainIn TypedOracleCompiler.Run.SeamAt
open TypedOracleCompiler.Run.KeyPageRounds (ordOf)
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM TypedOracleCompiler.Run.LinkFirstAns
open TypedOracleCompiler.Run.ArmRounds TypedOracleCompiler.Run.ArmDirect TypedOracleCompiler.Slice.ArmRead
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open OnBytes.Slice (seedEntry)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {lg s : ℕ} (D : XD) (d₁ : Sd1 lg s) (cfg : ByteArray) (hcfg : cfg.size = 32)
  (pd : Dig 256) (rest1 : ByteArray)
  {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Ls D d₁) .link) (annOf (Ls D d₁) .link))
  (isPL : PlainPart (shapeOf L2 .link) (annOf L2 .link) → Bool)
  (hpL : ∀ p, isPL p = true ↔
    p = pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s)))
  {An : Type} (cA : An → List (Dig 256)) (tr : An → List T3) (hinj : Function.Injective cA)
  (hlen : ∀ a a', (cA a).length = (cA a').length) (htr : Function.Injective tr) (K : ℕ)

/-- **The code of the link's chain queries over L2**, with K + 1 blocks in an answer. -/
def linkAt : LinkCode L2 K :=
  linkD L2 K (pinsE D d₁ cfg hcfg pd rest1).l (pinsE D d₁ cfg hcfg pd rest1).hlt
    (pinsE D d₁ cfg hcfg pd rest1).hR
    (lf0 L2 .link (pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))) isPL pd
      cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
    (lf0_is L2 .link _ isPL pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink)
    (laterM (Ls D d₁) L2 pbF) (e162 (pinsE D d₁ cfg hcfg pd rest1) K)
    (e162_is (pinsE D d₁ cfg hcfg pd rest1) K)

/-- **`implL2` is `implS` at `linkAt`.** -/
theorem implL2_linkAt (V : Leaves (Ls D d₁)) (bd : L2.Bd ≃ (Ls D d₁).Bd)
    (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
    (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256))
    (sh : Bits) (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1)
    (rest : ByteArray) (back : StrCode (AllPts 256 K L2)) :
    implL2 D d₁ cfg hcfg pd rest1 V L2 pbF bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest isPL hpL cA tr
        hinj hlen htr K back =
      implS L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
        (linkAt D d₁ cfg hcfg pd rest1 L2 pbF isPL hpL cA tr hinj hlen htr K)
        (leavesAlong (leafM (Ls D d₁) L2 bd) V) cfg hcfg back := rfl

/-- **What it writes at the first query, at the last block.** -/
theorem linkAt_first (first further : OnBytes.Params.TableName) (c₀ c₁ : Dig 256) (an an' : An)
    (salt : List Bool) (r₀ : first.root = digToBytes c₀) (r₁ : further.root = digToBytes c₁)
    (a₀ : tr an = first.answers.map OnBytes.E.triple) (a₁ : tr an' = further.answers.map OnBytes.E.triple)
    (l₀ : first.answers.length < 2 ^ 32) (l₁ : further.answers.length < 2 ^ 32)
    (hl : salt = [] ∨ salt.length = 256) :
    (linkAt D d₁ cfg hcfg pd rest1 L2 pbF isPL hpL cA tr hinj hlen htr K).pL.put
        (⟨0, .f1 (c₀ :: c₁ :: (cA an ++ cA an')) none salt, [],
          pbF.symm (p0E D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s))⟩,
          Fin.last K) =
      some (bytesToBits (_root_.Fmt.oStr 0 160 0 OnBytes.Params.labelLink _root_.Fmt.zero32
        (_root_.Fmt.firstBytes (digToBytes pd) (OnBytes.Params.Link.statement first further)
          ByteArray.empty (runOf salt)))) := by
  unfold linkAt linkD
  exact linkOf_first _ _ _ _ _ _ _ _ rfl _
    (lf0_link L2 .link _ isPL pd cA tr hpL hinj hlen htr OnBytes.Params.labelLink first further c₀
      c₁ an an' salt r₀ r₁ a₀ a₁ l₀ l₁ hl)

/-- **What it writes at the written round k, at every block.** -/
theorem linkAt_round (hK : K < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true)
    (j : Fin (K + 1)) :
    (linkAt D d₁ cfg hcfg pd rest1 L2 pbF isPL hpL cA tr hinj hlen htr K).pL.put
        (⟨k.val + 1, .f2 none ρ, rt,
          pbF.symm (inE D (earlyTwo (A := List T3 × List T3) d₁) (seedEntry lg s) k z)⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr
        (UInt8.ofNat ((blockTo (ordOf (D.ds.get k)) K j).val % 2)) 162
        OnBytes.Params.labelLink (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
            (GPlain.old (b := (D.ds.get k).entry.work) z) ++
          _root_.Fmt.tail (D.ds.get k).kind (D.ds.get k).entry.work
            (GPlain.nonce (b := (D.ds.get k).entry.work) z)
            ((blockTo (ordOf (D.ds.get k)) K j).val / 2)))) := by
  unfold linkAt linkD
  exact (linkOf_round _ _ _ _ _ _ _ _ (Nat.succ_ne_zero _) j).trans
    ((roundsAlong_put _ _ _ _ (sel_round L2 pbF k ρ rt z) j).trans
      (e162_put (pinsE D d₁ cfg hcfg pd rest1) K hK k hi hw ρ hρ rt z hok j))

end TypedOracleCompiler.Slice.ArmLinkCode
