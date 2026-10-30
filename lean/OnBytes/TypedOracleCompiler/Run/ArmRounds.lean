-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ArmRounds.lean: the encoding over a second interface of
OnBytes/TypedOracleCompiler/Run/ArmDirect.lean, made from the codes of an entry's page
(OnBytes/TypedOracleCompiler/Run/EntryFb.lean); and what the page's code of the written rounds writes.

`implE_round` (OnBytes/TypedOracleCompiler/Run/EntryPage.lean) gives the string of the page's encoding at the
written round k. Inside its proof stands what the code of the written rounds writes there. Here that
fact is a lemma of its own (`e162_put`), in that proof's words: the encoding over the second
interface takes that code in, carried along the pair `laterM` (OnBytes/TypedOracleCompiler/Run/LinkAlongM.lean), and
no page over the first interface.

Main definition.
 `implAt`        the encoding over L2: the link's first query by a code f0 over L2; the later rounds
                 by `e162 P K`, the leaves by a code V of the entry's leaves, both carried.
Main theorems.
 `e162_put`      what the code of the written rounds writes at the written round k, at its own plain
                 part, at every block: under `implE_round`'s premises, the string of `implE_round`.
 `sel_round`     the pair reads ⟨k + 1, f2 none ρ, rt, pbF.symm (inE … k z)⟩ over L2 as
                 ⟨k + 1, f2 none ρ, rt, inE … k z⟩ over the page's interface.

Not claimed. That a verifier over L2 asks these queries alone. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Run.EntryPage
import OnBytes.TypedOracleCompiler.Run.ArmDirect
import OnBytes.TypedOracleCompiler.Run.LinkAlongM

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.ArmRounds
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.EntryFb TypedOracleCompiler.Run.EntryPage TypedOracleCompiler.Run.PageG TypedOracleCompiler.Run.Apart
open TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.PlainIn TypedOracleCompiler.Run.Chain162G
open TypedOracleCompiler.Run.KeyPageRounds (pRound_eq kind_lt ordOf)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open TypedOracleCompiler.Run.LinkAlong TypedOracleCompiler.Run.LinkAlongM TypedOracleCompiler.Run.ArmDirect
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} {D : XD}
  {early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd} {e : _root_.Fmt.Entry}
  (P : PinsE D early e) (K : ℕ) (V : Leaves (Le D early e))

/-- **What the code of the written rounds writes at the written round k.** The words of
`implE_round`'s proof. -/
theorem e162_put (hK : K < 2 ^ 48) (k : Fin D.ds.length) (hi : k.val + 1 < 2 ^ 64)
    (hw : (D.ds.get k).entry.work < 256) (ρ : Bits) (hρ : ρ.length = 256) (rt : List (Dig 256))
    (z : PlainD (D.ds.get k))
    (hok : PQ.okRound (D.ds.get k).entry.work (D.ds.get k).items rt z = true)
    (j : Fin (K + 1)) :
    (e162 P K).put (⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr
        (UInt8.ofNat ((blockTo (ordOf (D.ds.get k)) K j).val % 2)) 162
        P.l (k.val + 1) (bitsToBytes ρ)
        (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
            (GPlain.old (b := (D.ds.get k).entry.work) z) ++
          _root_.Fmt.tail (D.ds.get k).kind (D.ds.get k).entry.work
            (GPlain.nonce (b := (D.ds.get k).entry.work) z)
            ((blockTo (ordOf (D.ds.get k)) K j).val / 2)))) := by
  have hr := rdE_at D k
  have ek : kindE D (k.val + 1) = (D.ds.get k).kind.num := by unfold kindE; rw [hr]; rfl
  have ew : workE D (k.val + 1) = (D.ds.get k).entry.work := by unfold workE; rw [hr]; rfl
  have eo : ordE D (k.val + 1) = ordOf (D.ds.get k) := by unfold ordE; rw [hr]; rfl
  have ho : onE D.ds.length (k.val + 1) = true :=
    decide_eq_true ⟨Nat.le_add_left 1 _, k.isLt⟩
  have h := p162G_str (linkChain P) K hK (k.val + 1) ho P.hlt hi
    (by show kindE D (k.val + 1) < 256; rw [ek]; exact kind_lt _)
    (by show workE D (k.val + 1) < 256; rw [ew]; exact hw) ρ hρ rt (inE D early e k z) _ _
    ((rcE_at D early e k rt z).trans (pRound_eq _ _ rt z hok)) j
  have h' : (e162 P K).put (⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩, j) =
      some (bytesToBits (_root_.Fmt.oStr
        (UInt8.ofNat ((blockTo (ordE D (k.val + 1)) K j).val % 2)) 162 P.l (k.val + 1)
        (bitsToBytes ρ)
        (roundBytes (PQ.bytesL (rt.map digToBytes) (D.ds.get k).items
            (GPlain.old (b := (D.ds.get k).entry.work) z))
          (kindE D (k.val + 1)) (workE D (k.val + 1))
          ((blockTo (ordE D (k.val + 1)) K j).val / 2)
          (GPlain.nonce (b := (D.ds.get k).entry.work) z)))) := h
  rw [ek, ew, eo, KeyPageRounds.roundBytes_tail] at h'
  exact h'

variable {I2 X2 : Type} (L2 : BatchProtocolWithLeafBody I2 X2)
  (pbF : PlainPart (shapeOf L2 .link) (annOf L2 .link) ≃
    PlainPart (shapeOf (Le D early e) .link) (annOf (Le D early e) .link))
  (bd : L2.Bd ≃ (Le D early e).Bd)

/-- The pair reads the carried query of the written round k as the page's own. -/
theorem sel_round (k : Fin D.ds.length) (ρ : Bits) (rt : List (Dig 256))
    (z : PlainD (D.ds.get k)) :
    (laterM (Le D early e) L2 pbF).sel
        ⟨k.val + 1, .f2 none ρ, rt, pbF.symm (inE D early e k z)⟩ =
      some ⟨k.val + 1, .f2 none ρ, rt, inE D early e k z⟩ := by
  show some (⟨k.val + 1, .f2 none ρ, rt, pbF (pbF.symm (inE D early e k z))⟩ :
    FbIn 256 (Le D early e) .link) = _
  rw [Equiv.apply_symm_apply]

variable (p0 p1 : PlainPart (shapeOf L2 .test) (annOf L2 .test))
  (isP0 isP1 : PlainPart (shapeOf L2 .test) (annOf L2 .test) → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ p, isP0 p = true ↔ p = p0) (hp1 : ∀ p, isP1 p = true ↔ p = p1) (rest : ByteArray)
  (f0 : PCode (FbIn 256 L2 .link)) (h0 : ∀ q s, f0.put q = some s → Is160 P.l s)
  (back : StrCode (AllPts 256 K L2))

/-- The encoding over L2, made from the page's codes: the first query by f0; the later rounds by the
page's code of the written rounds, and the leaves by the page's code of leaves, both carried. -/
abbrev implAt : OracleCoding (typedOracleFamily 256 K L2) 256 :=
  implArmD L2 p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K P.l P.hlt P.hR f0 h0
    (laterM (Le D early e) L2 pbF) (e162 P K) (e162_is P K) (leafM (Le D early e) L2 bd) V P.cfg
    P.hcfg back

end TypedOracleCompiler.Run.ArmRounds
