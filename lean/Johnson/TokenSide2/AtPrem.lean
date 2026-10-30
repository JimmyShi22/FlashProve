-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/AtPrem.lean: THE TOKEN SIDE's LETTERS AT THE LETTERS OF THE STATEMENT OF INDEX
PRIVACY (Johnson/WholeKey/Premises.lean): one definition, and what shows that the premises on these
letters which the lemmas on the token side ask follow from the statement's own premises.

Definitions and lemmas of one step of a proof. This file states no goal of the release. The token
programs are a device of that step and stand in no statement on the scheme.

  tokAt W p a c    the lengths, starts and fixed values of the token side's secret strings (TokLen,
                   Johnson/TokenSide/Whole.lean), read off the honest side's letters a, the
                   verifier's parameters p, the letters c of the laws on coins, and the wire's three
                   depths of request trees.
  fitsWin_of       a window with enough rounds that holds all trees of a wire (WithinWin) is wide
                   enough for a run (FitsWin, Johnson/TokenSide/SpecSame.lean).
  tokFit_tokAt     TokFit (Johnson/TokenSide2/Sess.lean) from the laws on all coins (CoinsFit) and
                   the wires' laws (OKA).
  lensOK_tokAt     LensOK (Johnson/TokenRules/Spec.lean) at the bits that stand in the written
                   error: the free bits of a leaf's salt; the shorter of a first salt and a digest.
So TokFit and LensOK can be met wherever the statement's premises can.

-/
import Johnson.TokenSide2.Sess
import Johnson.WholeKey.Premises
import Johnson.TokenRules.Spec

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The token side's letters at the letters of the statement.** -/
def tokAt (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params) (a : AtRecs lam L Bd aT aL)
    (c : CoinNums Bd) : TokLen lam (typedOracleCarrier L Bd aT aL) a.side.KT a.side.KL a.side.KB where
  preE := c.pre₀
  frE := c.ℓ
  T := ⟨p.sFS, c.ℓ, c.ℓr, a.rtail c.slotT, W.depthReqT, c.padT, c.slotT⟩
  Lk := ⟨p.sFS, c.ℓ, c.ℓr, a.rtail c.slotL, W.depthReqL, c.padL, c.slotL⟩
  B := ⟨p.sFS, c.ℓ, c.ℓr, a.rtail c.slotB, W.depthReq, c.padB, c.slotB⟩
  stT := fun κ => a.startT (a.rvT κ)
  stL := fun κ => a.startL (a.rvL κ)
  stB := fun κ => a.startB (a.rvB κ)

theorem fitsWin_of {K : ℕ} (nR nK nJ : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), WithinWin nK nJ s A W →
      i + s.length ≤ nR → FitsWin nR nK nJ s A W i
  | [], _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), i, h, hi => by
      have hi' : i + (s.length + 1) ≤ nR := hi
      exact ⟨by omega, h.1.2.1, h.1.1, h.1.2.2.2, h.1.2.2.1,
        fitsWin_of nR nK nJ s A W (i + 1) h.2 (by omega)⟩

/-- **The token side's letters fit the honest side's**, under the statement's own premises. -/
theorem tokFit_tokAt {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {cA : L.OutOfDomainAnswer → List (Dig lam)}
    {p : Params} {a : AtRecs lam L Bd aT aL} {c : CoinNums Bd} (hc : CoinsFit W p a c)
    (hw : OKA W cA) : TokFit W a.side (tokAt W p a c) where
  sl := hc.sl
  coT := hc.coT
  coL := hc.coL
  coB := hc.coB
  rsT := rfl
  rsL := rfl
  rsB := rfl
  stT := fun _ => rfl
  stL := fun _ => rfl
  stB := fun _ => rfl
  okT := hw.T
  okL := hw.Lk
  okB := hw.B
  fitT := fitsWin_of _ _ _ _ _ _ 0 hc.winT (by rw [Nat.zero_add]; exact hc.rounds.1)
  fitL := fitsWin_of _ _ _ _ _ _ 0 hc.winL (by rw [Nat.zero_add]; exact hc.rounds.2.1)
  fitB := fitsWin_of _ _ _ _ _ _ 0 hc.winB (by rw [Nat.zero_add]; exact hc.rounds.2.2)

/-- The rules' letters at the bits of the written error do not pass the lengths of these tokens. -/
theorem lensOK_tokAt (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (p : Params)
    (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) :
    OnBytes.TokenRules.LensOK c.ℓ (min p.sFS lam) (tokAt W p a c) where
  frE := le_rfl
  frT := le_rfl
  frL := le_rfl
  frB := le_rfl
  sT := min_le_left _ _
  sL := min_le_left _ _
  sB := min_le_left _ _
  dig := min_le_right _ _

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.tokFit_tokAt
#print axioms OnBytes.TokenSide.lensOK_tokAt
