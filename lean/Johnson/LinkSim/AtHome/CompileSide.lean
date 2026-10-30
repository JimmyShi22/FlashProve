-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtHome/CompileSide.lean: at parameters that satisfy LaidLink, if the fill string and
the slot fit, the randomness given to a hashed run of the link has the lengths that the verifier's
strict format asks.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has. Two lemmas on the lengths of bit strings. The theorem on completeness,
complete_argW (Johnson/WholeKey/Complete.lean), has a premise SideFit with four conditions on
lengths. This file proves the one for the link proof, SideFit.coL.

The setting. The randomness of a hashed run is one value of Coins (OnBytes/Prover/Defs.lean): a
first salt, a salt for each Merkle leaf, a slot (a leaf index in the request tree), that leaf's path
of sibling digests, and more. Only part of it is sampled. The public map dress
(Johnson/WholeKey/Defs.lean) fills in the rest: it puts a public prefix in front of each leaf salt's
sampled bits, puts a constant string fill in place of the sampled bits outside the window
nR, nK, nJ, and appends a public word rtail behind the string rsalt. Coins.Fit
(OnBytes/Prover/Inv.lean) lists the four lengths that the verifier's strict format asks: the first
salt has sFS bits; every leaf salt, inside the window or not, has sMT bits; the slot is below
2 ^ depth; and the path has depth digests. It has no condition on rsalt.

  fit_dress_coinsPre   for all parameters: if the length of every public prefix plus ℓ is sMT, if
      fill has exactly ℓ bits, and if the slot is below 2 ^ dq, then every member of coinsPre
      (Johnson/WholeKey/CoinLaws.lean), after dress, meets Coins.Fit at sMT, sFS and dq. It needs no
      condition on rtail or ℓr (Coins.Fit has none on rsalt), on the window's bounds, or on E
      listing each value once. coinsPre's own constant fill' is never read, since dress puts its own
      string outside the window.
  sideFit_coL   for all protocol structures L, compilation data W and parameters p, a, c, v₀: if
      LaidLink W p a c v₀ holds (Johnson/LinkSim/AtHome/CompileSpec.lean: the link's components of a
      are set as the substitution sets them), if a.fill has exactly c.ℓ bits, and if
      c.slotL < 2 ^ W.depthReqL, then SideFit.coL holds for the honest party a.side. The last two
      premises are on parameters that LaidLink leaves free. The proof uses three of LaidLink's nine
      fields: coL, startL and free; so not its three conditions on the window, nor that v₀ is well
      formed, nor that E lists each value once. The bound on attempts, a.rtail and c.ℓr occur in no
      premise.

How it fits. It serves completeness, not index privacy. SideFit.coL is not a clause of PremW
(Johnson/WholeKey/Premises.lean), nor one of LinkCompile's eleven (CompileSpec.lean; LinkCompile.coL
is another clause), though it concerns the same honest prover at the same parameters. Under
Johnson/LinkSim/ no other file calls either theorem; here sideFit_coL calls fit_dress_coinsPre.
Johnson/LinkSim/AtHome/CompileFit.lean names sideFit_coL among what is proved towards completeness
after the substitution.

Limits.
  Only one of SideFit's four conditions is proved here. The conditions on the tables' salts, on
      the first table's sub-protocol and on the sessions are not spoken of, so SideFit as a whole is
      not established.
  sideFit_coL has two premises beyond LaidLink, on the length of a.fill and on the slot. LaidLink
      does not give them.
  Lengths alone.
  That a run returns, or that a verifier accepts, is not said.
  Whether the values that LaidLink prescribes are the programs' is not said (see CompileSpec.lean's
      limits).

Sources. The proof of fit_dress_coinsPre follows closely, in general form, that of a lemma of ours
(fitCoinsThree) in a file that is not in this repository, so it cannot be checked against it from
here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtHome.CompileSpec
import Johnson.WholeKey.Complete

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtHome
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **Coins of the form coinsPre, after dress, have the lengths that the verifier's strict format
asks**, if the public prefixes, fill and the slot have the right lengths. coinsPre's own fill' is
not read. -/
theorem fit_dress_coinsPre {I' X' : Type} {lam : ℕ} {L' : BatchProtocolWithLeafBody I' X'}
    (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits) (nR nK nJ sFS ℓ ℓr dq sMT : ℕ)
    (pad : Body L') (slot : ℕ) (fill fill' : Bits) (E : Enum (RunBits lam nR nK nJ sFS ℓ ℓr dq))
    (hs : ∀ i b s, (start i b s).length + ℓ = sMT) (hf : fill.length = ℓ) (hslot : slot < 2 ^ dq)
    (e : Fin ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill' E).n + 1)) :
    (dress start rtail nR nK nJ fill
      ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill' E).e e)).Fit sMT sFS dq where
  salt := List.length_ofFn
  leaf := fun i b k j => by
    show (start i b _ ++ if i < nR ∧ k < nK ∧ j < nJ then
      ((coinsPre (L := L') nR nK nJ sFS ℓ ℓr dq pad slot fill' E).e e).leaf i b k j
      else fill).length = sMT
    by_cases hw : i < nR ∧ k < nK ∧ j < nJ
    · rw [if_pos hw]
      show (start i b _ ++ if h : i < nR ∧ k < nK ∧ j < nJ then List.ofFn _ else fill').length = sMT
      rw [dif_pos hw, List.length_append, List.length_ofFn]
      exact hs i b _
    · rw [if_neg hw, List.length_append, hf]
      exact hs i b _
  slot := hslot
  path := List.length_ofFn

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- **The link's condition SideFit.coL of the premise on lengths**, at parameters that satisfy
LaidLink, under two premises more: on the length of a.fill, and on the slot. -/
theorem sideFit_coL {W : QueryLayout lam (typedOracleCarrier L Bd aT aL)} {p : Params}
    {a : AtRecs lam L Bd aT aL} {c : CoinNums Bd} {v₀ : a.RV} (h : LaidLink W p a c v₀)
    (hf : a.fill.length = c.ℓ) (hslot : c.slotL < 2 ^ W.depthReqL) :
    ∀ e k, (a.side.dressL (a.side.rvL (a.side.kL.e k)) (a.side.coL.e e)).Fit p.sMT p.sFS
      W.depthReqL := by
  obtain ⟨E, -, hco⟩ := h.coL
  have key : ∀ (en : Enum (Coins lam (typedOracleCarrier L Bd aT aL))),
      en = coinsPre a.nR a.nK a.nJ p.sFS c.ℓ c.ℓr W.depthReqL c.padL c.slotL a.fill E →
      ∀ (v : a.RV) (e : Fin (en.n + 1)),
        (dress (a.startL v) a.rtail a.nR a.nK a.nJ a.fill (en.e e)).Fit p.sMT p.sFS
          W.depthReqL := by
    rintro _ rfl v e
    exact fit_dress_coinsPre (L' := typedOracleCarrier L Bd aT aL) (a.startL v) a.rtail a.nR a.nK a.nJ p.sFS
      c.ℓ c.ℓr W.depthReqL p.sMT c.padL c.slotL a.fill a.fill E
      (fun i b s => by rw [h.startL v i b s]; exact Nat.sub_add_cancel h.free) hf hslot e
  exact fun e k => key a.coL hco (a.rvL (a.kL.e k)) e

end OnBytes.LinkSim.AtHome

#print axioms OnBytes.LinkSim.AtHome.fit_dress_coinsPre
#print axioms OnBytes.LinkSim.AtHome.sideFit_coL
