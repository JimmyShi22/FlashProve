-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/GhostSide/TwinWhole.lean: the committer, the prover and the challenger of
Johnson/TokenSide/Whole.lean are routed.

One definition (GhostOK), one statement (Spec.routedTwin) and its proof. This file states no goal of
the release. A DEVICE OF A PROOF: the names fbw t k, the exchange of queries and "routed" stand in
no statement on the scheme. What "routed" is, and what for: the heads of Johnson/GhostSide/Defs.lean
and Johnson/GhostSide/Twin.lean.

Main names (namespace OnBytes.GhostSide).
  GhostOK W S capT capL capB   what is asked of the wires: the plain parts of a seed's two queries
                 stand for the number 0; in the rounds of the three protocols each number up to the
                 cap of tries is read back (Back, Johnson/GhostSide/Twin.lean).
  rt_…           routed, program by program.
  Spec.routedTwin, routedTwin   under GhostOK at the honest side's three caps: the committer
                 commitT, the prover proveWT and every step of the challenger challT are routed.
  plainOf_commitT, plainOf_proveWT   so these programs as ordinary oracle algorithms, with fb t
                 written back, are what erase makes of them, translated by the exchange of queries.
Limits: those of Compile/Batch/SpecGhost.lean. GhostOK is a premise here. It follows from the
clauses backT, backL, backB and plain of PremW (Johnson/WholeKey/Premises.lean): ghostOK_prem,
Johnson/LateSide/Whole.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.GhostSide.Twin

set_option autoImplicit false

noncomputable section

namespace OnBytes.GhostSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms OnBytes.TokenSide Rom
open OnBytes.Prover OnBytes.WholeKey
open _root_.Compile.GlueB (GCall ownPf)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}
variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)

/-- What is asked of the wires. -/
structure GhostOK (capT capL capB : ℕ → ℕ) : Prop where
  seed0 : clsPB _ _ (shW W S.t) S.pl0 = 0
  seed1 : clsPB _ _ (shW W S.t) S.pl1 = 0
  backT : Back L.offline.shape aT (wTC W).sh capT 0
  backL : Back L.link.shape aL (wLC W).sh capL 0
  backB : Back L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0

variable (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
  (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB)

namespace Spec

/-- Under GhostOK at the honest side's caps the token programs are routed. -/
def routedTwin : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape)
      (aL : RoundSplits L.link.shape) (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
      (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL)
      (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB),
    GhostOK W S h.capT h.capL h.capB →
      (∀ i, RoutedT W (commitT W S cA h tl i)) ∧
      (∀ isk b, RoutedT W (proveWT W cA r₀ h tl isk b)) ∧
      ∀ i s c, RoutedT W ((challT W S cA r₀ h tl i).step s c)

end Spec

local notation "Rt" => RoutedT W

variable {W S} (hG : GhostOK W S h.capT h.capL h.capB)
include hG

theorem rt_seedsT (cm : Dig lam) : Rt (seedsT W S cm) :=
  ⟨hG.seed0, fun _ => ⟨hG.seed1, fun _ => trivial⟩⟩

theorem rt_tabT (b₀ : Bd) (i : I) (r : L.EncodingRandomness) : Rt (tabT W S h tl b₀ i r) :=
  (rt_treeT W _ _ _ _ _).bind fun T => (rt_seedsT h hG T.root).bind fun _ => trivial

theorem rt_tabsT (i : I) : ∀ ds : List (DrawCopyD L h.KL), Rt (tabsT W S h tl i ds)
  | [] => trivial
  | d :: ds => (rt_tabT h tl hG h.b₀ i d.r).bind fun _ => (rt_tabsT i ds).bind fun _ => trivial

theorem rt_linkT (i : I) (t₁ t₂ : TabT lam L Bd aT aL) (d : DrawCopyD L h.KL) :
    Rt (linkT W cA h tl i t₁ t₂ d) :=
  (rt_proveC W Tag.link (batLC L aL) (wLC W) W.embL id _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)
    hG.backL).bind fun _ => trivial

theorem rt_linksT (i : I) (t₁ : TabT lam L Bd aT aL) :
    ∀ l : List (DrawCopyD L h.KL × TabT lam L Bd aT aL), Rt (linksT W cA h tl i t₁ l)
  | [] => trivial
  | a :: l => (rt_linkT cA h tl hG i t₁ a.2 a.1).bind fun _ =>
      (rt_linksT i t₁ l).bind fun _ => trivial

theorem rt_commitAtT (i : I) (d : DrawCD L h.KT h.KL) : Rt (commitAtT W S cA h tl i d) :=
  (rt_tabT h tl hG h.b₀ i d.r).bind fun t₁ =>
    (rt_tabsT h tl hG i d.copies).bind fun ts =>
    (rt_proveC W Tag.test (batTC L aT) (wTC W) W.embT id _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)
      hG.backT).bind fun _ =>
    (rt_linksT cA h tl hG i t₁ _).bind fun _ => trivial

omit hG in
theorem rt_coinsCopyT : Rt (coinsCopyT W h) := fun _ _ => trivial

omit hG in
theorem rt_coinsCopiesT : ∀ n : ℕ, Rt (coinsCopiesT W h n)
  | 0 => trivial
  | n + 1 => (rt_coinsCopyT h).bind fun _ => (rt_coinsCopiesT n).bind fun _ => trivial

omit hG in
theorem rt_coinsCT : Rt (coinsCT W h) := fun _ _ =>
  (rt_coinsCopiesT h (h.M + 1)).bind fun _ => trivial

theorem rt_commitT (i : I) : Rt (commitT W S cA h tl i) :=
  (rt_coinsCT h).bind fun d => rt_commitAtT cA h tl hG i d

theorem rt_proveAtT (isk : IskT lam L Bd aT aL) (x : X) (d : DrawPD h.KB) :
    Rt (proveAtT W cA r₀ h tl isk x d) := by
  unfold proveAtT
  split
  next => trivial
  next t _ =>
    exact (rt_proveC W Tag.onl L.onlineBatch (wBC W) W.embB id _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)
      hG.backB).bind fun _ => trivial

omit hG in
theorem rt_coinsPT : Rt (coinsPT W h) := fun _ _ => trivial

theorem rt_proveWT (isk : IskT lam L Bd aT aL) (b : ZKCP.Gen.Batch X Unit) :
    Rt (proveWT W cA r₀ h tl isk b) := by
  unfold proveWT
  split
  next x _ =>
    exact (rt_coinsPT h).bind fun d => (rt_proveAtT cA r₀ h tl hG isk x d).bind fun _ => trivial
  next => trivial

theorem rt_challT (i : I) (s : Option (IskT lam L Bd aT aL)) (c : GCall X Unit) :
    Rt ((challT W S cA r₀ h tl i).step s c) := by
  cases c with
  | setup =>
    cases s with
    | none => exact (rt_commitT cA h tl hG i).bind fun _ => trivial
    | some k => trivial
  | batch b =>
    cases s with
    | none => trivial
    | some k => exact (rt_proveWT cA r₀ h tl hG k b).bind fun _ => trivial

/-- The committer as an ordinary oracle algorithm. -/
theorem plainOf_commitT (i : I) (vs : List Bits) :
    plainOf (commitT W S cA h tl i) vs = (erase (commitT W S cA h tl i) vs).via (ghost W) :=
  plainOf_via (rt_commitT cA h tl hG i) vs

/-- The prover as an ordinary oracle algorithm. -/
theorem plainOf_proveWT (isk : IskT lam L Bd aT aL) (b : ZKCP.Gen.Batch X Unit) (vs : List Bits) :
    plainOf (proveWT W cA r₀ h tl isk b) vs =
      (erase (proveWT W cA r₀ h tl isk b) vs).via (ghost W) :=
  plainOf_via (rt_proveWT cA r₀ h tl hG isk b) vs

omit hG in
theorem routedTwin : Spec.routedTwin :=
  fun _ _ _ _ _ _ _ _ _ cA r₀ h tl hG =>
    ⟨rt_commitT cA h tl hG, rt_proveWT cA r₀ h tl hG, rt_challT cA r₀ h tl hG⟩

end OnBytes.GhostSide

#print axioms OnBytes.GhostSide.routedTwin
#print axioms OnBytes.GhostSide.plainOf_commitT
#print axioms OnBytes.GhostSide.plainOf_proveWT
