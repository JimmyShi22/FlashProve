-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/SameTab.lean: THE TOKEN SIDE's TABLE IS THE SCHEME's TABLE: the proof of
Spec.sameTab (Johnson/TokenSide/SpecSame.lean).

A lemma of one step of a proof. This file states no goal of the release. The token programs are a
device of that step and stand in no statement on the scheme.

Both sides build one tree and then ask the seed's two queries at its root. The tree is the tie on
one tree (tie_tree, Johnson/TokenSide/TieTree.lean). There the builder is handed salts for every
natural number; the scheme hands its builder salts that are cut behind the tree (cutS,
Johnson/WholeKey/Defs.lean). The builder asks the oracle at the leaves of the tree alone, where the
cut changes nothing (the last part of the proof); what it keeps are the salts as handed, and these
are, leaf by leaf, the token side's table at the store's values (kept_eq): at a leaf of the tree the
coins hold the value of the leaf's token (get_patchT_in), and behind the tree both are empty.
The seed's two queries are one algorithm on both sides (plainOf_seedsT_bind).

-/
import Johnson.TokenSide.SpecSame

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

section Tree
variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {Ω : Type} {μ : PMF Ω} {ℓ : ℕ}
  {Z : ℕ → Bool → ℕ → ℕ → Prop}

/-- The tree that the scheme's builder keeps, at coins into which the drawn bits are laid and which
are cut behind the tree, is the token side's tree at the store's values. -/
theorem kept_eq (ll : LeafLens Ω μ ℓ Z) (pre : Bits) (i : ℕ) (b : Bool) (k d : ℕ) (vs : List Bits)
    (ω : Ω) (T : TreeT lam L) (hT : TreeOK ℓ d vs T) (hz : ∀ j, j < 2 ^ d → Z i b k j) :
    (⟨fun j => ⟨T.body j,
        cutS (2 ^ d) (fun j => pre ++ ll.get (patchT ll i b k T vs ω) i b k j) j⟩, T.lv⟩ :
      TreeK lam L) = T.toK (fun u => vs.getD u []) pre := by
  unfold TreeT.toK
  refine congrArg (fun f => (⟨f, T.lv⟩ : TreeK lam L)) (funext fun j => ?_)
  refine congrArg (fun s => (⟨T.body j, s⟩ : LeafIn L)) ?_
  cases e : T.tok[j]? with
  | none =>
      have hj : ¬ j < 2 ^ d := by
        rw [← hT.1]
        exact Nat.not_lt.mpr (List.getElem?_eq_none_iff.mp e)
      show cutS (2 ^ d) (fun j => pre ++ ll.get (patchT ll i b k T vs ω) i b k j) j = []
      unfold cutS
      rw [if_neg hj]
  | some a =>
      have hj : j < 2 ^ d := by
        rw [← hT.1]
        exact (List.getElem?_eq_some_iff.mp e).1
      show cutS (2 ^ d) (fun j => pre ++ ll.get (patchT ll i b k T vs ω) i b k j) j =
        pre ++ vs.getD a.1 []
      unfold cutS
      rw [if_pos hj]
      beta_reduce
      rw [get_patchT_in ll i b k d vs ω T hT hz j a e]

end Tree

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape}

/-- The seed's two queries are one algorithm on both sides. -/
theorem plainOf_seedsT_bind {β : Type} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL))
    (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL) (cm : Dig lam)
    (g : L.OutOfDomainSeed → StT lam W.K (typedOracleCarrier L Bd aT aL) β) (vs : List Bits) :
    plainOf ((seedsT W S cm).bind g) vs = (seedsO W S cm).bind fun e => plainOf (g e) vs := rfl

/-- **ONE TABLE.** -/
theorem sameTab : Spec.sameTab := by
  intro I X lam L Bd aT aL W S h tl bd i r Ω μ Z ll i₀ b₀ k₀ vs hz
  show Tie μ _ _ (plainOf ((treeT (K := W.K) tl.frE [] (fun _ => tl.preE) W.depth
    fun j => (committerLeafInput W bd (L.encodeIndex i r) (fun _ => []) j).body).bind fun T =>
      (seedsT W S T.root).bind fun e => Step.pure (⟨r, T, e⟩ : TabT lam L Bd aT aL)) vs) _
  rw [plainOf_bind]
  refine (Tie.bindW (tie_tree ll [] (fun _ => tl.preE) tl.preE i₀ b₀ k₀ W.depth _ vs hz
    (fun _ e => absurd e List.not_mem_nil) rfl)
    (f' := fun ω T => (seedsO W S T.root).bind fun e => .pure (⟨r, ⟨fun j => ⟨(T.inp j).body,
      cutS (2 ^ W.depth) (fun j => tl.preE ++ ll.get ω i₀ b₀ k₀ j) j⟩, T.lv⟩, e⟩ :
        TabK lam L Bd aT aL)) fun p hp => ?_).congr fun ω => ?_
  · rw [plainOf_seedsT_bind]
    refine Tie.left (seedsO W S p.1.root) (f' := fun ω e => .pure (⟨r, ⟨fun j => ⟨p.1.body j,
      cutS (2 ^ W.depth) (fun j => tl.preE ++ ll.get (patchT ll i₀ b₀ k₀ p.1 p.2 ω) i₀ b₀ k₀ j) j⟩,
        p.1.lv⟩, e⟩ : TabK lam L Bd aT aL)) fun e => ?_
    refine .done hp fun ω => ?_
    beta_reduce
    rw [kept_eq ll tl.preE i₀ b₀ k₀ W.depth p.2 ω p.1 hp.2 hz]
    rfl
  · show ((treeO (K := W.K) W.depth (committerLeafInput W bd (L.encodeIndex i r)
        (cutS (2 ^ W.depth) fun j => tl.preE ++ ll.get ω i₀ b₀ k₀ j))).bind fun T =>
      (seedsO W S T.root).bind fun e => OComp.pure (⟨r, T, e⟩ : TabK lam L Bd aT aL)) = _
    have e1 : (List.range (2 ^ W.depth)).map (committerLeafInput W bd (L.encodeIndex i r)
          (cutS (2 ^ W.depth) fun j => tl.preE ++ ll.get ω i₀ b₀ k₀ j)) =
        (List.range (2 ^ W.depth)).map fun j =>
          (⟨(committerLeafInput W bd (L.encodeIndex i r) (fun _ => []) j).body, tl.preE ++ ll.get ω i₀ b₀ k₀ j⟩ :
            LeafIn (typedOracleCarrier L Bd aT aL)) :=
      List.map_congr_left fun j hj => by
        show (⟨(committerLeafInput W bd (L.encodeIndex i r) (fun _ => []) j).body,
          cutS (2 ^ W.depth) (fun j => tl.preE ++ ll.get ω i₀ b₀ k₀ j) j⟩ :
            LeafIn (typedOracleCarrier L Bd aT aL)) = _
        unfold cutS
        rw [if_pos (List.mem_range.mp hj)]
    unfold treeO
    rw [e1, Tie.obind_assoc, Tie.obind_assoc]
    refine congrArg _ (funext fun l => ?_)
    rw [Tie.obind_assoc, Tie.obind_assoc]
    rfl

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.sameTab
