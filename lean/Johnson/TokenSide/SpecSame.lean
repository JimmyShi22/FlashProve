-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide/SpecSame.lean: THE TOKEN SIDE DOES WHAT THE SCHEME's OWN TERMS DO: TWO STATEMENTS,
each a Prop under a name, and what shows that their premises on the coins can be met. NO PROOF of
the two statements here: Spec.sameRun is proved in Johnson/TokenSide/TieRun.lean, Spec.sameTab in
Johnson/TokenSide2/SameTab.lean.

Statements of one step of a proof. This file states no goal of the release.

  Spec.sameRun   ONE COMPILED RUN. The token program proveC (Johnson/TokenRules/Chunks.lean), as an
      ordinary algorithm with the names fbw t k written back to fb t (plainOf,
      Johnson/TokenSide/Erased.lean), is tied (Tie, Johnson/TokenSide/Tie.lean) to the family
      ω ↦ "the compiled prover proveX at the coins coRun .. ω, and then what is handed out of its
      outcome (shown stop)". The two outputs are EQUAL: a proof string or "none".
  Spec.sameTab   ONE TABLE. tabT (Johnson/TokenSide/Whole.lean) is tied to the family
      ω ↦ tabO at the salts "start, then the free bits that are read off ω", cut behind the tree.
      The token side returns handles; the table as the scheme keeps it is TabT.toK of them at the
      store's values.

WHAT A TIE GIVES (Tie.sound): for EVERY handler of queries h and every state s,
  μ.bind (fun ω => (family ω).interp h s) = (the token side).interp h s, with its output mapped.
So one statement serves the run under lazy sampling and the run in which marked points are deferred
and logged: the log is part of the handler's state.

THE PREMISES.
  The coins: a letter Ω with a law μ and a RunLens (Johnson/TokenSide/Lens.lean); the law is asked
  at the coordinates in Z alone. CoversRun: Z holds all that a run reads. THEY CAN BE MET:
  CoinLens.finset is a member at every finite set of coordinates, and coversRun_winRun shows a
  finite set that holds all that a run reads, a window that is wide enough (FitsWin).
  wq.OKG: of it the proof uses that a position's place is a leaf of its tree, that the wire lays the
  position at that place, and that the wire's list of external positions holds them all.
  ExtTie: the external strings' trees as the compiled prover is handed them (xtK) and with tokens
  (xt) have the same levels, and at each external position's leaf the same salt, the tokens read at
  the store's values; the leaf's token, if the tree has that leaf, is in the store.

Limits. Statements. Both are of the ERASED programs (plainOf): tokens are strings in a store, and
the names fbw t k are written back to fb t. Nothing here speaks of these names, or of the two modes
of deferred programming (Rom/Defer.lean): they are the matter of Johnson/HopSide/,
Johnson/GhostSide/ and Compile/DeferRun/. No member of wq.OKG or of ExtTie is shown here. One slot.
The slot, the padding and the public end of the string behind the slot value are fixed values on
both sides (RunLen).
Terms: lean/GLOSSARY.md.

-/
import Johnson.TokenSide.Lens
import Johnson.TokenSide.TieChain
import Johnson.TokenSide.Whole

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- Z holds every coordinate that a compiled run reads. -/
def CoversRun {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (Z : RunCo → Prop) (ln : RunLen lam L)
    (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) : Prop :=
  Z .salt ∧ Z .rs ∧ (∀ n, n < ln.dq → Z (.path n)) ∧ Covers (fun i b k j => Z (.leaf i b k j)) s A W
      0

/-- The external strings' trees, as the compiled prover is handed them and with tokens, agree where
an external position stands. -/
def ExtTie {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {E : ExtSpec} (we : WireE E)
    (xtK : ℕ → TreeK lam L) (xt : ℕ → TreeT lam L) (preX : Bits) (vs : List Bits) : Prop :=
  ∀ p : E.Pos, (xtK (we.which p)).lv = (xt (we.which p)).lv ∧
    ((xtK (we.which p)).inp (we.leaf p)).salt =
      (((xt (we.which p)).toK (fun u => vs.getD u []) preX).inp (we.leaf p)).salt ∧
    ∀ a, (xt (we.which p)).tok[we.leaf p]? = some a → a.1 < vs.length

/-- **ONE COMPILED RUN.** -/
def Spec.sameRun : Prop :=
  ∀ {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xtK : ℕ → TreeK lam L) (xt : ℕ → TreeT lam L)
    (preX : Bits) (σ : Strat Q.loc.shape Unit) (ln : RunLen lam L) (pre : ℕ → Bool → Bits → Bits)
    (cap : ℕ → ℕ) (stop : Rho Q.loc.shape → Bool) {Ω : Type} {μ : PMF Ω} {Z : RunCo → Prop}
    (rl : RunLens Ω μ ln Z) (vs : List Bits),
    wq.OKG → CoversRun Z ln Q.loc.shape Q.ann wq.sh → ExtTie wq.ext xtK xt preX vs →
    Tie μ (fun (p : Option (OneProtocolProof lam Q) × List Bits) _ => p.1) (fun p => vs <+: p.2)
      (plainOf (proveC t Q wq embS embP xin cms x y xt preX σ ln pre cap stop) vs)
      (fun ω => (proveX t Q wq embS embP xin cms x y xtK σ (coRun rl pre ω) cap).bind
        fun r => .pure (shown stop r))

/-- **ONE TABLE.** The salts that the scheme's builder is handed are cut behind the tree (cutS,
Johnson/WholeKey/Defs.lean), as at the scheme's own calls. So the table that it keeps IS the token
side's table with the store's values in the place of the tokens (TabT.toK): nothing of the coins
that were not drawn is left in it. (i₀, b₀, k₀): where the table's salts stand among the
coordinates. -/
def Spec.sameTab : Prop :=
  ∀ {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
    (h : HonestSide lam L Bd aT aL) (tl : TokLen lam (typedOracleCarrier L Bd aT aL) h.KT h.KL h.KB) (bd : Bd)
    (i : I) (r : L.EncodingRandomness) {Ω : Type} {μ : PMF Ω} {Z : ℕ → Bool → ℕ → ℕ → Prop}
    (ll : LeafLens Ω μ tl.frE Z) (i₀ : ℕ) (b₀ : Bool) (k₀ : ℕ) (vs : List Bits),
    (∀ j, j < 2 ^ W.depth → Z i₀ b₀ k₀ j) →
    Tie μ (fun (p : TabT lam L Bd aT aL × List Bits) _ =>
        p.1.toK (fun u => p.2.getD u []) tl.preE)
      (fun p => vs <+: p.2 ∧ TreeOK tl.frE W.depth p.2 p.1.tree)
      (plainOf (tabT W S h tl bd i r) vs)
      (fun ω => tabO W S bd i r (cutS (2 ^ W.depth) fun j => tl.preE ++ ll.get ω i₀ b₀ k₀ j))

/-! ## The premises can be met -/

/-- the coordinates within a window: rounds below nR, trees below nK, leaves below nJ, sibling
digests below dq -/
def winRun (nR nK nJ dq : ℕ) : Finset RunCo :=
  {RunCo.salt, RunCo.rs} ∪ (Finset.range dq).image RunCo.path ∪
    ((Finset.range nR ×ˢ (Finset.univ : Finset Bool)) ×ˢ (Finset.range nK ×ˢ Finset.range nJ)).image
      fun c => RunCo.leaf c.1.1 c.1.2 c.2.1 c.2.2

theorem mem_winRun_leaf {nR nK nJ dq i k j : ℕ} (b : Bool) (hi : i < nR) (hk : k < nK)
    (hj : j < nJ) : RunCo.leaf i b k j ∈ winRun nR nK nJ dq := by
  refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨((i, b), (k, j)), ?_, rfl⟩)
  simp only [Finset.mem_product, Finset.mem_range, Finset.mem_univ, and_true]
  exact ⟨hi, hk, hj⟩

/-- a window holds the leaves of the rounds s if it is wide enough -/
def FitsWin {lam K : ℕ} (nR nK nJ : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → Prop
  | [], _, _, _ => True
  | _ :: s, (_, A), (w, W), i =>
      i < nR ∧ w.depthJ.length ≤ nK ∧ w.depth0.length ≤ nK ∧ (∀ d ∈ w.depthJ, 2 ^ d ≤ nJ) ∧
        (∀ d ∈ w.depth0, 2 ^ d ≤ nJ) ∧ FitsWin nR nK nJ s A W (i + 1)

theorem covers_winRun {lam K : ℕ} (nR nK nJ dq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), FitsWin nR nK nJ s A W i →
      Covers (fun i b k j => RunCo.leaf i b k j ∈ winRun nR nK nJ dq) s A W i
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (w, W), i, h =>
    ⟨fun n d hn j hj => mem_winRun_leaf true h.1
        (by
          have h0 := (List.getElem?_eq_some_iff.mp hn).1
          have h1 := h.2.1
          omega)
        (Nat.lt_of_lt_of_le hj (h.2.2.2.1 d (List.mem_of_getElem? hn))),
      fun n d hn j hj => mem_winRun_leaf false h.1
        (by
          have h0 := (List.getElem?_eq_some_iff.mp hn).1
          have h1 := h.2.2.1
          omega)
        (Nat.lt_of_lt_of_le hj (h.2.2.2.2.1 d (List.mem_of_getElem? hn))),
      covers_winRun nR nK nJ dq s A W (i + 1) h.2.2.2.2.2⟩

/-- **CoversRun can be met** by a finite set of coordinates: so, with CoinLens.finset, the premises
on the coins of Spec.sameRun have a member at every shape and wire at which a window is wide enough
(FitsWin). That some window is wide enough at every shape and wire is not typed here. -/
theorem coversRun_winRun {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} (ln : RunLen lam L) (nR nK nJ : ℕ)
    (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (h : FitsWin nR nK nJ s A W 0) :
    CoversRun (fun c => c ∈ winRun nR nK nJ ln.dq) ln s A W :=
  ⟨by simp [winRun], by simp [winRun],
    fun n hn => Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hn, rfl⟩)),
    covers_winRun nR nK nJ ln.dq s A W 0 h⟩

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.coversRun_winRun
