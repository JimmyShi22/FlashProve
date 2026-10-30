-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUUnif.lean: under lazily sampled oracles and the hypotheses of the statements,
the verifier randomness of any one slot with a request is exactly uniform, except for the
proof-of-work bits, for the prover with free empty slots; the distribution of the hash blocks that
such a slot sees (words of this library: lean/GLOSSARY.md). Towards completeness of the compiled
scheme.

The statements are on the algorithms without tokens of Compile/Batch/CompleteURefDefs.lean (a token
is a position in a store: Compile/Batch/CompleteRefDefs.lean). The number i of the round is a field
of the query; so, when the slot's own algorithm is run from a table with `FbLt t i`, each query
along the transcript of that slot is new when it is made; in a run of all slots another slot may
have made it in the same local round (Compile/Batch/CompleteUnif.lean, item 2). What the request
root is does not matter: it is made without a query to the Fiat-Shamir oracle.

  1  `optO`, `rleavesOU`, `reqRootOU`: which oracles they query; what a run of `optO` returns.
  2  `chainOU_blocks`: the hash blocks that a slot with a request gathers are independent, each with
     the distribution of its round (`ublkG`, `zero_ublkG`, Compile/Batch/CompleteUnif.lean: uniform
     in a round without proof-of-work bits; that of the final attempt in a round with them).
  3  `blocks_proveOUG`, `pr_noneAtU`: one execution; the proof string of a slot with a request is
     `none` with exactly the probability of the withheld set. (not all hypotheses are named here:
     see its statement)
  4  `pr_batOU`: one batch on a given node, under `W.OK`, `Fmt`: exactly the probability of the
     withheld set (not all hypotheses are named here: see its statement). `unifBU`: the small
     experiment `RBU` shows `none` with probability at most `M.pO`, under `L.Props`, `W.OK`, `Fmt`,
     for a request x in `Ryes i`.

`chainOU_blocks`, `blocks_proveOUG`, `pr_noneAtUG` are for `RoundsQueryLayout.OKG`, with no proof-of-work bits
or `embP` injective (the attempts of a search must be different queries), among other hypotheses;
`pr_noneAtUG` also needs that the withheld set does not depend on the proof-of-work bits;
`pr_noneAtU`, `pr_batOU`, `unifBU` are the statements without proof-of-work bits (`RoundsQueryLayout.OK`,
`W.OK`; among other hypotheses). `batOU` ends in `Ref.badAt` (`none`, or a failed search); without
proof-of-work bits that is `none`.

Notation: `Q`: a `BatchInteractiveOracleProof` (Iop/Batch.lean): a batch IOP: the local verifier, and the annotation
of its shape; `H`: a `BatchHonestProver Q Wt` (Iop/Batch.lean): the honest side of a batch IOP; `t`: a `Tag`
(Compile/Oracles.lean): test, link or onl; `sMT`, `sFS`: natural numbers: the length of the salt of
a leaf, and of the salt of a chain (Compile/Batch/Verifier.lean); `cms`: a `List (Dig lam)`: the
external roots (`verifyB`, Compile/Batch/Verifier.lean); `embS`, `embP` say how symbols and plain
parts are written into queries (`verifyB`, Compile/Batch/Verifier.lean); `xin`: `Y → Option X`:
`xin x` is the x of `recomputeChain` (Compile/Batch/Verifier.lean): the whole instance (none: Test, Link);
`depthReq`, `dR`: a natural number; in `QueryLayout` (Iop/BatchWire.lean): depth of a request tree: there
are 2^depthReq slots; `ph`: a `PhO` (Compile/Batch/CompleteRefDefs.lean): `first`, `loc`, `shr ρ0`
or `aft`; `.f4`, `.f5` (`Head`, Compile/Batch/Oracles.lean): (F4): the joining round; (F5): a later
shared round; `gr0`, `grJ` (fields of `WireRB`, Iop/BatchWire.lean): an `Option (GrW ..)`: has the
Fiat-Shamir query of a shared round, formats (F4) and (F5), a test? none: no; `grJ`: the same for
the Fiat-Shamir query of a slot in a local round; `FbLt t i T` (Compile/Batch/CompleteUnif.lean): a
proposition: every entry of the Fiat-Shamir oracle of t has a round below i; `hearO`
(Compile/Batch/CompleteRefDefs.lean): a slot receives a shared verifier message; `slotsOfReq σ xs`
(Compile/Batch/Star.lean): what the slots hold: request number a is in slot σ a; `RBU`
(Compile/Batch/CompleteURefDefs.lean): a fresh node and one batch on it; a node (`nodeO`,
Compile/Batch/CompleteRefDefs.lean): a fresh encoding of i and the root of its tree; `M.pO`: a field
of `M`, an `LH.Nums` (Iop/InteractiveOracleProof.lean: all numbers of the interface), in ℝ≥0∞; `Fmt` (`RoundSplits.Fmt`,
Iop/BatchFmt.lean): a proposition: every round has a format, and an unsent component is empty.

Limits: no bound on a failed search is proved here. Nothing on an empty slot. Nothing on the joint
distribution of several slots.
-/
import Compile.Batch.CompleteUnif
import Compile.Batch.CompleteURefDefs
import Compile.Batch.CompleteAcc

noncomputable section

open scoped ENNReal

namespace Compile.Batch.CompleteUUnif
open Iop Rom Prob Compile.Batch.Ref Compile.Batch.RefU Compile.Batch.CompleteUnif

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## 1. The new algorithms -/

section Opt
variable {σ τ γ : Type}

theorem onlyQ_optO {P : (o : OracleName) → domOf lam L o → Prop} {g : σ → TypedOracleComputation lam K L τ}
    (hg : ∀ a, OnlyQ (S := spec lam K L) P (g a)) :
    ∀ o : Option σ, OnlyQ (S := spec lam K L) P (optO g o)
  | none => trivial
  | some a => OnlyQ.bind (hg a) fun _ => trivial

/-- a function of the result of a slot with a request has the distribution that it has for the
slot's own algorithm -/
theorem map_optO_some (g : σ → TypedOracleComputation lam K L τ) (h : Option τ → γ) (v : σ) (T : Table (spec lam K L)) :
    ((optO g (some v)).runLazy T).map (fun x => h x.1) =
      ((g v).runLazy T).map fun x => h (some x.1) := by
  show (((g v).bind fun v' => OComp.pure (some v')).runLazy T).map _ = _
  rw [OComp.runLazy_bind, PMF.map_bind]
  simp only [OComp.runLazy, PMF.pure_map]
  rw [← PMF.bind_pure_comp]
  rfl

/-- in every run, a slot with a request stays one, and its result comes from a run of its own
algorithm -/
theorem supp_optO (g : σ → TypedOracleComputation lam K L τ) (R : σ → τ → Prop)
    (hg : ∀ a T, ∀ y ∈ ((g a).runLazy T).support, R a y.1) :
    ∀ (a : Option σ) (T : Table (spec lam K L)),
      ∀ y ∈ ((optO g a).runLazy T).support, ∀ v, a = some v → ∃ v', y.1 = some v' ∧ R v v' := by
  rintro a T y hy v rfl
  have hy' : y ∈ (((g v).bind fun v' => OComp.pure (some v')).runLazy T).support := hy
  rw [OComp.runLazy_bind] at hy'
  obtain ⟨y1, h1, hy'⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
  simp only [OComp.runLazy, PMF.support_pure, Set.mem_singleton_iff] at hy'
  rw [hy']
  exact ⟨y1.1, rfl, hg v T y1 h1⟩

end Opt

theorem onlyQ_rleavesOU (t : Tag) :
    ∀ cs : List (Option Bits),
      OnlyQ (S := spec lam K L) (NotFb t) (rleavesOU (lam := lam) (K := K) (L := L) cs)
  | [] => trivial
  | some _ :: cs =>
    OnlyQ.bind (onlyQ_askV t OracleName.rleaf (by simp) _) fun _ =>
      OnlyQ.bind (onlyQ_rleavesOU t cs) fun _ => trivial
  | none :: cs =>
    OnlyQ.bind (onlyQ_freshO t _) fun _ => OnlyQ.bind (onlyQ_rleavesOU t cs) fun _ => trivial

theorem onlyQ_reqRootOU (t : Tag) (dR : ℕ) (cs : List (Option Bits)) :
    OnlyQ (S := spec lam K L) (NotFb t) (reqRootOU (lam := lam) (K := K) (L := L) dR cs) :=
  OnlyQ.bind (onlyQ_rleavesOU t cs) fun _ =>
    OnlyQ.bind (onlyQ_levelsM t (fun _ _ => onlyQ_askV t OracleName.rnode (by simp) _) dR _)
      fun _ => trivial

/-! ## 2. The hash blocks of one slot -/

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (dR : ℕ)

/-- The hash blocks that one slot with a request gathers are independent, each with the distribution
of its round, from every state of the execution: whatever the other slots, the strategies, the
request root and the shared Fiat-Shamir chain are, if the table holds no Fiat-Shamir query of a
round that is still to come. Further hypotheses are in the statement. -/
theorem chainOU_blocks (n : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhO) (σ0 : SStrat s A)
        (vs : List (Option (VSlot lam K X s))) (v : VSlot lam K X s) (T : Table (spec lam K L)),
      RoundsQueryLayout.OKG s A W → (RoundsQueryLayout.OK s A W ∨ Function.Injective embP) →
      RoundSplits.FmtFrom s A (toFO ph) → vs[n]? = some (some v) → FbLt t i T →
      ((chainOU sMT t cms dR s A W embS embP i ph σ0 vs).runLazy T).map (fun x => x.1.getD n []) =
        (ublkG s A W).map fun l => v.blocks ++ l
  | [], _, _, _, _, _, _, _, vs, v, T, _, _, _, hv, _ => by
    show ((OComp.pure (vs.map blocksU) : TypedOracleComputation lam K L _).runLazy T).map _ = (PMF.pure []).map _
    simp only [OComp.runLazy, PMF.pure_map, List.append_nil]
    congr 1
    simp [List.getD, hv, blocksU]
  | r :: s, (a, A), (w, W), embS, embP, i, ph, σ0, vs, v, T, hW, hE, hF, hv, hT => by
    have hE' : RoundsQueryLayout.OK s A W ∨ Function.Injective fun z => embP (.inr z) :=
      hE.imp (fun h => h.2) fun h x y e => Sum.inr.inj (h e)
    have hqJ : ∀ g,
        w.grJ = some g → Function.Injective fun α => embP (.inl (.inr α)) := fun g hg => by
      rcases hE with h | h
      · rw [h.1.grJ_none] at hg; cases hg
      · exact fun x y e => Sum.inr.inj (Sum.inl.inj (h e))
    have hq0 : ∀ g,
        w.gr0 = some g → Function.Injective fun α => embP (.inl (.inl α)) := fun g hg => by
      rcases hE with h | h
      · rw [h.1.gr0_none] at hg; cases hg
      · exact fun x y e => Sum.inl.inj (Sum.inl.inj (h e))
    have hsh : ∀ b : List (Blk lam K), a.kind = .sh →
        ((gAns w.gr0 w.chal).bind fun ans => (ublkG s A W).map fun l => (b ++ [ans.1]) ++ l) =
          (ublkG (r :: s) (a, A) (w, W)).map fun l => b ++ l := fun b hk => by
      rw [← ublkG_step a A w W b]
      have e : rblk a w = gblk w.gr0 w.chal := by unfold rblk; rw [hk]
      rw [e]
      unfold gblk
      rw [PMF.bind_map]
      rfl
    cases hk : a.kind with
    | lo =>
      have hF' : RoundSplits.FmtFrom s A (toFO ph.afterLo) := by
        rw [toFO_afterLo]
        have : a.NoShared ∧ RoundSplits.FmtFrom s A (toFO ph).afterLo := by
          simpa only [RoundSplits.FmtFrom, hk] using hF
        exact this.2
      rw [chainOU_lo sMT t cms dR w W embS embP i σ0 vs hk ph, OComp.runLazy_bind, PMF.map_bind]
      have step : ∀ y ∈
              ((eachO (optO (slotLoO sMT t cms a w (fun p => embS (.inl p))
                      (fun α => embP (.inl (.inr α))) i ph)) vs).runLazy T).support,
            ((chainOU sMT t cms dR s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
                  ph.afterLo (σ0.2 (a.kind.shOf (w.chal (blk0 lam K)))) y.1).runLazy y.2).map
                (fun x => x.1.getD n []) =
              (fun b : List (Blk lam K) => (ublkG s A W).map fun l => b ++ l)
                (atN blocksU [] n y.1) := by
        intro y hy
        obtain ⟨o', e, ho'⟩ := supp_eachO_entry _
          (fun (a' : Option (VSlot lam K X (r :: s))) (b' : Option (VSlot lam K X s)) =>
            ∀ v, a' = some v → ∃ v', b' = some v' ∧ True)
          (supp_optO _ (fun _ _ => True) fun _ _ _ _ => trivial) n vs (some v) hv T y hy
        obtain ⟨v', rfl, -⟩ := ho' v rfl
        rw [chainOU_blocks n s A W _ _ (i + 1) _ _ y.1 v' y.2 hW.2 hE' hF' e
            (FbLt.of_fbAt
              (onlyQ_eachO (onlyQ_optO (onlyQ_slotLoO sMT t cms a w _ _ i ph)) vs) hT y hy)]
        simp [atN, e, blocksU]
      have e : ∀ p : PMF (List (Option (VSlot lam K X s)) × Table (spec lam K L)),
          (p.bind fun y =>
              (fun b : List (Blk lam K) => (ublkG s A W).map fun l => b ++ l)
                (atN blocksU [] n y.1)) =
            (p.map fun y => atN blocksU [] n y.1).bind fun b =>
              (ublkG s A W).map fun l => b ++ l := fun p => by
        rw [PMF.bind_map]; rfl
      rw [Rom.bind_congr_support _ step, e,
        lazy_eachO_entry _ blocksU [] n vs (some v) hv T, map_optO_some]
      show (((slotLoO sMT t cms a w (fun p => embS (.inl p))
            (fun α => embP (.inl (.inr α))) i ph v).runLazy T).map
          fun x => x.1.blocks).bind _ = _
      rw [blocks_slotLoO sMT t cms a w _ _ i ph v T hT hW.1.grJ_ok hqJ, PMF.bind_map]
      have er : rblk a w = gblk w.grJ w.chal := by unfold rblk; rw [hk]
      rw [← er]
      exact ublkG_step a A w W v.blocks
    | sh =>
      cases ph with
      | first => simp only [RoundSplits.FmtFrom, hk, toFO] at hF
      | aft => simp only [RoundSplits.FmtFrom, hk, toFO] at hF
      | loc =>
        have hF' : RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toFO] using hF
        rw [chainOU_join sMT t cms dR w W embS embP i σ0 vs hk, OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y1 h1 => ?_
        have t1 :=
          FbLt.of_notFb (onlyQ_eachO (onlyQ_optO (onlyQ_slotJoinO sMT t a w _ _ i)) vs) hT y1 h1
        obtain ⟨o1, e1, ho1⟩ := supp_eachO_entry _
          (fun (a' b' : Option (VSlot lam K X (r :: s))) =>
            ∀ v, a' = some v → ∃ v', b' = some v' ∧ v'.blocks = v.blocks)
          (supp_optO _ (fun v v' : VSlot lam K X (r :: s) => v'.blocks = v.blocks)
            fun a' T' => supp_slotJoinO sMT t a w _ _ i a' T')
          n vs (some v) hv T y1 h1
        obtain ⟨v1, rfl, b1⟩ := ho1 v rfl
        rw [OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y2 h2 => ?_
        have t2 := FbLt.of_notFb (onlyQ_reqRootOU t dR _) t1 y2 h2
        rw [OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y3 h3 => ?_
        have t3 := FbLt.of_notFb (onlyQ_rootOO t sMT _ _ _) t2 y3 h3
        refine (askG_then t w.gr0 hW.1.gr0_ok w.chal
            (fun α => (⟨i, .f4 cms (List.ofFn y2.1), y3.1, embP (.inl (.inl α))⟩ : FbIn lam L t))
            (fun g hg x y e => hq0 g hg (congrArg FbIn.plain e)) _ _ _
            (fun ans => (ublkG s A W).map fun l => (v.blocks ++ [ans.1]) ++ l) y3.2
            (fun β => t3.new _ rfl) fun ans T' hT' => ?_).trans
          (hsh v.blocks hk)
        have ih := chainOU_blocks n s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
          (i + 1) (.shr (List.ofFn ans.2)) (σ0.2 (a.kind.shOf (w.chal ans.1)))
          (y1.1.map (Option.map (hearO w ans.1))) (hearO w ans.1 v1) T' hW.2 hE' hF'
          (by simp [e1]) (t3.left t (fun _ => rfl) hT')
        refine ih.trans ?_
        show (ublkG s A W).map (fun l => (v1.blocks ++ [ans.1]) ++ l) = _
        rw [b1]
      | shr ρ0 =>
        have hF' : RoundSplits.FmtFrom s A .shr := by
          have : a.NoSlot ∧ RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toFO] using hF
          exact this.2
        rw [chainOU_shr sMT t cms dR w W embS embP i σ0 vs hk ρ0, OComp.runLazy_bind, PMF.map_bind]
        refine bind_const_supp fun y3 h3 => ?_
        have t3 := FbLt.of_notFb (onlyQ_rootOO t sMT _ _ _) hT y3 h3
        refine (askG_then t w.gr0 hW.1.gr0_ok w.chal
            (fun α => (⟨i, .f5 ρ0, y3.1, embP (.inl (.inl α))⟩ : FbIn lam L t))
            (fun g hg x y e => hq0 g hg (congrArg FbIn.plain e)) _ _ _
            (fun ans => (ublkG s A W).map fun l => (v.blocks ++ [ans.1]) ++ l) y3.2
            (fun β => t3.new _ rfl) fun ans T' hT' => ?_).trans
          (hsh v.blocks hk)
        exact chainOU_blocks n s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
          (.shr (List.ofFn ans.2)) (σ0.2 (a.kind.shOf (w.chal ans.1)))
          (vs.map (Option.map (hearO w ans.1))) (hearO w ans.1 v) T' hW.2 hE' hF'
          (by simp [hv]) (t3.left t (fun _ => rfl) hT')

end Rounds

/-! ## 3. One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

/-- under the hypotheses below, the hash blocks that slot number n, which holds a request, sees in
one execution are independent, each with the distribution of its round -/
theorem blocks_proveOUG (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hE : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh ∨ Function.Injective embP) (hF : Q.ann.Fmt)
    (xs : List (Option Y)) (n : ℕ) (x : Y) (hn : xs[n]? = some (some x))
    (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    ((proveOU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map
        (fun x => x.1.getD n []) =
      ublkG Q.loc.shape Q.ann wq.sh := by
  unfold proveOU
  rw [OComp.runLazy_bind, PMF.map_bind]
  refine bind_const_supp fun y0 h0 => ?_
  have t0 := FbLt.of_notFb (onlyQ_drawO t wp.coin0) hT y0 h0
  rw [OComp.runLazy_bind, PMF.map_bind]
  refine bind_const_supp fun y1 h1 => ?_
  have t1 := FbLt.of_notFb
    (onlyQ_eachO (onlyQ_optO fun x => onlyQ_initO sFS t Q H wp xin w y0.1 (some x)) xs) t0 y1 h1
  obtain ⟨o, e, ho⟩ := supp_eachO_entry _
    (fun (a' : Option Y) (b' : Option (VSlot lam K X Q.loc.shape)) =>
      ∀ v, a' = some v → ∃ v', b' = some v' ∧ v'.blocks = [])
    (supp_optO _ (fun _ (v' : VSlot lam K X Q.loc.shape) => v'.blocks = []) fun a' T' =>
      supp_initO sFS Q H wp xin w y0.1 (some a') T')
    n xs (some x) hn y0.2 y1 h1
  obtain ⟨v, rfl, b⟩ := ho x rfl
  rw [chainOU_blocks sMT t cms depthReq n Q.loc.shape Q.ann wq.sh embS embP 0 .first _
        y1.1 v y1.2 hW hE hF e t1, b]
  exact PMF.map_id _

/-- Under the hypotheses below, the proof string of a slot with a request is `none` with exactly the
probability of the withheld set, if the withheld set does not depend on the proof-of-work bits. -/
theorem pr_noneAtUG (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh)
    (hE : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh ∨ Function.Injective embP) (hF : Q.ann.Fmt)
    (xs : List (Option Y)) (n : ℕ) (x : Y) (hn : xs[n]? = some (some x))
    (hwh : ∀ ρ, ρ ∈ H.one.withheld w x ↔ RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ ∈ H.one.withheld w x)
    (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    pr (((proveOU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | noneAt Q H wq wp w x n bss = true} =
      prRho (H.one.withheld w x) := by
  have h := blocks_proveOUG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW hE hF xs n x hn T hT
  have e : {bss : List (List (Blk lam K)) | noneAt Q H wq wp w x n bss = true} =
      (fun bss : List (List (Blk lam K)) =>
          RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n [])))
        ⁻¹' (H.one.withheld w x) := by
    ext bss
    simp only [noneAt, Set.mem_setOf_eq, decide_eq_true_eq, Set.mem_preimage]
    exact hwh _
  have e2 : prRho (H.one.withheld w x) =
      pr ((unif (Rho Q.loc.shape)).map (RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh))
        (H.one.withheld w x) := by
    rw [pr_map]
    exact congrArg _ (Set.ext fun ρ => hwh ρ)
  rw [e, ← pr_map, PMF.map_comp, e2, ← zero_ublkG Q.loc.shape Q.ann wq.sh hW, ← h, PMF.map_comp]
  rfl

theorem pr_noneAtU (hW : RoundsQueryLayout.OK Q.loc.shape Q.ann wq.sh) (hF : Q.ann.Fmt) (xs : List (Option Y))
    (n : ℕ) (x : Y) (hn : xs[n]? = some (some x)) (T : Table (spec lam K L)) (hT : FbLt t 0 T) :
    pr (((proveOU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).runLazy T).map Prod.fst)
        {bss | noneAt Q H wq wp w x n bss = true} =
      prRho (H.one.withheld w x) :=
  pr_noneAtUG sMT sFS t Q H wq wp embS embP xin depthReq cms w hW.toG (Or.inl hW) hF xs n x hn
    (fun ρ => by rw [zero_of_ok _ _ _ hW]) T hT

end Prove

/-! ## 4. The small experiment -/

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

theorem pr_batOU (hW : W.OK) (hF : L.onlineBatch.ann.Fmt) (xs : List X) (a : Fin L.maxBatchSize)
    (x : X) (hx : xs[a.val]? = some x) (nd : L.EncodingRandomness × Dig lam)
    (T : Table (spec lam W.K L)) (hT : FbLt Tag.onl 0 T) :
    pr (((batOU W WP p i xs a x nd).runLazy T).map Prod.fst) {b | b = true} =
      prRho (L.honestOnlineBatchProver.one.withheld (i, nd.1) x) := by
  unfold batOU
  rw [OComp.runLazy_bind, PMF.map_bind, pr_bind]
  refine (expect_congr_support _ fun y hy => ?_).trans (expect_const _ _)
  rw [pr_bind_pure]
  refine Eq.trans (congrArg (pr _) (Set.ext fun bss => ?_))
    (pr_noneAtU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [nd.2] (i, nd.1)
      hW.B.sh hF (slotsOfReq y.1 xs) (y.1 a).val x (by rw [Cmpl.getElem?_slotsOfReq, hx]) y.2
      (FbLt.of_notFb (onlyQ_drawO Tag.onl WP.perm) hT y hy))
  show badAt _ _ _ _ _ _ _ bss = true ↔ noneAt _ _ _ _ _ _ _ bss = true
  rw [badAt_of_ok _ _ _ _ _ hW.B.sh]

/-- Under the hypotheses below: the small experiment shows `none` with probability at most `M.pO`.
-/
theorem unifBU {Ryes Rno : I → X → Prop} {M : LH.Nums} (h : L.Props Ryes Rno M)
    (hW : W.OK) (hF : L.onlineBatch.ann.Fmt) (xs : List X) (a : Fin L.maxBatchSize) (x : X)
    (hxa : xs[a.val]? = some x) (hx : Ryes i x) :
    pr (RBU W WP p i xs a x).law {b | b = true} ≤ M.pO :=
  pr_bind_le _ _ _ _ _ fun y hy =>
    (le_of_eq (pr_batOU W WP p i hW hF xs a x hxa y.1 y.2
          (FbLt.of_notFb (onlyQ_nodeO W WP p i Tag.onl) (fbLt_empty _) y hy))).trans
      (h.complete.prB _ _ hx)

end Scheme

end Compile.Batch.CompleteUUnif
