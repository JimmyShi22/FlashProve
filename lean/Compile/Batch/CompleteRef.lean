-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteRef.lean: for fixed oracle functions, values that the honest programs with
tokens compute have the distributions of their counterparts without tokens
(Compile/Batch/CompleteRefDefs.lean), each under the hypotheses of its statement. First part: the
calculus of distributions (`LawS`), trees, slots, rounds (words of this library: lean/GLOSSARY.md).
Towards completeness of the compiled scheme whose rounds may have proof-of-work bits.

The aim of this file and the two after it (Compile/Batch/CompleteRefChain.lean,
Compile/Batch/CompleteRefStarG.lean): under `RealFam`, a run of the honest committer's program of
the compiled scheme (`CpX`, Compile/Batch/StarX.lean) shows `none`, or a failed search ("bad":
`badAt`), in a given place with the distribution of a small experiment without tokens. A token is a
position in a store (the head of Compile/Batch/CompleteRefDefs.lean); the store is the list of
strings for which the tokens stand; an erased program (`erase`) works on strings in the store. The
lemmas on rounds with a Fiat-Shamir query assume `RealFam` (Compile/Batch/CompleteChain.lean).

  Part 1  distributions of a function of the output and of the store of an erased program (`LawS`)
  Part 2  `commitT`, `reqT`, `commitE` against `rootO`, `reqRootO`, `rootEO`
  Part 3  `slotLo`, `slotJoin`, `eachM`, `joinM` against `slotLoO`, `slotJoinO`, `eachO`
  Part 4  the rounds of `chainO`, unfolded

Notation: `lam`, `K`: natural numbers; a `Dig lam` (Iop/Wire.lean): a hash block (a digest or a
chaining value): lam bits; a `Blk lam K` (Compile/Batch/Prover.lean): `Fin K → Dig lam`; `L`: an
`BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with the honest sides;
`sMT`: a natural number: the length of the salt of a leaf (Compile/Batch/Verifier.lean); `t`: a
`Tag` (Compile/Oracles.lean): test, link or onl; `cms`: a `List (Dig lam)`: the external roots
(`verifyB`, Compile/Batch/Verifier.lean); `xin`: `Y → Option X`: `xin x` is the x of `recomputeChain`
(Compile/Batch/Verifier.lean): the whole instance (none: Test, Link); `dv lam vs`
(Compile/Batch/CompleteTree.lean): `Tok → Dig lam`: the digest for which a token stands; `nc`: an
`Option ℕ`: the number of the final attempt (`putO`, Compile/Batch/CompleteChain.lean); `embS`,
`embP` say how symbols and plain parts are written into queries (`verifyB`,
Compile/Batch/Verifier.lean).
-/
import Compile.Batch.CompleteRefDefs
import Compile.Batch.CompleteAcc
import Rom.Forget

noncomputable section

namespace Compile.Batch.Ref
open Iop Rom Prob Compile.Batch.Cmpl

/-! ## Part 1. Distributions -/

section Law
variable {S : OSpec} {sp : Split S} {α β γ δ : Type} (f : Fam S)

/-- μ is the distribution of φ of the output and the final store of the erased program c, started
with the store vs, over its coins, for fixed oracle functions. -/
def LawS (c : Step S sp α) (vs : List Bits) (φ : α → List Bits → β) (μ : PMF β) : Prop :=
  ((erase c vs).runEager f).map (fun o => φ o.1 o.2) = μ

variable {f}

theorem lawS_pure (a : α) (vs : List Bits) (φ : α → List Bits → β) :
    LawS f (Step.pure a : Step S sp α) vs φ (PMF.pure (φ a vs)) :=
  PMF.pure_map _ _

theorem tri_true' (c : Step S sp α) (vs : List Bits) : Tri f c vs fun _ _ => True := fun _ _ =>
  trivial

/-- A sequence: the distribution of the second part may depend on the first part through φ only. -/
theorem LawS.bind {c : Step S sp α} {g : α → Step S sp γ} {vs : List Bits} {φ : α → List Bits → β}
    {ψ : γ → List Bits → δ} {μ : PMF β} {ν : β → PMF δ} {Q : α → List Bits → Prop}
    (hc : LawS f c vs φ μ) (hQ : Tri f c vs Q)
    (hg : ∀ a vs', Q a vs' → LawS f (g a) vs' ψ (ν (φ a vs'))) :
    LawS f (c.bind g) vs ψ (μ.bind ν) := by
  unfold LawS at hc ⊢
  rw [erase_bind, OComp.runEager_bind, PMF.map_bind]
  have h := Rom.bind_congr_support ((erase c vs).runEager f)
    (f := fun a => PMF.map (fun o : γ × List Bits => ψ o.1 o.2) ((erase (g a.1) a.2).runEager f))
    (g := fun o => ν (φ o.1 o.2)) fun o ho => hg o.1 o.2 (hQ o ho)
  rw [h, ← hc, PMF.bind_map]
  rfl

/-- A first part on which the distribution of the second part does not depend can be dropped. -/
theorem LawS.bind_drop {c : Step S sp α} {g : α → Step S sp γ} {vs : List Bits}
    {ψ : γ → List Bits → δ} {ν : PMF δ} {Q : α → List Bits → Prop} (hQ : Tri f c vs Q)
    (hg : ∀ a vs', Q a vs' → LawS f (g a) vs' ψ ν) : LawS f (c.bind g) vs ψ ν := by
  unfold LawS
  rw [erase_bind, OComp.runEager_bind, PMF.map_bind]
  have h := Rom.bind_congr_support ((erase c vs).runEager f)
    (f := fun a => PMF.map (fun o : γ × List Bits => ψ o.1 o.2) ((erase (g a.1) a.2).runEager f))
    (g := fun _ => ν) fun o ho => hg o.1 o.2 (hQ o ho)
  rw [h, PMF.bind_const]

/-- If φ is always b, its distribution is the point mass at b. -/
theorem lawS_const {c : Step S sp α} {vs : List Bits} {φ : α → List Bits → β} {b : β}
    (h : Tri f c vs fun a vs' => φ a vs' = b) : LawS f c vs φ (PMF.pure b) := by
  unfold LawS
  rw [← PMF.bind_pure_comp]
  have h' := Rom.bind_congr_support ((erase c vs).runEager f)
    (f := PMF.pure ∘ fun o : α × List Bits => φ o.1 o.2) (g := fun _ => PMF.pure b)
    fun o ho => by rw [Function.comp_apply, h o ho]
  rw [h', PMF.bind_const]

/-- Two functions that agree on all outputs have the same distribution. -/
theorem LawS.congr_fun {c : Step S sp α} {vs : List Bits} {φ φ' : α → List Bits → β} {μ : PMF β}
    (h : LawS f c vs φ μ) (hQ : Tri f c vs fun a vs' => φ' a vs' = φ a vs') : LawS f c vs φ' μ := by
  unfold LawS at h ⊢
  rw [← h, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact Rom.bind_congr_support _ fun o ho => by
    rw [Function.comp_apply, Function.comp_apply, hQ o ho]

theorem LawS.congr {c : Step S sp α} {vs : List Bits} {φ : α → List Bits → β} {μ μ' : PMF β}
    (h : LawS f c vs φ μ) (e : μ = μ') :
    LawS f c vs φ μ' := e ▸ h

theorem LawS.map {c : Step S sp α} {vs : List Bits} {φ : α → List Bits → β} {μ : PMF β}
    (h : LawS f c vs φ μ) (ψ : β → γ) :
    LawS f c vs (fun a vs' => ψ (φ a vs')) (μ.map ψ) := by
  unfold LawS at h ⊢
  rw [← h, PMF.map_comp]
  rfl

theorem lawS_sample {n : ℕ} {k : Fin (n + 1) → Step S sp α} {vs : List Bits} {φ : α → List Bits → β}
    {ν : Fin (n + 1) → PMF β} (h : ∀ r, LawS f (k r) vs φ (ν r)) :
    LawS f (Step.sample n k) vs φ ((unif (Fin (n + 1))).bind ν) := by
  unfold LawS
  rw [erase_sample, OComp.runEager, PMF.map_bind]
  exact congrArg _ (funext h)

theorem lawS_fresh {l : ℕ} {k : Tok → Step S sp α} {vs : List Bits}
    {φ : α → List Bits → β} {ν : Fin (2 ^ l - 1 + 1) → PMF β}
    (h : ∀ r : Fin (2 ^ l - 1 + 1),
      LawS f (k vs.length) (vs ++ [List.ofFn fun i : Fin l => r.val.testBit i]) φ (ν r)) :
    LawS f (Step.fresh l k) vs φ ((unif (Fin (2 ^ l - 1 + 1))).bind ν) := by
  unfold LawS
  rw [erase_fresh, OComp.runEager, PMF.map_bind]
  exact congrArg _ (funext h)

theorem lawS_marked {o : S.ι} {t : Tok} {us : List Tok} {pt : Bits → List Bits → S.Dom o}
    {inj : ∀ vs, Function.Injective fun v => pt v vs} {k : sp.Vis o → Tok → Step S sp α}
    {vs : List Bits} {φ : α → List Bits → β} {μ : PMF β}
    (h : LawS f
      (k (sp.split o (f o (pt (vs.getD t []) (us.map fun u => vs.getD u [])))).1 vs.length)
      (vs ++ [List.ofFn (sp.split o (f o (pt (vs.getD t []) (us.map fun u => vs.getD u [])))).2])
      φ μ) :
    LawS f (Step.marked o t us pt inj k) vs φ μ := h

theorem lawS_plain {o : S.ι} {q : S.Dom o} {k : S.Rng o → Step S sp α} {vs : List Bits}
    {φ : α → List Bits → β} {μ : PMF β} (h : LawS f (k (f o q)) vs φ μ) :
    LawS f (Step.plain o q k) vs φ μ := h

theorem lawS_reveal {ts : List Tok} {k : List Bits → Step S sp α} {vs : List Bits}
    {φ : α → List Bits → β} {μ : PMF β} (h : LawS f (k (ts.map fun u => vs.getD u [])) vs φ μ) :
    LawS f (Step.reveal ts k) vs φ μ := h

end Law

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 2. Trees -/

theorem runEager_askV (o : OracleName) (q : domOf lam L o) :
    (askTypedOracle (K := K) (L := L) o q).runEager f = PMF.pure (f o q) := rfl

theorem runEager_freshO_bind {β : Type} (l : ℕ) (g : Bits → TypedOracleComputation lam K L β) :
    ((freshO l).bind g).runEager f =
      (unif (Fin (2 ^ l - 1 + 1))).bind fun r => (g (bitsOf l r)).runEager f := rfl

theorem runEager_drawO_bind {β γ : Type} (e : Enum β) (g : β → TypedOracleComputation lam K L γ) :
    ((drawO e).bind g).runEager f = (unif (Fin (e.n + 1))).bind fun r => (g (e.e r)).runEager f :=
  rfl

theorem lawS_leafT (sMT : ℕ) (b : Body L) (vs : List Bits) :
    LawS f (leafT (lam := lam) (K := K) sMT b) vs
      (fun o vs' => dv lam vs' o.2) ((leafO sMT b).runEager f) := by
  unfold leafT leafO
  rw [runEager_freshO_bind]
  refine lawS_fresh fun r => lawS_marked ((lawS_pure _ _ _).congr ?_)
  show PMF.pure _ = PMF.pure (f OracleName.leaf (⟨b, bitsOf sMT r⟩ : LeafIn L))
  congr 1
  refine (isDig_concat _ _).2.trans ?_
  show f OracleName.leaf (⟨b, (vs ++ [_]).getD vs.length []⟩ : LeafIn L) = _
  rw [getD_concat_length]
  rfl

theorem runEager_eachO_cons {σ τ : Type} (g : σ → TypedOracleComputation lam K L τ) (a : σ) (l : List σ) :
    (eachO g (a :: l)).runEager f =
      ((g a).runEager f).bind fun b =>
        ((eachO g l).runEager f).bind fun r => PMF.pure (b :: r) := by
  simp only [eachO, OComp.runEager_bind]
  rfl

theorem lawS_leavesT (sMT : ℕ) :
    ∀ (l : List (Body L)) (vs : List Bits),
      LawS f (leavesT (lam := lam) (K := K) sMT l) vs
        (fun o vs' => o.1.map (dv lam vs')) ((eachO (leafO sMT) l).runEager f)
  | [], vs => lawS_pure _ _ _
  | b :: t, vs => by
      rw [runEager_eachO_cons]
      refine LawS.bind (lawS_leafT f sMT b vs) (tri_leafT f sMT b vs) fun x vs1 hx => ?_
      refine LawS.bind (lawS_leavesT sMT t vs1) (tri_prefix _ vs1) fun r vs2 hp =>
        ((lawS_pure _ _ _).congr ?_)
      rw [List.map_cons, dv_of_prefix hp hx.2.1.1]

/-- an oracle algorithm that evaluates to a value -/
theorem runEager_of_evalsTo {β : Type} {c : TypedOracleComputation lam K L β} {b : β} (h : EvalsTo f c b) :
    c.runEager f = PMF.pure b := h

theorem runEager_levels_root (d : ℕ) (ds : List (Dig lam)) :
    ((levelsM (hashTreeNode (L := L) (K := K)) d ds).bind fun lv => OComp.pure (rootOf lv)).runEager f
      = PMF.pure (rootOf (levelsF (nodeFB f) d ds)) := by
  rw [OComp.runEager_bind,
    runEager_of_evalsTo f
      ((evaluates_eager f).levelsM (qN := hashTreeNode (L := L) (K := K)) (hN := nodeFB f)
        (fun a b => evalsTo_ask f OracleName.node (List.ofFn a, List.ofFn b)) d ds), PMF.pure_bind]
  rfl

/-- The root of a token tree has the distribution of rootO. -/
theorem lawS_commitT (sMT d : ℕ) (leaf : ℕ → Body L) (vs : List Bits) :
    LawS f (commitT (lam := lam) (K := K) sMT d leaf) vs
      (fun tr vs' => dv lam vs' tr.root) ((rootO sMT d leaf).runEager f) := by
  unfold rootO
  rw [OComp.runEager_bind]
  refine LawS.bind (lawS_leavesT f sMT _ vs) (tri_leavesT f sMT _ vs) fun x vs1 hx => ?_
  rw [runEager_levels_root]
  refine lawS_const
    (Tri.bind (tri_levelsT (tri_nodeT f) d x.1 vs1 hx.2.2.1) fun lv vs2 hlv => tri_pure_iff.2 ?_)
  have hlen : (x.1.map (dv lam vs1)).length = 2 ^ d := by
    rw [hx.2.2.2]
    simp [hx.1]
  exact rootOf_map (dv lam vs2) (nodeFB f) d lv _ hlen hlv.2

/-- The tree over a component that may have none: its root has the distribution of rootOO, and what
follows may depend on the tree through the root only. -/
theorem lawS_withTree {γ δ : Type} (sMT : ℕ) (has : Bool) (d : ℕ)
    (leaf : ℕ → Body L) (k : Option TTree → St lam K L γ) (vs : List Bits)
    (ψ : γ → List Bits → δ) (ν : Option (Dig lam) → PMF δ)
    (h : ∀ tr vs1,
      vs <+: vs1 → OTreeOK f sMT vs1 has tr d leaf → LawS f (k tr) vs1 ψ (ν (rootV lam vs1 tr))) :
    LawS f (withTree sMT has d leaf k) vs ψ
      (((rootOO (lam := lam) (K := K) sMT has d leaf).runEager f).bind ν) := by
  cases has with
  | true =>
    show LawS f ((commitT sMT d leaf).bind fun tr => k (some tr)) vs ψ
      ((((rootO sMT d leaf).bind fun rt => OComp.pure (some rt)).runEager f).bind ν)
    rw [OComp.runEager_bind, PMF.bind_bind]
    refine LawS.bind (lawS_commitT f sMT d leaf vs)
      (tri_commitT f sMT d leaf vs).with_prefix fun tr vs1 htr => ?_
    refine (h (some tr) vs1 htr.2 htr.1).congr ?_
    exact (PMF.pure_bind _ _).symm
  | false =>
    show LawS f (k none) vs ψ ((PMF.pure none).bind ν)
    rw [PMF.pure_bind]
    exact h none vs (List.prefix_refl _) trivial

/-- The trees over a component: their roots have the distribution of rootsOO, and what follows may
depend on the trees through the roots only. -/
theorem lawS_withTrees {γ δ : Type} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) (k : List TTree → St lam K L γ) (vs : List Bits)
      (ψ : γ → List Bits → δ) (ν : List (Dig lam) → PMF δ),
      (∀ trs vs1, vs <+: vs1 → OTreesOK f sMT vs1 ds trs leaf →
        LawS f (k trs) vs1 ψ (ν (rootsV lam vs1 trs))) →
      LawS f (withTrees sMT ds leaf k) vs ψ
        (((rootsOO (lam := lam) (K := K) sMT ds leaf).runEager f).bind ν)
  | [], _, k, vs, ψ, ν, h => by
      show LawS f (k []) vs ψ ((PMF.pure []).bind ν)
      rw [PMF.pure_bind]
      exact h [] vs (List.prefix_refl _) trivial
  | d :: ds, leaf, k, vs, ψ, ν, h => by
      show LawS f
        ((commitT sMT d (leaf 0)).bind fun tr =>
          withTrees sMT ds (fun n => leaf (n + 1)) fun trs => k (tr :: trs))
        vs ψ
        ((((rootO sMT d (leaf 0)).bind fun rt =>
          (rootsOO sMT ds fun n => leaf (n + 1)).bind fun rts =>
            OComp.pure (rt :: rts)).runEager f).bind ν)
      rw [OComp.runEager_bind, PMF.bind_bind]
      refine LawS.bind (lawS_commitT f sMT d (leaf 0) vs)
        (tri_commitT f sMT d (leaf 0) vs).with_prefix fun tr vs1 htr => ?_
      rw [OComp.runEager_bind, PMF.bind_bind]
      refine (lawS_withTrees sMT ds (fun n => leaf (n + 1)) (fun trs => k (tr :: trs)) vs1 ψ
        (fun rts => ν (dv lam vs1 tr.root :: rts)) fun trs vs2 hp h2 => ?_).congr ?_
      · have e : rootsV lam vs2 (tr :: trs) = dv lam vs1 tr.root :: rootsV lam vs2 trs :=
          congrArg (· :: rootsV lam vs2 trs) (dv_of_prefix hp (TTreeOK.isDig_root htr.1).1)
        show LawS f (k (tr :: trs)) vs2 ψ (ν (dv lam vs1 tr.root :: rootsV lam vs2 trs))
        rw [← e]
        exact h (tr :: trs) vs2 (htr.2.trans hp) ⟨htr.1.mono hp, h2⟩
      · exact congrArg (PMF.bind _) (funext fun rts => (PMF.pure_bind _ _).symm)

theorem runEager_eachO_ask (o : OracleName) : ∀ l : List (domOf lam L o),
    (eachO (fun c => askTypedOracle (L := L) (K := K) o c) l).runEager f = PMF.pure (l.map (f o))
  | [] => rfl
  | a :: l => by
      rw [runEager_eachO_cons, runEager_askV]
      refine (PMF.pure_bind _ _).trans ?_
      rw [runEager_eachO_ask o l]
      exact PMF.pure_bind _ _

theorem map_rleaf (vs : List Bits) :
    ∀ cs : List Tok, (∀ c ∈ cs, IsDig lam vs c) →
      List.map (f OracleName.rleaf) (List.map (fun c => vs.getD c []) cs) =
        List.map (rleafFB f) (List.map (dv lam vs) cs)
  | [], _ => rfl
  | c :: cs, h => by
      have e : f OracleName.rleaf (vs.getD c []) = rleafFB f (dv lam vs c) := by
        unfold rleafFB
        rw [← (h c (by simp)).2]
      show f OracleName.rleaf (vs.getD c []) :: _ = rleafFB f (dv lam vs c) :: _
      rw [e, map_rleaf vs cs fun u hu => h u (by simp [hu])]
      rfl

/-- The root of the request tree over 2^depthReq slot values that are digests is the value of
reqRootO on them. -/
theorem lawS_reqT (depthReq : ℕ) (cs : List Tok) (vs : List Bits)
    (h : ∀ c ∈ cs, IsDig lam vs c) (hl : cs.length = 2 ^ depthReq) :
    LawS f (reqT (lam := lam) (K := K) (L := L) depthReq cs) vs (fun rq vs' => dv lam vs' rq.root)
      ((reqRootO depthReq (cs.map fun c => vs.getD c [])).runEager f) := by
  have e : (reqRootO (lam := lam) (K := K) (L := L) depthReq
        (cs.map fun c => vs.getD c [])).runEager f =
      PMF.pure (rootOf (levelsF (rnodeFB f) depthReq ((cs.map (dv lam vs)).map (rleafFB f)))) := by
    unfold reqRootO
    rw [OComp.runEager_bind, runEager_eachO_ask f OracleName.rleaf]
    refine (PMF.pure_bind _ _).trans ?_
    rw [OComp.runEager_bind,
      runEager_of_evalsTo f
        ((evaluates_eager f).levelsM (qN := rnodeV (L := L) (K := K)) (hN := rnodeFB f)
          (fun a b => evalsTo_ask f OracleName.rnode (List.ofFn a, List.ofFn b)) depthReq _)]
    refine (PMF.pure_bind _ _).trans ?_
    show PMF.pure _ = _
    congr 3
    exact map_rleaf f vs cs h
  rw [e]
  refine lawS_const ((tri_reqT f depthReq cs vs h).mono fun rq vs' hrq => ?_)
  exact rootOf_map (dv lam vs') (rnodeFB f) depthReq rq.levels _ (by simpa using hl) hrq.2

theorem lawS_leafE (sMT : ℕ) (x : Body L × Bool) (vs : List Bits) :
    LawS f (leafE (lam := lam) (K := K) sMT x.1 x.2) vs
      (fun o _ => o.1) ((leafEO sMT x).runEager f) := by
  obtain ⟨b, bl⟩ := x
  unfold leafE leafEO
  cases bl with
  | true =>
    simp only [if_true]
    have h := LawS.bind (ψ := fun (o : Dig lam × Option (Tok × Tok)) (_ : List Bits) => o.1)
      (ν := PMF.pure)
      (g := fun x => (showT (lam := lam) (K := K) (L := L) x.2).bind fun d => Step.pure (d, some x))
      (lawS_leafT f sMT b vs) (tri_true' _ vs) fun x vs1 _ => lawS_reveal (lawS_pure _ _ _)
    rw [PMF.bind_pure] at h
    exact h
  | false =>
    simp only [Bool.false_eq_true, if_false]
    exact lawS_plain (lawS_pure _ _ _)

theorem lawS_leavesE (sMT : ℕ) :
    ∀ (l : List (Body L × Bool)) (vs : List Bits),
      LawS f (leavesE (lam := lam) (K := K) sMT l) vs
        (fun o _ => o.1) ((eachO (leafEO sMT) l).runEager f)
  | [], vs => lawS_pure _ _ _
  | (b, bl) :: t, vs => by
      rw [runEager_eachO_cons]
      refine LawS.bind (lawS_leafE f sMT (b, bl) vs) (tri_true' _ vs) fun x vs1 _ => ?_
      exact LawS.bind (lawS_leavesE sMT t vs1) (tri_true' _ vs1) fun r vs2 _ => lawS_pure _ _ _

/-- The root of a tree over an encoded index has the distribution of rootEO. -/
theorem lawS_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) (vs : List Bits) :
    LawS f (commitE (lam := lam) (K := K) sMT d leaf) vs
      (fun t _ => t.root) ((rootEO sMT d leaf).runEager f) := by
  unfold rootEO
  rw [OComp.runEager_bind]
  refine LawS.bind (lawS_leavesE f sMT _ vs) (tri_true' _ vs) fun x vs1 _ => ?_
  rw [runEager_levels_root]
  refine lawS_const (Tri.bind (tri_levelsE f d x.1 vs1) fun lv vs2 hlv => tri_pure_iff.2 ?_)
  rw [hlv.1]
  rfl

/-! ## Part 3. Slots and rounds -/

section Slot
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- the slot value as a string, once the chains have joined -/
def cOf (vs : List Bits) : PhT → SlotAcc lam K Y → Bits
  | .first, _ => []
  | .loc, _ => []
  | .shr _, acc => vs.getD acc.c []
  | .aft, acc => vs.getD acc.c []

/-- a slot, with the strings for which its tokens stand -/
def valOf {s : Shape} (vs : List Bits) (ph : PhT) (z : SlotSt lam K Y s) : VSlot lam K X s :=
  ⟨z.1, z.2.x.bind xin, vs.getD z.2.tk [], cOf vs ph z.2, z.2.blocks⟩

def valPh (vs : List Bits) : PhT → PhO
  | .first => .first
  | .loc => .loc
  | .shr tk0 => .shr (vs.getD tk0 [])
  | .aft => .aft

/-- the tokens of the slot and of the phase point into the store -/
def LPre (vs : List Bits) (ph : PhT) (acc : SlotAcc lam K Y) : Prop :=
  acc.tk < vs.length ∧ SlotPre vs ph acc

theorem LPre.mono {vs vs' : List Bits} (hp : vs <+: vs') {ph : PhT}
    {acc : SlotAcc lam K Y} (h : LPre vs ph acc) : LPre vs' ph acc :=
  ⟨lt_of_lt_of_le h.1 hp.length_le, h.2.mono hp⟩

theorem cOf_of_prefix {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc → cOf vs' ph acc = cOf vs ph acc
  | .first, _, _ => rfl
  | .loc, _, _ => rfl
  | .shr _, _, h => getD_of_prefix hp h.2.1
  | .aft, _, h => getD_of_prefix hp h.2.1

theorem valOf_of_prefix {s : Shape} {vs vs' : List Bits} (hp : vs <+: vs') {ph : PhT}
    {z : SlotSt lam K Y s} (h : LPre vs ph z.2) :
    valOf xin vs' ph z = valOf xin vs ph z := by
  unfold valOf
  rw [getD_of_prefix hp h.1, cOf_of_prefix hp h.2]

theorem valPh_of_prefix {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc → valPh vs' ph = valPh vs ph
  | .first, _, _ => rfl
  | .loc, _, _ => rfl
  | .shr _, _, h => by simp only [valPh, getD_of_prefix hp h.1]
  | .aft, _, _ => rfl

theorem headO_valOf {s : Shape} (vs : List Bits) (i : ℕ) : ∀ (ph : PhT) (z : SlotSt lam K Y s),
    headO L cms i (valPh vs ph) (valOf xin vs ph z) = headLo cms L vs (z.2.x.bind xin) i ph z.2
  | .first, _ => rfl
  | .loc, _ => rfl
  | .shr _, _ => rfl
  | .aft, _ => rfl

theorem cOf_afterLo {vs vs' : List Bits} (hp : vs <+: vs') (tl : Tok) :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc →
      ∀ (bl : List (Blk lam K)) (tr : List (Option TTree)) (tk : List Tok)
          (nn : List ℕ) (dd : List Tok),
        cOf vs' ph.afterLo (⟨acc.x, tl, acc.c, bl, tr, tk, nn, dd⟩ : SlotAcc lam K Y) =
          cOf vs ph acc
  | .first, _, _, _, _, _, _, _ => rfl
  | .loc, _, _, _, _, _, _, _ => rfl
  | .shr _, _, h, _, _, _, _, _ => getD_of_prefix hp h.2.1
  | .aft, _, h, _, _, _, _, _ => getD_of_prefix hp h.2.1

/-! ### The search over nonces -/

section Loop
variable (i : ℕ)

theorem lawS_fbT_iff {β δ : Type} (tk : Tok) (us : List Tok) (tr : Option TTree)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β) (vs : List Bits)
    (ψ : β → List Bits → δ) (μ : PMF δ) :
    LawS f (fbT t i tk us (tr.map TTree.root) hd hinj pl k) vs ψ μ ↔
    LawS f (k (f (OracleName.fb t)
          (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u []) (vs.getD tk []),
            rootV lam vs tr,
            pl⟩ : FbIn lam L t)).1 vs.length)
      (vs ++ [List.ofFn
            (f (OracleName.fb t)
              (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u [])
                  (vs.getD tk []),
                rootV lam vs tr,
                pl⟩ : FbIn lam L t)).2])
      ψ μ := by
  rw [← rt_eq_rootV us tr vs]
  exact Iff.rfl

theorem lawS_fbTw_iff {β δ : Type} (j : ℕ) (tk : Tok) (us : List Tok) (tr : Option TTree)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β) (vs : List Bits)
    (ψ : β → List Bits → δ) (μ : PMF δ) :
    LawS f (fbTw t j i tk us (tr.map TTree.root) hd hinj pl k) vs ψ μ ↔
    LawS f (k (f (OracleName.fbw t j)
          (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u []) (vs.getD tk []),
            rootV lam vs tr,
            pl⟩ : FbIn lam L t)).1 vs.length)
      (vs ++ [List.ofFn
            (f (OracleName.fbw t j)
              (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u [])
                  (vs.getD tk []),
                rootV lam vs tr,
                pl⟩ : FbIn lam L t)).2])
      ψ μ := by
  rw [← rt_eq_rootV us tr vs]
  exact Iff.rfl

theorem runEager_askW_zero {C P : Type} (g : GrW C P) (chal : Blk lam K → C)
    (q : ℕ → FbIn lam L t) (j : ℕ) :
    (askW g chal t q 0 j).runEager f = PMF.pure (f (OracleName.fb t) (q j)) := rfl

theorem runEager_askW_succ {C P : Type} (g : GrW C P) (chal : Blk lam K → C)
    (q : ℕ → FbIn lam L t) (n j : ℕ) :
    (askW g chal t q (n + 1) j).runEager f =
      if g.ok (chal (f (OracleName.fb t) (q j)).1) then PMF.pure (f (OracleName.fb t) (q j))
      else (askW g chal t q n (j + 1)).runEager f := by
  show (if g.ok (chal (f (OracleName.fb t) (q j)).1) then OComp.pure (f (OracleName.fb t) (q j))
      else askW g chal t q n (j + 1)).runEager f = _
  split_ifs <;> rfl

/-- under the hypotheses below, the attempts after the first have the distribution of askW -/
theorem lawS_fbW (hf : RealFam f) {β δ C P : Type} (g : GrW C P) (chal : Blk lam K → C) (tk : Tok)
    (us : List Tok) (tr : Option TTree) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : ℕ → List Tok → Blk lam K → Tok → St lam K L β) (vs : List Bits) (ψ : β → List Bits → δ)
    (ν : (Fin K → Dig lam) × Dig lam → PMF δ) (h0 : Head lam X) (rt : Option (Dig lam))
    (hst : ∀ vs1, vs <+: vs1 →
      hd ((us ++ (tr.map TTree.root).toList).map fun u => vs1.getD u []) (vs1.getD tk []) = h0 ∧
      rootV lam vs1 tr = rt)
    (h : ∀ (m : ℕ) (dd : List Tok) (vs1 : List Bits), vs <+: vs1 →
      LawS f (k m dd (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t)).1 vs1.length)
        (vs1 ++ [List.ofFn (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t)).2]) ψ
        (ν (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t)))) :
    ∀ (n j : ℕ) (dd : List Tok) (vs1 : List Bits), vs <+: vs1 →
      LawS f (fbW g chal t i tk us (tr.map TTree.root) hd hinj emb α k n j dd) vs1 ψ
        (((askW g chal t (fun m => (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t))
          n (j + 1)).runEager f).bind ν)
  | 0, j, dd, vs1, hp => by
      rw [fbW, lawS_fbTw_iff, (hst vs1 hp).1, (hst vs1 hp).2, hf, runEager_askW_zero]
      exact (h (j + 1) dd vs1 hp).congr (PMF.pure_bind _ _).symm
  | n + 1, j, dd, vs1, hp => by
      rw [fbW, lawS_fbTw_iff, (hst vs1 hp).1, (hst vs1 hp).2, hf, runEager_askW_succ]
      by_cases hok : g.ok
          (chal (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put (j + 1) α)⟩ : FbIn lam L t)).1) = true
      · rw [if_pos hok, if_pos hok]
        exact (h (j + 1) dd vs1 hp).congr (PMF.pure_bind _ _).symm
      · rw [if_neg hok, if_neg hok]
        exact lawS_fbW hf g chal tk us tr hd hinj emb α k vs ψ ν h0 rt hst h n (j + 1)
          _ _ (hp.trans (List.prefix_append _ _))

/-- Under the hypotheses below, a Fiat-Shamir query with proof-of-work bits or without has the
distribution of askG: what follows is run on the final attempt's answer, and may depend on the
search through that answer only. -/
theorem lawS_fbG (hf : RealFam f) {β δ C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C)
    (tk : Tok) (us : List Tok) (tr : Option TTree) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) (vs : List Bits)
    (ψ : β → List Bits → δ) (ν : (Fin K → Dig lam) × Dig lam → PMF δ) (h0 : Head lam X)
    (rt : Option (Dig lam))
    (hst : ∀ vs1, vs <+: vs1 →
      hd ((us ++ (tr.map TTree.root).toList).map fun u => vs1.getD u []) (vs1.getD tk []) = h0 ∧
      rootV lam vs1 tr = rt)
    (h : ∀ (nc : Option ℕ) (dd : List Tok) (vs1 : List Bits), vs <+: vs1 →
      LawS f (k nc dd (f (OracleName.fb t) (⟨i, h0, rt, emb (putO gr nc α)⟩ : FbIn lam L t)).1 vs1.length)
        (vs1 ++ [List.ofFn (f (OracleName.fb t) (⟨i, h0, rt, emb (putO gr nc α)⟩ : FbIn lam L t)).2]) ψ
        (ν (f (OracleName.fb t) (⟨i, h0, rt, emb (putO gr nc α)⟩ : FbIn lam L t)))) :
    LawS f (fbG gr chal t i tk us (tr.map TTree.root) hd hinj emb α k) vs ψ
      (((askG gr chal t (fun α' => (⟨i, h0, rt, emb α'⟩ : FbIn lam L t)) α).runEager
        f).bind ν) := by
  have e := hst vs (List.prefix_refl _)
  cases gr with
  | none =>
      rw [fbG_none, lawS_fbT_iff, e.1, e.2]
      exact (h none [] vs (List.prefix_refl _)).congr (PMF.pure_bind _ _).symm
  | some g =>
      show LawS f (fbTG g chal t i tk us (tr.map TTree.root) hd hinj emb α fun m => k (some m)) vs ψ
        (((askW g chal t (fun m => (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t))
          g.more 0).runEager f).bind ν)
      unfold fbTG
      split
      · rename_i hm
        rw [lawS_fbT_iff, e.1, e.2, hm, runEager_askW_zero]
        exact (h (some 0) [] vs (List.prefix_refl _)).congr (PMF.pure_bind _ _).symm
      · rename_i n hm
        rw [lawS_fbT_iff, e.1, e.2, hm, runEager_askW_succ]
        by_cases hok : g.ok (chal (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put 0 α)⟩ : FbIn lam L t)).1) =
          true
        · rw [if_pos hok, if_pos hok]
          exact (h (some 0) [] vs (List.prefix_refl _)).congr (PMF.pure_bind _ _).symm
        · rw [if_neg hok, if_neg hok]
          exact lawS_fbW f t i hf g chal tk us tr hd hinj emb α (fun m => k (some m)) vs ψ ν h0 rt
            hst (fun m dd vs1 hp => h (some m) dd vs1 hp) n 0 _ _ (List.prefix_append _ _)

end Loop

variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
  (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- Under `RealFam` and `LPre`, a local round in one slot has the distribution of slotLoO. -/
theorem lawS_slotLo (hf : RealFam f) (ph : PhT) (z : SlotSt lam K Y (r :: s))
    (vs : List Bits) (hpre : LPre vs ph z.2) :
    LawS f (slotLo sMT t cms xin a w emb plJ i ph z) vs (fun z' vs' => valOf xin vs' ph.afterLo z')
      ((slotLoO sMT t cms a w emb plJ i (valPh vs ph) (valOf xin vs ph z)).runEager f) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  unfold slotLoO slotLo
  rw [OComp.runEager_bind]
  refine lawS_withTree f sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1)
    _ vs _ _ fun tr vs1 hp htr => ?_
  rw [OComp.runEager_bind, headO_valOf]
  have key : ∀ (nc : Option ℕ) (dd : List Tok) (vs2 : List Bits), vs1 <+: vs2 →
      ∀ ans : (Fin K → Dig lam) × Dig lam,
        LawS f (Step.pure
            ((k (w.chal ans.1),
              ⟨acc.x, vs2.length, acc.c, acc.blocks ++ [ans.1], acc.trees ++ [tr],
                acc.toks ++ [vs2.length], nc.toList ++ acc.nons,
                dd ++ acc.dead⟩) : SlotSt lam K Y s) : St lam K L (SlotSt lam K Y s))
          (vs2 ++ [List.ofFn ans.2]) (fun z' vs' => valOf xin vs' ph.afterLo z')
          ((OComp.pure
            (⟨k (w.chal ans.1), acc.x.bind xin, List.ofFn ans.2, cOf vs ph acc,
              acc.blocks ++ [ans.1]⟩ : VSlot lam K X s) : TypedOracleComputation lam K L _).runEager f) := by
    intro nc dd vs2 hp2 ans
    refine (lawS_pure _ _ _).congr ?_
    show PMF.pure _ = PMF.pure _
    congr 1
    unfold valOf
    rw [getD_concat_length, cOf_afterLo ((hp.trans hp2).trans (List.prefix_append _ _)) _ hpre.2]
  cases ph with
  | first =>
    simp only [fbSlotG]
    exact lawS_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _ _
      (headLo cms L vs (acc.x.bind xin) i .first acc) (rootV lam vs1 tr)
      (fun vs2 hp2 =>
        ⟨by simp only [headLo, getD_of_prefix (hp.trans hp2) hpre.1], htr.rootV_of_prefix hp2⟩)
      (fun nc dd vs2 hp2 => key nc dd vs2 hp2 _)
  | loc =>
    simp only [fbSlotG]
    exact lawS_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _ _
      (headLo cms L vs (acc.x.bind xin) i .loc acc) (rootV lam vs1 tr)
      (fun vs2 hp2 =>
        ⟨by simp only [headLo, getD_of_prefix (hp.trans hp2) hpre.1], htr.rootV_of_prefix hp2⟩)
      (fun nc dd vs2 hp2 => key nc dd vs2 hp2 _)
  | shr tk0 =>
    simp only [fbSlotG]
    exact lawS_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _ _
      (headLo cms L vs (acc.x.bind xin) i (.shr tk0) acc) (rootV lam vs1 tr)
      (fun vs2 hp2 => ⟨by
        simp only [headLo, ← getD_of_prefix (hp.trans hp2) hpre.2.1,
          ← getD_of_prefix (hp.trans hp2) hpre.2.2.1]
        rfl, htr.rootV_of_prefix hp2⟩) (fun nc dd vs2 hp2 => key nc dd vs2 hp2 _)
  | aft =>
    simp only [fbSlotG]
    exact lawS_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _ _
      (headLo cms L vs (acc.x.bind xin) i .aft acc) (rootV lam vs1 tr)
      (fun vs2 hp2 =>
        ⟨by simp only [headLo, getD_of_prefix (hp.trans hp2) hpre.1], htr.rootV_of_prefix hp2⟩)
      (fun nc dd vs2 hp2 => key nc dd vs2 hp2 _)

/-- If the slot's token tk is in the store, the joining round in one slot has the distribution of
slotJoinO. The slot is seen as in the phase after the round (tk0 is any token). -/
theorem lawS_slotJoin (tk0 : Tok) (z : SlotSt lam K Y (r :: s))
    (vs : List Bits) (hpre : z.2.tk < vs.length) :
    LawS f (slotJoin sMT t a w emb plJ i z) vs (fun z' vs' => valOf xin vs' (.shr tk0) z')
      ((slotJoinO sMT t a w emb plJ i (valOf xin vs .loc z)).runEager f) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  unfold slotJoinO slotJoin
  rw [OComp.runEager_bind]
  refine lawS_withTree f sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1)
    _ vs _ _ fun tr vs1 hp htr => ?_
  unfold gT
  refine lawS_marked ((lawS_pure _ _ _).congr ?_)
  show PMF.pure _ = PMF.pure _
  congr 1
  unfold valOf
  simp only [cOf]
  rw [getD_concat_length,
    getD_of_prefix (List.prefix_append _ _) (lt_of_lt_of_le hpre hp.length_le),
    getD_of_prefix hp hpre]
  cases tr <;> rfl

end Slot

/-! ### All slots -/

section All

/-- run g in each slot, under the hypotheses below: the strings of all slots have the distribution
of eachO -/
theorem lawS_eachM {σ τ σ' τ' : Type} (g : σ → St lam K L τ) (go : σ' → TypedOracleComputation lam K L τ')
    (val : List Bits → σ → σ') (val' : List Bits → τ → τ') (Pre : σ → List Bits → Prop)
    (Post : τ → List Bits → Prop)
    (hPre : ∀ z vs vs', vs <+: vs' → Pre z vs → Pre z vs' ∧ val vs' z = val vs z)
    (hPost : ∀ z' vs vs', vs <+: vs' → Post z' vs → val' vs' z' = val' vs z')
    (hT : ∀ z vs, Pre z vs → Tri f (g z) vs fun z' vs' => Post z' vs')
    (hg : ∀ z vs,
      Pre z vs → LawS f (g z) vs (fun z' vs' => val' vs' z') ((go (val vs z)).runEager f)) :
    ∀ (zs : List σ) (vs : List Bits), (∀ z ∈ zs, Pre z vs) →
      LawS f (eachM g zs) vs (fun zs' vs' => zs'.map (val' vs'))
        ((eachO go (zs.map (val vs))).runEager f)
  | [], vs, _ => lawS_pure _ _ _
  | z :: zs, vs, h => by
      rw [List.map_cons, runEager_eachO_cons]
      refine LawS.bind (hg z vs (h z (by simp)))
        (hT z vs (h z (by simp))).with_prefix fun z' vs1 hz' => ?_
      have e : zs.map (val vs) = zs.map (val vs1) :=
        List.map_congr_left fun u hu => ((hPre u vs vs1 hz'.2 (h u (by simp [hu]))).2).symm
      rw [e]
      refine LawS.bind
        (lawS_eachM g go val val' Pre Post hPre hPost hT hg zs vs1 fun u hu =>
          (hPre u vs vs1 hz'.2 (h u (by simp [hu]))).1)
        (tri_prefix _ vs1) fun r vs2 hp => ((lawS_pure _ _ _).congr ?_)
      rw [List.map_cons, hPost z' vs1 vs2 hp hz'.1]

end All

section Join
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem valOf_shr_of_prefix {s : Shape} {vs vs' : List Bits} (hp : vs <+: vs') (tk0 tk0' : Tok)
    {z : SlotSt lam K Y s} (h1 : z.2.tk < vs.length) (h2 : z.2.c < vs.length) :
    valOf xin vs' (.shr tk0') z = valOf xin vs (.shr tk0) z := by
  unfold valOf
  simp only [cOf]
  rw [getD_of_prefix hp h1, getD_of_prefix hp h2]

variable {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- the joining round in all slots -/
theorem lawS_joinM (tk0 : Tok) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits), (∀ z ∈ zs, z.2.tk < vs.length) →
      LawS f (joinM sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs) vs
        (fun o vs' => o.1.map (valOf xin vs' (.shr tk0)))
        ((eachO (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i)
          (zs.map (valOf xin vs .loc))).runEager f)
  | [], vs, _ => lawS_pure _ _ _
  | z :: zs, vs, h => by
      rw [List.map_cons, runEager_eachO_cons]
      have hz : z.2.tk < vs.length := h z (by simp)
      obtain ⟨⟨m, k⟩, acc⟩ := z
      refine LawS.bind (lawS_slotJoin f sMT t xin a w _ _ i tk0 _ vs hz)
        (tri_slotJoin f sMT t a w _ _ i m k acc vs hz).with_prefix fun z' vs1 hz' => ?_
      obtain ⟨⟨tr, c, q, -, -, hc, -, rfl⟩, hp1⟩ := hz'
      have e : zs.map (valOf xin vs .loc) =
          zs.map (valOf xin vs1 .loc) := List.map_congr_left fun u hu =>
        (valOf_of_prefix xin hp1 (ph := .loc) ⟨h u (by simp [hu]), h u (by simp [hu])⟩).symm
      rw [e]
      refine LawS.bind
        (lawS_joinM tk0 zs vs1 fun u hu => lt_of_lt_of_le (h u (by simp [hu])) hp1.length_le)
        (tri_prefix _ vs1) fun o vs2 hp => ((lawS_pure _ _ _).congr ?_)
      exact congrArg (fun v => PMF.pure (v :: List.map (valOf xin vs2 (.shr tk0)) o.1))
        (valOf_shr_of_prefix xin hp tk0 tk0
          (z := (((m, k),
              ⟨acc.x, acc.tk, c, acc.blocks, acc.trees ++ [tr], acc.toks ++ [c],
                acc.nons, acc.dead⟩) : SlotSt lam K Y (r :: s)))
          (lt_of_lt_of_le hz hp1.length_le) hc.1)

end Join

/-! ## Part 4. The rounds of chainO, unfolded -/

section UnfoldO
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (depthReq : ℕ) {r : Round} {s : Shape}
  (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m0 : a.M0)
  (k0 : a.kind.Sh r.Chal → SStrat s A) (vs : List (VSlot lam K X (r :: s)))

theorem chainO_lo (hk : a.kind = .lo) (ph : PhO) :
    chainO sMT t cms depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) vs =
      (eachO (slotLoO sMT t cms a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        vs).bind fun vs' =>
          chainO sMT t cms depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) vs' := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl

theorem chainO_join (hk : a.kind = .sh) :
    chainO sMT t cms depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) vs =
      (eachO (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i)
        vs).bind fun vs1 =>
          (reqRootO depthReq (vs1.map fun v => v.c)).bind fun rq =>
          (root0O sMT a w (fun p => embS (.inl p)) m0).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f4 cms (List.ofFn rq), rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 m0)).bind fun ans =>
          chainO sMT t cms depthReq s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (.shr (List.ofFn ans.2))
              (k0 (a.kind.shOf (w.chal ans.1))) (vs1.map (hearO w ans.1)) := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

theorem chainO_shr (hk : a.kind = .sh) (ρ0 : Bits) :
    chainO sMT t cms depthReq (r :: s) (a, A) (w, W) embS embP i (.shr ρ0) (m0, k0) vs
      = (root0O sMT a w (fun p => embS (.inl p)) m0).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f5 ρ0, rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 m0)).bind fun ans =>
          chainO sMT t cms depthReq s A W (fun p => embS (.inr p))
              (fun z => embP (.inr z)) (i + 1) (.shr (List.ofFn ans.2))
              (k0 (a.kind.shOf (w.chal ans.1))) (vs.map (hearO w ans.1)) := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

end UnfoldO

end Compile.Batch.Ref
