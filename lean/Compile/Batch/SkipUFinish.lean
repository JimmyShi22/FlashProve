-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SkipUFinish.lean: from the Fiat-Shamir chains to the proof strings, and one execution
of the two provers, in the relation `Rom.Skip`. Third part of the proof of `Spec.skipPp`
(Compile/Batch/SpecSkipU.lean). (Words of this library: lean/GLOSSARY.md.)

After the chains the two provers `proveB` (Compile/Batch/Prover.lean) and `proveBU`
(Compile/Batch/ProverU.lean) run the same term, `finishAll`, on slots and shared parts that
correspond (Compile/Batch/SkipUChain.lean). A proof string is a function of the strings that a
reveal shows, which are the same on both sides, of hash blocks and numbers of final attempts, which
are equal, and of lengths of corresponding lists, which agree. At the start of an empty slot the
first program alone samples coins and a salt, which is dead (without a counterpart: `Wd.dd`,
Rom/Skip.lean). (The fields `dead` of `SlotAcc` and `Acc0`, Compile/Batch/Prover.lean, are something
else.)

Notation: `Rom.Skip Q w c₁ c₂` (Rom/Skip.lean): a `Prop` on a `Rom.Wd` and two programs (`Step`,
Rom/Defer.lean); "Q: what holds of the two results, with the correspondence at the end."; `w`: a
`Rom.Wd` (Rom/Skip.lean): "how the tokens of two programs correspond"; `RL`: "two lists of tokens
correspond, entry by entry"; `RT`: "two token trees correspond"; `ROT`: "two optional token trees
correspond"; `SelfE`: "the tokens of a tree over an encoded index denote the same strings in both
programs" (the four: Compile/Batch/SkipUTree.lean); `FullR`: "what two full slots have gathered
corresponds"; `RS`: "two slots correspond while the chains run"; `RAcc`: "two slots correspond at
the end of the chains"; `RA0`: "what the two shared parts have gathered corresponds" (the four:
Compile/Batch/SkipUChain.lean).

Limits: nothing about probability and nothing about runs: these are statements about programs as
terms.
-/
import Compile.Batch.SkipUChain

noncomputable section

namespace Compile.Batch.SkipU
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. What a slot shows -/

theorem rl_optRoot {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {a b : Option TTree}, ROT w a b → RL w (a.map TTree.root).toList (b.map TTree.root).toList
  | some _, some _, h => .cons (RT.root h0 h) .nil
  | none, none, _ => .nil

theorem rl_rootToks {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {l₁ l₂ m₁ m₂ : List (Option TTree)}, List.Forall₂ (ROT w) l₁ l₂ →
      List.Forall₂ (ROT w) m₁ m₂ → RL w (rootToks l₁ m₁) (rootToks l₂ m₂)
  | _, _, _, _, .nil, _ => by simp only [rootToks]; exact .nil
  | _, _, _, _, .cons _ _, .nil => by simp only [rootToks]; exact .nil
  | _, _, _, _, .cons h t, .cons h' t' =>
    f2_app (f2_app (rl_optRoot h0 h) (rl_optRoot h0 h')) (rl_rootToks h0 t t')

theorem rl_optPath {w : Wd} (h0 : w.ρ 0 0) (j : ℕ) :
    ∀ {a b : Option TTree}, ROT w a b →
      RL w ((a.map fun rq => pathOf rq.levels j).getD [])
        ((b.map fun rq => pathOf rq.levels j).getD [])
  | some _, some _, h => rl_pathOf h0 h.levels j
  | none, none, _ => .nil

theorem rl_optAnc {w : Wd} (h0 : w.ρ 0 0) (j : ℕ) : ∀ {a b : Option TTree}, ROT w a b →
    RL w ((a.map fun rq => ancOf rq.levels j).getD []) ((b.map fun rq => ancOf rq.levels j).getD [])
  | some _, some _, h => rl_ancOf h0 h.levels j
  | none, none, _ => .nil

/-! ## Part 2. The openings -/

theorem sk_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    {tr₁ tr₂ : TTree} (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (js : List ℕ) {w : Wd}, w.ρ 0 0 → RT w tr₁ tr₂ →
      Skip (fun _ g₁ g₂ => g₁ = g₂) w (opensComp (K := K) (L := L) dec posAt o tr₁ isRead f js)
        (opensComp dec posAt o tr₂ isRead f js)
  | [], _, _, _ => .pure rfl
  | j :: js, w, h0, h => by
    unfold opensComp
    refine Skip.bind' (sk_opensComp dec posAt o isRead f js h0 h) fun v f₁ f₂ hv hf => ?_
    subst hf
    cases posAt j with
    | none => exact .pure rfl
    | some p =>
      by_cases hr : isRead p = true
      · simp only [hr, if_true]
        refine Skip.bind' (sk_openT (hv.ρ _ _ h0) (h.mono hv) j _) fun _ op op' _ e => ?_
        subst e
        exact .pure rfl
      · simp only [hr, Bool.false_eq_true, if_false]
        exact .pure rfl

theorem sk_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    {w : Wd} (h0 : w.ρ 0 0) :
    ∀ {tr₁ tr₂ : Option TTree}, ROT w tr₁ tr₂ →
      Skip (fun _ g₁ g₂ => g₁ = g₂) w (opensOpt (K := K) (L := L) dec posAt depth o tr₁ isRead f)
        (opensOpt dec posAt depth o tr₂ isRead f)
  | some _, some _, h => sk_opensComp dec posAt o isRead f _ h0 h
  | none, none, _ => .pure rfl

/-- The openings of a component with a list of trees: the same in both programs, if the two lists of
trees correspond (`RLT`, Compile/Batch/SkipUTree.lean). Nothing is asked of the number of depths:
both programs get the same depths and equally many trees, so both stop at the same tree. -/
theorem sk_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) {w : Wd},
      w.ρ 0 0 → ∀ {trs₁ trs₂ : List TTree}, RLT w trs₁ trs₂ →
      Skip (fun _ g₁ g₂ => g₁ = g₂) w
        (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs₁ f)
        (opensTrees dec posAt o isRead k ds trs₂ f)
  | _, [], _, _, _, _, _, _ => .pure rfl
  | _, _ :: _, _, _, _, _, _, .nil => .pure rfl
  | k, _ :: ds, f, _, h0, _, _, .cons ht hts =>
    Skip.bind' (sk_opensTrees dec posAt o isRead (k + 1) ds f h0 hts) fun _ f₁ _ hv e =>
      e ▸ sk_opensComp dec (posAt k) o isRead f₁ _ (hv.ρ _ _ h0) (RT.mono hv ht)

theorem sk_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs₁ tjs₂ t0s₁ t0s₂ : List (Option TTree)) (isRead : OPos s → Bool) (w : Wd),
      w.ρ 0 0 → List.Forall₂ (ROT w) tjs₁ tjs₂ → List.Forall₂ (ROT w) t0s₁ t0s₂ →
      Skip (fun _ g₁ g₂ => g₁ = g₂) w (opensB (L := L) s A W τ tjs₁ t0s₁ isRead)
        (opensB s A W τ tjs₂ t0s₂ isRead)
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => .pure rfl
  | r :: s, (_, A), (wr, W), (m, _, τ), tjs₁, tjs₂, t0s₁, t0s₂, isRead, w, h0, hj, h0s => by
    unfold opensB
    refine Skip.bind'
      (sk_opensOpt wr.pt.decPos wr.posAt0 wr.depth0 m.1 _ _ h0
        (f2_headD (d₁ := none) (d₂ := none) trivial h0s))
      fun v f₁ f₂ hv e => ?_
    subst e
    refine Skip.bind'
      (sk_opensOpt wr.pt.decPos wr.posAtJ wr.depthJ m.1 _ _ (hv.ρ _ _ h0)
        (f2_headD (d₁ := none) (d₂ := none) trivial (ROTs.mono hv hj)))
      fun v₂ g₁ g₂ hv₂ e => ?_
    subst e
    have hw := Wd.le_trans hv hv₂
    refine Skip.bind'
      (sk_opensB s A W τ _ _ _ _ _ v₂ (hw.ρ _ _ h0)
        (f2_tail (ROTs.mono hw hj)) (f2_tail (ROTs.mono hw h0s)))
      fun _ k₁ k₂ _ e => ?_
    subst e
    exact .pure rfl

theorem selfE_getD {w : Wd} {trees : List (TreeH lam)} (h : ∀ tr ∈ trees, SelfE w tr) (j : ℕ) :
    SelfE w (trees.getD j ⟨[], []⟩) := by
  rw [List.getD_eq_getElem?_getD]
  cases hj : trees[j]? with
  | none => exact fun _ _ hs => nomatch hs
  | some tr => exact h tr (List.mem_of_getElem? hj)

theorem sk_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ (ps : List E.Pos) {w : Wd}, (∀ tr ∈ trees, SelfE w tr) →
      Skip (fun _ g₁ g₂ => g₁ = g₂) w (opensExtB (K := K) (L := L) we y trees isRead ps)
        (opensExtB we y trees isRead ps)
  | [], _, _ => .pure rfl
  | p :: ps, w, h => by
    unfold opensExtB
    refine Skip.bind' (sk_opensExtB we y trees isRead ps h) fun v f₁ f₂ hv e => ?_
    subst e
    by_cases hr : isRead p = true
    · simp only [hr, if_true]
      refine Skip.bind' (sk_openE ((selfE_getD h _).mono hv) _ _) fun _ op op' _ e => ?_
      subst e
      exact .pure rfl
    · simp only [hr, Bool.false_eq_true, if_false]
      exact .pure rfl

theorem sk_drawT {β : Type} (e : Enum β) (w : Wd) :
    Skip (fun _ a b => a = b) w (drawT (lam := lam) (K := K) (L := L) e) (drawT e) :=
  Skip.sample _ fun _ => .pure rfl

/-! ## Part 3. The proof strings -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (wt : Wt)

/-- Under the hypotheses below: the proof string of a full slot is the same in both programs. -/
theorem sk_finishSlot (c0 : H.Coin0) {a₁ a₂ : Acc0} (j : ℕ) (x : Y) (cj : H.Coin)
    {acc₁ acc₂ : SlotAcc lam K (Y × H.Coin)} {w : Wd} (h0 : w.ρ 0 0) (hT : ∀ tr ∈ trees, SelfE w tr)
    (ha : RA0 w a₁ a₂) (hf : FullR w acc₁ acc₂) :
    Skip (fun _ π₁ π₂ => π₁ = π₂) w (finishSlot (L := L) Q H wq wp trees wt c0 a₁ j x cj acc₁)
      (finishSlot Q H wq wp trees wt c0 a₂ j x cj acc₂) := by
  have hroots := rl_rootToks h0 hf.trees ha.trees
  have hpath := rl_optPath h0 j ha.req
  dsimp only [finishSlot]
  rw [hf.blocks, hroots.length_eq, hpath.length_eq, hf.nons, ha.nons]
  by_cases hw : rhoOf Q.loc.shape Q.ann wq.sh acc₂.blocks ∈ H.one.withheld wt x
  · rw [if_pos hw, if_pos hw]
    exact .pure rfl
  · rw [if_neg hw, if_neg hw]
    refine Skip.reveal
      (.cons (f2_headD h0 hf.toks)
        (f2_app (f2_app
            (f2_app
              (f2_app (f2_app (f2_app hroots hpath) (rl_optRoot h0 ha.req)) (rl_optAnc h0 j ha.req))
              hf.toks) ha.toks)
          (f2_app hf.dead ha.dead))) fun vs => ?_
    refine Skip.bind' (sk_opensB _ _ _ _ _ _ _ _ _ w h0 hf.trees ha.trees) fun v f₁ f₂ hv e => ?_
    subst e
    refine Skip.bind' (sk_opensExtB _ _ trees _ _ fun tr htr => (hT tr htr).mono hv)
      fun _ g₁ g₂ _ e => ?_
    subst e
    exact .pure rfl

/-- Under the hypotheses below: the proof strings of all slots are the same in both programs. -/
theorem sk_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) {a₁ a₂ : Acc0} :
    ∀ (j : ℕ) (zs₁ zs₂ : List (SlotAcc lam K (Y × H.Coin))) {w : Wd}, w.ρ 0 0 →
      (∀ tr ∈ trees, SelfE w tr) → RA0 w a₁ a₂ → List.Forall₂ (RAcc w) zs₁ zs₂ →
      Skip (fun _ π₁ π₂ => π₁ = π₂) w (finishAll (L := L) Q H wq wp trees wt fl c0 a₁ j zs₁)
        (finishAll Q H wq wp trees wt fl c0 a₂ j zs₂)
  | _, [], _, _, _, _, _, .nil => .pure rfl
  | j, acc₁ :: t₁, acc₂ :: t₂, w, h0, hT, ha, .cons hacc ht => by
    unfold finishAll
    refine Skip.bind' (Q := fun _ π₁ π₂ => π₁ = π₂) ?_ fun v π₁ π₂ hv e => ?_
    · cases hacc with
      | full y h₁ h₂ hf =>
        obtain ⟨x, cj⟩ := y
        simp only [h₁, h₂]
        cases fl j
        · exact .pure rfl
        · exact sk_finishSlot Q H wq wp trees wt c0 j x cj h0 hT ha hf
      | empty h₁ h₂ =>
        simp only [h₁, h₂]
        exact .pure rfl
    · subst e
      refine Skip.bind'
        (sk_finishAll fl c0 (j + 1) t₁ t₂ (hv.ρ _ _ h0) (fun tr htr => (hT tr htr).mono hv)
          (ha.mono hv) (ht.imp fun _ _ y => y.mono hv))
        fun _ r₁ r₂ _ e => ?_
      subst e
      exact .pure rfl

/-! ## Part 4. The start of a slot -/

/-- A slot at the start: if `w.ρ 0 0`, the two slots correspond. For an empty slot the first program
alone samples coins and a salt; the salt is dead. -/
theorem sk_initSlot (c0 : H.Coin0) (x : Option Y) {w : Wd} (h0 : w.ρ 0 0) :
    Skip (fun v z₁ z₂ => RS v (isShr .first) z₁ z₂) w
      (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp wt c0 x)
      (initSlotU sFS Q H wp wt c0 x) := by
  cases x with
  | some x =>
    show Skip _ w (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp wt c0 (some x))
      (initSlot sFS Q H wp wt c0 (some x))
    unfold initSlot
    refine Skip.bind' (sk_drawT wp.coin w) fun v cj cj' hv e => ?_
    subst e
    refine Skip.fresh' _ fun v' s₁ s₂ hv' hs => ?_
    exact .pure
      (.full (x, cj) rfl rfl ⟨hs, hv'.ρ _ _ (hv.ρ _ _ h0), rfl, .nil, .cons hs .nil, rfl, .nil⟩)
  | none =>
    show Skip _ w (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp wt c0 none)
      (Step.pure
        (Strat.dflt Q.loc.shape (),
          (⟨none, 0, 0, [], [], [], [], []⟩ : SlotAcc lam K (Y × H.Coin))))
    refine Skip.sampleL _ fun cj => ?_
    refine Skip.freshL' _ fun v s _ hs => ?_
    exact .pure (.empty rfl rfl hs fun j => j.elim)

theorem f2_refl {α : Type} : ∀ l : List α, List.Forall₂ (fun a b => a = b) l l
  | [] => .nil
  | _ :: t => .cons rfl (f2_refl t)

/-! ## Part 5. One execution -/

/-- One execution: under `w.ρ 0 0` and `SelfE` for the trees, `proveBU` is `proveB` without the work
of the empty slots, and the two give the same proof strings. -/
theorem sk_proveB (fl : ℕ → Bool) (xs : List (Option Y)) {w : Wd}
    (h0 : w.ρ 0 0) (hT : ∀ tr ∈ trees, SelfE w tr) :
    Skip (fun _ π₁ π₂ => π₁ = π₂) w
      (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees wt fl xs)
      (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees wt fl xs) := by
  unfold proveB proveBU
  refine Skip.bind' (sk_drawT wp.coin0 w) fun v c0 c0' hv e => ?_
  subst e
  refine Skip.bind'
    (sk_eachM (R := fun _ a b => a = b) (R' := fun v => RS v (isShr .first)) (fun _ _ _ _ _ x => x)
      (fun _ _ _ _ h x => x.mono h)
      (fun u a b hu e => by subst e; exact sk_initSlot sFS Q H wp wt c0 a (hu.ρ _ _ (hv.ρ _ _ h0)))
      xs xs (Wd.le_refl v) (f2_refl xs))
    fun v₂ zs₁ zs₂ hv₂ hz => ?_
  have h02 : v₂.ρ 0 0 := hv₂.ρ _ _ (hv.ρ _ _ h0)
  refine Skip.bind'
    (sk_chain sMT t _ _ depthReq _ _ _ embS embP 0 .first .first _ zs₁ zs₂ _ _ v₂ h02 trivial
      hz ⟨.nil, .nil, trivial, rfl, .nil⟩)
    fun v₃ o₁ o₂ hv₃ ho => ?_
  exact sk_finishAll Q H wq wp trees wt fl c0 0 _ _ (hv₃.ρ _ _ h02)
    (fun tr htr => (hT tr htr).mono (Wd.le_trans hv (Wd.le_trans hv₂ hv₃))) ho.2 ho.1

end Prove

end Compile.Batch.SkipU
