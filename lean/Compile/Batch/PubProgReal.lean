-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubProgReal.lean: the first two hops of zero-knowledge compilation for batches, for
any program in the place of the prover's (the experiments of Compile/Batch/PubProg.lean). Each is an
equality of the adversary's output distributions:

  `map_fst_interact_realWPG`   under `MaskProg`: the real experiment of the token form `argBPGT`
      against `RealBPG'`
  `hopRPG`   for an adversary that asks for one setup, first (exactly: `GAdm`,
      Compile/Batch/SpecGlue.lean: then at most n batches, each allowed by ok), from a state without
      strings: `RealBPG'` against mode R of the challenger, VCBPG.world false; the modes:
      Rom/Defer.lean
  `real_eq_modeRPG`   the two together, under `MaskProg` and `GAdm`

Notation:
  `argBPGT`: the token form of the scheme `argBPG`: the same without `realQ`; `RealBPG'`, `VCBPG`,
    `MaskProg`: the head of Compile/Batch/PubProg.lean
  `erase c vs`: forget the rules: tokens are strings, kept in a list; fresh = sample; marked =
    query; reveal = read (Compile/Star.lean); vs: that list
  `pq`: an `FProg`: a prover's program with flags: pq k fr xs: the key with tokens, for which
    requests a proof string is made, the instances (Compile/Batch/PubProg.lean)
  `ownFlag b`: is request number a of the batch the adversary's own (Compile/Batch/Chall.lean); fun
    _ => true: all flags true
  `pw`: IVK lam L → WKey lam L → V, an arbitrary function (the head of Compile/Batch/PubChall.lean);
    `Vf`: any verifier (`argBPG`)
  `WP`: a `WireBP L`: the prover's data for the three protocols, and the enumeration of the encoding
    randomness (Iop/BatchWireP.lean)
  `p`: a `Params` (Compile/Star.lean); `i`: I, the index; `N₀`, `t₀`: number N₀ of tokens of the
    setup, number t₀ of tokens so far (`LeafGame.sess`, Compile/Batch/OverrunGen.lean)
-/
import Compile.Batch.PubProg

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (GCall GAdm realW ownPf)
open Compile.Life2
  (virt viewVals ofOComp_reply chall_reply runLazy_bind_pure run_fresh0 run_bind map_fst_call
    map_fst_query viewVals_dummy run_false_virt run_false_eq_erase vals_prefix)

/-! ## Under `MaskProg`: what is not shown is not made -/

section RealP

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (pq : FProg lam L W.K) (i : I)

theorem erase_Pp_replyPG (hM : MaskProg pq) {γ : Type} (k : IskH lam L) (b : ZKCP.Gen.Batch X Unit)
    (vs : List Bits) (st : γ) :
    ((erase (pq k (ownFlag b) (reqs b)) vs).bind fun o => OComp.pure (replyOfP V b o.1, st)) =
      (erase (pq k (fun _ => true) (reqs b)) vs).bind fun o =>
        OComp.pure (replyOfP V b o.1, st) := by
  have h := congrArg
    (fun c : TypedOracleComputation lam W.K L (BIn lam L × γ) => c.bind fun y => OComp.pure (toP V y.1, y.2))
    (hM γ k b vs st)
  simp only [OComp.bind_assoc, OComp.bind] at h
  exact h

/-- Under `MaskProg`: the real experiment of the token form `argBPGT` of the scheme that publishes
gives the same output as the experiment without what is not shown. -/
theorem map_fst_interact_realWPG (hM : MaskProg pq) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    {α : Type} (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α)
    (s : Option (ISK lam L)) (T : Table (spec lam W.K L)) :
    (interact (realW (argBPGT W WP p pw pq Vf) i) A (s, T)).map Prod.fst =
      (interact (RealBPG' W WP p pw pq i) A (s, T)).map Prod.fst := by
  refine Rom.forgetCall _ _ _ _ _ _ (stepRealBPG' W WP p pw pq i) (fun s m => ?_) A s T
  rcases m with _ | b
  · left
    show ((Ctok W WP p i).bind fun o => OComp.pure (Sum.inl (pw o.1 (keyOf o.2.1)), some o.2)) =
      ((Ctok W WP p i).bind fun o => OComp.pure (pw o.1 (keyOf o.2.1), o.2)).bind
        fun o => OComp.pure (Sum.inl o.1, some o.2)
    rw [OComp.bind_assoc]
    rfl
  · rcases s with _ | k
    · exact Or.inl rfl
    · cases hb : hasOwn b
      · refine Or.inr ⟨_, progP W (fun k xs => pq k (fun _ => true) xs) k b.pairs, .inr [], ?_, ?_⟩
        · show ((progP W (fun k xs => pq k (fun _ => true) xs) k b.pairs).bind fun πs =>
              OComp.pure (Sum.inr (ownPf b πs.val), some k)) = _
          exact congrArg _ (funext fun πs => by rw [RealB.ownPf_of_not_hasOwn b hb])
        · show (if hasOwn b then _ else _) = _
          rw [hb]
          rfl
      · left
        show (if hasOwn b then _ else _) =
          ((progP W (fun k xs => pq k (fun _ => true) xs) k b.pairs).bind fun πs =>
            OComp.pure (Sum.inr (ownPf b πs.val), some k))
        rw [hb, if_pos rfl]
        unfold progP
        rw [OComp.bind_assoc]
        exact erase_Pp_replyPG W pq hM k.1 b k.2 (some k)

end RealP

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (pq : FProg lam L W.K) (i : I)

namespace HopRPG

abbrev DS (W : QueryLayout lam L) : Type := DSt (spec lam W.K L)

/-! ## The replies, unfolded -/

theorem stepRealBP'_setupG (s : Option (ISK lam L)) :
    stepRealBPG' W WP p pw pq i s .setup =
      (Ctok W WP p i).bind fun o => pure (.inl (pw o.1 (keyOf o.2.1)), some o.2) := rfl

theorem stepRealBP'_ownG (k : ISK lam L) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    stepRealBPG' W WP p pw pq i (some k) (.batch b) =
      (erase (pq k.1 (ownFlag b) (reqs b)) k.2).bind fun o => pure (replyOfP V b o.1, some k) := by
  show (if hasOwn b then _ else _) = _
  rw [h, if_pos rfl]

theorem stepRealBP'_noneG (k : ISK lam L) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    stepRealBPG' W WP p pw pq i (some k) (.batch b) = pure (.inr [], some k) := by
  show (if hasOwn b then _ else _) = _
  rw [h]
  rfl

theorem VCBP_setupG :
    (VCBPG W WP p pw pq i).step none .setup =
      (Cp W WP p i).bind fun o =>
        Step.fresh 0 fun t => Step.pure (.inl (pw o.1 (keyOf o.2)), some (o.2, t)) := rfl

theorem VCBP_ownG (k : IskH lam L) (N₀ : ℕ) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    (VCBPG W WP p pw pq i).step (some (k, N₀)) (.batch b) = Step.fresh 0 fun t₀ =>
      (virt N₀ (t₀ + 1 - N₀) (pq k (ownFlag b) (reqs b))).bind fun πs =>
          Step.pure (replyOfP V b πs, some (k, N₀)) := by
  show (if hasOwn b then _ else _) = _
  rw [h, if_pos rfl]

theorem VCBP_noneG (k : IskH lam L) (N₀ : ℕ) (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    (VCBPG W WP p pw pq i).step (some (k, N₀)) (.batch b) = Step.pure (.inr [], some (k, N₀)) := by
  show (if hasOwn b then _ else _) = _
  rw [h]
  rfl

theorem reply_setup_RealBP'G (s : Option (ISK lam L)) (T : Table (spec lam W.K L)) :
    (RealBPG' W WP p pw pq i).reply (s, T) .setup =
      ((erase (Cp W WP p i) []).runLazy T).map fun y =>
        (.inl (pw y.1.1.1 (keyOf y.1.1.2)), (some (y.1.1.2, y.1.2), y.2)) := by
  rw [ofOComp_reply, stepRealBP'_setupG, Ctok, runLazy_bind_pure, runLazy_bind_pure,
    PMF.map_comp, PMF.map_comp]
  rfl

theorem reply_own_RealBP'G (k : IskH lam L) (vs : List Bits) (T : Table (spec lam W.K L))
    (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    (RealBPG' W WP p pw pq i).reply (some (k, vs), T) (.batch b) =
      ((erase (pq k (ownFlag b) (reqs b)) vs).runLazy T).map fun y =>
        (replyOfP V b y.1.1, (some (k, vs), y.2)) := by
  rw [ofOComp_reply, stepRealBP'_ownG W WP p pw pq i _ b h, runLazy_bind_pure, PMF.map_comp]
  rfl

theorem reply_none_RealBP'G (k : ISK lam L) (T : Table (spec lam W.K L))
    (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    (RealBPG' W WP p pw pq i).reply (some k, T) (.batch b) =
      (PMF.pure ()).map fun _ => (.inr [], (some k, T)) := by
  rw [ofOComp_reply, stepRealBP'_noneG W WP p pw pq i _ b h, PMF.pure_map]
  exact PMF.pure_map _ _

theorem reply_setup_VCBPG (m : Bool) (D : DS W) :
    ((VCBPG W WP p pw pq i).world m).reply (none, D) .setup
      = ((Cp W WP p i).run m D).map fun y =>
          (.inl (pw y.1.1 (keyOf y.1.2)),
            (some (y.1.2, y.2.vals.length), { y.2 with vals := y.2.vals ++ [[]] })) := by
  rw [chall_reply, VCBP_setupG, run_bind]
  simp only [run_fresh0]
  simp only [Step.run, PMF.map_bind, PMF.pure_map]
  rfl

theorem reply_own_VCBPG (m : Bool) (k : IskH lam L) (N₀ : ℕ) (D : DS W)
    (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = true) :
    ((VCBPG W WP p pw pq i).world m).reply (some (k, N₀), D) (.batch b) =
      ((virt N₀ (D.vals.length + 1 - N₀) (pq k (ownFlag b) (reqs b))).run
        m { D with vals := D.vals ++ [[]] }).map fun y =>
            (replyOfP V b y.1, (some (k, N₀), y.2)) := by
  rw [chall_reply, VCBP_ownG W WP p pw pq i k N₀ b h, run_fresh0, run_bind]
  simp only [Step.run, PMF.map_bind, PMF.pure_map]
  rfl

theorem reply_none_VCBPG (m : Bool) (k : IskH lam L) (N₀ : ℕ) (D : DS W)
    (b : ZKCP.Gen.Batch X Unit) (h : hasOwn b = false) :
    ((VCBPG W WP p pw pq i).world m).reply (some (k, N₀), D) (.batch b) =
      (PMF.pure ()).map fun _ => (.inr [], (some (k, N₀), D)) := by
  rw [chall_reply, VCBP_noneG W WP p pw pq i k N₀ b h, PMF.pure_map]
  exact PMF.pure_map _ _

end HopRPG

open HopRPG

/-! ## The real experiment against mode R of the challenger -/

section Hop

variable {W WP p pw pq i}
variable {α : Type} (ok : ZKCP.Gen.Batch X Unit → Prop)

/-- After the setup. The key of the real experiment holds the first N₀ strings of the challenger's
experiment. -/
theorem hopRP_postG (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    ∀ (n : ℕ) (k : IskH lam L) (N₀ : ℕ) (D : DS W), GAdm ok A true n → N₀ ≤ D.vals.length →
      (interact (RealBPG' W WP p pw pq i) A (some (k, D.vals.take N₀), D.table)).map Prod.fst
        = (interact ((VCBPG W WP p pw pq i).world false) A (some (k, N₀), D)).map Prod.fst := by
  induction A with
  | halt a =>
    intro n k N₀ D _ _
    simp only [interact, PMF.pure_map]
  | sample n' k' ih =>
    intro n k N₀ D h hN
    simp only [interact, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r n k N₀ D (h r) hN)
  | query o q k' ih =>
    intro n k N₀ D h hN
    rw [map_fst_query (RealBPG' W WP p pw pq i) o q k' _ (lazyAnswer D.table o q)
          (fun x => (x.1, (some (k, D.vals.take N₀), x.2))) rfl,
      map_fst_query ((VCBPG W WP p pw pq i).world false) o q k' _ (lazyAnswer D.table o q)
        (fun x => (x.1, (some (k, N₀), { D with table := x.2 }))) rfl]
    exact congrArg _ (funext fun x => ih x.1 n k N₀ { D with table := x.2 } (h x.1) hN)
  | call c k' ih =>
    intro n k N₀ D h hN
    rcases c with _ | b
    · simp only [GAdm] at h
      exact absurd h.1 (by simp)
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [GAdm] at h
        obtain ⟨-, -, h⟩ := h
        cases hb : hasOwn b
        · rw [map_fst_call _ _ _ _ _ _ (reply_none_RealBP'G W WP p pw pq i _ _ b hb),
            map_fst_call _ _ _ _ _ _ (reply_none_VCBPG W WP p pw pq i false k N₀ D b hb),
            PMF.pure_bind, PMF.pure_bind]
          exact ih _ n k N₀ D (h _) hN
        · rw [map_fst_call _ _ _ _ _ _ (reply_own_RealBP'G W WP p pw pq i k _ _ b hb),
            map_fst_call _ _ _ _ _ _ (reply_own_VCBPG W WP p pw pq i false k N₀ D b hb)]
          have hl : N₀ + (D.vals.length + 1 - N₀) ≤ (D.vals ++ [[]]).length := by
            simp only [List.length_append, List.length_singleton]; omega
          rw [← viewVals_dummy hN [],
            ← run_false_virt (pq k (ownFlag b) (reqs b))
              ({ D with vals := D.vals ++ [[]] } : DS W) hl, PMF.bind_map]
          refine bind_congr_support _ fun y hy => ?_
          have hp := vals_prefix false _ _ y hy
          have hN' : N₀ ≤ y.2.vals.length := by
            have := hp.length_le
            simp only [List.length_append, List.length_singleton] at this
            omega
          have ht : y.2.vals.take N₀ = D.vals.take N₀ := by
            obtain ⟨t, ht⟩ := hp
            rw [← ht, List.append_assoc, List.take_append_of_le_length hN]
          have h1 := ih (replyOfP V b y.1) n k N₀ y.2 (h _) hN'
          rw [ht] at h1
          simp only [Function.comp_def, viewVals_dummy hN]
          exact h1

/-- The real experiment, without what is not shown, gives the same output as mode R of the
challenger, for an adversary that asks for one setup, first (exactly: `GAdm`,
Compile/Batch/SpecGlue.lean: then at most n batches, each allowed by ok), from a state without
strings. -/
theorem hopRPG (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    ∀ (n : ℕ) (D : DS W), GAdm ok A false n → D.vals = [] →
      (interact (RealBPG' W WP p pw pq i) A (none, D.table)).map Prod.fst =
        (interact ((VCBPG W WP p pw pq i).world false) A (none, D)).map Prod.fst := by
  induction A with
  | halt a =>
    intro n D _ _
    simp only [interact, PMF.pure_map]
  | sample n' k' ih =>
    intro n D h hD
    simp only [interact, PMF.map_bind]
    exact congrArg _ (funext fun r => ih r n D (h r) hD)
  | query o q k' ih =>
    intro n D h hD
    rw [map_fst_query (RealBPG' W WP p pw pq i) o q k' _ (lazyAnswer D.table o q)
          (fun x => (x.1, (none, x.2))) rfl,
      map_fst_query ((VCBPG W WP p pw pq i).world false) o q k' _ (lazyAnswer D.table o q)
        (fun x => (x.1, (none, { D with table := x.2 }))) rfl]
    exact congrArg _ (funext fun x => ih x.1 n { D with table := x.2 } (h x.1) hD)
  | call c k' ih =>
    intro n D h hD
    rcases c with _ | b
    · simp only [GAdm] at h
      have he : erase (Cp W WP p i) [] = erase (Cp W WP p i) D.vals := by rw [hD]
      rw [map_fst_call _ _ _ _ _ _ (reply_setup_RealBP'G W WP p pw pq i none D.table),
        map_fst_call _ _ _ _ _ _ (reply_setup_VCBPG W WP p pw pq i false D), he,
        ← run_false_eq_erase, PMF.bind_map]
      refine congrArg _ (funext fun y => ?_)
      have h1 := hopRP_postG (W := W) (WP := WP) (p := p) (pw := pw) (pq := pq) (i := i) ok
        (k' (.inl (pw y.1.1 (keyOf y.1.2)))) n y.1.2 y.2.vals.length
        { y.2 with vals := y.2.vals ++ [[]] } (h.2 _) (by simp)
      rw [show ({ y.2 with vals := y.2.vals ++ [[]] } : DS W).vals.take y.2.vals.length = y.2.vals
          from by simp] at h1
      exact h1
    · cases n with
      | zero => exact h.elim
      | succ n =>
        simp only [GAdm] at h
        exact absurd h.1 (by simp)

/-- Under `MaskProg`: the real experiment of the token form `argBPGT` of the scheme that publishes
gives the same output as mode R of the challenger, for an adversary that asks for one setup, first
(exactly: `GAdm`, Compile/Batch/SpecGlue.lean: then at most n batches, each allowed by ok). -/
theorem real_eq_modeRPG (hM : MaskProg pq) (Vf : V → X → Prf lam L → TypedOracleComputation lam W.K L Bool)
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ) (h : GAdm ok A false n) :
    (interact (realW (argBPGT W WP p pw pq Vf) i) A (none, Table.empty _)).map Prod.fst =
      (interact ((VCBPG W WP p pw pq i).world false) A (none, DSt.init _)).map Prod.fst :=
  (map_fst_interact_realWPG W WP p pw pq i hM Vf A none _).trans (hopRPG ok A n (DSt.init _) h rfl)

end Hop

end Compile.Batch
