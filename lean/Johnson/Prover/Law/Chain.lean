-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Law/Chain.lean: THE LAW OF THE COMPILED PROVER's OUTCOME: from any table that is
fresh for this chain, the prover's search runs out, or it draws verifier messages in a set B, with
probability at most (the searches' failure) + (the uniform measure of B, the test bits set to 0). It
proves Spec.prove_law (Johnson/Prover/Law/Defs.lean).

How. Round by round (chain_law). A round's trees, and at the joining round the query to g and the
request tree, leave the column fb t as it was (Johnson/Prover/Law/Asks.lean). Its Fiat-Shamir
queries hold the round's own number and a plain part of that round: they are new in a fresh table,
they differ from each other, and they leave the table fresh for the rounds to come. So fs_le
(Johnson/Prover/Law/Round.lean) applies, with the bound for the rest of the rounds at the slice of
B; the mean over the round's verifier message is one step of Fubini.

Main names.
  EvC   the event at the chain: a search has run out, or the verifier messages lie in B.
  PrFrom_pure, PrFrom_mono, tail_le, sum_eq, fresh_after   the steps.
  chain_law   the law at every (rounds that are left, number of the first, phase, table).
  prove_law   THE STATEMENT: Spec.prove_law.

Limits. One slot, one chain. B is a letter: nothing says that any B with an accept law is small. No
completeness error follows from this file alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Law.Round
import Johnson.Prover.Law.Asks

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The event at the chain: a search has run out, or the verifier messages lie in B. -/
def EvC (s : Shape) (B : Set (Rho s)) : Set (Res (OutP lam L s)) :=
  {r | (∃ j, r = .ranOut j) ∨ ∃ z, r = .ok z ∧ z.1 ∈ B}

theorem PrFrom_pure {S : OSpec} {α : Type} (T : Table S) (a : α) (E : Set α) (h : a ∉ E) :
    PrFrom T (OComp.pure a) E = 0 := by
  classical
  rw [PrFrom_eq_lazy]
  show pr ((PMF.pure (a, T)).map Prod.fst) E = 0
  rw [PMF.pure_map, pr_pure, if_neg h]

theorem PrFrom_mono {S : OSpec} {α : Type} (T : Table S) (c : OComp S α) {E F : Set α}
    (h : E ⊆ F) : PrFrom T c E ≤ PrFrom T c F := by
  rw [PrFrom_eq_lazy, PrFrom_eq_lazy]
  exact pr_mono _ h

/-- what follows a round's Fiat-Shamir query: the rest of the chain, at the slice of B -/
theorem tail_le {r : Round} {s : Shape} (B : Set (Rho (r :: s))) (T : Table (typedOracleFamily lam K L))
    (c : r.Chal) (kp : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq : Option (Dig lam))
    (prog : TypedOracleComputation lam K L (Res (OutP lam L s))) {ε : ℝ≥0∞}
    (h : PrFrom T prog (EvC s {ρ | ((c, ρ) : Rho (r :: s)) ∈ B}) ≤ ε) :
    PrFrom T (prog.bind fun u => .pure (u.map (consP c kp rq))) (EvC (r :: s) B) ≤ ε := by
  rw [PrFrom_bind_pure]
  refine (PrFrom_mono T prog fun u hu => ?_).trans h
  cases u with
  | ok z =>
    rcases hu with ⟨j, e⟩ | ⟨z', e, hz⟩
    · cases e
    · obtain rfl : consP c kp rq z = z' := Res.ok.inj e
      exact Or.inr ⟨z, rfl, hz⟩
  | noFormat =>
    rcases hu with ⟨j, e⟩ | ⟨z', e, -⟩
    · cases e
    · cases e
  | ranOut j => exact Or.inl ⟨j, rfl⟩

/-- one step of Fubini, with the sums in order -/
theorem sum_eq {r : Round} {s : Shape} (B : Set (Rho (r :: s))) (f : r.Chal → r.Chal)
    (F : Rho s → Rho s) (κ γ : ℝ≥0∞) :
    (expect (unif r.Chal) fun c =>
        κ + pr (unif (Rho s)) {ρ | F ρ ∈ {ρ' | ((f c, ρ') : Rho (r :: s)) ∈ B}}) + γ =
      (γ + κ) +
        pr (unif (Rho (r :: s))) {ρ : Rho (r :: s) | ((f ρ.1, F ρ.2) : Rho (r :: s)) ∈ B} := by
  have h : pr (unif (Rho (r :: s))) {ρ : Rho (r :: s) | ((f ρ.1, F ρ.2) : Rho (r :: s)) ∈ B} =
      expect (unif r.Chal) fun c =>
        pr (unif (Rho s)) {ρ | F ρ ∈ {ρ' | ((f c, ρ') : Rho (r :: s)) ∈ B}} := by
    show pr (unif (r.Chal × Rho s)) _ = _
    rw [unif_prod, pr_prod]
    rfl
  rw [h, expect_add, expect_const, add_comm, add_assoc]

/-- after a round's Fiat-Shamir queries the table is fresh for the rounds to come -/
theorem fresh_after {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s}
    {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)} {i : ℕ}
    {T T' : Table (typedOracleFamily lam K L)} (h : FreshFrom t (r :: s) (a, A) embP i T) {P : Type}
    (qf : P → FbIn lam L t) (hr : ∀ β, (qf β).round = i)
    (e : ∀ q, (∀ β', q ≠ qf β') → T' (OracleName.fb t) q = T (OracleName.fb t) q) :
    FreshFrom t s A (fun z => embP (.inr z)) (i + 1) T' := fun q hq => by
  obtain ⟨z, h1, h2⟩ := hq
  rw [e q fun β' e' => by
    have := hr β'
    rw [← e', h2] at this
    omega]
  exact fresh_next h q ⟨z, h1, h2⟩

theorem zero_lo {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .lo) (c : r.Chal) :
    w.zero c = zeroOf w.grJ c := by
  unfold TypedOracleCompiler.Iop.WireRB.zero
  rw [hk]
  cases w.grJ <;> rfl

theorem zero_sh {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hk : a.kind = .sh) (c : r.Chal) :
    w.zero c = zeroOf w.gr0 c := by
  unfold TypedOracleCompiler.Iop.WireRB.zero
  rw [hk]
  cases w.gr0 <;> rfl

section
variable (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ)

/-- **The law at the chain.** -/
theorem chain_law : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (T : Table (typedOracleFamily lam K L)),
    FreshFrom t s A embP i T → RoundsQueryLayout.OKG s A W → PutsApart s A W cap i →
    Function.Injective embP → ∀ B : Set (Rho s),
    PrFrom T (chainO t cms x co cap s A W embS embP i ph σ) (EvC s B) ≤
      capFail s A W cap i + pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ B}
  | [], A, W, _, _, _, ph, _, T, _, _, _, _, B => by
    by_cases hB : (() : Rho []) ∈ B
    · refine (PrFrom_le_one _ _ _).trans ?_
      have : {ρ : Rho [] | TypedOracleCompiler.Iop.RoundsQueryLayout.zero [] A W ρ ∈ B} = Set.univ :=
        Set.eq_univ_of_forall fun _ => hB
      rw [this]
      refine le_add_self.trans' (le_of_eq ?_)
      exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _) |>.symm
    · refine le_of_eq_of_le (PrFrom_pure T _ _ fun h => ?_) (zero_le _)
      rcases h with ⟨j, e⟩ | ⟨z, e, hz⟩
      · cases e
      · obtain rfl := Res.ok.inj e
        exact hB hz
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), T, hT, hW, hP, hE, B => by
    simp only [chainO]
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      refine le_of_eq_of_le (PrFrom_pure T _ _ fun h => ?_) (zero_le _)
      rcases h with ⟨j, e'⟩ | ⟨z, e', -⟩
      · cases e'
      · cases e'
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          have hk := (act_own e).1
          have hP' := hP
          simp only [PutsApart, hk] at hP'
          refine PrFrom_bind_le T _ _ _ fun out hout => ?_
          have hT1 : FreshFrom t (r :: s) (a, A) embP i out.2 :=
            fresh_of_kept hT (fb_kept_treesO t _ _ _ _ _ _ _ T out hout)
          refine (fs_le w.grJ (cap i) w.chal t
            (fun β => (⟨i, h.withLate (lateInstancePart L i x), out.1.map TreeK.root, embP (.inl (.inr β))⟩ :
              FbIn lam L t)) (a.plain m.2).2 _ (EvC (r :: s) B)
            (fun c => capFail s A W cap (i + 1) +
              pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ {ρ' | ((c, ρ') : Rho (r :: s)) ∈ B}})
            hW.1.grJ_ok hW.1.chal_unif out.2
            (fun β => hT1 _ ⟨.inl (.inr β), rfl, rfl⟩)
            (fun β β' e' => Sum.inr.inj (Sum.inl.inj (hE (congrArg FbIn.plain e'))))
            hP'.1 fun β ans T' hT' => ?_).trans ?_
          · exact tail_le B T' _ _ _ _ (chain_law s A W _ _ (i + 1) _ _ T'
              (fresh_after hT1 _ (fun _ => rfl) hT') hW.2 hP'.2
              (fun _ _ e' => Sum.inr.inj (hE e')) _)
          · rw [sum_eq B (zeroOf w.grJ) (RoundsQueryLayout.zero s A W)]
            refine le_of_eq ?_
            simp only [capFail, hk]
            congr 2
            ext ρ
            show _ ↔ ((w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B
            rw [zero_lo w hk]
            rfl
        | false =>
          have hk := (act_shared e).1
          have hP' := hP
          simp only [PutsApart, hk] at hP'
          refine PrFrom_bind_le T _ _ _ fun out hout => ?_
          have hT1 : FreshFrom t (r :: s) (a, A) embP i out.2 :=
            fresh_of_kept hT (fb_kept_treesO t _ _ _ _ _ _ _ T out hout)
          refine (fs_le w.gr0 (cap i) w.chal t
            (fun β => (⟨i, h, out.1.map TreeK.root, embP (.inl (.inl β))⟩ : FbIn lam L t))
            (a.plain m.2).1 _ (EvC (r :: s) B)
            (fun c => capFail s A W cap (i + 1) +
              pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ {ρ' | ((c, ρ') : Rho (r :: s)) ∈ B}})
            hW.1.gr0_ok hW.1.chal_unif out.2
            (fun β => hT1 _ ⟨.inl (.inl β), rfl, rfl⟩)
            (fun β β' e' => Sum.inl.inj (Sum.inl.inj (hE (congrArg FbIn.plain e'))))
            hP'.1 fun β ans T' hT' => ?_).trans ?_
          · exact tail_le B T' _ _ _ _ (chain_law s A W _ _ (i + 1) _ _ T'
              (fresh_after hT1 _ (fun _ => rfl) hT') hW.2 hP'.2
              (fun _ _ e' => Sum.inr.inj (hE e')) _)
          · rw [sum_eq B (zeroOf w.gr0) (RoundsQueryLayout.zero s A W)]
            refine le_of_eq ?_
            simp only [capFail, hk]
            congr 2
            ext ρ
            show _ ↔ ((w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B
            rw [zero_sh w hk]
            rfl
      | join ρ₀ =>
        have hk := (act_join e).1
        have hP' := hP
        simp only [PutsApart, hk] at hP'
        refine PrFrom_bind_le T _ _ _ fun o1 ho1 => ?_
        refine PrFrom_bind_le o1.2 _ _ _ fun o2 ho2 => ?_
        refine PrFrom_bind_le o2.2 _ _ _ fun o3 ho3 => ?_
        refine PrFrom_bind_le o3.2 _ _ _ fun o4 ho4 => ?_
        refine PrFrom_bind_le o4.2 _ _ _ fun o5 ho5 => ?_
        have hT1 : FreshFrom t (r :: s) (a, A) embP i o5.2 :=
          fresh_of_kept (fresh_of_kept (fresh_of_kept (fresh_of_kept (fresh_of_kept hT
            (fb_kept_treesO t _ _ _ _ _ _ _ T o1 ho1))
            (fb_kept_treesO t _ _ _ _ _ _ _ o1.2 o2 ho2))
            (fb_kept_g t t _ o2.2 o3 ho3)) (fb_kept_rleaf t _ o3.2 o4 ho4))
            (fb_kept_climbO t _ _ _ o4.2 o5 ho5)
        refine (fs_le w.gr0 (cap i) w.chal t
          (fun β => (⟨i, .f4 cms (List.ofFn o5.1), o2.1.map TreeK.root, embP (.inl (.inl β))⟩ :
            FbIn lam L t)) (a.plain m.2).1 _ (EvC (r :: s) B)
          (fun c => capFail s A W cap (i + 1) +
            pr (unif (Rho s)) {ρ | RoundsQueryLayout.zero s A W ρ ∈ {ρ' | ((c, ρ') : Rho (r :: s)) ∈ B}})
          hW.1.gr0_ok hW.1.chal_unif o5.2
          (fun β => hT1 _ ⟨.inl (.inl β), rfl, rfl⟩)
          (fun β β' e' => Sum.inl.inj (Sum.inl.inj (hE (congrArg FbIn.plain e'))))
          hP'.1 fun β ans T' hT' => ?_).trans ?_
        · exact tail_le B T' _ _ _ _ (chain_law s A W _ _ (i + 1) _ _ T'
            (fresh_after hT1 _ (fun _ => rfl) hT') hW.2 hP'.2
            (fun _ _ e' => Sum.inr.inj (hE e')) _)
        · rw [sum_eq B (zeroOf w.gr0) (RoundsQueryLayout.zero s A W)]
          refine le_of_eq ?_
          simp only [capFail, hk]
          congr 2
          ext ρ
          show _ ↔ ((w.zero ρ.1, RoundsQueryLayout.zero s A W ρ.2) : Rho (r :: s)) ∈ B
          rw [zero_sh w hk]
          rfl

end

/-- **THE STATEMENT.** -/
theorem prove_law : Spec.prove_law := by
  intro I X lam K L t Y E Q wq embS embP xin cms x y xt σ co cap T hT hw _ hP hE B
  unfold proveX
  rw [PrFrom_bind_pure]
  refine (PrFrom_mono T _ fun u hu => ?_).trans
    (chain_law t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ T hT hw.sh hP hE B)
  cases u with
  | ok z =>
    rcases hu with ⟨j, e⟩ | ⟨π, τ, e, hτ⟩
    · cases e
    · obtain ⟨-, rfl⟩ := Prod.mk.inj (Res.ok.inj e)
      rw [rho_trK] at hτ
      exact Or.inr ⟨z, rfl, hτ⟩
  | noFormat =>
    rcases hu with ⟨j, e⟩ | ⟨π, τ, e, -⟩
    · cases e
    · cases e
  | ranOut j => exact Or.inl ⟨j, rfl⟩

end OnBytes.Prover
