-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Nonces.lean: WHICH NUMBERS THE COMPILED PROVER WRITES AS NONCES: in round number i
with a test the plain part that was hashed is the strategy's with a number of at most cap i written
in; in a round without a test it is the strategy's own.

Why. `Puts` (OnBytes/Prover/Inv.lean) says "some number". Whoever writes the string into a file
needs a bound: there a nonce is one word.

Main names:
  `search_lt`, `fs_cap`   a search returns one of the numbers that it may try
  `PutsLe`       two transcripts are one but for numbers of at most cap i, written in as nonces in
                 the rounds with a test, and there alone
  `chain_putsLe`, `proveX_putsLe`   so are the strategy's own run and the transcript as hashed
  `PutsLe.puts`  it says more than `Puts`

Limits: nothing on probability. Nothing on what `put` writes: that is the wire record's.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Main

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- A search returns one of the numbers that it may try. -/
theorem search_lt {C P : Type} (g : Fam (typedOracleFamily lam K L)) (gr : GrW C P)
    (chal : (Fin K → Dig lam) → C) (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (α : P) :
    ∀ (fuel n : ℕ) (β : P) (a : FsAns lam K),
      (searchO gr chal ask α fuel n).det g = some (β, a) →
      ∃ m, n ≤ m ∧ m < n + fuel ∧ β = gr.put m α
  | 0, _, _, _, h => by cases h
  | fuel + 1, n, β, a, h => by
    rw [det_searchO_succ] at h
    by_cases hk : gr.ok (chal ((ask (gr.put n α)).det g).1) = true
    · rw [if_pos hk] at h
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨n, le_rfl, by omega, rfl⟩
    · rw [if_neg hk] at h
      obtain ⟨m, h1, h2, h3⟩ := search_lt g gr chal ask α fuel (n + 1) β a h
      exact ⟨m, by omega, by omega, h3⟩

/-- What a Fiat-Shamir query hashes: α where there is no test; else α with a number of at most cap
written in. -/
theorem fs_cap {C P : Type} (g : Fam (typedOracleFamily lam K L)) (gr : Option (GrW C P)) (cap : ℕ)
    (chal : (Fin K → Dig lam) → C) (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (α : P) {β : P}
    {a : FsAns lam K} (h : (fsO gr cap chal ask α).det g = some (β, a)) :
    (gr = none ∧ β = α) ∨ ∃ r n, n ≤ cap ∧ gr = some r ∧ β = r.put n α := by
  cases gr with
  | none =>
    rcases (fs_some g none cap chal ask α h).2 with h1 | ⟨r, _, h1, -, -⟩
    · exact Or.inl h1
    · cases h1
  | some r =>
    obtain ⟨m, -, h2, h3⟩ := search_lt g r chal ask α (cap + 1) 0 β a h
    exact Or.inr ⟨r, m, by omega, rfl, h3⟩

/-- τ' is τ but for nonces of at most cap i in round number i: the same oracles and verifier
messages; in a round with a test the plain part of the hashed component is τ's with such a number
written in; in a round without a test the same plain part. i: the number of the first round. -/
def PutsLe (cap : ℕ → ℕ) : ℕ → (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Tr s → Tr s → Prop
  | _, [], _, _, _, _ => True
  | i, _ :: s, (a, A), (w, W), (m, c, τ), (m', c', τ') =>
      m'.1 = m.1 ∧ c' = c ∧
      (match a.kind with
        | .lo => (w.grJ = none ∧ m'.2 = m.2) ∨ ∃ g n, n ≤ cap i ∧ w.grJ = some g ∧
            m'.2 = a.plain.symm ((a.plain m.2).1, g.put n (a.plain m.2).2)
        | .sh => (w.gr0 = none ∧ m'.2 = m.2) ∨ ∃ g n, n ≤ cap i ∧ w.gr0 = some g ∧
            m'.2 = a.plain.symm (g.put n (a.plain m.2).1, (a.plain m.2).2)) ∧
      PutsLe cap (i + 1) s A W τ τ'

/-- It says more than `Puts`. -/
theorem PutsLe.puts {cap : ℕ → ℕ} : ∀ (i : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (τ τ' : Tr s), PutsLe cap i s A W τ τ' → Puts s A W τ τ'
  | _, [], _, _, _, _, _ => trivial
  | i, _ :: s, (a, A), (w, W), (m, c, τ), (m', c', τ'), h => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨h1, h2, ?_, PutsLe.puts (i + 1) s A W τ τ' h4⟩
    cases hk : a.kind with
    | lo =>
      simp only [hk] at h3
      rcases h3 with ⟨-, e⟩ | ⟨g, n, -, e1, e2⟩
      · exact Or.inl e
      · exact Or.inr (Or.inl ⟨g, n, rfl, e1, e2⟩)
    | sh =>
      simp only [hk] at h3
      rcases h3 with ⟨-, e⟩ | ⟨g, n, -, e1, e2⟩
      · exact Or.inl e
      · exact Or.inr (Or.inr ⟨g, n, rfl, e1, e2⟩)

section
variable (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
  (co : Coins lam L) (cap : ℕ → ℕ)

/-- **The transcript as hashed is the strategy's own run but for nonces of at most cap i.** -/
theorem chain_putsLe : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : Phase lam) (σ : Strat s Unit) (z : OutP lam L s),
    (chainO t cms x co cap s A W embS embP i ph σ).det g = .ok z →
    PutsLe cap i s A W (σ.run z.1).1 (trK s z.2.1 z.1)
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k), z, hz => by
    cases e : actOf cms (x.map L.early) co.salt a.kind ph with
    | none =>
      rw [det_noFormat g t cms x co cap w W embS embP i ph m k e] at hz
      cases hz
    | some ac =>
      cases ac with
      | one h own next =>
        cases own with
        | true =>
          rw [det_own g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          refine ⟨rfl, rfl, ?_, chain_putsLe s A W _ _ (i + 1) _ _ z' hz'⟩
          simp only [(act_own e).1]
          rcases fs_cap g _ _ _ _ _ hq with ⟨h1, h2⟩ | ⟨u, n, hn, h1, h2⟩
          · refine Or.inl ⟨h1, ?_⟩
            show a.plain.symm ((a.plain m.2).1, q.1) = m.2
            rw [h2, Prod.mk.eta, Equiv.symm_apply_apply]
          · refine Or.inr ⟨u, n, hn, h1, ?_⟩
            show a.plain.symm ((a.plain m.2).1, q.1) = _
            rw [h2]
        | false =>
          rw [det_shared g t cms x co cap w W embS embP i ph m k e] at hz
          obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
          obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
          refine ⟨rfl, rfl, ?_, chain_putsLe s A W _ _ (i + 1) _ _ z' hz'⟩
          simp only [(act_shared e).1]
          rcases fs_cap g _ _ _ _ _ hq with ⟨h1, h2⟩ | ⟨u, n, hn, h1, h2⟩
          · refine Or.inl ⟨h1, ?_⟩
            show a.plain.symm (q.1, (a.plain m.2).2) = m.2
            rw [h2, Prod.mk.eta, Equiv.symm_apply_apply]
          · refine Or.inr ⟨u, n, hn, h1, ?_⟩
            show a.plain.symm (q.1, (a.plain m.2).2) = _
            rw [h2]
      | join ρ =>
        rw [det_join g t cms x co cap w W embS embP i ph m k e] at hz
        obtain ⟨q, hq, hq'⟩ := onFsF_eq_ok hz
        obtain ⟨z', hz', rfl⟩ := Res.map_eq_ok hq'
        refine ⟨rfl, rfl, ?_, chain_putsLe s A W _ _ (i + 1) _ _ z' hz'⟩
        simp only [(act_join e).1]
        rcases fs_cap g _ _ _ _ _ hq with ⟨h1, h2⟩ | ⟨u, n, hn, h1, h2⟩
        · refine Or.inl ⟨h1, ?_⟩
          show a.plain.symm (q.1, (a.plain m.2).2) = m.2
          rw [h2, Prod.mk.eta, Equiv.symm_apply_apply]
        · refine Or.inr ⟨u, n, hn, h1, ?_⟩
          show a.plain.symm (q.1, (a.plain m.2).2) = _
          rw [h2]

end

/-- The same at the prover. -/
theorem proveX_putsLe (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ) (g : Fam (typedOracleFamily lam K L))
    (π : OneProtocolProof lam Q) (τ : Tr Q.loc.shape)
    (hp : (proveX t Q wq embS embP xin cms x y xt σ co cap).det g = .ok (π, τ)) :
    PutsLe cap 0 Q.loc.shape Q.ann wq.sh (σ.run τ.rho).1 τ := by
  obtain ⟨z, hz, rfl, rfl⟩ := (proveX_ok_iff t Q wq embS embP xin cms x y xt σ co cap g π τ).1 hp
  rw [rho_trK]
  exact chain_putsLe g t cms (xin x) co cap _ _ _ _ _ 0 .first σ z hz

end OnBytes.Prover
