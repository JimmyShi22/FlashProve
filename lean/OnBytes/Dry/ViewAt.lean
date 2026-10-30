-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Dry/ViewAt.lean: THE STATEMENTS ON CONTROL AND ON THE VIEW, PUT TOGETHER FOR THEIR USE: at
answers that a first, dry pass has recorded, with the verifier messages ρ₀, the replay at the honest
strategy and the replay at the strategy made from the honest run's disclosed view hand out the same.

General lemmas. This file states no goal of the release.

Main names.
  plains_stratOfView, read_stratOfView   the strategy made from plain parts and symbols
      (stratOfView, Johnson/WholeKey/Sim.lean) sends these, whatever the verifier says.
  view_agrees    so the strategy made from the disclosed view (InteractiveOracleProof.dview, Iop/InteractiveOracleProof.lean) of σ's
      run at ρ₀ meets, against σ, the two premises of Spec.ofView on strategies.
  rho_of_replay  every replay, at any strategy, of answers that a first pass has recorded has that
      pass's verifier messages (from Spec.control).
  unguard        from the runs with the verifier messages ρ₀ to all runs, where all runs have them.
  ofView_at      two strategies with one view at ρ₀, at such answers: the same law of what is
      handed out, with no guard.
  sameWork_at    any two strategies, at any recorded answers: the same law of the table after the
      run. It is what is handed out where the string is withheld.

Limits. One slot, one chain.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Dry.View
import Rom.Dry.Support
import Prob.LawKit

set_option autoImplicit false

noncomputable section

namespace OnBytes.Dry
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob OnBytes.Prover
open OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## The strategy made from a view -/

theorem plains_stratOfView : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (pl : Plains s)
    (orc : (p : OPos s) → Option (OSym s p)) (ρ : Rho s),
    ((stratOfView s A W pl orc).run ρ).1.plains = pl
  | [], _, _, (), _, _ => rfl
  | r :: s, (_, A), (_, W), (pl, pls), orc, (c, ρ) => by
    show ((pl, ((stratOfView s A W pls fun p => orc (.inr p)).run ρ).1.plains) :
      r.Plain × Plains s) = (pl, pls)
    rw [plains_stratOfView s A W pls _ ρ]

theorem read_stratOfView : ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (pl : Plains s)
    (orc : (p : OPos s) → Option (OSym s p)) (ρ : Rho s) (p : OPos s) (a : OSym s p),
    orc p = some a → ((stratOfView s A W pl orc).run ρ).1.read p = a
  | r :: _, (_, _), (w, _), (_, _), orc, (_, _), .inl p, a, h => by
    show r.rd (w.pt.ofSyms fun p => (orc (.inl p)).getD (w.pt.zero p)) p = a
    rw [w.pt.rd_ofSyms, h]
    rfl
  | _ :: s, (_, A), (_, W), (_, pls), orc, (_, ρ), .inr q, a, h =>
    read_stratOfView s A W pls (fun p => orc (.inr p)) ρ q a h

/-- **The strategy made from the disclosed view of σ's run at ρ₀ agrees with σ at ρ₀**: the same
plain parts, and the same symbols at the positions that the verifier reads. -/
theorem view_agrees {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)
    (y : E.Str) (σ : Strat Q.loc.shape Unit) (ρ₀ : Rho Q.loc.shape) :
    (σ.run ρ₀).1.plains =
        ((stratFor Q wq (some (Q.loc.dview x y (σ.run ρ₀).1))).run ρ₀).1.plains ∧
      ∀ p ∈ Q.loc.reads x ρ₀ (σ.run ρ₀).1.plains, (σ.run ρ₀).1.read p =
        ((stratFor Q wq (some (Q.loc.dview x y (σ.run ρ₀).1))).run ρ₀).1.read p := by
  refine ⟨(plains_stratOfView _ _ _ _ _ ρ₀).symm, fun p hp => ?_⟩
  refine (read_stratOfView _ _ _ _ _ ρ₀ p _ ?_).symm
  refine if_pos (Or.inl ?_)
  rw [Strat.rho_run]
  exact hp

/-! ## At answers that a first pass has recorded -/

section
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms₁ cms : List (Dig lam)) (x₁ x : Y) (cap : ℕ → ℕ) (σ₁ : Strat Q.loc.shape Unit)
  (co₁ co : Coins lam L)

/-- **Every replay of a first pass's recorded answers has that pass's verifier messages.** The first
pass: at any outer roots, instance, strategy, and coins with as many sibling digests as the
replay's. -/
theorem rho_of_replay (hlen : co₁.path.length = co.path.length) (σ : Strat Q.loc.shape Unit)
    (T : Table (typedOracleFamily lam K L)) (lg : Trace (typedOracleFamily lam K L)) :
    ∀ a ∈ ((rhoO t cms₁ (xin x₁) co₁ cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ₁).record
        mkRun).support,
      ∀ o ∈ ((chainX t Q wq embS embP xin cms x cap σ co).runReplay mkRun T lg a.2).support,
        a.1 = o.1.map fun z => z.1 := fun a ha o ho =>
  (OComp.support_record_runReplay (S := typedOracleFamily lam K L) (fun _ _ e => e)
    (control lateRun t rfl rfl cms₁ cms (xin x₁) (xin x) co₁ co cap hlen Q.loc.shape Q.ann wq.sh
      embS embP 0 .first σ₁ σ) T lg a ha o ho).1

end

/-- From the runs with the verifier messages ρ₀ to all runs, where all runs have them. -/
theorem unguard {s : Shape} {St γ : Type} {ρ₀ : Rho s} {H H' : Res (OutP lam L s) × St → γ}
    {p q : PMF (Res (OutP lam L s) × St)}
    (hp : ∀ o ∈ p.support, (o.1.map fun z => z.1) = .ok ρ₀)
    (hq : ∀ o ∈ q.support, (o.1.map fun z => z.1) = .ok ρ₀)
    (h : p.map (atRho ρ₀ H) = q.map (atRho ρ₀ H')) : p.map H = q.map H' := by
  have key : ∀ (F : Res (OutP lam L s) × St → γ) (u : PMF (Res (OutP lam L s) × St)),
      (∀ o ∈ u.support, (o.1.map fun z => z.1) = .ok ρ₀) →
      u.map (atRho ρ₀ F) = (u.map F).map some := by
    intro F u hu
    rw [PMF.map_comp]
    refine map_congr_support u fun o ho => ?_
    obtain ⟨r, st⟩ := o
    have e := hu _ ho
    cases r with
    | ok z => exact atRho_pos F z st (Res.ok.inj e)
    | noFormat => cases e
    | ranOut j => cases e
  rw [key H p hp, key H' q hq] at h
  exact map_some_inj h

section
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms₁ cms : List (Dig lam)) (x₁ x : Y) (y y' : E.Str) (xt xt' : ℕ → TreeK lam L) (cap : ℕ → ℕ)
  (σ₁ σ σ' : Strat Q.loc.shape Unit) (co₁ co : Coins lam L) (ρ₀ : Rho Q.loc.shape)

/-- **Two strategies with one view at ρ₀, at recorded answers whose pass had the verifier messages
ρ₀: the same law of what is handed out.** -/
theorem ofView_at (hlen : co₁.path.length = co.path.length)
    (hfree : ∀ τ τ' : Tr Q.loc.shape, Puts Q.loc.shape Q.ann wq.sh τ τ' →
      Q.loc.reads x τ.rho τ'.plains = Q.loc.reads x τ.rho τ.plains)
    (hpl : (σ.run ρ₀).1.plains = (σ'.run ρ₀).1.plains)
    (hrd : ∀ p ∈ Q.loc.reads x ρ₀ (σ.run ρ₀).1.plains,
      (σ.run ρ₀).1.read p = (σ'.run ρ₀).1.read p)
    (hx : ∀ p ∈ Q.loc.extReads x ρ₀, E.rd y p = E.rd y' p ∧
      (xt (wq.ext.which p)).inp (wq.ext.leaf p) = (xt' (wq.ext.which p)).inp (wq.ext.leaf p) ∧
      (xt (wq.ext.which p)).lv = (xt' (wq.ext.which p)).lv)
    (T : Table (typedOracleFamily lam K L)) (lg : Trace (typedOracleFamily lam K L))
    (a : Res (Rho Q.loc.shape) × Record (typedOracleFamily lam K L))
    (ha : a ∈ ((rhoO t cms₁ (xin x₁) co₁ cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ₁).record
      mkRun).support) (hρ : a.1 = .ok ρ₀) :
    ((chainX t Q wq embS embP xin cms x cap σ co).runReplay mkRun T lg a.2).map
        (handOut Q wq x y xt true co) =
      ((chainX t Q wq embS embP xin cms x cap σ' co).runReplay mkRun T lg a.2).map
        (handOut Q wq x y' xt' true co) :=
  unguard
    (fun o ho => (rho_of_replay t Q wq embS embP xin cms₁ cms x₁ x cap σ₁ co₁ co hlen σ T lg a ha o
      ho).symm.trans hρ)
    (fun o ho => (rho_of_replay t Q wq embS embP xin cms₁ cms x₁ x cap σ₁ co₁ co hlen σ' T lg a ha o
      ho).symm.trans hρ)
    (ofView t Q wq embS embP xin cms x y y' xt xt' cap σ σ' co ρ₀ hfree hpl hrd hx T lg a.2)

/-- **Any two strategies, coins that are alike, any recorded answers: the same law of the table
after the run.** -/
theorem sameWork_at (co' : Coins lam L) (hco : Alike co co') (T : Table (typedOracleFamily lam K L))
    (lg lg' : Trace (typedOracleFamily lam K L)) (Rc : Record (typedOracleFamily lam K L)) :
    ((chainX t Q wq embS embP xin cms x cap σ co).runReplay mkRun T lg Rc).map (fun o => o.2.base) =
      ((chainX t Q wq embS embP xin cms x cap σ' co').runReplay mkRun T lg' Rc).map
        fun o => o.2.base := by
  have e := congrArg (PMF.map fun w : Res (Rho Q.loc.shape) × Table (typedOracleFamily lam K L) ×
      Record (typedOracleFamily lam K L) × Bool => w.2.1)
    (sameWork lateRun t (runMarks_lateRun t) cms (xin x) co co' cap hco Q.loc.shape Q.ann wq.sh embS
      embP 0 .first σ σ' T lg lg' Rc)
  rw [PMF.map_comp, PMF.map_comp] at e
  exact e

end

end OnBytes.Dry

#print axioms OnBytes.Dry.view_agrees
#print axioms OnBytes.Dry.rho_of_replay
#print axioms OnBytes.Dry.ofView_at
#print axioms OnBytes.Dry.sameWork_at
