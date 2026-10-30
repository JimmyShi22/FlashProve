-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/HoistProofs.lean: proofs of the statements of Ior/Hoist.lean, on a transformation of interactive
oracle reductions (IORs) in which messages that the prover can fix early are sent in one first
message.

Nothing is assumed beyond the hypotheses of the statements and whatever the arguments hold as
proofs.
A marking μ of a shape: each round is kept, or marked, with a value u of its verifier message
(`Marks`: see the head of Ior/Hoist.lean). The old shape is s. The new shape `μ.shape` is the first
message followed by the kept (unmarked) rounds. Read back: taken from the new shape to the old by
`μ.trOld`, `μ.rhoOld`, `μ.orcsOld`, `μ.old`.
The three conditions (Ior/Hoist.lean):
 `μ.OK`: the value is the only value of the verifier message of a marked round.
 `ε.ZeroAt μ`: the errors of the marked rounds are 0.
 `σ.Early μ`: the marked messages do not depend on the verifier messages of the kept rounds.

Main names (statements and hypotheses: Ior/Hoist.lean):
  `doomed_hoist`: "the prover has lost" in the new shape.
  `know_hoist`: round-by-round knowledge soundness of `R.hoist μ`.
  `isLocal_hoist`, `point_hoist`, `acc_hoist`: locality; strings; completeness.
  `prRho_hoist`: probabilities of sets of verifier randomness.
  `exact_hoist`: see its statement.
  `good_hoist`: the bundle of Ior/Chain.lean.
  `early_of_free`, `free_seq`, `ok_app`, `zeroAt_app`: how the conditions are put together along
    `IOR.seq` (`H.Free μ`: Ior/Hoist.lean).

Limits: see Limits in the head of Ior/Hoist.lean.
Terms: lean/GLOSSARY.md.
-/
import Ior.Hoist
import Ior.ExactSeq
import Ior.ChainProofs

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-! ## 1. The maps between the two shapes -/

namespace Marks

theorem rho_tr :
    ∀ {s : Shape} (μ : Marks s) (M : μ.Orc × μ.Plain) (τ : Tr μ.rest), (μ.tr M τ).rho = μ.rho τ.rho
  | [], _, _, _ => rfl
  | _ :: _, (none, μ), M, (_, c, τ) => by
      show (c, (tr μ M τ).rho) = (c, rho μ τ.rho)
      rw [rho_tr μ M τ]
  | _ :: _, (some u, μ), M, τ => by
      show (u, (tr μ (M.1.2, M.2.2) τ).rho) = (u, rho μ τ.rho)
      rw [rho_tr μ _ τ]
      rfl

theorem plains_tr :
    ∀ {s : Shape} (μ : Marks s) (M : μ.Orc × μ.Plain) (τ : Tr μ.rest),
      (μ.tr M τ).plains = μ.plains M.2 τ.plains
  | [], _, _, _ => rfl
  | _ :: _, (none, μ), M, (m, _, τ) => by
      show (m.2, (tr μ M τ).plains) = (m.2, plains μ M.2 τ.plains)
      rw [plains_tr μ M τ]
  | _ :: _, (some _, μ), M, τ => by
      show (M.2.1, (tr μ (M.1.2, M.2.2) τ).plains) = (M.2.1, plains μ M.2.2 τ.plains)
      rw [plains_tr μ _ τ]
      rfl

theorem plM_plains :
    ∀ {s : Shape} (μ : Marks s) (P : μ.Plain) (π : Plains μ.rest), μ.plM (μ.plains P π) = P
  | [], _, (), _ => rfl
  | _ :: _, (none, μ), P, (_, π) => plM_plains μ P π
  | _ :: _, (some _, μ), P, π => by
      show (P.1, plM μ (plains μ P.2 π)) = P
      rw [plM_plains μ P.2 π]
      rfl

theorem plR_plains :
    ∀ {s : Shape} (μ : Marks s) (P : μ.Plain) (π : Plains μ.rest), μ.plR (μ.plains P π) = π
  | [], _, _, () => rfl
  | _ :: _, (none, μ), P, (a, π) => by
      show (a, plR μ (plains μ P π)) = (a, π)
      rw [plR_plains μ P π]
  | _ :: _, (some _, μ), P, π => plR_plains μ P.2 π

theorem read_tr :
    ∀ {s : Shape} (μ : Marks s) (M : μ.Orc × μ.Plain) (τ : Tr μ.rest) (p : OPos s),
      (μ.tr M τ).read p = μ.orcs (μ.rd M.1) τ.read p
  | _ :: _, (none, _), _, (_, _, _), .inl _ => rfl
  | _ :: _, (none, μ), M, (_, _, τ), .inr p => read_tr μ M τ p
  | _ :: _, (some _, _), _, _, .inl _ => rfl
  | _ :: _, (some _, μ), M, τ, .inr p => read_tr μ (M.1.2, M.2.2) τ p

theorem orcs_old_inl :
    ∀ {s : Shape} (μ : Marks s) (oM : (p : μ.Pos) → μ.Sym p) (o : Orcs μ.rest) (p : μ.Pos),
      μ.orcs oM o (μ.old (.inl p)) = μ.symOld (.inl p) (oM p)
  | _ :: _, (none, μ), oM, o, p => orcs_old_inl μ oM (fun q => o (.inr q)) p
  | _ :: _, (some _, _), _, _, .inl _ => rfl
  | _ :: _, (some _, μ), oM, o, .inr p => orcs_old_inl μ (fun q => oM (.inr q)) o p

theorem orcs_old_inr :
    ∀ {s : Shape} (μ : Marks s) (oM : (p : μ.Pos) → μ.Sym p) (o : Orcs μ.rest) (p : OPos μ.rest),
      μ.orcs oM o (μ.old (.inr p)) = μ.symOld (.inr p) (o p)
  | _ :: _, (none, _), _, _, .inl _ => rfl
  | _ :: _, (none, μ), oM, o, .inr p => orcs_old_inr μ oM (fun q => o (.inr q)) p
  | _ :: _, (some _, μ), oM, o, p => orcs_old_inr μ (fun q => oM (.inr q)) o p

theorem symNew_symOld :
    ∀ {s : Shape} (μ : Marks s) (q : OPos μ.shape) (x : OSym μ.shape q),
      μ.symNew q (μ.symOld q x) = x
  | _ :: _, (none, μ), .inl p, x => symNew_symOld μ (.inl p) x
  | _ :: _, (none, _), .inr (.inl _), _ => rfl
  | _ :: _, (none, μ), .inr (.inr p), x => symNew_symOld μ (.inr p) x
  | _ :: _, (some _, _), .inl (.inl _), _ => rfl
  | _ :: _, (some _, μ), .inl (.inr p), x => symNew_symOld μ (.inl p) x
  | _ :: _, (some _, μ), .inr p, x => symNew_symOld μ (.inr p) x

theorem old_surjective : ∀ {s : Shape} (μ : Marks s), Function.Surjective μ.old
  | [], _ => fun p => p.elim
  | _ :: _, (none, μ) => by
      rintro (p | p)
      · exact ⟨.inr (.inl p), rfl⟩
      · obtain ⟨q | q, rfl⟩ := old_surjective μ p
        · exact ⟨.inl q, rfl⟩
        · exact ⟨.inr (.inr q), rfl⟩
  | _ :: _, (some _, μ) => by
      rintro (p | p)
      · exact ⟨.inl (.inl p), rfl⟩
      · obtain ⟨q | q, rfl⟩ := old_surjective μ p
        · exact ⟨.inl (.inr q), rfl⟩
        · exact ⟨.inr q, rfl⟩

theorem rhoR_rho : ∀ {s : Shape} (μ : Marks s) (ρ : Rho μ.rest), μ.rhoR (μ.rho ρ) = ρ
  | [], _, () => rfl
  | _ :: _, (none, μ), (c, ρ) => by
      show (c, rhoR μ (rho μ ρ)) = (c, ρ)
      rw [rhoR_rho μ ρ]
  | _ :: _, (some _, μ), ρ => rhoR_rho μ ρ

theorem rho_rhoR : ∀ {s : Shape} (μ : Marks s), μ.OK → ∀ ρ : Rho s, μ.rho (μ.rhoR ρ) = ρ
  | [], _, _, () => rfl
  | _ :: _, (none, μ), h, (c, ρ) => by
      show (c, rho μ (rhoR μ ρ)) = (c, ρ)
      rw [rho_rhoR μ h ρ]
  | _ :: _, (some u, μ), h, (c, ρ) => by
      show (u, rho μ (rhoR μ ρ)) = (c, ρ)
      rw [rho_rhoR μ h.2 ρ, h.1 c]

variable {s : Shape} (μ : Marks s)

theorem rho_trOld (τ : Tr μ.shape) : (μ.trOld τ).rho = μ.rhoOld τ.rho := rho_tr μ τ.1 τ.2.2

theorem plains_trOld (τ : Tr μ.shape) : (μ.trOld τ).plains = μ.plains τ.plains.1 τ.plains.2 :=
  plains_tr μ τ.1 τ.2.2

theorem read_trOld (τ : Tr μ.shape) : (μ.trOld τ).read = μ.orcsOld τ.read :=
  funext fun p => read_tr μ τ.1 τ.2.2 p

/-- What a transcript read back has at the old position of q is what the transcript has at q. -/
theorem read_old (τ : Tr μ.shape) (q : OPos μ.shape) :
    (μ.trOld τ).read (μ.old q) = μ.symOld q (τ.read q) := by
  rw [read_trOld]
  rcases q with p | p
  · exact orcs_old_inl μ _ _ p
  · exact orcs_old_inr μ _ _ p

/-- Under `μ.OK`, the verifier's randomness of the two shapes corresponds one to one. -/
def rhoEquiv (h : μ.OK) : Rho μ.shape ≃ Rho s where
  toFun := μ.rhoOld
  invFun ρ := ((), μ.rhoR ρ)
  left_inv ρ := Prod.ext rfl (rhoR_rho μ ρ.2)
  right_inv ρ := rho_rhoR μ h ρ

end Marks

namespace Strat

/-- The run of the kept rounds, with the marked messages along the same verifier messages, is the
old run. -/
theorem run_drop :
    ∀ {s : Shape} (μ : Marks s) {β : Type} (σ : Strat s β) (ρ : Rho μ.rest),
      μ.tr (σ.masksAt μ ρ) ((σ.drop μ).run ρ).1 = (σ.run (μ.rho ρ)).1 ∧
      ((σ.drop μ).run ρ).2 = (σ.run (μ.rho ρ)).2
  | [], _, _, _, _ => ⟨rfl, rfl⟩
  | _ :: _, (none, μ), _, (m, k), (c, ρ) => by
      obtain ⟨h1, h2⟩ := run_drop μ (k c) ρ
      refine ⟨?_, h2⟩
      show (m, c, μ.tr ((k c).masksAt μ ρ) (((k c).drop μ).run ρ).1) =
        (m, c, ((k c).run (μ.rho ρ)).1)
      rw [h1]
  | _ :: _, (some u, μ), _, (m, k), ρ => by
      obtain ⟨h1, h2⟩ := run_drop μ (k u) ρ
      refine ⟨?_, h2⟩
      show (m, u, μ.tr ((k u).masksAt μ ρ) (((k u).drop μ).run ρ).1) =
        (m, u, ((k u).run (μ.rho ρ)).1)
      rw [h1]

variable {s : Shape} (μ : Marks s) (ρ₀ : Rho μ.rest) {β : Type} (σ : Strat s β)

theorem run_hoist_snd (ρ : Rho μ.shape) : ((σ.hoist μ ρ₀).run ρ).2 = (σ.run (μ.rhoOld ρ)).2 :=
  (run_drop μ σ ρ.2).2

theorem run_hoist_fst (h : σ.Early μ) (ρ : Rho μ.shape) :
    μ.trOld ((σ.hoist μ ρ₀).run ρ).1 = (σ.run (μ.rhoOld ρ)).1 := by
  show μ.tr (σ.masksAt μ ρ₀) ((σ.drop μ).run ρ.2).1 = _
  rw [h ρ₀ ρ.2]
  exact (run_drop μ σ ρ.2).1

end Strat

/-! ## 2. "The prover has lost" -/

theorem doomed_rest :
    ∀ {s : Shape} (μ : Marks s) (ε : Err s) (bad : Tr s → Prop),
      ε.ZeroAt μ → Doomed s ε bad → ∀ M, Doomed μ.rest (ε.rest μ) fun τ => bad (μ.tr M τ)
  | [], _, _, _, _, h, _ => h
  | _ :: _, (none, μ), (_, ε), bad, hz, h, M => fun m =>
      le_trans (cnt_mono fun c hc hd => hc (doomed_rest μ ε (fun τ => bad (m, c, τ)) hz hd M)) (h m)
  | r :: s, (some u, μ), (e, ε), bad, hz, h, M => by
      have h1 : cnt (fun c : r.Chal => ¬ Doomed s ε fun τ => bad ((M.1.1, M.2.1), c, τ)) ≤ e :=
        h (M.1.1, M.2.1)
      have h2 : Doomed s ε fun τ => bad ((M.1.1, M.2.1), u, τ) := by
        by_contra hn
        have h3 : 1 ≤ cnt (fun c : r.Chal => ¬ Doomed s ε fun τ => bad ((M.1.1, M.2.1), c, τ)) := by
          rw [← cnt_eq_const u]
          exact cnt_mono fun c hc => hc ▸ hn
        rw [hz.1] at h1
        omega
      exact doomed_rest μ ε _ hz.2 h2 (M.1.2, M.2.2)

theorem doomed_hoist : Spec.doomed_hoist := by
  intro s μ ε bad hz h M
  rw [cnt_false fun c hc => hc (doomed_rest μ ε bad hz h M)]

/-! ## 3. The reduction, its honest side, the bundle -/

namespace IOR
variable {K Xi Xo : Type} {Ei Eo : ExtSpec} {Wi Wo : Type} (R : IOR Xi Ei Xo Eo) (μ : Marks R.shape)

theorem mem_reads_hoist {ρ : Rho μ.shape} {q : OPos μ.shape} :
    q ∈ (R.hoist μ).reads ρ ↔ μ.old q ∈ R.reads (μ.rhoOld ρ) := by
  show q ∈ Finset.preimage (R.reads (μ.rhoOld ρ)) μ.old μ.old_injective.injOn ↔ _
  exact Finset.mem_preimage

theorem mem_srcO_hoist {ρ : Rho μ.shape} {e : Eo.Pos} {q : OPos μ.shape} :
    q ∈ (R.hoist μ).srcO ρ e ↔ μ.old q ∈ R.srcO (μ.rhoOld ρ) e := by
  show q ∈ Finset.preimage (R.srcO (μ.rhoOld ρ) e) μ.old μ.old_injective.injOn ↔ _
  exact Finset.mem_preimage

theorem mem_image_old {inst : DecidableEq (OPos R.shape)}
    {T : Finset (OPos μ.shape)} {q : OPos μ.shape} :
    μ.old q ∈ @Finset.image _ _ inst μ.old T ↔ q ∈ T :=
  ⟨fun h => by
    obtain ⟨q', hq', e⟩ := Finset.mem_image.1 h
    rwa [← μ.old_injective e], fun h => Finset.mem_image_of_mem _ h⟩

open Classical in
/-- What the simulator is given of the implicit instance is the same. -/
theorem given_hoist (ρ : Rho μ.shape) (T : Finset (OPos μ.shape)) :
    (R.hoist μ).given ρ T = R.given (μ.rhoOld ρ) (T.image μ.old) := by
  ext p
  rw [mem_given, mem_given]
  constructor
  · rintro (h | ⟨q, hq, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨μ.old q, hq.imp (mem_reads_hoist R μ).1 (mem_image_old R μ).2, h⟩
  · rintro (h | ⟨r, hr, h⟩)
    · exact Or.inl h
    · obtain ⟨q, rfl⟩ := μ.old_surjective r
      exact Or.inr ⟨q, hr.imp (mem_reads_hoist R μ).2 (mem_image_old R μ).1, h⟩

open Classical in
theorem shown_hoist (τ : Tr μ.shape) (T : Finset (OPos μ.shape)) (q : OPos μ.shape) :
    (R.hoist μ).Shown τ.rho T q ↔ R.Shown (μ.trOld τ).rho (T.image μ.old) (μ.old q) := by
  unfold Shown
  rw [μ.rho_trOld]
  exact or_congr (mem_reads_hoist R μ) (or_congr (mem_image_old R μ).symm Iff.rfl)

open Classical in
/-- What a run shows in the new shape is what the run read back shows, written for the new shape. -/
theorem view_hoist (T : Finset (OPos μ.shape)) (τ : Tr μ.shape) :
    (R.hoist μ).view T τ = View.hoist μ (R.view (T.image μ.old) (μ.trOld τ)) := by
  refine View.ext' ?_ (funext fun q => ?_)
  · show τ.plains = (μ.plM (μ.trOld τ).plains, μ.plR (μ.trOld τ).plains)
    rw [μ.plains_trOld, μ.plM_plains, μ.plR_plains]
    rfl
  · show ((R.hoist μ).view T τ).orc q =
      Option.map (μ.symNew q) ((R.view (T.image μ.old) (μ.trOld τ)).orc (μ.old q))
    by_cases h : (R.hoist μ).Shown τ.rho T q
    · have e1 : ((R.hoist μ).view T τ).orc q = some (τ.read q) :=
        view_orc_of_shown (R := R.hoist μ) T τ h
      have e2 : (R.view (T.image μ.old) (μ.trOld τ)).orc (μ.old q) =
          some ((μ.trOld τ).read (μ.old q)) :=
        view_orc_of_shown (R := R) _ _ ((shown_hoist R μ τ T q).1 h)
      rw [e2]
      refine e1.trans ?_
      show some (τ.read q) = some (μ.symNew q ((μ.trOld τ).read (μ.old q)))
      rw [μ.read_old, μ.symNew_symOld]
    · have e1 : ((R.hoist μ).view T τ).orc q = none := view_orc_of_not_shown (R := R.hoist μ) T τ h
      have e2 : (R.view (T.image μ.old) (μ.trOld τ)).orc (μ.old q) = none :=
        view_orc_of_not_shown (R := R) _ _ fun h' => h ((shown_hoist R μ τ T q).2 h')
      rw [e2]
      exact e1

end IOR

open IOR

theorem know_hoist : Spec.know_hoist := by
  intro Xi Xo Ei Eo R μ Wi Wo on RA RB ext ε hz h a ha
  refine Doomed.mono _ _ ?_ (doomed_hoist R.shape μ ε _ hz (h a ha))
  intro τ hτ b w hb hw
  have h1 : RA a (ext a.2 (μ.trOld τ).read w) := hτ b w hb hw
  have e : (μ.trOld τ).read = μ.orcsOld τ.read := μ.read_trOld τ
  show RA a (ext a.2 (μ.orcsOld τ.read) w)
  rw [← e]
  exact h1

theorem isLocal_hoist : Spec.isLocal_hoist := by
  intro Xi Xo Ei Eo R μ h
  refine ⟨fun x y y' τ τ' hρ hpl hy hτ => ?_, fun y y' τ τ' e hρ hpl hy hτ => ?_⟩
  · refine h.out x y y' (μ.trOld τ) (μ.trOld τ')
      ((μ.rho_trOld τ).trans ((congrArg μ.rhoOld hρ).trans (μ.rho_trOld τ').symm))
      ((μ.plains_trOld τ).trans
        ((congrArg (fun π : Plains μ.shape => μ.plains π.1 π.2) hpl).trans
          (μ.plains_trOld τ').symm))
      ?_ ?_
    · intro p hp
      rw [μ.rho_trOld] at hp
      exact hy p hp
    · intro p hp
      rw [μ.rho_trOld] at hp
      obtain ⟨q, rfl⟩ := μ.old_surjective p
      rw [μ.read_old, μ.read_old]
      exact congrArg (μ.symOld q) (hτ q ((mem_reads_hoist R μ).2 hp))
  · refine h.imp y y' (μ.trOld τ) (μ.trOld τ') e
      ((μ.rho_trOld τ).trans ((congrArg μ.rhoOld hρ).trans (μ.rho_trOld τ').symm))
      ((μ.plains_trOld τ).trans
        ((congrArg (fun π : Plains μ.shape => μ.plains π.1 π.2) hpl).trans
          (μ.plains_trOld τ').symm))
      ?_ ?_
    · intro p hp
      rw [μ.rho_trOld] at hp
      exact hy p hp
    · intro p hp
      rw [μ.rho_trOld] at hp
      obtain ⟨q, rfl⟩ := μ.old_surjective p
      rw [μ.read_old, μ.read_old]
      exact congrArg (μ.symOld q) (hτ q ((mem_srcO_hoist R μ).2 hp))

namespace Marks

/-- If all oracles of the old shape are strings (`s.IsPoint`), so are the kept rounds'. -/
def restPoint : {s : Shape} → (μ : Marks s) → s.IsPoint → μ.rest.IsPoint
  | [], _, _ => ()
  | _ :: _, (none, μ), (h, hs) => (h, restPoint μ hs)
  | _ :: _, (some _, μ), (_, hs) => restPoint μ hs

/-- If all oracles of the old shape are strings (`s.IsPoint`), the oracle part of the first message
is a string. -/
def frontPoint : {s : Shape} → (μ : Marks s) → s.IsPoint → μ.front.IsPoint
  | [], _, _ =>
      { finPos := inferInstanceAs (Fintype Empty),
        decPos := inferInstanceAs (DecidableEq Empty), ofSyms := fun _ => (),
        rd_ofSyms := fun _ p => p.elim, ofSyms_rd := fun _ => rfl, zero := fun p => p.elim }
  | _ :: _, (none, μ), (_, hs) => frontPoint μ hs
  | r :: _, (some _, μ), (h, hs) =>
      { finPos := @instFintypeSum r.Pos μ.Pos h.finPos (frontPoint μ hs).finPos
        decPos := @instDecidableEqSum r.Pos μ.Pos h.decPos (frontPoint μ hs).decPos
        ofSyms := fun f =>
          (h.ofSyms fun p => f (.inl p), (frontPoint μ hs).ofSyms fun p => f (.inr p))
        rd_ofSyms := fun f p => match p with
          | .inl p => h.rd_ofSyms (fun p => f (.inl p)) p
          | .inr p => (frontPoint μ hs).rd_ofSyms (fun p => f (.inr p)) p
        ofSyms_rd := fun o => Prod.ext (h.ofSyms_rd o.1) ((frontPoint μ hs).ofSyms_rd o.2)
        zero := fun p => match p with
          | .inl p => h.zero p
          | .inr p => (frontPoint μ hs).zero p }

end Marks

theorem point_hoist : Spec.point_hoist := fun _ μ ⟨h⟩ => ⟨(μ.frontPoint h, μ.restPoint h)⟩

theorem prRho_hoist : Spec.prRho_hoist := by
  intro s μ S h
  unfold prRho
  rw [← map_unif_equiv (μ.rhoEquiv h), pr_map]
  rfl

theorem acc_hoist : Spec.acc_hoist := by
  intro Xi Xo Ei Eo R μ ρ₀ Wi Wo H Ri Ro hE hA x y w c ρ hR hρ
  have h := hA x y w c (μ.rhoOld ρ) hR hρ
  have e1 := Strat.run_hoist_fst μ ρ₀ (H.strat w x c) (hE w x c) ρ
  have e2 := Strat.run_hoist_snd μ ρ₀ (H.strat w x c) ρ
  show R.out x y (μ.trOld (((H.strat w x c).hoist μ ρ₀).run ρ).1) =
      some (((H.strat w x c).hoist μ ρ₀).run ρ).2.1 ∧
    Ro (((H.strat w x c).hoist μ ρ₀).run ρ).2.1
      (R.imp y (μ.trOld (((H.strat w x c).hoist μ ρ₀).run ρ).1))
      (((H.strat w x c).hoist μ ρ₀).run ρ).2.2
  rw [e1, e2]
  exact h

theorem exact_hoist : Spec.exact_hoist := by
  classical
  intro Xi Xo Ei Eo R μ ρ₀ Wi Wo H Ri bud S hE hS x y w hR ρ hρ T hT
  have h := hS x y w hR (μ.rhoOld ρ) hρ (T.image μ.old) hT
  show _ = (S x (μ.rhoOld ρ) (T.image μ.old) (Ei.ans ((R.hoist μ).given ρ T) y)).map
      (Option.map (View.hoist μ))
  rw [given_hoist, ← h]
  by_cases hw : μ.rhoOld ρ ∈ H.withheld w x
  · rw [H.output_of_mem _ hw,
      (H.hoist μ ρ₀).output_of_mem T (show ρ ∈ (H.hoist μ ρ₀).withheld w x from hw), PMF.pure_map]
    rfl
  · rw [H.output_of_not_mem _ hw,
      (H.hoist μ ρ₀).output_of_not_mem T (show ρ ∉ (H.hoist μ ρ₀).withheld w x from hw),
      PMF.map_comp]
    refine congrArg (fun g => PMF.map g (unif H.Coin)) (funext fun c => ?_)
    show some ((R.hoist μ).view T (((H.strat w x c).hoist μ ρ₀).run ρ).1) =
      some (View.hoist μ (R.view (T.image μ.old) ((H.strat w x c).run (μ.rhoOld ρ)).1))
    rw [view_hoist, Strat.run_hoist_fst μ ρ₀ _ (hE w x c) ρ]

theorem good_hoist : Spec.good_hoist := by
  intro K Xi Xo Ei Eo R μ ρ₀ Wi Wo H A B ext P hOK hz hE g
  obtain ⟨S, hS⟩ := g.exact
  exact {
    point := point_hoist _ μ g.point
    isLocal := isLocal_hoist _ _ _ _ R μ g.isLocal
    acc := acc_hoist _ _ _ _ R μ ρ₀ _ _ H _ _ hE g.acc
    onOut := fun a τ b ha hb => g.onOut a (μ.trOld τ) b ha hb
    keeps := fun w x c ρ => by
      show B.core (((H.strat w x c).hoist μ ρ₀).run ρ).2.2 = A.core w
      rw [Strat.run_hoist_snd]
      exact g.keeps w x c _
    prBad := le_trans (le_of_eq (prRho_hoist _ μ H.Bad hOK)) g.prBad
    cover := fun w x ρ hρ => g.cover w x hρ
    prCov := fun k => le_trans (le_of_eq (prRho_hoist _ μ (P.cov k) hOK)) (g.prCov k)
    know := know_hoist _ _ _ _ R μ _ _ A.on A.relR B.relR ext P.err hz g.know
    exact := ⟨simHoist μ S, exact_hoist _ _ _ _ R μ ρ₀ _ _ H A.rel P.bud S hE hS⟩ }

/-! ## 4. The conditions along a chain -/

theorem early_of_free : Spec.early_of_free := fun _ _ _ _ _ _ _ _ _ h w x c ρ ρ' => h w x w x c ρ ρ'

theorem ok_app : Spec.ok_app := by
  intro s
  induction s with
  | nil => exact fun _ _ _ _ h => h
  | cons r s ih =>
      rintro t ⟨_ | u, μ⟩ ν h h'
      · exact ih t μ ν h h'
      · exact ⟨h.1, ih t μ ν h.2 h'⟩

theorem zeroAt_app : Spec.zeroAt_app := by
  intro s
  induction s with
  | nil => exact fun _ _ _ _ _ _ h => h
  | cons r s ih =>
      rintro t ⟨_ | u, μ⟩ ν ⟨e, ε⟩ ε' h h'
      · exact ih t μ ν ε ε' h h'
      · exact ⟨h.1, ih t μ ν ε ε' h.2 h'⟩

namespace Marks

/-- The marked messages of two shapes in a row, from those of the two. -/
def joinM :
    {s t : Shape} → (μ : Marks s) → (ν : Marks t) → μ.Orc × μ.Plain →
    ν.Orc × ν.Plain → (μ.app ν).Orc × (μ.app ν).Plain
  | [], _, _, _, _, N => N
  | _ :: _, _, (none, μ), ν, M, N => joinM μ ν M N
  | _ :: _, _, (some _, μ), ν, M, N =>
    ((M.1.1, (joinM μ ν (M.1.2, M.2.2) N).1), (M.2.1, (joinM μ ν (M.1.2, M.2.2) N).2))

end Marks

/-- The marked messages of a composed strategy are those of its first part and of its second part at
some value b, each along some verifier messages. -/
theorem masksAt_bind :
    ∀ {s t : Shape} (μ : Marks s) (ν : Marks t) {β γ : Type} (σ : Strat s β)
        (g : β → Strat t γ) (ρ : Rho (μ.app ν).rest),
      ∃ ρ₁ ρ₂ b,
        (Strat.bind σ g).masksAt (μ.app ν) ρ = μ.joinM ν (σ.masksAt μ ρ₁) ((g b).masksAt ν ρ₂)
  | [], _, _, _, _, _, σ, _, ρ => ⟨(), ρ, σ, rfl⟩
  | _ :: _, _, (none, μ), ν, _, _, (_, k), g, (c, ρ) => by
      obtain ⟨ρ₁, ρ₂, b, h⟩ := masksAt_bind μ ν (k c) g ρ
      exact ⟨(c, ρ₁), ρ₂, b, h⟩
  | _ :: _, _, (some u, μ), ν, _, _, (m, k), g, ρ => by
      obtain ⟨ρ₁, ρ₂, b, h⟩ := masksAt_bind μ ν (k u) g ρ
      refine ⟨ρ₁, ρ₂, b, ?_⟩
      show ((m.1, ((Strat.bind (k u) g).masksAt (μ.app ν) ρ).1),
          (m.2, ((Strat.bind (k u) g).masksAt (μ.app ν) ρ).2)) = _
      rw [h]
      rfl

theorem free_seq : Spec.free_seq := by
  intro X₁ X₂ X₃ E₁ E₂ E₃ R₁ R₂ μ₁ μ₂ W₁ W₂ W₃ H₁ H₂ h₁ h₂ w x w' x' c ρ ρ'
  obtain ⟨a₁, a₂, b, e⟩ := masksAt_bind μ₁ μ₂ (H₁.strat w x c.1) (fun o => H₂.strat o.2 o.1 c.2) ρ
  obtain ⟨a₁', a₂', b', e'⟩ :=
    masksAt_bind μ₁ μ₂ (H₁.strat w' x' c.1) (fun o => H₂.strat o.2 o.1 c.2) ρ'
  refine e.trans (Eq.trans ?_ e'.symm)
  rw [h₁ w x w' x' c.1 a₁ a₁', h₂ b.2 b.1 b'.2 b'.1 c.2 a₂ a₂']

end Iop
