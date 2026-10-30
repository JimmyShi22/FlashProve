-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LateWorld/Session.lean: ONE COMPILED RUN OF THE HONEST SIDE, LAID LATE, IS A RUN OF THE GAME
FOLLOWED BY THE REDUCTION's SECOND PASS. It proves Spec.session
(Johnson/LateWorld/SpecSession.lean).

General lemmas. This file states no goal of the release.

How.
  1. A run with fresh answers at the deferred queries is "a first, dry pass, at whatever letters,
     then a replay of its recorded answers" (late_eq_replay: Spec.control with record_runReplay,
     Rom/Handle/Laws.lean). The strategy's coins are drawn after the first pass: two independent
     draws.
  2. At each (outcome, recorded answers) of the first pass every replay has that pass's outcome
     (rho_of_replay, OnBytes/Dry/ViewAt.lean). So it is known, before the replay, whether a string
     will be handed out.
  3. If none is (a search ran out; no format; the messages are withheld): what is handed out is the
     table after the run, and that has one law at all strategies and at coins that are alike
     (sameWork_at).
  4. If one is: the honest strategy and the strategy made from its run's disclosed view have one
     view (view_agrees); the external strings and the tables' opened leaves made from the view agree
     with the honest side's at the positions that are read (ext_agrees); the coins made from the
     view's plain parts are the run's. So both hand out the same (ofView_at).

Main names.
  handOut_false    what is handed out where no string is.
  ext_agrees       the fourth premise of Spec.ofView, at what the second pass makes from a view.
  late_eq_replay   step 1.
  session          THE STATEMENT.
  interact_pass2A  the second pass as a program against a challenger is the second pass as a law.

Limits. One run.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LateWorld.SpecSession
import OnBytes.Dry.ViewAt

set_option autoImplicit false

noncomputable section

namespace OnBytes.LateWorld
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

section
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) (x : Y)

/-- Where no string is handed out: the table after the run. -/
theorem handOut_false (y : E.Str) (xt : ℕ → TreeK lam L) (co : Coins lam L)
    (o : Res (OutP lam L Q.loc.shape) × RSt (typedOracleFamily lam K L) (Table (typedOracleFamily lam K L))) :
    handOut Q wq x y xt false co o = (none, o.2.base) := rfl

/-- The fourth premise of Spec.ofView, at what the second pass makes from the disclosed view of a
transcript with the verifier messages ρ₀. -/
theorem ext_agrees (hE : wq.ext.OK) (embE : E.Sym → Body L) (y : E.Str) (xtR xtW : ℕ → TreeK lam L)
    (hT : TabAgree Q wq embE y xtR xtW) (τ : Tr Q.loc.shape) (ρ₀ : Rho Q.loc.shape)
    (hτ : τ.rho = ρ₀) :
    ∀ p ∈ Q.loc.extReads x ρ₀,
      E.rd y p = E.rd (wq.ext.build (ansOf Q (some (Q.loc.dview x y τ)))) p ∧
      (xtR (wq.ext.which p)).inp (wq.ext.leaf p) =
        (namedAt Q wq xtW embE (ansOf Q (some (Q.loc.dview x y τ))) (wq.ext.which p)).inp
          (wq.ext.leaf p) ∧
      (xtR (wq.ext.which p)).lv =
        (namedAt Q wq xtW embE (ansOf Q (some (Q.loc.dview x y τ))) (wq.ext.which p)).lv := by
  intro p hp
  have hans : ∀ p', ansOf Q (some (Q.loc.dview x y τ)) p' = Q.loc.extAns x ρ₀ y p' := fun p' => by
    rw [← hτ]
    rfl
  have hsome : ∀ p', (ansOf Q (some (Q.loc.dview x y τ)) p').isSome = true →
      ansOf Q (some (Q.loc.dview x y τ)) p' = some (E.rd y p') := fun p' h' => by
    rw [hans] at h' ⊢
    unfold InteractiveOracleProof.extAns at h' ⊢
    by_cases hm : p' ∈ Q.loc.extReads x ρ₀
    · rw [if_pos hm]
    · rw [if_neg hm] at h'
      cases h'
  have hp' : ansOf Q (some (Q.loc.dview x y τ)) p = some (E.rd y p) := by
    rw [hans]
    exact if_pos hp
  refine ⟨(hE.build_rd _ p _ hp').symm, ?_, hT.lv _⟩
  show _ = (match wq.ext.all.find? fun p' =>
      decide (wq.ext.which p' = wq.ext.which p) && decide (wq.ext.leaf p' = wq.ext.leaf p) &&
        (ansOf Q (some (Q.loc.dview x y τ)) p').isSome with
    | some p' => (⟨((ansOf Q (some (Q.loc.dview x y τ)) p').map embE).getD
        ((xtW (wq.ext.which p)).inp (wq.ext.leaf p)).body,
        ((xtW (wq.ext.which p)).inp (wq.ext.leaf p)).salt⟩ : LeafIn L)
    | none => (xtW (wq.ext.which p)).inp (wq.ext.leaf p))
  cases hf : wq.ext.all.find? fun p' =>
      decide (wq.ext.which p' = wq.ext.which p) && decide (wq.ext.leaf p' = wq.ext.leaf p) &&
        (ansOf Q (some (Q.loc.dview x y τ)) p').isSome with
  | none =>
    have h0 := List.find?_eq_none.1 hf p (hE.complete p)
    simp [hp'] at h0
  | some p' =>
    have h1 := List.find?_some hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨⟨hw, hl⟩, hs⟩ := h1
    have hb := hT.body p'
    rw [hw, hl] at hb
    show _ = (⟨((ansOf Q (some (Q.loc.dview x y τ)) p').map embE).getD
        ((xtW (wq.ext.which p)).inp (wq.ext.leaf p)).body,
        ((xtW (wq.ext.which p)).inp (wq.ext.leaf p)).salt⟩ : LeafIn L)
    rw [hsome p' hs, ← hT.salt]
    show _ = (⟨embE (E.rd y p'), ((xtR (wq.ext.which p)).inp (wq.ext.leaf p)).salt⟩ : LeafIn L)
    rw [← hb]

end

section
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms₁ cms : List (Dig lam)) (x : Y) (cap : ℕ → ℕ)

/-- **A run with fresh answers is a first, dry pass, at whatever letters, then a replay of its
recorded answers.** F: any function of the run's end. -/
theorem late_eq_replay {γ : Type} (co₁ co : Coins lam L) (hlen : co₁.path.length = co.path.length)
    (σ : Strat Q.loc.shape Unit) (T : Table (typedOracleFamily lam K L))
    (F : Res (OutP lam L Q.loc.shape) × RSt (typedOracleFamily lam K L) (Table (typedOracleFamily lam K L)) → γ) :
    ((chainX t Q wq embS embP xin cms x cap σ co).runDefer mkRun T []).map
        (fun o => F (o.1, ⟨o.2.1, o.2.2, [], false⟩)) =
      (pass1 t Q wq embS embP xin cms₁ x cap co₁).bind fun a =>
        ((chainX t Q wq embS embP xin cms x cap σ co).runReplay mkRun T [] a.2).map F := by
  have e := congrArg (PMF.map fun z : (Res (Rho Q.loc.shape) × Record (typedOracleFamily lam K L)) ×
      Res (OutP lam L Q.loc.shape) × RSt (typedOracleFamily lam K L) (Table (typedOracleFamily lam K L)) => F z.2)
    (OComp.record_runReplay (S := typedOracleFamily lam K L) (fun _ _ e => e)
      (OnBytes.Dry.control lateRun t rfl rfl cms₁ cms (xin x) (xin x) co₁ co cap hlen Q.loc.shape
        Q.ann wq.sh embS embP 0 .first (Strat.dflt _ ()) σ) T [])
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at e
  exact e.symm

end

/-- **THE STATEMENT.** -/
theorem session : Spec.session := by
  intro I X lam K L t Y E Q wq embS embP xin cms₁ cms x xtR xtW cap embE Wt H w stop co₁ coK coV hE
    hfree hstop hcoV hal hlen hT T
  -- the left side: the first pass, then the strategy's coins, then a replay
  have hL : ((unif H.Coin).bind fun κ =>
      lateProof t Q wq embS embP xin cms x (H.ext w) xtR cap stop (H.strat w x κ) (coK κ) T) =
      (pass1 t Q wq embS embP xin cms₁ x cap co₁).bind fun a => (unif H.Coin).bind fun κ =>
        ((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun T []
          a.2).map fun o => handOut Q wq x (H.ext w) xtR (goOf stop o.1) (coK κ) o := by
    rw [PMF.bind_comm]
    refine congrArg _ (funext fun κ => ?_)
    exact late_eq_replay t Q wq embS embP xin cms₁ cms x cap co₁ (coK κ) (hlen κ) (H.strat w x κ) T
      fun o => handOut Q wq x (H.ext w) xtR (goOf stop o.1) (coK κ) o
  rw [hL]
  unfold Hiop.Seeded.runAt
  rw [PMF.bind_bind]
  refine Rom.bind_congr_support _ fun a ha => ?_
  -- every replay of these recorded answers has the first pass's outcome
  have hρ : ∀ (σ : Strat Q.loc.shape Unit) (co : Coins lam L), co₁.path.length = co.path.length →
      ∀ o ∈ ((chainX t Q wq embS embP xin cms x cap σ co).runReplay mkRun T [] a.2).support,
        a.1 = o.1.map fun z => z.1 := fun σ co hl =>
    rho_of_replay t Q wq embS embP xin cms₁ cms x x cap (Strat.dflt _ ()) co₁ co hl σ T [] a ha
  -- where no string is handed out
  have hnone : (∀ z : OutP lam L Q.loc.shape, a.1 = .ok z.1 → stop z.1 = true) →
      ((unif H.Coin).bind fun κ =>
        ((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun T []
          a.2).map fun o => handOut Q wq x (H.ext w) xtR (goOf stop o.1) (coK κ) o) =
      pass2 t Q wq embS embP xin cms x xtW cap embE none (coV none) a.2 T := by
    intro hz
    have h1 : ∀ κ, (((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun
        T [] a.2).map fun o => handOut Q wq x (H.ext w) xtR (goOf stop o.1) (coK κ) o) =
        pass2 t Q wq embS embP xin cms x xtW cap embE none (coV none) a.2 T := by
      intro κ
      have h2 : (((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun
          T [] a.2).map fun o => handOut Q wq x (H.ext w) xtR (goOf stop o.1) (coK κ) o) =
          (((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun
            T [] a.2).map fun o => o.2.base).map fun B => (none, B) := by
        rw [PMF.map_comp]
        refine map_congr_support _ fun o ho => ?_
        have e := hρ _ _ (hlen κ) o ho
        have hg : goOf stop o.1 = false := by
          obtain ⟨r, st⟩ := o
          cases r with
          | ok z =>
            show (!stop z.1) = false
            rw [hz z e]
            rfl
          | noFormat => rfl
          | ranOut j => rfl
        rw [hg]
        rfl
      rw [h2, sameWork_at t Q wq embS embP xin cms x cap (H.strat w x κ) (Strat.dflt _ ()) (coK κ)
        (coV none) (hal κ) T [] [] a.2, PMF.map_comp]
      rfl
    simp only [h1]
    exact PMF.bind_const _ _
  obtain ⟨r, Rc⟩ := a
  cases r with
  | noFormat =>
    refine (hnone fun z e => by cases e).trans ?_
    show _ = (PMF.pure ((Res.noFormat, Rc), none)).bind _
    rw [PMF.pure_bind]
    rfl
  | ranOut j =>
    refine (hnone fun z e => by cases e).trans ?_
    show _ = (PMF.pure ((Res.ranOut j, Rc), none)).bind _
    rw [PMF.pure_bind]
    rfl
  | ok ρ₀ =>
    show _ = ((H.output w x ρ₀).map fun o => ((Res.ok ρ₀, Rc), o)).bind _
    rw [PMF.bind_map]
    unfold Honest.output
    by_cases hw : ρ₀ ∈ H.withheld w x
    · rw [if_pos hw, PMF.pure_bind]
      refine (hnone fun z e => ?_).trans rfl
      obtain rfl : ρ₀ = z.1 := Res.ok.inj e
      exact (hstop _).2 hw
    · rw [if_neg hw, PMF.bind_map]
      refine congrArg _ (funext fun κ => ?_)
      have hs : stop ρ₀ = false := by
        cases hb : stop ρ₀ with
        | false => rfl
        | true => exact absurd ((hstop _).1 hb) hw
      have h2 : (((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun
          T [] Rc).map fun o => handOut Q wq x (H.ext w) xtR (goOf stop o.1) (coK κ) o) =
          ((chainX t Q wq embS embP xin cms x cap (H.strat w x κ) (coK κ)).runReplay mkRun
            T [] Rc).map (handOut Q wq x (H.ext w) xtR true (coK κ)) := by
        refine map_congr_support _ fun o ho => ?_
        have e := hρ _ _ (hlen κ) o ho
        obtain ⟨r', st⟩ := o
        cases r' with
        | ok z =>
          obtain rfl : ρ₀ = z.1 := Res.ok.inj e
          show handOut Q wq x (H.ext w) xtR (!stop z.1) (coK κ) _ = _
          rw [hs]
          rfl
        | noFormat => cases e
        | ranOut j => cases e
      rw [h2]
      have hv := view_agrees Q wq x (H.ext w) (H.strat w x κ) ρ₀
      have hfin := ofView_at t Q wq embS embP xin cms₁ cms x x (H.ext w)
        (wq.ext.build (ansOf Q (some (Q.loc.dview x (H.ext w) ((H.strat w x κ).run ρ₀).1)))) xtR
        (namedAt Q wq xtW embE (ansOf Q (some (Q.loc.dview x (H.ext w)
          ((H.strat w x κ).run ρ₀).1)))) cap (Strat.dflt _ ()) (H.strat w x κ)
        (stratFor Q wq (some (Q.loc.dview x (H.ext w) ((H.strat w x κ).run ρ₀).1))) co₁ (coK κ) ρ₀
        (hlen κ) hfree hv.1 hv.2
        (ext_agrees Q wq x hE embE (H.ext w) xtR xtW hT _ ρ₀ (Strat.rho_run _ _)) T []
        (Res.ok ρ₀, Rc) ha rfl
      refine hfin.trans ?_
      show _ = pass2 t Q wq embS embP xin cms x xtW cap embE
        (some (Q.loc.dview x (H.ext w) ((H.strat w x κ).run ρ₀).1))
        (coV (some ((H.strat w x κ).run ρ₀).1.plains)) Rc T
      rw [hcoV κ ρ₀ hw]
      rfl

/-- The second pass as a program against a challenger, which it neither asks nor calls. -/
theorem interact_pass2A {Out In : Type} (G : World (typedOracleFamily lam K L) Out In) (t : Tag) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (cms : List (Dig lam)) (x : Y) (xt : ℕ → TreeK lam L) (cap : ℕ → ℕ) (embE : E.Sym → Body L)
    (v : Option (DView Q.loc)) (co : Coins lam L) (Rc : Record (typedOracleFamily lam K L))
    (T : Table (typedOracleFamily lam K L)) (g : G.σ) :
    interact G (pass2A t Q wq embS embP xin cms x xt cap embE v co Rc T) g =
      (pass2 t Q wq embS embP xin cms x xt cap embE v co Rc T).map fun y => (y, g) := by
  unfold pass2A pass2
  rw [interact_bind, interact_runReplayA, PMF.bind_map, PMF.map_comp]
  rfl

end OnBytes.LateWorld

#print axioms OnBytes.LateWorld.ext_agrees
#print axioms OnBytes.LateWorld.late_eq_replay
#print axioms OnBytes.LateWorld.session
#print axioms OnBytes.LateWorld.interact_pass2A
