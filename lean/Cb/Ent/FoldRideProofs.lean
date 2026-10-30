-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/FoldRideProofs.lean: the proofs of the statements of Cb/Ent/FoldRide.lean: the fold and the
base case whose own oracle rode in an earlier round.

Knowledge soundness: the blocks' own theorems (`ld_sum_know`, Cb/Ld/LdSumKnowProofs.lean;
`ldBase_know`, Cb/Ld/LdBaseProofs.lean) and the rule "compose, then pass once" (`know_pullC_seq`,
Ior/PullCProofs.lean). The closed forms: the image under `Carry.app` (`Carry.tr_app`,
Iop/CarryProofs.lean); for the fold the facts on k short rounds of Cb/Ent/FoldShortProofs.lean; for
the switch `ldEnt_col_tr` (Cb/Ent/ColRoundProofs.lean).

Main names: one theorem for each statement, of the same name; two helpers, `SumPar.upR_rho` and
`SumPar.out_upR`.

Limits: those in the head of Cb/Ent/FoldRide.lean.

Terms: lean/GLOSSARY.md.

-/
import Cb.Ent.FoldRide
import Cb.Ent.FoldShortProofs
import Cb.Ld.LdBaseProofs
import Cb.Ld.LdSwitchProofs
import Cb.Ent.ColRoundProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks

theorem ldEnt_ride_tr : Spec.ldEnt_ride_tr := by
  refine ⟨?_, ?_⟩
  · intro E P _ Y fx t₀ z τ
    obtain ⟨m, c, τ⟩ := τ
    show (some c).bind (fun c' =>
      ((sCar Y.val Y.n fx Y.k (m.2 + t₀ * Y.val c)).tr τ).map fun τ' => ((z, m.2), c', τ')) = _
    rw [sCar_tr]
    rfl
  · intro E P _ _ _ _ C t g τ
    obtain ⟨m, c, τ⟩ := τ
    show (some c).bind (fun c' => ((Carry.id _).tr τ).map fun τ' => ((g, m.2), c', τ')) = _
    rw [Carry.tr_id]
    rfl

theorem ldEnt_ride_fib : Spec.ldEnt_ride_fib :=
  ⟨fun _ _ _ Y fx _ _ =>
      ⟨fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
        fun _ _ => sCar_fib Y.val Y.n fx Y.k _⟩,
    fun _ _ _ _ _ _ _ _ _ =>
      ⟨fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
        fun _ _ => Carry.fib_id _⟩⟩

theorem ldEnt_ride_chal : Spec.ldEnt_ride_chal :=
  ⟨fun E _ _ Y =>
      congrArg (List.cons (Fintype.card Y.Ch)) (sRoundS_chal (E := E) (Ch := Y.Ch) Y.n Y.k),
    fun _ _ _ _ _ _ _ _ => rfl⟩

theorem ldEnt_rideFold_know : Spec.ldEnt_rideFold_know := by
  intro E P A WA _ _ _ Y fx K₁ s₁ F₁ ws₁ rd on RA e₁ ε₁ d₀ d e Lst mC mS mW h₁ hF h
  exact know_pullC_seq _ _ _ _ _ _ K₁ Y.ior.red s₁ Y.shapeR F₁
    (fun a τ₁ => Y.carR fx (tgtOf K₁ F₁ a τ₁) (rd τ₁)) ws₁ (Err.ones Y.shapeR) on (fun _ => True)
    RA _ _ e₁ (Y.ext d) ε₁ (Y.err Lst mC mS mW) d₀ h₁
    (ld_sum_know E P Y d e Lst mC mS mW h.codes h.errs h.inj h.deg h.qw)
    (fun _ _ _ _ _ => trivial) hF fun _ _ _ => ldEnt_ride_fib.1 E P Y fx _ _

theorem ldEnt_rideBase_know : Spec.ldEnt_rideBase_know := by
  intro E P A WA St _ _ _ _ C sl t cov K₁ s₁ F₁ ws₁ rd on RA e₁ ε₁ d₀ d e bad L2 h₁ hF hC hed hm hl
  exact know_pullC_seq _ _ _ _ _ _ K₁ (ldBaseIOR C sl t cov).red s₁ (ldBaseShapeN C t) F₁
    (fun _ τ₁ => ldBaseCarR C t (rd τ₁)) ws₁ (Err.ones _) on (fun _ => True)
    RA _ _ e₁ (ldBaseExt C t d) ε₁ (ldBaseErr C t e bad L2) d₀ h₁
    (ldBase_know C sl t cov hC hed hm hl)
    (fun _ _ _ _ _ => trivial) hF fun _ _ _ => ldEnt_ride_fib.2 E P C t _

theorem ldEnt_rideSwitchFold_know : Spec.ldEnt_rideSwitchFold_know := by
  intro E P P' St _ _ _ _ _ _ D Y fx Pt lf lfW f eM e₀ e L d Lst mC mS mW d₀ hD hM hY
  have h₁ : ((ldSwitch D).red.seq (stepRed f)).Know (fun _ => True) (ConL D.Cin.N e₀ D.sl.Holds)
      (ConL Y.Cin.N e Y.slIn.Holds)
      (Reduction.extSeq (ldSwitch D).red (stepRed f) (fun _ _ w' => D.back w') eM d₀)
      (Err.app (s := D.sh) (t := []) (D.W.err1 L, (D.W.err2 e₀ L, ())) ()) :=
    Reduction.Know.seq (ldSwitch_know E P P' St D e₀ e L hD.laws hD.list hD.okO hD.okB) hM
      (fun _ _ _ _ _ => trivial) d₀
  exact ldEnt_rideFold_know E P' _ _ Y fx ((ldSwitch D).red.seq (stepRed f))
    (D.shC Y.Cw Pt lf lfW) (fun _ => D.carC Y.Cw Pt lf lfW) (Err.ones _)
    (D.riderC Y.Cw Pt lf lfW) (fun _ => True) _ _ _ d₀ d e Lst mC mS mW h₁
    (fun _ _ => ldEnt_col_fib _ _ (D.colL Y.Cw Pt lf lfW) (D.Cout.sendPoint _ _ _) _) hY

/-- the verifier messages of the image of a transcript of the fold as sent -/
theorem SumPar.upR_rho {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E)
    (z : Y.Cw.Word) (τ : Tr Y.shapeR) : (Y.upR fx t₀ z τ).rho = Y.upRhoR τ.rho := by
  obtain ⟨m, c, τ⟩ := τ
  show (c, (sUp Y.val Y.n fx Y.k _ τ).rho) = (c, sUpRho Y.n Y.k τ.rho)
  rw [sUp_rho]

theorem ldEnt_ride_imp : Spec.ldEnt_ride_imp := by
  intro E P _ Y fx t₀ z y τ
  unfold SumPar.impR SumPar.imp
  rw [Y.upR_rho fx t₀ z τ]
  rfl

/-- the block's verifier on the image, at the statement's own target: no check is left -/
theorem SumPar.out_upR {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)
    (h : fx.2 * (HVar.plain E Y.n).mon fx.1 = 1) (x : Y.Xi) (z : Y.Cw.Word) (τ : Tr Y.shapeR) :
    Y.out x (Y.upR fx x.1 z τ) =
      some (Y.newX x (Y.upRhoR τ.rho)
        (sClaim Y.val Y.n fx Y.k (τ.1.2 + x.1 * Y.val τ.2.1) τ.2.2)) := by
  obtain ⟨m, c, τ⟩ := τ
  have hc : HCons Y.vars (Y.mu (Y.upR fx x.1 z (m, c, τ)).plains +
      x.1 * Y.eps (Y.upR fx x.1 z (m, c, τ)).rho) (Y.qs (Y.upR fx x.1 z (m, c, τ)).plains)
      (Y.gam (Y.upR fx x.1 z (m, c, τ)).rho) :=
    sUp_cons Y.val Y.n fx h Y.k (m.2 + x.1 * Y.val c) τ
  have hf : hFin Y.vars (Y.mu (Y.upR fx x.1 z (m, c, τ)).plains +
      x.1 * Y.eps (Y.upR fx x.1 z (m, c, τ)).rho) (Y.qs (Y.upR fx x.1 z (m, c, τ)).plains)
      (Y.gam (Y.upR fx x.1 z (m, c, τ)).rho) =
        sClaim Y.val Y.n fx Y.k (m.2 + x.1 * Y.val c) τ :=
    sUp_fin Y.val Y.n fx Y.k (m.2 + x.1 * Y.val c) τ
  unfold SumPar.out
  rw [if_pos hc, hf, Y.upR_rho fx x.1 z (m, c, τ)]

theorem ldEnt_rideFold_out : Spec.ldEnt_rideFold_out := by
  intro E P A _ Y fx h K₁ s₁ F₁ rd a τ₁ τ₂
  show ((Y.carRide fx K₁ F₁ rd a).tr (Tr.app τ₁ τ₂)).bind ((K₁.seq Y.ior.red).out a) =
    (((F₁ a).tr τ₁).bind (K₁.out a)).map _
  unfold SumPar.carRide
  rw [Carry.tr_app, ldEnt_ride_tr.1 E P Y fx _ _ τ₂]
  cases h1 : (F₁ a).tr τ₁ with
  | none => rfl
  | some τ₁' =>
    show (K₁.seq Y.ior.red).out a (Tr.app τ₁' (Y.upR fx (tgtOf K₁ F₁ a τ₁) (rd τ₁) τ₂)) =
      (K₁.out a τ₁').map _
    rw [Reduction.seq_out_app]
    cases h2 : K₁.out a τ₁' with
    | none => rfl
    | some b =>
      have ht : tgtOf K₁ F₁ a τ₁ = b.1.1 := by
        unfold tgtOf
        rw [h1, Option.bind_some, h2]
      rw [ht]
      show (Y.out b.1 (Y.upR fx b.1.1 (rd τ₁) τ₂)).map
        (fun xo => (xo, Y.imp b.2 (Y.upR fx b.1.1 (rd τ₁) τ₂))) = _
      rw [Y.out_upR fx h b.1 (rd τ₁) τ₂, ← ldEnt_ride_imp E P Y fx b.1.1 (rd τ₁) b.2 τ₂]
      rfl

open Classical in
theorem ldEnt_rideBase_out : Spec.ldEnt_rideBase_out := by
  intro E P A St _ _ _ _ C sl t cov K₁ s₁ F₁ rd a τ₁ τ₂
  show ((ldBaseCarRide C t K₁ F₁ rd a).tr (Tr.app τ₁ τ₂)).bind
      ((K₁.seq (ldBaseIOR C sl t cov).red).out a) = (((F₁ a).tr τ₁).bind (K₁.out a)).bind _
  unfold ldBaseCarRide
  rw [Carry.tr_app, ldEnt_ride_tr.2 E P C t _ τ₂]
  cases h1 : (F₁ a).tr τ₁ with
  | none => rfl
  | some τ₁' =>
    show (K₁.seq (ldBaseIOR C sl t cov).red).out a (Tr.app τ₁' (ldBaseUpR C t (rd τ₁) τ₂)) =
      (K₁.out a τ₁').bind _
    rw [Reduction.seq_out_app]
    cases h2 : K₁.out a τ₁' with
    | none => rfl
    | some b =>
      show Option.map (fun xo => (xo, ()))
          (if LdwAccept (ldCw C) (ldForm sl b.1) b.1.1 (C.T b.2) (C.T (rd τ₁)) τ₂.1.2 τ₂.2.1
              τ₂.2.2.1.2 τ₂.2.2.2.1 then some () else none) =
        if LdwAccept (ldCw C) (ldForm sl b.1) b.1.1 (C.T b.2) (C.T (rd τ₁)) τ₂.1.2 τ₂.2.1
            τ₂.2.2.1.2 τ₂.2.2.2.1 then some ((), ()) else none
      split_ifs <;> rfl

theorem ldEnt_colSwitch_out : Spec.ldEnt_colSwitch_out := by
  intro E P P' Pw St _ _ _ _ _ _ D Cw Pt lf lfW a τ
  show ((D.carC Cw Pt lf lfW).tr τ).bind ((ldSwitch D).red.out a) = _
  unfold LdSw.carC
  rw [ldEnt_col_tr]
  rfl

end Cb
