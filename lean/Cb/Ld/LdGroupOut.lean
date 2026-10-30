-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupOut.lean: this file tells the outputs of a batching round and a fold on several oracle
messages (the first half of a closing): the new oracles, and the witness with which the honest
prover ends.

In standard terms: the first half of a closing is a batching round (the bridge), a rearrangement of
the group's words that has no round, and a sumcheck that folds them (Cb/Ld/LdGroupFold.lean). (the
second half: `LdCloseD`, Cb/Req1/LdSegFit.lean)

Statements (in `Cb.Spec`) and proofs. It unfolds the term of Cb/Ld/LdGroupFold.lean (bridge,
arrangement, cut, fold, beside the carried part); nothing is assumed beyond the hypotheses of the
statements and whatever the arguments hold as proofs.
The term itself needs the group's set of common long positions, `G.P`, to be nonempty.

Main names:
  `Spec.ldGroup_out_word`: for every input and every transcript there is a point γ such that: the
    main part of the folded word is the fold at γ of the arranged words of the group's members; the
    further oracles and the kept words are handed on unchanged.
  `Spec.ldGroup_out_kept`: so, by "the fold returns the kept rows" (`Spec.ldGroup_fold_kept`): the
    slot some j of the main part of the folded word is the kept row j of the words as they were
    sent, whatever the transcript.
  `Spec.ldGroup_out_wit`: for every run of the honest prover there is a point γ such that: main
    message and main randomness of its last witness are the folds at γ of those of the arranged
    witness; the kept pairs and the further witness are handed on unchanged.
  `Spec.ldGroup_out_wit_kept`: so the slot some j of them is message and randomness of the kept row
    j.

Limits: this file does not say which point γ (it is read off the verifier's messages). On the mask
parts the file has one thing: `GShape.block_end` gives the whole last witness of the block's honest
prover (`(Sh.block ..).H`, Cb/Ld/LdGroupFold.lean) as `(Sh.fold Sb sl Z).honW (Sh.rho.up W) cf γ`
(`SumPar.honW`, Cb/Ld/LdSum.lean), for some cf and γ; beyond it no statement of the file speaks of
them.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdGroupFoldProofs
import Cb.Ld.LdSumHon

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

namespace Spec

def ldGroup_out_word : Prop :=
  ∀ (E B St₀ : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (d t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (y : (E₀.prod S.ext).Str)
      (τ : Tr (ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).shape),
    ∃ γ : Fin (Sh.h + Sh.g) → E,
      LdCode.fstW (C₁ := Sh.Cs) (C₂ := Sh.Zb.pair Sh.par.Zw)
          ((ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).imp y τ).1 =
        SumPar.foldW Sh.Cs γ (LdCode.fstW (Sh.rho.wd (G.word y.2))) ∧
      ((ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).imp y τ).2 =
        (y.1, S.res (T := OMsg.Str) kp y.2)

def ldGroup_out_kept : Prop :=
  ∀ (E B St₀ : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (d t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (y : (E₀.prod S.ext).Str)
      (τ : Tr (ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).shape) (j : Sh.Kp)
      (p : Sh.Cb.NP) (s : Sh.Cb.NS p),
    LdCode.fstW (C₁ := Sh.Cs) (C₂ := Sh.Zb.pair Sh.par.Zw)
        ((ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).imp y τ).1 p (some j, s) =
      LdCode.fstW (C₁ := Sh.Cb.il (Σ a, Sh.Rm a)) (C₂ := Sh.Zb.il (Σ a, Sh.Rz a))
        (Sh.flat.wd (G.word y.2)) p (Sh.kept j, s)

def ldGroup_out_wit : Prop :=
  ∀ (E B St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (d t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (w : S.Wit × Wp) x c ρ,
    ∃ γ : Fin (Sh.h + Sh.g) → E,
      (∀ n : Sh.Cs.J,
        (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat w x c).run
            ρ).2.2.1.1 (.inl n) =
          foldV γ (fun a => (Sh.rho.up (G.wit w.1)).1 (.inl a)) n) ∧
      (∀ n : Sh.Cs.Q,
        (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat w x c).run
            ρ).2.2.1.2 (.inl n) =
          foldV γ (fun a => (Sh.rho.up (G.wit w.1)).2 (.inl a)) n) ∧
      (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat
          w x c).run ρ).2.2.2 =
        (S.res (T := OMsg.Wit) kp w.1, w.2)

def ldGroup_out_wit_kept : Prop :=
  ∀ (E B St₀ Wp : Type) [Field E] [Fintype E] [Fintype B] (S : Sig E) (G : Grp S) [Nonempty G.P]
      (Sh : GShape G) (kp : S.O → Prop) [DecidablePred kp] (Sb : B → Type)
      (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B)) (E₀ : ExtSpec) (d t : ℕ)
      (Lst mC mS mW : ℕ → ℕ) (w : S.Wit × Wp) x c ρ (j : Sh.Kp),
    (∀ n : Sh.Cb.J,
      (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat
            w x c).run ρ).2.2.1.1
          (.inl (some j, n)) =
        (Sh.flat.up (G.wit w.1)).1 (.inl (Sh.kept j, n))) ∧
    (∀ n : Sh.Cb.Q,
      (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat
            w x c).run ρ).2.2.1.2
          (.inl (some j, n)) =
        (Sh.flat.up (G.wit w.1)).2 (.inl (Sh.kept j, n)))

end Spec

theorem ldGroup_out_word : Spec.ldGroup_out_word := by
  intro E B St₀ _ _ _ S G _ Sh kp _ Sb sl Z E₀ d t Lst mC mS mW y τ
  exact ⟨_, rfl, rfl⟩

theorem ldGroup_out_kept : Spec.ldGroup_out_kept := by
  intro E B St₀ _ _ _ S G _ Sh kp _ Sb sl Z E₀ d t Lst mC mS mW y τ j p s
  obtain ⟨γ, h1, -⟩ := ldGroup_out_word E B St₀ S G Sh kp Sb sl Z E₀ d t Lst mC mS mW y τ
  rw [h1]
  exact (ldGroup_fold_kept E S G Sh γ j).1 (G.word y.2) p s

/-- with what an honest prover ends that runs beside a carried part -/
theorem end_keep_carry {Xi Xo Zx : Type} {Ei Eo F : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wo Wz : Type}
    (H : R.Honest Wi Wo) (w : Wi × Wz) (a : Xi × Zx) (c : H.Coin) (ρ : Rho R.shape) :
    ((((H.keep Zx F).carry Wz).strat w a c).run ρ).2.2 =
      (((H.strat w.1 a.1 c).run ρ).2.2, w.2) := by
  rw [Honest.carry_run]
  show ((((H.keepX Zx).strat w.1 a c).run ρ).2.2, w.2) = _
  rw [Honest.keepX_run]

/-- with what the block's honest prover ends: the fold's new witness for the arranged pair.
(not all hypotheses are named here: see the statement below) -/
theorem GShape.block_end {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S}
    [Nonempty G.P] (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J)
    (Z : Evader E (G.Row B)) (d t : ℕ) (Lst mC mS mW : ℕ → ℕ) (W : (G.joint Sb sl Z).W)
    (X : (G.joint Sb sl Z).X) c ρ :
    ∃ (cf : (Sh.fold Sb sl Z).Coin) (γ : Fin (Sh.h + Sh.g) → E),
      (((Sh.block Sb sl Z d t Lst mC mS mW).H.strat W X c).run ρ).2.2 =
        (Sh.fold Sb sl Z).honW (Sh.rho.up W) cf γ := by
  have h : (((Sh.block Sb sl Z d t Lst mC mS mW).H.strat W X c).run ρ).2 =
      (((Sh.fold Sb sl Z).hon.strat (Sh.rho.up W) (X.1, (X.2, X.2)) c.2.2).run ρ).2 := rfl
  exact ⟨c.2.2,
    sPt _ _ ((Sh.fold Sb sl Z).gam ρ),
    (congrArg Prod.snd h).trans
      (congrArg Prod.snd
        (ld_sum_run E G.P (Sh.fold Sb sl Z) (Sh.rho.up W) (X.1, (X.2, X.2)) c.2.2 ρ).2.2.2)⟩

theorem ldGroup_out_wit : Spec.ldGroup_out_wit := by
  intro E B St₀ Wp _ _ _ S G _ Sh kp _ Sb sl Z E₀ d t Lst mC mS mW w x c ρ
  have h1 := Honest.run_seq (ldBridgeH G kp Sb Z St₀ Wp E₀)
    (((Sh.block Sb sl Z d t Lst mC mS mW).H.keep (LdCarX kp St₀) (LdCarE kp E₀)).carry
      (LdCarW kp Wp))
    w x c ρ
  have h2 : (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat
        w x c).run ρ).2.2 = _ :=
    congrArg (fun r => r.2.2) h1
  rw [h2, end_keep_carry]
  obtain ⟨cf, γ, h3⟩ := Sh.block_end Sb sl Z d t Lst mC mS mW (G.wit w.1)
    (((ldBridgeH G kp Sb Z St₀ Wp E₀).strat w x c.1).run (Rho.fst ρ)).2.1.1 c.2
    (Rho.snd (s := (ldBridge G kp Sb Z St₀ E₀).shape) ρ)
  refine ⟨γ, fun n => ?_, fun n => ?_, rfl⟩
  · exact congrArg (fun v => v.1 (.inl n)) h3
  · exact congrArg (fun v => v.2 (.inl n)) h3

theorem ldGroup_out_wit_kept : Spec.ldGroup_out_wit_kept := by
  intro E B St₀ Wp _ _ _ S G _ Sh kp _ Sb sl Z E₀ d t Lst mC mS mW w x c ρ j
  obtain ⟨γ, h1, h2, -⟩ := ldGroup_out_wit E B St₀ Wp S G Sh kp Sb sl Z E₀ d t Lst mC mS mW w x c ρ
  obtain ⟨-, k1, k2⟩ := ldGroup_fold_kept E S G Sh γ j
  exact ⟨fun n => (h1 (some j, n)).trans (k1 (G.wit w.1) n),
    fun n => (h2 (some j, n)).trans (k2 (G.wit w.1) n)⟩

end Cb
