-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/ToyFileAll.lean: the premises of the theorems on the compiled prover can be met
together: at the small file of OnBytes/TypedOracleCompiler/Joined/ToyFile.lean all of them are proved, and so, under
EVERY family of oracle functions, the compiled prover returns a string and the file's verifier says
yes to it.

Why. OnBytes/Prover/ToyFileRun.lean evaluates prover and verifier under 32 families; it calls no
theorem. Here `FileW.yes_of_prove` (OnBytes/Prover/AtFile.lean) and `proveX_returns`
(OnBytes/Prover/Main.lean) are CALLED, with each premise discharged: the laws of the joining round
and of the wire record and that the decision is local (ToyFile.lean's own theorems); at most maxRt
trees a component; the depths; the coins' lengths; the outer trees (there are no external
positions); no round has a test; and the interactive verifier accepts, since the transcript holds
the strategy's own strings.

Main names:
  `fewJ`, `few0`, `fit`, `extAt`, `noTest`, `accepts`   the premises, one by one
  `toy_all`   for every g: a string, and the verifier's yes to it

Limits: a toy: no round has a test, so no search can run out; no external string, so `ExtAt` is met
emptily; digests of one bit. It says nothing of any intended file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.AtFile
import OnBytes.Prover.ToyFileRun

set_option autoImplicit false

noncomputable section

namespace OnBytes.Prover.ToyFileRun
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Joined.Toy (G D L W F)

theorem fewJ : FewJ G.sh G.ann F.wq.sh := by
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem few0 : Few0 G.sh G.ann F.wq.sh := by
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide, trivial⟩

theorem fit : co.Fit 1 2 (W.dReq F.t) where
  salt := rfl
  leaf := fun _ _ _ _ => rfl
  slot := by decide
  path := rfl

theorem extAt (g : Fam (typedOracleFamily 1 W.K L)) : ExtAt g 1 F.wq.ext F.embE [] (fun p => p.elim0) xt where
  tree := fun p => p.elim0
  root := fun p => p.elim0
  body := fun p => p.elim0
  salt := fun p => p.elim0
  leaf := fun p => p.elim0

theorem noTest : ∀ j, hasTest G.sh G.ann F.wq.sh j = false
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl
  | _ + 6 => rfl

/-- the interactive verifier accepts every transcript that is the strategy's own run but for nonces
-/
theorem accepts (τ : Tr G.sh) (h : Puts G.sh G.ann F.wq.sh (σ₀.run τ.rho).1 τ) :
    D.accept true (fun p => p.elim0) τ = true := by
  have hs : Toy.str₁ τ = fun _ => true := congrArg Prod.fst h.2.2.2.1
  show (true && Toy.str₁ τ _ && Toy.str₁ τ _) = true
  rw [hs]
  rfl

/-- **Under every family of oracle functions the compiled prover returns a string, and the file's
verifier says yes to it.** -/
theorem toy_all (g : Fam (typedOracleFamily 1 W.K L)) :
    ∃ π τ, (F.proveX [] true (fun p => p.elim0) xt σ₀ co fun _ => 0).det g = .ok (π, τ) ∧
      (F.verify 1 2 [] true π).det g = true := by
  rcases proveX_returns F.t F.D.batch F.wq F.embS F.embP F.xin [] true (fun p => p.elim0) xt σ₀ co
    (fun _ => 0) g (G.ann_fmt Toy.laws) with ⟨⟨π, τ⟩, h⟩ | ⟨j, -, hj⟩
  · have h2 := F.yes_of_prove 1 2 [] true (fun p => p.elim0) xt σ₀ co (fun _ => 0) g Toy.laws
      Toy.wq_okg fewJ few0 Toy.isLocal (by decide) fit (extAt g) π τ h
    exact ⟨π, τ, h, h2.2.2.2 (accepts τ h2.2.1)⟩
  · rw [noTest j] at hj
    cases hj

end OnBytes.Prover.ToyFileRun
