-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/AtFile.lean: the compiled prover's string is accepted by the verifier of a file with
three joined hash chains: `yes_of_prove` (OnBytes/Prover/Main.lean) called at a written file
(`FileW`, OnBytes/TypedOracleCompiler/Joined/Wire.lean).

  `FileW.proveX`        the compiled prover at a written file's letters
  `FileW.yes_of_prove`  its string gets the yes of `FileW.verify` under the same oracle functions,
                        under Main.lean's premises; that the annotation is formatted and coherent
                        follows from the laws of the joining round (`Chains.ann_fmt`,
                        Compile/Joined/Ann.lean; `Chains.ann_coherent`, Compile/Joined/Laws.lean)
  `Chains.anySh_ann`, `anySh_allLocal`   a file has a shared round (the joining round); where all
                        rounds are local none is shared
  `FileW.finish_path`   so at a file the string holds the coins' sibling digests and the coins'
                        string behind the slot value, and a request root was made

Limits: those of OnBytes/Prover/Main.lean. Little is shown here: calls of that file's and of
OnBytes/Prover/Chain.lean's theorems.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Prover.Main
import OnBytes.TypedOracleCompiler.Joined.Verifier
import Compile.Joined.Ann
import Compile.Joined.Laws

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X} {W : QueryLayout lam L} {G : Chains} {Y : Type}
  {E : ExtSpec} (F : FileW W G Y E)

/-- local rounds in front change nothing in "some round is shared" -/
theorem anySh_local_app {t : Shape} (B : RoundSplits t) :
    ∀ s : Shape, anySh (s ++ t) (RoundSplits.app (RoundSplits.allLocal s) B) = anySh t B
  | [] => rfl
  | _ :: s => anySh_local_app B s

/-- where all rounds are local none is shared -/
theorem anySh_allLocal : ∀ s : Shape, anySh s (RoundSplits.allLocal s) = false
  | [] => rfl
  | _ :: s => anySh_allLocal s

/-- a file with three joined chains has a shared round: the joining round -/
theorem _root_.Compile.Joined.Chains.anySh_ann (G : Chains) (h : G.Laws) :
    anySh G.sh G.ann = true := by
  show anySh (G.s₁ ++ G.shJ) (RoundSplits.app (RoundSplits.allLocal G.s₁) G.annJ) = true
  rw [anySh_local_app]
  unfold Chains.annJ
  simp only [anySh, h.kindJ]

/-- the compiled prover at a written file's letters -/
def FileW.proveX (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat G.sh Unit) (co : Coins lam L) (cap : ℕ → ℕ) :
    TypedOracleComputation lam W.K L (Res (F.Prf × Tr G.sh)) :=
  OnBytes.Prover.proveX F.t F.D.batch F.wq F.embS F.embP F.xin cms x y xt σ co cap

/-- **The compiled prover's string is accepted by the verifier of the file.** -/
theorem FileW.yes_of_prove (sMT sFS : ℕ) (cms : List (Dig lam)) (x : Y) (y : E.Str)
    (xt : ℕ → TreeK lam L) (σ : Strat G.sh Unit) (co : Coins lam L) (cap : ℕ → ℕ)
    (g : Fam (typedOracleFamily lam W.K L)) (hG : G.Laws) (hw : F.wq.OKG) (hJ : FewJ G.sh G.ann F.wq.sh)
    (h0 : Few0 G.sh G.ann F.wq.sh) (hloc : F.D.proto.IsLocal)
    (hDe : F.wq.ext.depth ≤ F.wq.maxDepth) (hfit : co.Fit sMT sFS (W.dReq F.t))
    (hx : ExtAt g sMT F.wq.ext F.embE cms y xt) (π : F.Prf) (τ : Tr G.sh)
    (hp : (F.proveX cms x y xt σ co cap).det g = .ok (π, τ)) :
    RoundsQueryLayout.pass G.sh G.ann F.wq.sh τ.rho = true ∧ Puts G.sh G.ann F.wq.sh (σ.run τ.rho).1 τ ∧
      π.plains = τ.plains ∧
      (F.D.accept x y τ = true → (F.verify sMT sFS cms x π).det g = true) := by
  have h := OnBytes.Prover.yes_of_prove sMT sFS F.t F.D.batch F.wq F.embS F.embP F.xin F.embE
    (W.dReq F.t) cms x y xt σ co cap g hw hJ h0 hloc (G.ann_coherent hG) (G.ann_fmt hG) hDe hfit
    hx π τ hp
  refine ⟨h.1, h.2.1, h.2.2.1, fun ha => ?_⟩
  rw [F.verify_eq]
  exact h.2.2.2 ha

/-- At a file the string holds the coins' sibling digests and the coins' string behind the slot
value, and its request root is one that the prover has made. -/
theorem FileW.finish_path (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
    (σ : Strat G.sh Unit) (co : Coins lam L) (cap : ℕ → ℕ) (g : Fam (typedOracleFamily lam W.K L)) (hG : G.Laws)
    (z : OutP lam L G.sh)
    (hz : (chainO F.t cms (F.xin x) co cap G.sh G.ann F.wq.sh F.embS F.embP 0 .first σ).det g =
      .ok z) :
    (finish F.D.batch F.wq x y xt co z).path = co.path ∧
      (finish F.D.batch F.wq x y xt co z).rsalt = co.rsalt ∧ z.2.2.2.isSome = true := by
  obtain ⟨h1, h2⟩ := chain_joined g F.t cms (F.xin x) co cap G.sh G.ann F.wq.sh F.embS F.embP 0
    .first σ z hz rfl (G.anySh_ann hG)
  refine ⟨?_, ?_, h2⟩
  · show (if z.2.2.1.slotVal.isSome then co.path else []) = co.path
    rw [h1]
    rfl
  · show (if z.2.2.1.slotVal.isSome then co.rsalt else []) = co.rsalt
    rw [h1]
    rfl

end TypedOracleCompiler.Joined
