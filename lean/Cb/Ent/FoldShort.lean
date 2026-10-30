-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ent/FoldShort.lean: the fold (the sumcheck that folds, Cb/Ld/LdSum.lean) with short rounds: a
round sends its round polynomial without one coefficient, which the verifier sets by the round
equation. Round-by-round knowledge soundness, from the library's block, by the pass of
Ior/PullC.lean.

Definitions and statements; the proofs are in Cb/Ent/FoldShortProofs.lean.
The library's block `Y.ior` sends all n + 1 coefficients of each round polynomial and checks that
the polynomial "sums" to the running claim. Here a round sends n coefficients; the power `fx.1` is
left out, and its coefficient is completed from the running claim (`hFill`, Cb/Ld/LdHideShort.lean).
The block is used as it is: `Y.iorS fx` is `Y.ior` behind maps of messages between two typed shapes.
The first round (the fresh mask's oracle, the sum, the coefficient ε) and all verifier messages are
unchanged.

Main names:
  `sRoundS E Ch n`: a short round: n coefficients in the clear, a challenge. `Y.shapeS`.
  `sFill n fx σ q`: the completed round polynomial at the running claim σ.
  `sUp`, `sCar`, `sClaim`, `sUpRho`: for k short rounds from the running claim σ on: the image of a
    transcript; the maps; the running claim at the end; the verifier messages, retyped.
  `Y.upS fx t₀`, `Y.carS fx t₀`: the same for the whole fold, at the target t₀ of the statement.
  `Y.impS`, `Y.declS`: the new implicit instance and the declarations on positions, in the block's
    own words over the short shape. `Y.iorS fx`: the fold with short rounds.
  `Spec.ldEnt_foldS_tr`, `_fib`, `_imp`: every transcript has the image `Y.upS fx t₀ τ`; one
    verifier message goes to one; the implicit instance is the block's on the image.
  `Spec.ldEnt_foldS_know`: under the five premises of `Spec.ld_sum_know` (Cb/Ld/LdSumKnow.lean):
    knowledge soundness of `Y.iorS fx`: the block's relations, the block's extractor on the image.
  `Spec.ldEnt_foldS_err`, `Spec.ldEnt_foldS_chal`: its error counts are the block's, as lists, and
    its rounds have as many verifier messages as the block's.
  `Spec.ldEnt_foldS_out`: if `fx.2` is an inverse of the "sum" of the power `fx.1`, no check is
    left: the verifier never rejects, and outputs the block's new statement at the target `sClaim`.
  `Spec.ldEnt_foldS_lin`: the linear coefficient may be left out (fx = (1, 1), for 1 ≤ n).

Limits: `Spec.ldEnt_foldS_know` asks nothing of fx: with an fx that is no inverse the verifier still
checks the round equations on the completed polynomials. `Spec.ldEnt_foldS_know` alone is not about
a verifier without checks: that takes the premise of `Spec.ldEnt_foldS_out`. `Spec.ldEnt_foldS_out`
gives the explicit part of the output; no program is compared here. Not that any Y meets the five
premises, or that the errors are small: lists and agreement are conditions, with any numbers.
Nothing on an honest prover: no completeness, no zero knowledge. Nothing is proved of `Y.declS`: not
that `Y.iorS fx` is local, tied or made of strings. The fresh mask is still sent in the fold's first
round: a mask that rides in an earlier oracle is not treated here. No tower is built on `Y.iorS`
here.

Terms: lean/GLOSSARY.md.

-/
import Cb.Ld.LdSumKnow
import Cb.Ld.LdHideShort
import Ior.PullC

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

/-! ## Short rounds -/

/-- a short round of the sumcheck: n coefficients in the clear, a challenge -/
@[reducible] def sRoundS (E Ch : Type) [Field E] [Fintype Ch] [Nonempty Ch] (n : ℕ) : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim,
    Plain := Fin n → E, Chal := Ch, dOrc := (), dPlain := 0 }

section Rounds
variable {E Ch : Type} [Field E] [Fintype Ch] [Nonempty Ch] (val : Ch → E) (n : ℕ)
  (fx : Fin (n + 1) × E)

/-- The round polynomial that n sent coefficients stand for at the running claim σ: the coefficient
of the power `fx.1` is completed. -/
def sFill (σ : E) (q : Fin n → E) : Fin (n + 1) → E := hFill (HVar.plain E n) fx σ q

/-- the verifier messages of k short rounds, as those of k rounds -/
def sUpRho : (k : ℕ) → Rho (List.replicate k (sRoundS E Ch n)) →
    Rho (List.replicate k (sRound E Ch n))
  | 0, _ => ()
  | k + 1, ρ => (ρ.1, sUpRho k ρ.2)

/-- The image of a transcript of k short rounds, from the running claim σ on. -/
def sUp : (k : ℕ) → E → Tr (List.replicate k (sRoundS E Ch n)) →
    Tr (List.replicate k (sRound E Ch n))
  | 0, _, _ => ()
  | k + 1, σ, τ =>
      (((), sFill n fx σ τ.1.2), τ.2.1, sUp k (hev (sFill n fx σ τ.1.2) (val τ.2.1)) τ.2.2)

/-- The maps of k short rounds, from the running claim σ on. -/
def sCar : (k : ℕ) → E →
    Carry (List.replicate k (sRoundS E Ch n)) (List.replicate k (sRound E Ch n))
  | 0, _ => ()
  | k + 1, σ =>
      (fun m => ((), sFill n fx σ m.2), fun _ c => some c,
        fun m c => sCar k (hev (sFill n fx σ m.2) (val c)))

/-- The running claim after k short rounds. -/
def sClaim : (k : ℕ) → E → Tr (List.replicate k (sRoundS E Ch n)) → E
  | 0, σ, _ => σ
  | k + 1, σ, τ => sClaim k (hev (sFill n fx σ τ.1.2) (val τ.2.1)) τ.2.2

end Rounds

/-! ## The fold with short rounds -/

namespace SumPar
variable {E P : Type} [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)

/-- the k short rounds -/
abbrev roundsS : Shape := List.replicate Y.k (sRoundS E Y.Ch Y.n)
/-- the fold's rounds: the block's first round, then the short rounds -/
abbrev shapeS : Shape := Y.round0 :: Y.roundsS

/-- the verifier messages, as those of the block -/
def upRho (ρ : Rho Y.shapeS) : Rho Y.shape := (ρ.1, sUpRho Y.n Y.k ρ.2)

/-- The image of a transcript, at the target t₀ of the statement: the first round as it is; the
running claim starts at (the sum sent) + t₀ ε. -/
def upS (t₀ : E) (τ : Tr Y.shapeS) : Tr Y.shape :=
  (τ.1, τ.2.1, sUp Y.val Y.n fx Y.k (τ.1.2 + t₀ * Y.val τ.2.1) τ.2.2)

/-- The maps of the fold, at the target t₀ of the statement. -/
def carS (t₀ : E) : Carry Y.shapeS Y.shape :=
  (fun m => m, fun _ c => some c, fun m c => sCar Y.val Y.n fx Y.k (m.2 + t₀ * Y.val c))

/-- The new implicit instance: the three tables, folded: the words of `SumPar.imp`. -/
def impS (y : Y.Cin.Word) (τ : Tr Y.shapeS) : Y.Cout.Word :=
  LdCode.mkW (foldW Y.C (Y.pt (Y.upRho τ.rho)) (LdCode.fstW y))
    (LdCode.mkW (C₁ := Y.Z) (C₂ := Y.Zw) (foldW Y.Z (Y.pre (Y.pt (Y.upRho τ.rho))) (LdCode.sndW y))
      (foldW Y.Zw (Y.pre (Y.pt (Y.upRho τ.rho))) τ.1.1))

/-- The declarations on positions: the words of `SumPar.ior`. -/
def declS : IOR.Decl Y.shapeS Y.Cin.ext Y.Cout.ext where
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  srcE := fun _ x => {x}
  srcO := fun _ x => (Y.srcW x).map ⟨Sum.inl, Sum.inl_injective⟩
  tie := fun _ _ => ∅

/-- The fold with short rounds. (Not computable only because the block `Y.ior` is not.) -/
noncomputable def iorS : IOR Y.Xi Y.Cin.ext Y.Xo Y.Cout.ext :=
  Y.ior.pullC Y.shapeS (fun a => Y.carS fx a.1.1) Y.impS Y.declS

end SumPar

namespace Spec

/-- Every transcript has an image. -/
def ldEnt_foldS_tr : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E) (τ : Tr Y.shapeS),
    (Y.carS fx t₀).tr τ = some (Y.upS fx t₀ τ)

/-- One verifier message goes to one. -/
def ldEnt_foldS_fib : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E),
    (Y.carS fx t₀).Fib (Err.ones Y.shapeS)

/-- The implicit instance is the block's on the image, whatever the target. -/
def ldEnt_foldS_imp : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E) (t₀ : E) (y : Y.Cin.Word)
      (τ : Tr Y.shapeS),
    Y.impS y τ = Y.imp y (Y.upS fx t₀ τ)

/-- Round-by-round knowledge soundness of the fold with short rounds: the conditions, relations and
extractor (on the image) of `Spec.ld_sum_know`. d₀: the extractor's value where there is no image
(nowhere: `Spec.ldEnt_foldS_tr`). -/
def ldEnt_foldS_know : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E)
      (d e : ℕ) (Lst mC mS mW : ℕ → ℕ) (d₀ : Y.Cin.N.Wit),
    Spec.CodesOK E P Y.C Y.Z Y.Zw d e → Y.ErrOK e Lst mC mS mW → Function.Injective Y.val →
    2 ≤ Y.n → Y.QwDeg →
    (Y.iorS fx).red.Know (fun _ => True) (ConL Y.Cin.N e Y.slIn.Holds)
      (ConL Y.Cout.N e Y.slOut.Holds)
      (Y.ior.red.extC Y.shapeS (fun a => Y.carS fx a.1.1) (Y.ext d) d₀)
      (mulErr Y.shapeS Y.shape (Err.ones Y.shapeS) (Y.err Lst mC mS mW))

/-- The error counts are the block's, as lists. -/
def ldEnt_foldS_err : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] (Y : SumPar E P) (Lst mC mS mW : ℕ → ℕ),
    (mulErr Y.shapeS Y.shape (Err.ones Y.shapeS) (Y.err Lst mC mS mW)).toList =
      (Y.err Lst mC mS mW).toList

/-- The rounds have as many verifier messages as the block's. -/
def ldEnt_foldS_chal : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P), Y.shapeS.chalList = Y.shape.chalList

/-- No check is left, if `fx.2` is an inverse of the "sum" of the power that is left out. -/
def ldEnt_foldS_out : Prop :=
  ∀ (E P : Type) [Field E] (Y : SumPar E P) (fx : Fin (Y.n + 1) × E),
    fx.2 * (HVar.plain E Y.n).mon fx.1 = 1 →
    ∀ (x : Y.Xi) (y : Y.Cin.Word) (τ : Tr Y.shapeS),
      (Y.iorS fx).out x y τ =
        some (Y.newX x (Y.upRho τ.rho)
          (sClaim Y.val Y.n fx Y.k (τ.1.2 + x.1 * Y.val τ.2.1) τ.2.2))

/-- The "sum" of X over 0 and 1 is 1: the linear coefficient may be left out. -/
def ldEnt_foldS_lin : Prop :=
  ∀ (E : Type) [Field E] (n : ℕ), (1 : E) * (HVar.plain E (n + 1)).mon 1 = 1

end Spec
end Cb
