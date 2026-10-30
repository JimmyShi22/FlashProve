-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaKit.lean: "every round's error, as a probability, is at most κ" (`Err.Below`,
Iop/InteractiveOracleProof.lean), block by block: the kit; the cores of the test for linear constraints and of the
link. The quoted words say e ≤ κ · v, with e the round's error, a count of values of its verifier
message (`Err`, Iop/Rbr.lean), and v the number of all values of that message. These errors are
numbers that a link lists (the data fields `Nums.err`, Ior/Chain.lean, and `Link.P.err`): that a
link is sound at the numbers that it lists is no statement of this file.

Definitions (two records on numbers) and theorems: glue along the rules of composition; nothing is
evaluated.

Why: take c, the largest round error over five lists of errors:
weights-formedness, the test for
linear constraints at one instance, the link, a request's preamble, the test at N instances. These
lists are composed terms. To bound c by one number κ one has to say, for each kind of round, what
"its error, as a probability, is at most κ" comes to in numbers. Cb/Req1/LdReqBelow.lean has that
for a request's preamble. This file begins the same for the other four lists.

Main names:
  `kap_pure`, `kap_peek`, `kap_send`, `kap_seq`: what "at most κ" asks of a step without rounds:
    nothing; of a round in which the verifier draws and reads: err ≤ κ · (number of values drawn);
    of a sending with its sample: `ldSendFamErr` (Cb/Ld/LdSendFam.lean: the sum over members a of
    `Sd.mult a` times pairs in the list times the sample's exceptional seeds) ≤ κ · (number of
    seeds), and a second round with error 0; of two in a row: the same of both.
  `ldKappa_lin`: `P.KapC S εf κ` (`LdLinP.KapC`) → every error of every link (`IOR.Link`) of the
    chain `P.chain on0 S εf`, as a probability, is at most κ (`ErrBelow`, Cb/Req1/LdReqBelow.lean).
  `ldKappa_link`: `P.KapC S ε₀ ε₁ κ` (`LdLkP.KapC`) → every error of every link of the chain
    `P.coreC on0 on1 S ε₀ ε₁`, as a probability, is at most κ.
  Both theorems take the type ι of positions nonempty.

Limits: this file says nothing on the size of any number. The numbers εf, ε₀, ε₁ (the folds'
exceptional points) are parameters here (no value is fixed); what they have to be is asked elsewhere
(`FoldErr`). It says nothing on the closings behind the cores: other files.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinChain
import Cb.Ld.LdLinkChain
import Cb.Req1.LdReqBelow

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

section
variable {K Xi Xo : Type} {Ei Eo : ExtSpec}

theorem kap_pure (f : Xi → Option Xo) (g : ExtMap Ei Eo) (κ : ℝ≥0∞) :
    Err.Below (Nums.pure K f g).err κ := trivial

theorem kap_peek (V : PeekV Xi Ei Xo Eo) (err : ℕ) (κ : ℝ≥0∞)
    (h : (err : ℝ≥0∞) ≤ κ * (Fintype.card V.D : ℝ≥0∞)) :
    Err.Below (Nums.peek K V err).err κ := ⟨h, trivial⟩

theorem kap_seq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂}
    {R₂ : IOR X₂ E₂ X₃ E₃} (P₁ : Nums K R₁) (P₂ : Nums K R₂) (κ : ℝ≥0∞)
    (h₁ : Err.Below P₁.err κ) (h₂ : Err.Below P₂.err κ) : Err.Below (P₁.seq P₂).err κ :=
  Err.Below.app h₁ h₂

end

theorem kap_send {E : Type} [Field E] (N : Sig E) (Sd : N.Seeds) (X : Type) (E₀ : ExtSpec)
    (Kc : Type) (L t : N.O → ℕ) (κ : ℝ≥0∞)
    (h : (ldSendFamErr N Sd L : ℝ≥0∞) ≤ κ * (Fintype.card Sd.D : ℝ≥0∞)) :
    Err.Below (ldSendFamNums N Sd X E₀ Kc L t).err κ :=
  ⟨h, by simp, trivial⟩

/-- The core of the test for linear constraints: six numbers: three sendings (sW, sU, sO); the point
(pt: `P.errPt εf`); the locations (loc: `P.errLoc`); the last point (zeta: `P.errZeta`). -/
structure LdLinP.KapC {E ι κ' J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι]
    [Fintype κ'] [Fintype J] [Fintype Y] (P : LdLinP E ι κ' J Y) (S : P.Snd) (εf : ℕ) (κ : ℝ≥0∞) :
    Prop where
  sW   : (ldSendFamErr P.NW P.SdW S.LW : ℝ≥0∞) ≤ κ * (Fintype.card P.SdW.D : ℝ≥0∞)
  pt   : (P.errPt εf : ℝ≥0∞) ≤ κ * (Fintype.card P.vPt.D : ℝ≥0∞)
  sU   : (ldSendFamErr P.NU P.SdU S.LU : ℝ≥0∞) ≤ κ * (Fintype.card P.SdU.D : ℝ≥0∞)
  loc  : (P.errLoc : ℝ≥0∞) ≤ κ * (Fintype.card P.vLoc.D : ℝ≥0∞)
  sO   : (ldSendFamErr P.NO P.SdO S.LO : ℝ≥0∞) ≤ κ * (Fintype.card P.SdO.D : ℝ≥0∞)
  zeta : (P.errZeta : ℝ≥0∞) ≤ κ * (Fintype.card P.vZeta.D : ℝ≥0∞)

theorem ldKappa_lin {E ι κ' J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ']
    [Fintype J] [Fintype Y] (P : LdLinP E ι κ' J Y) (on0 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop)
    (S : P.Snd) (εf : ℕ) (κ : ℝ≥0∞) (h : P.KapC S εf κ) :
    (P.chain on0 S εf).ErrBelow κ := by
  unfold LdLinP.chain
  simp only [errBelow_snoc, errBelow_one]
  exact ⟨⟨⟨⟨⟨⟨kap_pure _ _ κ, kap_send _ _ _ _ _ _ _ κ h.sW⟩, kap_peek _ _ κ h.pt⟩,
          kap_send _ _ _ _ _ _ _ κ h.sU⟩,
        kap_peek _ _ κ h.loc⟩,
      kap_send _ _ _ _ _ _ _ κ h.sO⟩,
    kap_peek _ _ κ h.zeta⟩

/-- The core of the link: four numbers: the point (gam: `P.errGam ε₀ ε₁`); the sending (snd); the
locations (loc); the last point (phi). -/
structure LdLkP.KapC {E ι κ' J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ']
    [Fintype J] [Fintype Λ] (P : LdLkP E ι κ' J Λ) (S : P.Snd) (ε₀ ε₁ : ℕ) (κ : ℝ≥0∞) : Prop where
  gam : (P.errGam ε₀ ε₁ : ℝ≥0∞) ≤ κ * (Fintype.card P.vGam.D : ℝ≥0∞)
  snd : (ldSendFamErr P.N S.Sd S.L : ℝ≥0∞) ≤ κ * (Fintype.card S.Sd.D : ℝ≥0∞)
  loc : (P.errLoc : ℝ≥0∞) ≤ κ * (Fintype.card P.vLoc.D : ℝ≥0∞)
  phi : (P.errPhi : ℝ≥0∞) ≤ κ * (Fintype.card P.vPhi.D : ℝ≥0∞)

theorem ldKappa_link {E ι κ' J Λ : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι]
    [Fintype κ'] [Fintype J] [Fintype Λ] (P : LdLkP E ι κ' J Λ)
    (on0 on1 : (P.D.X.Row → ι → E) → P.D.X.Rec → Prop) (S : P.Snd) (ε₀ ε₁ : ℕ)
    (κ : ℝ≥0∞) (h : P.KapC S ε₀ ε₁ κ) :
    (P.coreC on0 on1 S ε₀ ε₁).ErrBelow κ := by
  unfold LdLkP.coreC
  simp only [errBelow_snoc, errBelow_one]
  exact ⟨⟨⟨kap_peek _ _ κ h.gam, kap_send _ _ _ _ _ _ _ κ h.snd⟩, kap_peek _ _ κ h.loc⟩,
    kap_peek _ _ κ h.phi⟩

end Cb
