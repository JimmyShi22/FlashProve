-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Value.lean: what the verifier of the short sumcheck block with the round of values (`shortR`,
Cb/G6/Carried.lean) puts out, as a total function.

Definitions, statements and proofs.

Main names:
  `vFinT`: the loop, with a tail of further rounds left as it is: the last value, the point, the
    tail.
  `shortV Y F x τ : Y.Out`: a total function: it completes each short message by the library's
    `hFill`, evaluates at the draw, collects the point and copies the values. No test of a
    proposition, no composition of reductions and no choice occurs in it.
  `short_out`: under `HFixs.OK` the block's verifier puts out just that, for all inputs.
  `short_red_out`, `short_red_outC`: the same of the blocks as reductions between statements
    (`IOR.red`).
  `red_seq_some`: for two reductions in a row: a first one that rejects nothing drops out of the
    composition's test.

Limits: `shortV` has code. Its loop does not read the finiteness of a challenge set, but a format
carries it as data, so to build the parameters is to enumerate each variable's challenge set: this
is not code for a large field. (An argument in words.) That the programs' routine computes `shortV`
is not said here.

-/
import Cb.G6.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TWhole
open Iop Prob Cb Johnson.L5.Layers Johnson.L5.Door

section Foot
variable {E : Type} [Field E]

/-- The loop of `shortV`: the last value, the point, and the rounds behind. -/
def vFinT : (l : List (PFmt E)) → (d : PDats l) → HFixs (pVars l d) → E → (t : Shape) →
    Tr (sRounds l ++ t) → (E × PPt l) × Tr t
  | [], _, _, σ, _, τ => ((σ, ()), τ)
  | f :: l, d, F, σ, t, (m, c, τ) =>
    (((vFinT l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ).1.1,
        (f.val c, (vFinT l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ).1.2)),
      (vFinT l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ).2)

theorem vFinT_fin : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (t : Shape) (τ : Tr (sRounds l ++ t)),
    hFin (pVars l d) σ (pQ l d (Tr.fst ((cShort l d F σ t).tr τ)).plains)
      (pH l d (pG l (Tr.fst ((cShort l d F σ t).tr τ)).rho)) = (vFinT l d F σ t τ).1.1
  | [], _, _, _, _, _ => rfl
  | f :: l, d, F, σ, t, (m, c, τ) =>
    vFinT_fin l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ

theorem vFinT_pt : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (t : Shape) (τ : Tr (sRounds l ++ t)),
    pG l (Tr.fst ((cShort l d F σ t).tr τ)).rho = (vFinT l d F σ t τ).1.2
  | [], _, _, _, _, _ => rfl
  | f :: l, d, F, σ, t, (m, c, τ) =>
    congrArg (fun p => (f.val c, p))
      (vFinT_pt l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ)

theorem vFinT_snd : ∀ (l : List (PFmt E)) (d : PDats l) (F : HFixs (pVars l d)) (σ : E)
    (t : Shape) (τ : Tr (sRounds l ++ t)),
    Tr.snd (s := pRounds l) ((cShort l d F σ t).tr τ) = (vFinT l d F σ t τ).2
  | [], _, _, _, t, τ => Carry.tr_refl t τ
  | f :: l, d, F, σ, t, (m, c, τ) =>
    vFinT_snd l d.2 F.2 (hev (hFill (f.var d.1) F.1 σ m.2) (f.val c)) t τ

end Foot

variable {E : Type} [Field E] [Fintype E] (Y : PscPar E) (F : ∀ st, HFixs (Y.vars st))
  (Ex : ExtSpec)

/-- What the verifier puts out under `HFixs.OK` (`short_out`). -/
def shortV (x : E × Y.St) (τ : Tr (shapeS Y)) : Y.Out :=
  ⟨x.2, τ.2.1,
    (vFinT Y.fmt (Y.dat x.2) (F x.2) (τ.1.2 + τ.2.1 * x.1) [pRoundV E Y.A] τ.2.2).1.2,
    (vFinT Y.fmt (Y.dat x.2) (F x.2) (τ.1.2 + τ.2.1 * x.1) [pRoundV E Y.A] τ.2.2).1.1,
    (vFinT Y.fmt (Y.dat x.2) (F x.2) (τ.1.2 + τ.2.1 * x.1) [pRoundV E Y.A] τ.2.2).2.1.2⟩

/-- Under `HFixs.OK` the verifier puts out `shortV`, for all inputs. -/
theorem short_out (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (x : E × Y.St) (y : Ex.Str)
    (τ : Tr (shapeS Y)) : (shortR Y F Ex).out x y τ = some (shortV Y F x τ) := by
  obtain ⟨m, ε, τ⟩ := τ
  have hc := cShort_cons Y.fmt (Y.dat x.2) (F x.2) (hF x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ
  have hc' : HCons (Y.vars x.2)
      (Y.mu (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))) +
        Y.eps (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))) * x.1)
      (Y.qs x.2 (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))))
      (Y.hp x.2 (Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))))) := hc
  have e1 : Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))) =
      (vFinT Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ).1.2 :=
    vFinT_pt Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ
  have e2 : hFin (Y.vars x.2)
      (Y.mu (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))) +
        Y.eps (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))) * x.1)
      (Y.qs x.2 (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))))
      (Y.hp x.2 (Y.pt (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ))))) =
      (vFinT Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ).1.1 :=
    vFinT_fin Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ
  have e3 : Tr.snd (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ)) =
      (vFinT Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ).2 :=
    vFinT_snd Y.fmt (Y.dat x.2) (F x.2) (m.2 + ε * x.1) [pRoundV E Y.A] τ
  show ((Y.outC x (Tr.fst (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ)))).bind fun z =>
    (Y.ends Ex).out z y (Tr.snd (s := Y.shapeC) ((carryS Y x (F x.2) Ex).tr (m, ε, τ)))) = _
  unfold PscPar.outC
  rw [if_pos hc', e2, e1, e3]
  rfl

/-- The same of the block as a reduction between statements. -/
theorem short_red_out (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (a : (E × Y.St) × Ex.Str)
    (τ : Tr (shapeS Y)) : (shortR Y F Ex).red.out a τ = some (shortV Y F a.1 τ, a.2) := by
  show ((shortR Y F Ex).out a.1 a.2 τ).map (fun xo => (xo, a.2)) = _
  rw [short_out Y F Ex hF]
  rfl

/-- The same for the block without the round of values. -/
theorem short_red_outC (hF : ∀ st, HFixs.OK (Y.vars st) (F st)) (a : (E × Y.St) × Ex.Str)
    (τ : Tr (shapeSC Y)) : (shortRC Y F Ex).red.out a τ = some (shortVC Y F a.1 τ, a.2) := by
  show ((shortRC Y F Ex).out a.1 a.2 τ).map (fun xo => (xo, a.2)) = _
  rw [short_outC Y F Ex hF]
  rfl

/-- Two reductions in a row: a first one that rejects nothing drops out of the composition's
test. -/
theorem red_seq_some {A B C : Type} (K₁ : Reduction A B) (K₂ : Reduction B C)
    (v₁ : A → Tr K₁.shape → B)
    (h : ∀ a τ, K₁.out a τ = some (v₁ a τ)) (a : A) (τ : Tr (K₁.seq K₂).shape) :
    (K₁.seq K₂).out a τ = K₂.out (v₁ a (Tr.fst τ)) (Tr.snd τ) := by
  show (K₁.out a (Tr.fst τ)).bind (fun b => K₂.out b (Tr.snd τ)) = _
  rw [h]
  rfl

end TWhole
