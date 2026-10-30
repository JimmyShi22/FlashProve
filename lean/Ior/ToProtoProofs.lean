-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/ToProtoProofs.lean: the three statements of Ior/ToProto.lean, proved.

Under the hypotheses of these statements: an IOR (`IOR`, Ior/Ior.lean) to the trivial statement,
with its honest side, gives an IOP with three of the properties that the interface to the compiler
asks: round-by-round soundness for the language of the relation, together with all statements
outside `on` (from knowledge soundness), pointwise completeness, and honest-verifier
zero knowledge in the compiler's form (from the exact form with no further reads).

The simulator of `hvzk_toProto` is named in the proof: it runs the IOR's simulator with the empty
set of further positions on the answers that it is given, and lays these same answers into the
view as the external answers.

Limits: this file says nothing on locality (`Spec.isLocal_toProto` is elsewhere); nothing on how
the hypotheses are met.

Terms: lean/GLOSSARY.md.
-/
import Ior.ToProto

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace IOR
variable {X Wt Wi : Type} {E : ExtSpec}

/-- The view of the IOP from the view of the IOR and the external answers. -/
def View.toD {R : IOR X E Unit extNone} (a : E.Pos → Option E.Sym) (v : View R) : DView R.toInteractiveOracleProof :=
  ⟨v.plains, a, v.orc⟩

open Classical in
/-- If the verifier itself reads all that is tied to its positions, then with no further reads the
simulator is given of the implicit instance the verifier's positions and no more. -/
theorem given_empty {Xo : Type} {Eo : ExtSpec} (R : IOR X E Xo Eo) (ρ : Rho R.shape)
    (h : (R.reads ρ).biUnion (R.tie ρ) ⊆ R.extReads ρ) : R.given ρ ∅ = R.extReads ρ := by
  unfold given
  rw [Finset.union_empty]
  exact Finset.union_eq_left.2 h

theorem ans_extReads (R : IOR X E Unit extNone) (x : X) (ρ : Rho R.shape) (y : E.Str) :
    E.ans (R.extReads ρ) y = R.toInteractiveOracleProof.extAns x ρ y := rfl

/-- The disclosed view of the IOP is the view of the IOR with no further reads, together with the
external answers. -/
theorem dview_toProto (R : IOR X E Unit extNone) (x : X) (y : E.Str) (τ : Tr R.shape) :
    R.toInteractiveOracleProof.dview x y τ = View.toD (R.toInteractiveOracleProof.extAns x τ.rho y) (R.view ∅ τ) := by
  classical
  unfold InteractiveOracleProof.dview View.toD view
  congr 1
  funext p
  by_cases h : p ∈ R.reads τ.rho ∨ R.blinded p = false
  · exact (if_pos h).trans (if_pos (h.elim Or.inl fun h => Or.inr (Or.inr h))).symm
  · exact (if_neg h).trans
      (if_neg fun h' =>
        h (h'.elim Or.inl fun h' =>
            h'.elim (fun h' => absurd h' (Finset.notMem_empty p)) Or.inr)).symm

/-- The output of the IOP's honest side is that of the IOR's with no further reads, with the
external answers laid in. -/
theorem Honest.output_toProto {R : IOR X E Unit extNone} (H : R.Honest Wi Unit) (ext : Wt → E.Str)
    (inp : Wt → X → Wi) (w : Wt) (x : X) (ρ : Rho R.shape) :
    (H.toProto ext inp).output w x ρ =
      (H.output (inp w x) x ρ ∅).map (Option.map (View.toD (R.toInteractiveOracleProof.extAns x ρ (ext w)))) := by
  classical
  by_cases hρ : ρ ∈ H.withheld (inp w x) x
  · have hρ' : ρ ∈ (H.toProto ext inp).withheld w x := hρ
    unfold IOR.Honest.output
    rw [if_pos hρ, PMF.pure_map]
    exact if_pos hρ'
  · have hρ' : ρ ∉ (H.toProto ext inp).withheld w x := hρ
    unfold IOR.Honest.output
    rw [if_neg hρ, PMF.map_comp]
    refine (if_neg hρ').trans ?_
    refine congrArg (fun f => (unif H.Coin).map f) ?_
    funext c
    show some
        (R.toInteractiveOracleProof.dview x (ext w) ((Strat.map (fun _ => ()) (H.strat (inp w x) x c)).run ρ).1) = _
    rw [Strat.run_map, dview_toProto, Strat.rho_run]
    rfl

end IOR

open IOR

theorem sound_toProto : Spec.sound_toProto := by
  intro X W E R on RA ext ε h x y hL
  have hon : on (x, y) := by_contra fun hn => hL (Or.inl hn)
  refine Doomed.mono _ _ ?_ (h (x, y) hon)
  intro τ hτ
  show (R.out x y τ).isSome = false
  cases hout : R.out x y τ with
  | none => rfl
  | some u =>
    exact absurd
      (Or.inr ⟨_, hτ (u, R.imp y τ) () (by show (R.out x y τ).map _ = _; rw [hout]; rfl) trivial⟩)
      hL

theorem acc_toProto : Spec.acc_toProto := by
  intro X Wt Wi E R H ext inp valid Ri hA hR w x c ρ hv hρ
  show (R.out x (ext w) ((Strat.map (fun _ => ()) (H.strat (inp w x) x c)).run ρ).1).isSome = true
  rw [Strat.run_map, (hA x (ext w) (inp w x) c ρ (hR w x hv) hρ).1]
  rfl

theorem hvzk_toProto : Spec.hvzk_toProto := by
  intro X Wt Wi E R H ext inp valid Ri bud z hE hb ht hR hz
  obtain ⟨S, hS⟩ := hE
  refine Iop.Honest.HVZK.of_exact (H.toProto ext inp) valid z
    (fun x ρ a => (S x ρ ∅ a).map (Option.map (View.toD a))) (fun w x => H.Hid (inp w x) x) ?_ hz
  intro w x hv ρ hρ
  rw [Honest.output_toProto, hS x (ext w) (inp w x) (hR w x hv) ρ hρ ∅ (hb ρ),
    given_empty R ρ (ht ρ), ans_extReads R x ρ (ext w)]
  rfl

end Iop
