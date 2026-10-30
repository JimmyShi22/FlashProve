-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/RowLaws.lean: each of the three stages of a file is local, and so is the row
(OnBytes/Maker/Row.lean; CompileK/Joined/Row.lean, `Row.IsLocal`).

A reduction is local (`IOR.IsLocal`, Ior/Ior.lean) if its verifier's output and the symbols of what
it leaves depend on the oracles only at the positions that it declares.

  `sCol_congr`, `sCarries_congr`, `sView_congr`, `sTests_congr`: the column at a want, the test on
    the table's symbols, the view and the tests before the run are the same at two implicit
    instances and two transcripts that agree at the wants' positions.
  `stageIOR_isLocal`, `lastIOR_isLocal`: the two reductions of OnBytes/Maker/Stage.lean are local.
    No hypothesis on the data or on the run.
  `noTrees_isLocal`: so is the step that lays "no tree at hand" beside the stored table.
  `rowOf_isLocal`: the row's three laws.

What is not claimed. Nothing on soundness. That the row's verifier is `reductionOfWholeFile`'s.


-/
import OnBytes.Maker.Row
import OnBytes.Maker.TreesLaws
import Ior.FrameProofs
import Ior.FrameProofsBasic

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ _root_.Compile.Joined _root_.CompileK.Joined

section
variable (C : CK) (S : StageD)

/-- The column at a want hangs on the implicit instance and on the transcript only at the want's
position. -/
theorem sCol_congr (y y' : S.Ei.Str) (τ τ' : Iop.Tr (uLT C S.ds)) (w : Want)
    (hE : ∀ p, sExtPos S w = some p → S.Ei.rd y p = S.Ei.rd y' p)
    (hO : ∀ p, sOwnPos C S w = some p → τ.read p = τ'.read p) :
    sCol C S y τ w = sCol C S y' τ' w := by
  cases w with
  | table item x =>
    simp only [sCol]
    by_cases h : x < 2 ^ S.a
    · have e : y.1 ⟨x, h⟩ = y'.1 ⟨x, h⟩ := Sum.inl.inj (hE (.inl ⟨x, h⟩) (dif_pos h))
      rw [dif_pos h, dif_pos h, e]
    · rw [dif_neg h, dif_neg h]
  | tree j x =>
    simp only [sCol]
    by_cases h1 : j < S.base
    · rw [if_pos h1, if_pos h1]
      cases hq : posL S.Lin j x with
      | none => rfl
      | some p =>
        have e : y.2 p = y'.2 p := Sum.inr.inj (hE (.inr p) (by
          show (if j < S.base then (posL S.Lin j x).map Sum.inr else none) = _
          rw [if_pos h1, hq]
          rfl))
        show some (y.2 p) = some (y'.2 p)
        rw [e]
    · rw [if_neg h1, if_neg h1]
      exact colAtST_congr C S.ds τ τ' (j - S.base) x fun p hp => hO p (by
        show (if j < S.base then none else posAtST C S.ds (j - S.base) x) = _
        rw [if_neg h1, hp])

/-- The test on the symbols read of the stored table hangs on the table only at these. -/
theorem sCarries_congr (y y' : S.Ei.Str) : ∀ ws : List Want,
    (∀ w ∈ ws, ∀ p, sExtPos S w = some p → S.Ei.rd y p = S.Ei.rd y' p) →
      sCarries S y ws = sCarries S y' ws
  | [], _ => rfl
  | w :: ws, h => by
    have ih := sCarries_congr y y' ws fun w hw => h w (List.mem_cons_of_mem _ hw)
    unfold sCarries at ih ⊢
    rw [List.all_cons, List.all_cons, ih]
    congr 1
    cases w with
    | table item x =>
      by_cases hx : x < 2 ^ S.a
      · have e : y.1 ⟨x, hx⟩ = y'.1 ⟨x, hx⟩ :=
          Sum.inl.inj (h _ List.mem_cons_self (.inl ⟨x, hx⟩) (dif_pos hx))
        simp only [dif_pos hx]
        rw [e]
      · simp only [dif_neg hx]
    | tree j x => rfl

variable (y y' : S.Ei.Str) (τ τ' : Iop.Tr (uLT C S.ds)) (hρ : τ.rho = τ'.rho)
  (hp : τ.plains = τ'.plains)
  (hE : ∀ p ∈ ((sWants C S τ.rho).filterMap (sExtPos S)).toFinset, S.Ei.rd y p = S.Ei.rd y' p)
  (hO : ∀ p ∈ ((sWants C S τ.rho).filterMap (sOwnPos C S)).toFinset, τ.read p = τ'.read p)

include hρ hp hE hO in
theorem sView_congr : sView C S y τ = sView C S y' τ' := by
  unfold sView
  rw [rvT_congr C S.ds τ τ' hρ hp, rhoT_eq, rhoT_eq, ← hρ]
  congr 1
  refine List.filterMap_congr fun w hw => ?_
  rw [sCol_congr C S y y' τ τ' w
    (fun p h => hE p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨w, hw, h⟩)))
    (fun p h => hO p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨w, hw, h⟩)))]

include hρ hE in
theorem sTests_congr : sTests C S y τ = sTests C S y' τ' := by
  unfold sTests
  rw [rhoT_eq, rhoT_eq, ← hρ, sCarries_congr S y y' (sWants C S τ.rho) fun w hw p h =>
    hE p (List.mem_toFinset.2 (List.mem_filterMap.2 ⟨w, hw, h⟩))]

end

/-- **A chain that hands claims on is local.** -/
theorem stageIOR_isLocal (C : CK) (S : StageD) {Xi Xo : Type} (run : Xi → View → Option Xo) :
    (stageIOR C S run).IsLocal where
  out := fun x y y' τ τ' hρ hp hE hO => by
    show (if sTests C S y τ then run x (sView C S y τ) else none) =
      if sTests C S y' τ' then run x (sView C S y' τ') else none
    rw [sTests_congr C S y y' τ τ' hρ hE, sView_congr C S y y' τ τ' hρ hp hE hO]
  imp := fun y y' τ τ' q _ _ hE hO => by
    cases q with
    | inl p =>
      have e : y.1 p = y'.1 p := Sum.inl.inj (hE (.inl p) (Finset.mem_singleton_self _))
      show (Sum.inl (y.1 p) : SgX ⊕ List UInt64) = Sum.inl (y'.1 p)
      rw [e]
    | inr p =>
      show (Sum.inr (sLeft C S y τ p) : SgX ⊕ List UInt64) = Sum.inr (sLeft C S y' τ' p)
      unfold sLeft
      rw [sCol_congr C S y y' τ τ' _ (fun z h => hE z (Option.mem_toFinset.2 h))
        (fun z h => hO z (Option.mem_toFinset.2 h))]

/-- **A last chain is local.** -/
theorem lastIOR_isLocal (C : CK) (S : StageD) {Xi : Type} (run : Xi → View → Bool) :
    (lastIOR C S run).IsLocal where
  out := fun x y y' τ τ' hρ hp hE hO => by
    show (if (sTests C S y τ && run x (sView C S y τ)) = true then some () else none) =
      if (sTests C S y' τ' && run x (sView C S y' τ')) = true then some () else none
    rw [sTests_congr C S y y' τ τ' hρ hE, sView_congr C S y y' τ τ' hρ hp hE hO]
  imp := fun _ _ _ _ q => q.elim

theorem noTrees_isLocal (E : ExtSpec) : (noTrees E).IsLocal :=
  extMap_isLocal.2.2.2.2 E E (EjOf []) _ _ (extMap_isLocal.1 E) fun _ _ q => q.1.elim0

/-- **The row is local.** -/
theorem rowOf_isLocal (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
    (L₁ L₂ : List LeftT) {Y X₁ X₂ : Type} (okF : Y → TF → Bool) (okJ : X₁ → TJ → Bool)
    (ok3 : X₂ → T3 → Bool) (run₁ : Y → View → Option X₁) (run₂ : X₁ → View → Option X₂)
    (run₃ : X₂ → View → Bool) :
    (rowOf C D tF tJ t3 L₁ L₂ okF okJ ok3 run₁ run₂ run₃).IsLocal where
  loc₁ := Stage.cons_isLocal _ _ _
    (IOR.IsLocal.pre some (noTrees _) (stageIOR_isLocal C (D.st₁ L₁) run₁) (noTrees_isLocal _))
  loc₂ := Stage.cons_isLocal _ _ _ (stageIOR_isLocal C (D.st₂ L₁ L₂) run₂)
  loc₃ := Stage.cons_isLocal _ _ _ (lastIOR_isLocal C (D.st₃ L₂) run₃)

end OnBytes.Maker
