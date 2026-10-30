-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/Close.lean: the closing of the table side: the claim on the leaves of the table's
tree becomes one linear row, by a sumcheck that shows no value, with a degree for each variable.

It imports the library, Letters.lean, Idle.lean and Cb/Pv/Lookup/Know/LtK.lean (the sumcheck as a
letter `PscLtK`; under it Cb/Pv/Lookup/Blocks/EndM.lean: `LkEndM`, `pfMix`, `dgEnd`, `endM_*`). No
file of the port. `Clo.pVars_mix` restates `E2H2.pVars_mix` (Cb/Pv/Lookup/Blocks/EndMFelt.lean),
which this file does not import. Below, k := mu + d and q := the number of elements of E.

How dead planes are served. `LkEndM` is used as it stands, with J := Option A.J. A corner of a dead
plane is the place `none`, the entries are read by `ext0` (0 at `none`, Idle.lean), all mask places
are `some …`, and the end row is brought back to A.J by the library's `Row.pull some`. So the
closing needs no entry for a dead plane and reads none, spends no mask place on one, and the row
has no coefficient for one. The summand 1 + bit · (al − 1 − table) has degree 1 in a plane's
variable and 2 in a row's. No condition on pl is asked.

The order. Variables are bound from the highest down: first the d variables of the rows, then the
mu of the planes.

  `ordC k`        the order: round i binds variable k − 1 − i.
  `ClPl A`        the places of the masks of the closing (wE) and of the test of the bits (wB, cB).
  `A.En P`        the closing's data, a value of `LkEndM`. `en_ok`: its condition on shapes holds.
  `en_holds`      its claim at (x.top.tg, x) and the entries `ext0 μ` is `TopAt x μ d`
                  (Letters.lean), for every pl.
  `A.rowE P zz`   the end row, on A.J. `row_iff`: the end claim holds of `ext0 μ` exactly if the row
                  holds of μ.
  `A.closeK P SK` the block: into the sumcheck's state, the letter's sumcheck without end values,
                  back into the flat state with the row appended.
  `close_know`    `Know` from `Table d` to `Closed` (Letters.lean), beside every R0, for every Mu,
                  under one condition on the letter: `SK.CoreK` at this sumcheck.
  `close_lib`     the library's verifier (`PscLtK.lib`) meets that condition.
  `close_errs`    at the library's verifier: errors 1, then d times 2, then mu times 1; q values in
                  each of the 1 + d + mu rounds.
  `en_vars_at`    place i of the list of variables is a cube variable of degree 1 if k − 1 − i < mu,
                  else 2, with the equality weight at coordinate k − 1 − i of x.pt.
  `en_Y`          for every γ: the data's map `Y` at γ is the extension of the bits at the point
                  whose coordinate t is γ (k − 1 − t). That γ holds the rounds' challenges is shown
                  in ClosePoint.lean and CloseLaid.lean.
Not shown: an honest side; which of a round's coefficients is sent (that is the letter's).

-/
import Cb.Pv.KeyLookup.Idle
import Cb.Pv.Lookup.Know.LtK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Finset

noncomputable section

/-- The order of the closing's and of the bits' rounds: round i binds variable k − 1 − i. -/
abbrev ordC (k : ℕ) : Equiv.Perm (Fin k) := Fin.revPerm

/-- Place j of the list of variables: degree dg j, equality weight at z j. It restates
`E2H2.pVars_mix` (Cb/Pv/Lookup/Blocks/EndMFelt.lean), which this file does not import. -/
theorem Clo.pVars_mix (E : Type) [Field E] [Fintype E] : ∀ (k : ℕ) (dg : Fin k → ℕ) (z : Fin k → E),
    pVars (pfMix E k dg) (pdMix E k dg z) =
      List.ofFn fun j : Fin k => (pfCube E (dg j)).var (pdEq E (dg j) (z j))
  | 0, _, _ => by simp [pfMix, pVars]
  | k + 1, dg, z => by
    rw [List.ofFn_succ]
    exact congrArg (fun t => (pfCube E (dg 0)).var (pdEq E (dg 0) (z 0)) :: t)
      (Clo.pVars_mix E k (fun i => dg i.succ) fun i => z i.succ)

/-- The places of the masks of the closing and of the test of the bits. -/
structure ClPl {E : Type} [Field E] [Fintype E] (A : Dat E) where
  /-- the closing's hiding polynomial -/
  wE : PIdx (pfMix E (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d)))) → A.J
  /-- the bits' test: its hiding polynomial, and the mask of its one shown value -/
  wB : PIdx (List.replicate (A.mu + A.d) (pfCube E 2) ++ [pDummy E 2]) → A.J
  cB : A.J

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A)

/-- The closing's data. -/
def En : LkEndM E where
  X := A.XS
  J := Option A.J
  k := A.mu + A.d
  dg := dgEnd A.mu A.d (ordC (A.mu + A.d))
  tAt := fun b => A.cell fun v => b ((ordC (A.mu + A.d)).symm v)
  z := fun x i => x.pt (ordC (A.mu + A.d) i)
  kr := A.d
  rw := fun r => (ordC (A.mu + A.d)).symm (Fin.natAdd A.mu r)
  cp := fun x r => x.al - 1 - A.tab x.st (numLE r)
  inc := fun x => ext0 x.top.mf
  wAt := fun i => some (P.wE i)

theorem en_ok : (A.En P).OK :=
  ⟨fun r r' h => Fin.natAdd_injective _ _ ((ordC (A.mu + A.d)).symm.injective h),
    fun r => by
      show 2 ≤ if ((ordC (A.mu + A.d) ((ordC (A.mu + A.d)).symm (Fin.natAdd A.mu r)) :
        Fin (A.mu + A.d)) : ℕ) < A.mu then 1 else 2
      rw [Equiv.apply_symm_apply, Fin.val_natAdd, if_neg (by omega)],
    fun i => by
      show 1 ≤ if ((ordC (A.mu + A.d) i : Fin (A.mu + A.d)) : ℕ) < A.mu then 1 else 2
      split_ifs <;> omega⟩

/-- The leaves, corner by corner, in the reading of Idle.lean. -/
def leafC (x : A.XS) (μ : A.J → E) (c : Fin (A.mu + A.d) → Bool) : E :=
  1 + ext0 μ (A.cell c) * (x.al - 1 - A.tab x.st (numLE fun r : Fin A.d => c (Fin.natAdd A.mu r)))

theorem tabU_leafC (x : A.XS) (μ : A.J → E) :
    (fun c : Fin (A.mu + A.d) → Bool => A.tabU x.st μ x.al A.d (numLE c)) = A.leafC x μ := by
  funext c
  rw [A.tabU_top, A.bitN_cell, numLE_div]
  rfl

/-- The closing's claim is the table side's claim at level d: for every number of live planes. -/
theorem en_holds (x : A.XS) (μ : A.J → E) :
    (A.En P).Holds (x.top.tg, x) (ext0 μ) ↔ A.TopAt x μ A.d := by
  have hm := Alg.mle_equiv (ordC (A.mu + A.d)) (A.leafC x μ) (fun i : Fin (A.mu + A.d) => x.pt i)
  have hs : ∑ o, ext0 x.top.mf o * ext0 μ o = ∑ j, x.top.mf j * μ j := sum_ext0 _ μ
  have h1 : (A.En P).Holds (x.top.tg, x) (ext0 μ) ↔
      Alg.mle (A.leafC x μ) (fun i : Fin (A.mu + A.d) => x.pt i) + ∑ j, x.top.mf j * μ j =
        x.top.tg :=
    Iff.of_eq (congrArg₂ (fun a b => a + b = x.top.tg) hm hs)
  refine h1.trans ?_
  unfold TopAt SCl.Holds mleN
  rw [A.tabU_leafC x μ]

/-- The end row, on A.J: no coefficient at `none`. -/
def rowE (zz : (A.En P).par.Mid) : Row E A.J :=
  Row.pull some
    ⟨(A.En P).par.slU (A.En P).rowB ((A.En P).outOf zz), (A.En P).par.tU ((A.En P).outOf zz)⟩

theorem row_iff (zz : (A.En P).par.Mid) (μ : A.J → E) :
    (A.En P).par.MidHolds zz (ext0 μ) ↔ (A.rowE P zz).Holds μ :=
  (endM_row E (A.En P) zz (ext0 μ)).trans
    (row_pull0
      ⟨(A.En P).par.slU (A.En P).rowB ((A.En P).outOf zz), (A.En P).par.tU ((A.En P).outOf zz)⟩
      μ).symm

/-- Into the sumcheck, and back into the flat state. -/
def closeIn (x : A.XS) : E × A.XS := (x.top.tg, x)
def closeOut (zz : (A.En P).par.Mid) : A.XS :=
  let x : A.XS := zz.st
  { x with rows := x.rows ++ [A.rowE P zz] }

variable {Ex : ExtSpec}

/-- The block. -/
def closeK (SK : PscLtK E Ex) : BkK A.XS A.XS Ex :=
  ((SK.core (A.En P).par).preM A.closeIn).postM (A.closeOut P)

/-- Knowledge soundness (`BkK.Know`): from `Table d` to `Closed`. -/
theorem close_know (Kc M Wp : Type) (SK : PscLtK E Ex) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop)
    (hL : SK.CoreK M Wp Kc (A.En P).par fun ms => ext0 (msg ms)) :
    (A.closeK P SK).Know (A.jt R0 msg Mu fun x μ => A.Table x μ A.d) (A.jt R0 msg Mu A.Closed) := by
  let A0 : Rels Kc A.XS Ex (M × Wp) := A.jt R0 msg Mu fun x μ => A.Side x μ ∧ A.AllCls x μ
  have g := endMK_know E (A.En P) Ex M Wp Kc SK A0 (fun ms => ext0 (msg ms)) hL
  refine know_postM (A.closeOut P) (know_preM A.closeIn (fun _ _ h => h) ?_ g) (fun _ _ h => h) ?_
  · intro x y w _ h
    exact ⟨h.1.1, h.1.2.1, h.1.2.2, (A.en_holds P x _).1 h.2⟩
  · intro zz y w _ h
    obtain ⟨hR, ⟨hbn, hrows⟩, hc⟩ := h
    exact ⟨⟨hR, ⟨hbn, fun r hr => hrows r (List.mem_append_left _ hr)⟩, hc⟩,
      (A.row_iff P zz _).2 (hrows _ (List.mem_append_right _ (List.mem_singleton.2 rfl)))⟩

/-- At the library's verifier the premise on the letter holds. -/
theorem close_lib (Kc M Wp : Type) (msg : M → Option A.J → E) :
    (PscLtK.lib E Ex).CoreK M Wp Kc (A.En P).par msg :=
  PscLtK.lib_coreK M Wp Kc (A.En P).par msg (endM_vars E (A.En P)).1
    (endM_deg E (A.En P) (A.en_ok P)) (endM_vars E (A.En P)).2

/-- At the library's verifier: errors and numbers of values, by the library's own readers. -/
theorem close_errs :
    (A.closeK P (PscLtK.lib E Ex)).e.toList = 1 :: (List.replicate A.d 2 ++ List.replicate A.mu 1) ∧
    (A.closeK P (PscLtK.lib E Ex)).R.shape.chalList =
      Fintype.card E :: List.replicate (A.mu + A.d) (Fintype.card E) := by
  have h := endM_errs E (A.En P) Ex Unit
  refine ⟨?_, h.2⟩
  refine h.1.trans ?_
  exact congrArg (List.cons 1) (dgEnd_rev A.mu A.d)

/-- Which variable a round binds, with which degree. -/
theorem en_vars_at (x : A.XS) :
    (A.En P).par.vars x =
      List.ofFn fun i : Fin (A.mu + A.d) =>
        (pfCube E (if (i.rev : ℕ) < A.mu then 1 else 2)).var
          (pdEq E (if (i.rev : ℕ) < A.mu then 1 else 2) (x.pt i.rev)) :=
  Clo.pVars_mix E (A.mu + A.d) (dgEnd A.mu A.d (ordC (A.mu + A.d))) _

/-- For every γ: the data's map `Y` at γ is the extension of the bits at the point whose
coordinate t is γ (k − 1 − t). -/
theorem en_Y (μ : A.J → E) (γ : Fin (A.mu + A.d) → E) :
    (A.En P).Y (ext0 μ) γ = Alg.mle (fun c => ext0 μ (A.cell c)) fun t => γ t.rev := by
  have h := Alg.mle_equiv (ordC (A.mu + A.d)) (fun c => ext0 μ (A.cell c))
    (fun v => γ ((ordC (A.mu + A.d)).symm v))
  simp only [Equiv.symm_apply_apply] at h
  exact h

end Dat
end
end Lk6
