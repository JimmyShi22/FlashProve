-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Alg/TwOrdL.lean.
Laws of the loops over a tree's levels and the tie's steps in `TwV.traceOfFlat`
(Cb/Pv/Lookup/Out/TwV.lean). Lists alone.

Definitions, and theorems with their proofs, on `TwV.inRounds`, `TwV.lvGo`, `TwV.tieGo`.
Main names:
  `getD_ofFn`, `ofFn_snoc`: two laws of lists.
  `inRounds_ofFn`: a point by coordinate, read in the order of the rounds.
  `lvGo_zero`, `lvGo_succ`, `lvGo_snoc`: c + 1 levels are c levels, then one.
  `tieGoT`: the tie's loop that hands back the next target too. `tieGo_eq`: `TwV.tieGo` is `tieGoT`
    less that target. `tieGoT_snoc`: c + 1 steps are c steps, then one.
Limits: equations between functions on lists, for all inputs; no typed record is named.

-/
import Cb.Pv.Lookup.Out.TwV
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.GetD
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false

namespace Tw
open TwV

section
variable {K : Type}

theorem getD_ofFn {k : ℕ} (p : Fin k → K) (i : Fin k) (d : K) : (List.ofFn p).getD (i : ℕ) d = p i
    := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact i.2), List.getElem_ofFn]

theorem ofFn_snoc {k : ℕ} (g : Fin k → K) (x : K) :
    List.ofFn (Fin.snoc g x : Fin (k + 1) → K) = List.ofFn g ++ [x] := by
  rw [List.ofFn_succ_last]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

variable [CommRing K]

theorem inRounds_ofFn {k n : ℕ} (σ : Fin n → Fin k) (p : Fin k → K) :
    inRounds (List.ofFn fun j : Fin n => ((σ j : Fin k) : ℕ)) (List.ofFn p) =
      List.ofFn fun j : Fin n => p (σ j) := by
  unfold inRounds
  rw [List.map_ofFn]
  exact congrArg List.ofFn (funext fun j => getD_ofFn p (σ j) 0)

theorem lvGo_zero (o : ℕ → List ℕ) (l : ℕ) (tg : K) (pt : List K) (rs : Rounds K) :
    lvGo o 0 l tg pt rs = ([], tg, pt, rs) := rfl

theorem lvGo_succ (o : ℕ → List ℕ) (c l : ℕ) (tg : K) (pt : List K) (rs : Rounds K) :
    lvGo o (c + 1) l tg pt rs =
      (((takeSc rs tg (inRounds (o l) pt ++ [0]) true).1,
          ((takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.headD ([], [])).2.headD 0) ::
        (lvGo o c (l + 1)
          (lineTg (takeSc rs tg (inRounds (o l) pt ++ [0]) true).1
            (((takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.headD ([], [])).2.headD 0))
          (byVar (o l) (takeSc rs tg (inRounds (o l) pt ++ [0]) true).1.xs ++
            [((takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.headD ([], [])).2.headD 0])
          (takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.tail).1,
        (lvGo o c (l + 1)
          (lineTg (takeSc rs tg (inRounds (o l) pt ++ [0]) true).1
            (((takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.headD ([], [])).2.headD 0))
          (byVar (o l) (takeSc rs tg (inRounds (o l) pt ++ [0]) true).1.xs ++
            [((takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.headD ([], [])).2.headD 0])
          (takeSc rs tg (inRounds (o l) pt ++ [0]) true).2.tail).2) := rfl

/-- c + 1 levels: c levels, then one. -/
theorem lvGo_snoc (o : ℕ → List ℕ) : ∀ (c l : ℕ) (tg : K) (pt : List K) (rs : Rounds K),
    lvGo o (c + 1) l tg pt rs =
      ((lvGo o c l tg pt rs).1 ++
          (lvGo o 1 (l + c) (lvGo o c l tg pt rs).2.1 (lvGo o c l tg pt rs).2.2.1
            (lvGo o c l tg pt rs).2.2.2).1,
        (lvGo o 1 (l + c) (lvGo o c l tg pt rs).2.1 (lvGo o c l tg pt rs).2.2.1
          (lvGo o c l tg pt rs).2.2.2).2)
  | 0, _, _, _, _ => rfl
  | c + 1, l, tg, pt, rs => by
    rw [lvGo_succ o (c + 1), lvGo_snoc o c (l + 1), lvGo_succ o c l tg pt rs]
    rw [show l + 1 + c = l + (c + 1) by omega]
    rfl

/-- the tie's loop, handing back the next target too -/
def tieGoT : ℕ → ℕ → K → Rounds K → List (Sc K) × K × Rounds K
  | 0, _, tg, rs => ([], tg, rs)
  | c + 1, l, tg, rs =>
    ((takeSc rs tg [0] true).1 ::
        (tieGoT c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).1,
      (tieGoT c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).2)

theorem tieGo_eq : ∀ (c l : ℕ) (tg : K) (rs : Rounds K),
    tieGo c l tg rs = ((tieGoT c l tg rs).1, (tieGoT c l tg rs).2.2)
  | 0, _, _, _ => rfl
  | c + 1, l, tg, rs => by
    show ((takeSc rs tg [0] true).1 ::
        (tieGo c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).1,
      (tieGo c (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).2) = _
    rw [tieGo_eq c (l + 1)]
    rfl

theorem tieGoT_snoc : ∀ (c l : ℕ) (tg : K) (rs : Rounds K),
    tieGoT (c + 1) l tg rs =
      ((tieGoT c l tg rs).1 ++
          (tieGoT 1 (l + c) (tieGoT c l tg rs).2.1 (tieGoT c l tg rs).2.2).1,
        (tieGoT 1 (l + c) (tieGoT c l tg rs).2.1 (tieGoT c l tg rs).2.2).2)
  | 0, _, _, _ => rfl
  | c + 1, l, tg, rs => by
    show ((takeSc rs tg [0] true).1 ::
        (tieGoT (c + 1) (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).1,
      (tieGoT (c + 1) (l + 1) ((takeSc rs tg [0] true).1.v (nxAt l)) (takeSc rs tg [0] true).2).2) =
          _
    rw [tieGoT_snoc c (l + 1), show l + 1 + c = l + (c + 1) by omega]
    rfl

end
end Tw
#print axioms Tw.inRounds_ofFn
#print axioms Tw.lvGo_snoc
#print axioms Tw.tieGo_eq
#print axioms Tw.tieGoT_snoc
