-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Lists/TwAsm.lean.
The rounds and the errors of the whole lookup, for every record A of its letters and every letter SK
for the sumcheck, under the letter's two laws alone.

Main statements.
  asmK_roundIs: LtShape SK → the rounds of (A.baseKS SK).R.shape are the entries entG wk A.v' A.d
    A.w A.n (the closing's degrees in A's own order of variables).
  asmK_eps: LtErr SK → the errors of A.baseKS SK are epsG A.v' A.d A.w A.n |E| (the same degrees).
  entG_port, epsG_port: with the closing's degrees d times 2, then w times 1, the two lists are
    TwPlan.entN and TwErr.epsN. asmK_roundIs_port, asmK_eps_port: so it is where A.oE =
    Fin.revPerm.
  asmK_len: the chain has as many rounds as the list has entries.
General in the four sizes, in the orders of variables, in the padding and in the places of the
entries.
Limit: ShapeIs (OnBytes/G4/RoundIs.lean) ties msg, drawE and drawNZ alone; an entry's name, its work
wk and its other numbers are tied to the round by nothing.

-/
import OnBytes.Tie.Pv.Lookup.Lists.TwShape

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TwRound
open Iop IOR Cb Cb.LdLkp Cb.LdLkp.Kn TwPlan TwErr OnBytes.G4 Johnson.L5.Layers

/-- entN with the closing's degrees as a list. -/
def entG (wk v' d w n : Nat) (dgE : List Nat) : List Fmt.Entry :=
  [rd wk "LKP" 0 1] ++ pscN wk [] true 3 3 ++ (List.range n).flatMap (fun _ => pscN wk [] true 3 2)
      ++ [rd wk "JOIN" 0 w] ++
  (List.range (v' + 1)).flatMap (fun l => pscN wk (List.replicate l 2) true 2 2 ++
      [rd wk "LINE" 0 1]) ++
  (List.range d).flatMap (fun l => pscN wk (List.replicate (w + l) 2) true 2 2 ++
      [rd wk "LINE" 0 1]) ++
  pscN wk dgE false 0 0 ++
  [rd wk "ZERO" 0 (w + d)] ++ pscN wk (List.replicate (w + d) 2) true 2 1

def epsG (v' d w n q : Nat) (dgE : List Nat) : List Nat :=
  [2 ^ (v' + 1) - 1] ++ (List.range (n + 1)).flatMap (fun _ => pscC 0 0 3) ++ [w * q ^ (w - 1)] ++
  (List.range (v' + 1)).flatMap (fun l => pscC l 2 2 ++ [1]) ++
  (List.range d).flatMap (fun l => pscC (w + l) 2 2 ++ [1]) ++
  ([1] ++ dgE) ++
  [(w + d) * q ^ (w + d - 1)] ++ pscC (w + d) 2 2

theorem entG_port (wk v' d w n : Nat) : entG wk v' d w n (List.replicate d 2 ++ List.replicate w 1)
    = entN wk v' d w n := rfl
theorem epsG_port (v' d w n q : Nat) : epsG v' d w n q (List.replicate d 2 ++ List.replicate w 1) =
    epsN v' d w n q := by
  simp [epsG, epsN, List.append_assoc]

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec}

/-! ### the tie -/

theorem tie_card (D : TieF E) (l : ℕ) : Fintype.card (D.lv l).T.A = if l = 0 then 3 else 2 := by
  cases l <;> rfl

theorem ri_tieStep {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) (D : TieF E) (l : ℕ) :
    RI E (D.stepK SK l) (pscN wk [] true 3 (if l = 0 then 3 else 2)) := by
  have h := ri_full hS wk (D.lv l).T 0 2 _ (D.fmt_nil l) (tie_card D l)
  rw [D.dy3 l] at h
  exact ri_postM h _

theorem el_tieStep {SK : PscLtK E Ex} (hS : LtErr SK) (D : TieF E) (l : ℕ) : EL (D.stepK SK l)
    (pscC 0 0 3) := by
  have h := el_full hS (D.lv l).T 0 2 (D.fmt_nil l)
  rw [D.dy3 l] at h
  exact el_postM h _

theorem flat_succ {α : Type} (f : ℕ → List α) (n : ℕ) :
    (List.range (n + 1)).flatMap f = f 0 ++ (List.range n).flatMap fun l => f (l + 1) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem ri_head {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) (H : LkHeadF E) :
    RI E (H.headK SK) ([rd wk "LKP" 0 1] ++ (pscN wk [] true 3 3 ++ (List.range H.n).flatMap fun _
        => pscN wk [] true 3 2)) := by
  have h := ri_chain (E := E) _ _ _ (ri_tieStep hS wk H.tie) H.n
  rw [flat_succ] at h
  exact ri_seq (ri_draw1 _ _ wk "LKP") (ri_preM h _)

theorem el_head {SK : PscLtK E Ex} (hS : LtErr SK) (H : LkHeadF E) :
    EL (H.headK SK) ([2 ^ H.v - 1] ++ (List.range (H.n + 1)).flatMap fun _ => pscC 0 0 3) :=
  el_seq (el_draw _ _) (el_preM (el_chain _ _ _ (el_tieStep hS H.tie) H.n) _)

/-! ### a tree's levels -/

theorem tree_card (D : TreeP E) (l : ℕ) : Fintype.card (D.lv l).T.A = 2 := by
  cases l <;> rfl

theorem ri_lev {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) (D : TreeP E) (l : ℕ) :
    RI E (D.levK SK l) (pscN wk (List.replicate (D.g + l) 2) true 2 2 ++ [rd wk "LINE" 0 1]) := by
  have h := ri_full hS wk (D.lv l).T (D.g + l) 2 2 (tree_fmt D l).1 (tree_card D l)
  rw [(tree_fmt D l).2] at h
  exact ri_seq h (ri_draw1 _ _ wk "LINE")

theorem el_lev {SK : PscLtK E Ex} (hS : LtErr SK) (D : TreeP E) (l : ℕ) :
    EL (D.levK SK l) (pscC (D.g + l) 2 2 ++ [1]) := by
  have h := el_full hS (D.lv l).T (D.g + l) 2 (tree_fmt D l).1
  rw [(tree_fmt D l).2] at h
  exact el_seq h (el_draw _ _)

end

/-! ### the assembly -/

section
variable {E : Type} [Field E] [Fintype E] {Ex : ExtSpec} (A : LkAsmH E)

theorem ri_forest {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) : ∀ l, RI E (A.forestK SK l)
    ((List.range (A.v' + 1)).flatMap (fun l => pscN wk (List.replicate l 2) true 2 2 ++
        [rd wk "LINE" 0 1]) ++
      (List.range l).flatMap fun l => pscN wk (List.replicate (A.w + l) 2) true 2 2 ++
          [rd wk "LINE" 0 1])
  | 0 => by
    have h := ri_chain (E := E) _ _ _ (ri_lev hS wk (A.IK.setV (A.v' + 1)).DK) A.v'
    have h2 : RI E (A.forestK SK 0) _ := ri_postM (ri_preM h _) A.enterT
    have e : (A.IK.setV (A.v' + 1)).DK.g = 0 := rfl
    simpa [e] using h2
  | l + 1 => by
    have hl : RI E (A.D.levK SK l) (pscN wk (List.replicate (A.w + l) 2) true 2 2 ++
        [rd wk "LINE" 0 1]) := ri_lev hS wk A.D l
    have h := ri_seq (ri_forest hS wk l) hl
    rw [List.range_succ (n := l), List.flatMap_append]
    simpa [List.append_assoc] using h

theorem el_forest {SK : PscLtK E Ex} (hS : LtErr SK) : ∀ l, EL (A.forestK SK l)
    ((List.range (A.v' + 1)).flatMap (fun l => pscC l 2 2 ++ [1]) ++ (List.range l).flatMap fun l =>
        pscC (A.w + l) 2 2 ++ [1])
  | 0 => by
    have h := el_chain _ _ _ (el_lev hS (A.IK.setV (A.v' + 1)).DK) A.v'
    have h2 : EL (A.forestK SK 0) _ := el_postM (el_preM h _) A.enterT
    have e : (A.IK.setV (A.v' + 1)).DK.g = 0 := rfl
    simpa [e] using h2
  | l + 1 => by
    have hl : EL (A.D.levK SK l) (pscC (A.w + l) 2 2 ++ [1]) := el_lev hS A.D l
    have h := el_seq (el_forest hS l) hl
    rw [List.range_succ (n := l), List.flatMap_append]
    simpa [List.append_assoc] using h

theorem ri_root (wk : Nat) : RI E (A.rootK Ex) [rd wk "JOIN" 0 A.w] :=
  ri_drawP (D := Fin (A.w + 0) → E) _ _ wk A.w "JOIN" (Equiv.refl _)

theorem el_root : EL (A.rootK Ex) [A.w * Fintype.card E ^ (A.w - 1)] := by
  show [A.R.toIn.ev.err] = _
  rw [ldLkpRoot_err E A.R]
  rfl

theorem ri_end {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) :
    RI E (A.endK SK) (pscN wk (List.ofFn (dgEnd A.w A.d A.oE)) false 0 0) := by
  unfold RI LkAsmH.endK
  rw [hS.core A.En.par]
  show List.Forall₂ (EntryIs E) ([pRound0 E] ++ sRounds (pfMix E (A.w + A.d) (dgEnd A.w A.d A.oE)))
      _
  unfold pscN
  simp only [Bool.false_eq_true, if_false, List.append_nil]
  exact f2_append (.cons (entryIs_r0 wk) .nil) (ri_mix wk _ _)

theorem el_end {SK : PscLtK E Ex} (hS : LtErr SK) : EL (A.endK SK)
    ([1] ++ List.ofFn (dgEnd A.w A.d A.oE)) := by
  unfold EL LkAsmH.endK
  rw [hS.core A.En.par]
  exact congrArg (List.cons 1) (mix_degs E (A.w + A.d) (dgEnd A.w A.d A.oE))

def eUnitProd (α : Type) : Unit × α ≃ α := ⟨Prod.snd, fun a => ((), a), fun _ => rfl, fun _ => rfl⟩

theorem ri_bit {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) :
    RI E (A.bitK SK) ([rd wk "ZERO" 0 (A.w + A.d)] ++ pscN wk (List.replicate (A.w + A.d) 2) true 2
        1) :=
  ri_seq (ri_drawP (D := Unit × (Fin (A.w + A.d) → E)) _ _ wk (A.w + A.d) "ZERO" (eUnitProd _))
    (ri_full hS wk A.Bt.zc.next (A.w + A.d) 2 1 rfl rfl)

theorem el_bit {SK : PscLtK E Ex} (hS : LtErr SK) :
    EL (A.bitK SK) ([(A.w + A.d) * Fintype.card E ^ (A.w + A.d - 1)] ++ pscC (A.w + A.d) 2 2) := by
  refine el_seq ?_ (el_full hS A.Bt.zc.next (A.w + A.d) 2 rfl)
  show [A.Bt.zc.toIn.ev.err] = _
  rw [ldLkpBitP_err E A.Bt]
  rfl

theorem asmK_roundIs {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) :
    ShapeIs E (A.baseKS SK).R.shape (entG wk A.v' A.d A.w A.n (List.ofFn (dgEnd A.w A.d A.oE))) :=
      by
  have h : RI E (A.baseKS SK) _ :=
    ri_postM (ri_seq (ri_seq (ri_seq (ri_seq (ri_head hS wk A.H) (ri_root A wk))
    (ri_forest A hS wk A.d)) (ri_end A hS wk)) (ri_bit A hS wk)) A.rd
  have e : A.H.n = A.n := rfl
  unfold RI at h
  unfold ShapeIs
  simpa [entG, e, List.append_assoc] using h

theorem asmK_eps {SK : PscLtK E Ex} (hS : LtErr SK) :
    TWhole.errList (A.baseKS SK).e = epsG A.v' A.d A.w A.n (Fintype.card E)
        (List.ofFn (dgEnd A.w A.d A.oE)) := by
  have h : EL (A.baseKS SK) _ :=
    el_postM (el_seq (el_seq (el_seq (el_seq (el_head hS A.H) (el_root A))
    (el_forest A hS A.d)) (el_end A hS)) (el_bit A hS)) A.rd
  have e : A.H.n = A.n := rfl
  have e2 : A.H.v = A.v' + 1 := rfl
  unfold EL at h
  simpa [epsG, e, e2, List.append_assoc] using h

theorem asmK_roundIs_port {SK : PscLtK E Ex} (hS : LtShape SK) (wk : Nat) (ho : A.oE = Fin.revPerm)
    :
    ShapeIs E (A.baseKS SK).R.shape (entN wk A.v' A.d A.w A.n) := by
  have h := asmK_roundIs A hS wk
  rw [ho, dgEnd_rev] at h
  exact h

theorem asmK_eps_port {SK : PscLtK E Ex} (hS : LtErr SK) (ho : A.oE = Fin.revPerm) :
    TWhole.errList (A.baseKS SK).e = epsN A.v' A.d A.w A.n (Fintype.card E) := by
  have h := asmK_eps A hS
  rw [ho, dgEnd_rev, epsG_port] at h
  exact h

theorem asmK_len {SK : PscLtK E Ex} (hS : LtShape SK) (ho : A.oE = Fin.revPerm) :
    (A.baseKS SK).R.shape.length = (entN 0 A.v' A.d A.w A.n).length :=
      List.Forall₂.length_eq (asmK_roundIs_port A hS 0 ho)

end
end TwRound
