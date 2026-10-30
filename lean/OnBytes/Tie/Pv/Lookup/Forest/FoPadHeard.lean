-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPadHeard.lean.
The record that the byte-level lookup routine returns holds the flat function's end values.

* `forall₂_getD`, `forall₂_of_getD`: a relation between two lists, member by member.
* `pad_heard`: at a lawful shape (`FoNums.ok`), from what the stretches of a run give together
(`PadRead`,
OnBytes/Tie/Pv/Lookup/Forest/FoPadFlat.lean): the
record written
  out in OnBytes/Tie/Pv/Lookup/Forest/FoPadCut.lean, with the state that the run leaves, holds
    `endsOf` at the run's shape, at
    the
  first free slot before the run, and at the calls of the run read as plain data (`HeardIs`).

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadFlat
import OnBytes.Tie.Pv.Lookup.Forest.FoEndsTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoWalksAt

set_option autoImplicit false

namespace Fo
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie

theorem forall₂_getD {α β : Type} {R : α → β → Prop} (a : α) (b : β) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ i, i < l₁.length →
      R (l₁.getD i a) (l₂.getD i b)
  | _, _, .nil, _, h => absurd h (Nat.not_lt_zero _)
  | _, _, .cons h _, 0, _ => h
  | _, _, .cons _ t, i + 1, h => forall₂_getD a b t i (Nat.lt_of_succ_lt_succ h)

theorem forall₂_of_getD {α β : Type} {R : α → β → Prop} (a : α) (b : β) :
    ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
      (∀ i, i < l₁.length → R (l₁.getD i a) (l₂.getD i b)) → List.Forall₂ R l₁ l₂
  | [], [], _, _ => .nil
  | x :: l₁, y :: l₂, hl, h =>
    .cons (h 0 (Nat.succ_pos _)) (forall₂_of_getD a b l₁ l₂ (Nat.succ.inj hl)
      fun i hi => h (i + 1) (Nat.succ_lt_succ hi))
  | [], _ :: _, hl, _ => absurd hl (by simp)
  | _ :: _, [], hl, _ => absurd hl (by simp)

theorem forall₂_mono {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons x t => .cons (h _ _ x) (forall₂_mono h t)

theorem take_rev {α : Type} (p : List α) (a b : ℕ) (h : p.length = a + b) :
    p.reverse.take a = (p.drop b).reverse := by
  rw [List.reverse_drop, h, Nat.add_sub_cancel]

theorem drop_rev {α : Type} (p : List α) (a b : ℕ) (h : p.length = a + b) :
    (p.reverse.drop a).take (a + b - a) = (p.take b).reverse := by
  rw [List.reverse_take, h, Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  exact List.take_of_length_le (by simp [h])

theorem zero_add_fun {α : Type} (f : ℕ → α) : (fun i => f (0 + i)) = f :=
  funext fun i => by rw [Nat.zero_add]

section
variable {K : Type} [CommRing K] (ρ : Reading K)

theorem pad_heard {lm : ℕ} {pub : Array Nat} {F : Fork} {c c' : Ctx} {M : PadMid} {l : List Ev}
    {scs : List (Sc K)} {ptT : Array OnBytes.E} {lvK lvT : List (Sc K × K)}
    {rowsK rowsT : List Aff} {evK evT : List Ev} {D : R5D}
    (R : PadRead ρ lm pub F c c' M l scs ptT lvK lvT rowsK rowsT evK evT D)
    (H : FoNums.ok (M.h pub) = true) :
    HeardIs ρ (M.heard pub F) M.G8 (endsOf (M.h pub) lm F.next (flEv ρ l)) := by
  have l78 : Later M.F7 M.G8 := R.r5.later
  have l68 : Later M.F6 M.G8 := R.table.later.trans l78
  have l58 : Later M.F5 M.G8 := R.keys.later.trans l68
  have hθ : ρ.val M.theta = (endsOf (M.h pub) lm F.next (flEv ρ l)).theta := R.theta.symm
  have hα : ρ.val M.alpha = (endsOf (M.h pub) lm F.next (flEv ρ l)).alpha := by
    show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).lam
    rw [R.trace]
  have hzb0 : rdA ρ M.zb0 = (endsOf (M.h pub) lm F.next (flEv ρ l)).zb0 := by
    show _ = (byVar (forN (M.h pub) lm F.next (flEv ρ l)).oE
      (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.xs).reverse
    rw [R.trace, R.nums]
    exact R.r5.zb0Is
  have hpn : pntK (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)) =
      pntTop (fun i => ordK (M.h pub) (0 + i)) [] lvK.reverse := by
    unfold pntK
    rw [R.trace, R.nums, zero_add_fun]
    rfl
  have hlen := pntK_len (K := K) (M.h pub) H lm F.next (flEv ρ l)
  have hrho : rdA ρ M.keys.rho =
      (pntK (forN (M.h pub) lm F.next (flEv ρ l))
        (forTrace (M.h pub) lm F.next (flEv ρ l))).reverse := by
    rw [hpn]
    exact R.keys.rho
  have hsz : M.keys.rho.size = (M.h pub).dT + (M.h pub).rK := by
    have := congrArg List.length hrho
    simpa [rdA, hlen] using this
  have hzx : rdA ρ (M.zx pub) = (endsOf (M.h pub) lm F.next (flEv ρ l)).zx := by
    show rdL ρ (M.keys.rho.extract 0 (M.h pub).dT) = ((pntK _ _).drop (M.h pub).rK).reverse
    rw [rdL_extract]
    show List.take ((M.h pub).dT - 0) (List.drop 0 (rdA ρ M.keys.rho)) = _
    rw [hrho, List.drop_zero, Nat.sub_zero]
    exact take_rev _ _ _ hlen
  have hzy : rdA ρ (M.zy pub) = (endsOf (M.h pub) lm F.next (flEv ρ l)).zy := by
    show rdL ρ (M.keys.rho.extract (M.h pub).dT M.keys.rho.size) =
      ((pntK _ _).take (M.h pub).rK).reverse
    rw [rdL_extract]
    show List.take (M.keys.rho.size - (M.h pub).dT) (List.drop (M.h pub).dT (rdA ρ M.keys.rho)) = _
    rw [hrho, hsz]
    exact drop_rev _ _ _ hlen
  have hN := R.nums
  have hT := R.trace
  -- the rows, as lists
  have hrows : List.Forall₂ (RowIs ρ M.G8) (M.table.rows.push M.row).toList
      (endsOf (M.h pub) lm F.next (flEv ρ l)).rows := by
    show List.Forall₂ _ _
      ((tieRowsR (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)).lam
          (forTrace (M.h pub) lm F.next (flEv ρ l)).tie.reverse).reverse ++
        (lvRowsR (forN (M.h pub) lm F.next (flEv ρ l)).ledK 0
          (fK (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)))
          (forTrace (M.h pub) lm F.next (flEv ρ l)).keys.reverse).reverse ++
        (lvRowsR (forN (M.h pub) lm F.next (flEv ρ l)).ledT
          (forN (M.h pub) lm F.next (flEv ρ l)).w
          (incT0 (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)))
          (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse).reverse ++
        [rowBitU (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l))])
    rw [Array.toList_push, R.table.pushed, R.keys.pushed, hN, hT]
    refine List.rel_append (List.rel_append (List.rel_append ?_ ?_) ?_) (.cons ?_ .nil)
    · refine forall₂_of_getD {} ⟨[], 0⟩ _ _ ?_ fun i hi => ?_
      · rw [List.length_reverse, tieRowsR_len, List.length_reverse, R.scsLen]
        exact R.tieN
      · have hi' : i < 31 := by simpa [R.tieN] using hi
        have := (R.tieRows i hi').later ρ l58
        rwa [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← List.getD_eq_getElem?_getD]
          at this
    · exact forall₂_mono (fun a b (h : RowIs ρ M.F6 a b) => h.later ρ l68) R.keys.rows0
    · exact forall₂_mono (fun a b (h : RowIs ρ M.F7 a b) => h.later ρ l78) R.table.rows0
    · exact R.bitRow _ rfl
  have hzd : (zdL (5 + (M.h pub).d) (M.h pub).d M.table.rho).map (fun p => ρ.val p.1) =
      (endsOf (M.h pub) lm F.next (flEv ρ l)).lvZs := by
    show _ = inRounds (forN (M.h pub) lm F.next (flEv ρ l)).oE
      (pntTop (forN (M.h pub) lm F.next (flEv ρ l)).oT
        (forTrace (M.h pub) lm F.next (flEv ρ l)).join
        (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse)
    rw [hN, hT, R.r5.lvZs, zero_add_fun]
    rfl
  have hdg : (zdL (5 + (M.h pub).d) (M.h pub).d M.table.rho).map (fun p => p.2) =
      (endsOf (M.h pub) lm F.next (flEv ρ l)).lvDg.map (· + 1) := by
    show _ = (dgE (forN (M.h pub) lm F.next (flEv ρ l))).map (· + 1)
    rw [hN]
    exact R.lvDg
  have hfirst : M.lv.first = (endsOf (M.h pub) lm F.next (flEv ρ l)).lvFirst :=
    R.r5.lvFirst.trans R.next7
  have htg : ρ.val M.lv.target = (endsOf (M.h pub) lm F.next (flEv ρ l)).lvTg := by
    show _ = tgTop (tgT0 (forN (M.h pub) lm F.next (flEv ρ l))
      (forTrace (M.h pub) lm F.next (flEv ρ l)))
      (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse
    rw [hN, hT, R.r5.lvTarget]
    exact (R.table.form0 M.F7 (Later.refl _)).1 D.tgL R.r5.target
  exact
    { theta := hθ
      alpha := hα
      a := by
        show _ = fac (forN (M.h pub) lm F.next (flEv ρ l))
          (forTrace (M.h pub) lm F.next (flEv ρ l)).lam
        rw [hN, hT]
        exact R.fac
      nRows := by
        have := hrows.length_eq
        rwa [Array.length_toList] at this
      rows := fun i hi => by
        have := forall₂_getD {} ⟨[], 0⟩ hrows i (by rwa [Array.length_toList])
        rwa [List.getD_eq_getElem?_getD, Array.getElem?_toList, ← Array.getD_eq_getD_getElem?]
          at this
      lvEps := by
        show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.eps
        rw [hT]
        exact R.r5.lvEps
      lvFin := by
        show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.fin
        rw [hT]
        exact R.r5.lvFin
      lvXs := by
        show _ = (forTrace (M.h pub) lm F.next (flEv ρ l)).cls.xs
        rw [hT]
        exact R.r5.lvXs
      lvVars := ⟨_, R.r5.lvVars, hzd, hdg⟩
      lvRan := ⟨D.muL, _, _, by
        have := R.r5.ranL
        rw [← R.r5.lvFirst, hfirst, ← this.eps_eq] at this
        exact this, hzd, hdg⟩
      lvSize := by
        have h1 := congrArg List.length R.r5.ranL.r_eq
        have h2 := congrArg List.length R.r5.ranL.vars_eq
        have h3 := R.r5.ranL.fits.length
        simp only [Array.length_toList, List.length_map, eqW] at h1 h2
        show M.lv.r.size = M.lv.vars.size
        omega
      lvFlags := R.r5.lvFlags
      lvTg := htg
      lvStart := by
        show FormIs ρ M.G8 M.lv.start
          (tgTop (tgT0 (forN (M.h pub) lm F.next (flEv ρ l))
            (forTrace (M.h pub) lm F.next (flEv ρ l)))
            (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse)
          (incTop (forN (M.h pub) lm F.next (flEv ρ l)).ledT
            (incT0 (forN (M.h pub) lm F.next (flEv ρ l))
              (forTrace (M.h pub) lm F.next (flEv ρ l)))
            (forTrace (M.h pub) lm F.next (flEv ρ l)).tabl.reverse)
        rw [hN, hT, R.r5.lvStart]
        exact R.table.form0.later ρ l78
      lvFirst := hfirst
      leavesA := heard_leavesA ρ (M.h pub) H lm F.next (flEv ρ l) M.theta M.alpha M.zb0 hθ hα hzb0
      sBit := by
        show _ = slotNo ((forN (M.h pub) lm F.next (flEv ρ l)).ledB.sh 0)
        rw [hN]
        exact R.sBit
      sBitAt := by
        show FormIs ρ M.G8 (Aff.slot M.sBit) ((forTrace (M.h pub) lm F.next (flEv ρ l)).bits.v 0)
          [(Pl.mask (slotNo ((forN (M.h pub) lm F.next (flEv ρ l)).ledB.sh 0)),
            (forTrace (M.h pub) lm F.next (flEv ρ l)).bits.be)]
        rw [hN, hT, ← R.sBit]
        exact R.sBitAt
      zx := hzx
      zy := hzy
      e := heard_e ρ (M.h pub) H lm F.next (flEv ρ l) (M.zy pub) hzy
      cEnd := by
        show FormIs ρ M.G8 M.keys.form (forTrace (M.h pub) lm F.next (flEv ρ l)).kT
          (incTop (forN (M.h pub) lm F.next (flEv ρ l)).ledK
            (fK (forN (M.h pub) lm F.next (flEv ρ l)) (forTrace (M.h pub) lm F.next (flEv ρ l)))
            (forTrace (M.h pub) lm F.next (flEv ρ l)).keys.reverse)
        rw [hN, hT]
        exact R.keys.form0.later ρ l68
      zb0 := hzb0
      zb1 := by
        show _ = (byVar (forN (M.h pub) lm F.next (flEv ρ l)).oB
          (forTrace (M.h pub) lm F.next (flEv ρ l)).bits.xs).reverse
        rw [hT, hN]
        exact R.r5.zb1Is
      tT := heard_tT ρ (M.h pub) H lm F.next (flEv ρ l) M.zb0 hzb0
      zk := heard_zk ρ (M.h pub) H lm F.next (flEv ρ l) (M.zx pub) (M.zy pub) hzx hzy }

end
end Fo
