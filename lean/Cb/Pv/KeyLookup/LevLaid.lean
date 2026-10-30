-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevLaid.lean: which variable a round binds, of the trees that the lookup with parts
lays; and, at the short sumcheck `SK₀`, that a round is a round of the transcript.

Of `A.part L i` and `A.tabT L`:
  `Pub.beginOK`  the clause `Adm.order` gives `BeginOK` at the last level of every part.
  `keyList first v l`, `tabList mu l`  the list of a level's order.
  `Dat.key_binds`, `Dat.tab_binds`  round j of level l binds the variable whose number is entry j of
                that list.
  `Dat.key_weighs`, `Dat.tab_weighs`  place j of that level's list of variables is the equality
                weight
                at that coordinate of the level's point.
At `SK₀`, where the verifier rejects nothing:
  `chS l t τ j`  the value of the challenge drawn in round j of a transcript of the short rounds of
                l.
  `lev_eq0`     at every level's sumcheck of every tree with orders each variable's weights sum to
                1.
  `lev_total_short`  at every x, y, τ that verifier puts out a state.
  `lev_out_short`  if it puts out o from (x, τ): o.st = x.2, and place j of o.pt is the challenge of
                round j of τ behind the first round.
  `lev_point_short`  coordinate t of the point that level l hands on is the challenge of the
                transcript's round that bound t.
Conditions: `Adm.order`; i < m; 1 ≤ v i. For the statements at `SK₀`: none.
Not claimed: the like at the library's sumcheck or at another letter; the orders of the closing and
of the test of bits.
Not claimed: anything on hiding.

-/
import Cb.Pv.KeyLookup.LevB2
import Cb.Pv.KeyLookup.LevShort
import Cb.Pv.KeyLookup.ShortPt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn Iop IOR Hiop Prob Johnson.L5.Layers

/-! ### (g1) the laid terms -/

namespace Lev
theorem foldl_min_le : ∀ (l : List ℕ) (a : ℕ), l.foldl min a ≤ a ∧ ∀ v ∈ l, l.foldl min a ≤ v
  | [], a => ⟨le_refl a, fun _ h => absurd h List.not_mem_nil⟩
  | b :: l, a => by
    have ih := foldl_min_le l (min a b)
    refine ⟨ih.1.trans (min_le_left a b), fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv
    · exact ih.1.trans (min_le_right a v)
    · exact ih.2 v hv
end Lev

theorem Pub.least_le (S : Pub) (i : ℕ) (hi : i < S.m) : S.least ≤ S.v i := by
  have e : S.v i = S.parts[i] := List.getD_eq_getElem _ _ hi
  rw [e]
  exact (Lev.foldl_min_le S.parts (S.v 0)).2 _ (List.getElem_mem hi)

theorem Pub.beginOK (S : Pub) (h : (∀ j ∈ S.order, j + 1 < S.least) ∧ S.order.Nodup) (i : ℕ) (hi : i
    < S.m) :
    BeginOK S.order (0 + (S.v i - 1)) :=
  ⟨fun j hj => by
    have h1 := h.1 j hj
    have h2 := S.least_le i hi
    omega, h.2⟩

/-- the list of a key level's order; of a level of the table's tree -/
def keyList (first : List ℕ) (v l : ℕ) : List ℕ :=
  if l + 1 = v then beginList first (0 + l) else (List.range (0 + l)).reverse
def tabList (mu l : ℕ) : List ℕ := (List.range (mu + l)).reverse

theorem ordKey_list (first : List ℕ) (v l : ℕ) (hb : l + 1 = v → BeginOK first (0 + l)) (j : Fin
    (0 + l)) :
    ((ordKey first v l j : Fin (0 + l)) : ℕ) = (keyList first v l).getD j.1 0 := by
  unfold keyList
  by_cases h : l + 1 = v
  · rw [if_pos h, ordKey_last first h]
    exact ordOf_val (hb h) j
  · rw [if_neg h, ordKey_other first h]
    exact rev_val (0 + l) j

section
variable {E : Type} [Field E] [Fintype E]

namespace Dat
variable (A : Dat E) (L : LevPl A)

/-- ON THE LAID TERM: which variable round j of level l of part i's tree binds. -/
theorem key_binds (hO : (∀ j ∈ A.order, j + 1 < A.least) ∧ A.order.Nodup) (i : ℕ) (hi : i < A.m)
    (hv : 1 ≤ A.v i) (X : Type) (pr : X → A.kb.X0) (l : ℕ) (j : Fin (0 + l)) :
    ((((A.part L i).tree X pr).sg l j : Fin (0 + l)) : ℕ) = (keyList A.order (A.v i) l).getD j.1
        0 := by
  have e : ((A.part L i).tree X pr).sg l = ordKey A.order (A.v i - 1 + 1) l := rfl
  rw [e, Nat.sub_add_cancel hv]
  refine ordKey_list _ _ _ (fun h => ?_) j
  have hl : l = A.v i - 1 := by omega
  rw [hl]
  exact A.toPub.beginOK hO i hi

/-- .. and at which coordinate of the level's point its weight stands. -/
theorem key_weighs (i : ℕ) (X : Type) (pr : X → A.kb.X0) (l : ℕ) (s : (((A.part L i).tree X pr).lv
    l).T.St) :
    (((A.part L i).tree X pr).lv l).T.vars s =
      List.ofFn fun j : Fin (0 + l) => (pfCube E 2).var
        (pdEq E 2 ((((A.part L i).tree X pr).lv l).pnt s (((A.part L i).tree X pr).sg l j))) :=
  b2_binds ((A.part L i).tree X pr) l s

theorem tab_binds (l : ℕ) (j : Fin (A.mu + l)) :
    (((A.tabT L).tree.sg l j : Fin (A.mu + l)) : ℕ) = (tabList A.mu l).getD j.1 0 :=
  rev_val (A.mu + l) j

theorem tab_weighs (l : ℕ) (s : ((A.tabT L).tree.lv l).T.St) :
    ((A.tabT L).tree.lv l).T.vars s =
      List.ofFn fun j : Fin (A.mu + l) => (pfCube E 2).var
        (pdEq E 2 (((A.tabT L).tree.lv l).pnt s ((A.tabT L).tree.sg l j))) :=
  b2_binds (A.tabT L).tree l s

end Dat

/-! ### (g3) the rounds are the transcript's -/

variable {Ex : ExtSpec}

/-- Every level's sumcheck: each variable's weights sum to 1. -/
theorem lev_eq0 (D : TreeP E) (l : ℕ) : TWhole.Eq0 (D.lv l).T.par :=
  TWhole.our_eq0 (D.lv l).T fun st v hv => by
    rw [b2_binds D l st] at hv
    simp only [List.mem_ofFn] at hv
    obtain ⟨j, rfl⟩ := hv
    exact TWhole.mon0_eq 2 _

theorem lev_total_short (D : TreeP E) (l : ℕ) (x : E × (D.lv l).T.St) (y : Ex.Str)
    (τ : Tr (shapeS (D.lv l).T.par)) :
    ((SK₀ E Ex).full (D.lv l).T.par).R.out x y τ =
      some (TWhole.shortV (D.lv l).T.par (TWhole.F₀ (D.lv l).T.par) x τ) :=
  SK₀_out Ex (D.lv l).T.par (lev_eq0 D l) x y τ

/-- What SK₀'s verifier puts out at level l: the state, and the transcript's challenges round by
round. -/
theorem lev_out_short (D : TreeP E) (l : ℕ) (x : E × (D.lv l).T.St) (y : Ex.Str)
    (τ : Tr (shapeS (D.lv l).T.par)) (o : (D.lv l).T.par.Out)
    (h : ((SK₀ E Ex).full (D.lv l).T.par).R.out x y τ = some o) :
    o.st = x.2 ∧ ∀ j : ℕ, ppGet (D.lv l).T.par.fmt o.pt j =
      chS (D.lv l).T.par.fmt [pRoundV E (D.lv l).T.par.A] τ.2.2 j := by
  have e := (lev_total_short D l x y τ).symm.trans h
  obtain rfl := Option.some.inj e
  exact ⟨rfl, fun j => ppGet_vFinT _ _ _ _ _ _ j⟩

/-- Coordinate t of the point handed on is the challenge of the transcript's round that bound t. -/
theorem lev_point_short (D : TreeP E) (l : ℕ) (x : E × (D.lv l).T.St) (y : Ex.Str)
    (τ : Tr (shapeS (D.lv l).T.par)) (o : (D.lv l).T.par.Out)
    (h : ((SK₀ E Ex).full (D.lv l).T.par).R.out x y τ = some o) (t : Fin (D.g + l)) :
    (D.lv l).gam o t = chS (D.lv l).T.par.fmt [pRoundV E (D.lv l).T.par.A] τ.2.2 ((D.sg l).symm
        t) := by
  rw [b2_point D l o t]
  exact (lev_out_short D l x y τ o h).2 _

end
end Lk6

#print axioms Lk6.Dat.key_binds
#print axioms Lk6.Dat.key_weighs
#print axioms Lk6.Dat.tab_binds
#print axioms Lk6.Dat.tab_weighs
#print axioms Lk6.lev_eq0
#print axioms Lk6.lev_out_short
#print axioms Lk6.lev_point_short
