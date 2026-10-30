-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoNumsEq.lean.
The public numbers and places of a sub-proof's lookup, described twice, and tied.

The lookup of a sub-proof is a value `forA E h L` of the record of an assembled lookup, built from
the verifier's own record `h` of a
forest's shape and from the caller's layout `L`. The rows that its verifier hands on are stated
through `numsOf (forA E h L) (st, θ) kAt`:
numbers, orders and places read off that value. The flat function reads `numsF h lm jLK θ`: the
same numbers, orders and places read off
`h` alone, with places of a plain type (`Fo.Pl`: an entry of the mask row, a cell of the planes'
matrix, a key, the place that is no cell).

This file states that the two records are equal, field by field, once the plain places are renamed
into the caller's entries (`placeOf`), and but
for the two fields on keys, which no row beside the keys' own reads (`Fo.noKey`).

Main names:
  `placeOf mk pl`: the renaming: entry j of the mask row to `some (mk j)`, cell (r, c) to `some (pl
  r c)`; the place that is no cell, and a key, to `none`.
  `led_eqG`: the places of one sumcheck's own masks, read through the names of the hiding
    polynomial's coefficients, are the ledger's, made total.
  `numsOf_forA`: the equation of records. Its hypotheses speak of public numbers and of the caller's
    layout alone: the trees have at least 2^10 keys;
    slot s of the lookup is entry jLK + s of the mask row; bit j of the count of row t of call c <
    NC stands in the cell that `cellRC` names.
  `numsOf_forA_made`: these hypotheses are met by the layout that is made from the two maps, at
    every lawful shape.
  `forA_rows16`: so every row that the lookup's verifier hands on, but the keys' own, is the flat
    function's row at the trace of the last state, with its places renamed.

Limits: this file says nothing on keys. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoTies
import OnBytes.Tie.Pv.Lookup.Forest.FoV
import Cb.Pv.Lookup.Forest.FoNat
import OnBytes.Tie.Pv.Lookup.Value.TwNumsEq
import Cb.Pv.Lookup.Out.TwRows16

set_option autoImplicit false

namespace Cb.Fo.NumsEq
open TwV Tw3 Cb Cb.Tw Cb.LdLkp Cb.Fo
open TwNums (Sizes Sc)
open TwNums.Sizes (Ent)

/-- The plain places, renamed into the caller's entries with the one entry more. -/
def placeOf {J₀ : Type} (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) : _root_.Fo.Pl → Option J₀
  | .mask j => some (mk j)
  | .cell r c => some (pl r c)
  | .key _ _ => none
  | .zero => none

/-- The places of one sumcheck's own masks, for any map g from slots to entries. -/
theorem led_eqG {E J : Type} (g : ℕ → J) (l : List (PFmt E)) (c : Sc) (hd : l.map PFmt.n = c.degs)
    (pl : Ent → ℕ)
    (sh : ℕ → J) (hs : ∀ a, sh a = g (pl (Ent.clamp c (.shown a)))) :
    ledOf l (fun i => g (pl (pEnt l i))) sh =
      ⟨fun r t => g (pl (Ent.clamp c (.coef r t))), g (pl (Ent.clamp c .const)),
          fun a => g (pl (Ent.clamp c (.shown a)))⟩ := by
  have e1 : (fun r t => g (pl (pEnt l (pAt l r t)))) = fun r t => g (pl (Ent.clamp c (.coef r t)))
      := by
    funext r t
    rw [pEnt_pAt, hd]
    rfl
  have e2 : g (pl (pEnt l (pEnd l))) = g (pl (Ent.clamp c .const)) := by
    rw [pEnt_pEnd]
    rfl
  have e3 : sh = fun a => g (pl (Ent.clamp c (.shown a))) := funext hs
  show (⟨fun r t => g (pl (pEnt l (pAt l r t))), g (pl (pEnt l (pEnd l))), sh⟩ : Led J) = _
  rw [e1, e2, e3]

theorem ofFn_asList {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    (List.ofFn fun j : Fin k => ((σ j : Fin k) : ℕ)) = E3.asList σ :=
  List.ofFn_eq_map

theorem two_sh {J : Type} (g : ℕ → J) (pl : Ent → ℕ) (c : Sc) (hc : c.shown = 2) (a : ℕ) :
    g (pl (.shown (TwNums.shownBool (decide (a ≠ 0))))) = g (pl (Ent.clamp c (.shown a))) := by
  show _ = g (pl (if c.shown = 0 then .const else .shown (min a (c.shown - 1))))
  rw [hc, if_neg (by decide)]
  rcases a with _ | a
  · rfl
  · show g (pl (.shown 1)) = g (pl (.shown (min (a + 1) 1)))
    rw [Nat.min_eq_right (by omega)]

section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh)
    (L : Lay E St₀ J₀)

theorem tie_sh (l a : ℕ) : tiePl (forA E h L) l a =
    some (L.mkS ((FoNums.S h).pTie l (Ent.clamp ((FoNums.S h).scTie l) (.shown a)))) := by
  cases l with
  | zero =>
    rcases a with _ | _ | a
    · rfl
    · rfl
    · show some (L.mkS ((FoNums.S h).pTie 0 (.shown 2))) = some
        (L.mkS ((FoNums.S h).pTie 0 (.shown (min (a + 2) 2))))
      rw [Nat.min_eq_right (by omega)]
  | succ l =>
    rcases a with _ | a
    · rfl
    · show some (L.mkS ((FoNums.S h).pTie (l + 1) (.shown 1))) = some
        (L.mkS ((FoNums.S h).pTie (l + 1) (.shown (min (a + 1) 1))))
      rw [Nat.min_eq_right (by omega)]

/-- The two descriptions of the public numbers and places are one. -/
theorem numsOf_forA (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (hd : 10 ≤ h.dT)
    (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC → L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1
        (FoNums.cellRC h lm (t, c, j)).2)
    (st : St₀) (θ : E) (kAt : ℕ → (forA E h L).J ⊕ E) :
    _root_.Fo.noKey (numsOf (forA E h L) (st, θ) kAt) =
      _root_.Fo.noKey (_root_.Fo.numsMap (placeOf mk pl) (_root_.Fo.numsF h lm jLK θ)) := by
  have hoK : (fun l => List.ofFn fun j : Fin (0 + l) => (((forA E h L).oK l j : Fin (0 + l)) : ℕ)) =
      FoNums.ordK h := by
    funext l
    refine (ofFn_asList _).trans ((asList_forOK h hd (0 + l)).trans ?_)
    rw [Nat.zero_add]
  have hoT : (fun l => List.ofFn fun j : Fin ((forA E h L).w + l) =>
      (((forA E h L).oT l j : Fin ((forA E h L).w + l)) : ℕ)) = FoNums.ordT :=
    funext fun l => (ofFn_asList _).trans (asList_default _)
  have hoE : (List.ofFn fun j : Fin ((forA E h L).w + (forA E h L).d) =>
      (((forA E h L).oE j : Fin _) : ℕ)) = FoNums.ordE h :=
    (ofFn_asList _).trans (tie_oE E h L)
  have hoB : (List.ofFn fun j : Fin ((forA E h L).w + (forA E h L).d) =>
      (((forA E h L).oB j : Fin _) : ℕ)) = FoNums.ordB h :=
    (ofFn_asList _).trans (tie_oB E h L)
  have hbA : (forA E h L).bAt = fun u j => placeOf mk pl ((_root_.Fo.numsF h lm jLK θ).bAt u j) :=
    by
    funext u j
    show (FoNums.cellOf h u j).map (fun x => L.bc x.1 x.2.1 x.2.2) = placeOf mk pl
        (match FoNums.cellOf h u j with
      | some x => .cell (FoNums.cellRC h lm x).1 (FoNums.cellRC h lm x).2
      | none => .zero)
    unfold FoNums.cellOf
    by_cases hc : u % 2 ^ h.cK < h.NC
    · rw [if_pos hc]
      exact congrArg some (hbc _ _ _ hc)
    · rw [if_neg hc]
      rfl
  have hTie : (fun l => ledOf _ ((forA E h L).wAt l) (tiePl (forA E h L) l)) =
      fun j => _root_.Fo.ledMap (placeOf mk pl) (_root_.Fo.ledF jLK ((FoNums.S h).pTieC j)) := by
    funext l
    refine (led_eqG (fun s => some (L.mkS s)) _ ((FoNums.S h).scTie l) (degs_tie E (FoNums.S h) l)
        ((FoNums.S h).pTie l) _
      (tie_sh E h L l)).trans ?_
    simp only [hmk]
    rfl
  have hK : (fun l => ledOf _ ((forA E h L).wK l) fun a => (forA E h L).cK l (decide (a ≠ 0))) =
      fun l => _root_.Fo.ledMap (placeOf mk pl) (_root_.Fo.ledF jLK ((FoNums.S h).pKeyC l)) := by
    funext l
    refine (led_eqG (fun s => some (L.mkS s)) _ ((FoNums.S h).scKey l) (degs_key E (FoNums.S h) l)
        ((FoNums.S h).pKey l) _
      (two_sh (fun s => some (L.mkS s)) ((FoNums.S h).pKey l) _ rfl)).trans ?_
    simp only [hmk]
    rfl
  have hT : (fun l => ledOf _ ((forA E h L).wT l) fun a => (forA E h L).cT l (decide (a ≠ 0))) =
      fun l => _root_.Fo.ledMap (placeOf mk pl) (_root_.Fo.ledF jLK ((FoNums.S h).pTabC l)) := by
    funext l
    refine (led_eqG (fun s => some (L.mkS s)) _ ((FoNums.S h).scTab l) (degs_tab E (FoNums.S h) l)
        ((FoNums.S h).pTab l) _
      (two_sh (fun s => some (L.mkS s)) ((FoNums.S h).pTab l) _ rfl)).trans ?_
    simp only [hmk]
    rfl
  have hB : (ledOf _ (forA E h L).wB fun _ => (forA E h L).cB) =
      _root_.Fo.ledMap (placeOf mk pl) (_root_.Fo.ledF jLK (FoNums.S h).pBitC) := by
    refine (led_eqG (fun s => some (L.mkS s)) _ (FoNums.S h).scBit (degs_bit E (FoNums.S h))
        (FoNums.S h).pBit _ fun a => ?_).trans ?_
    · show some (L.mkS ((FoNums.S h).pBit (.shown 0))) = some
        (L.mkS ((FoNums.S h).pBit (.shown (min a 0))))
      rw [Nat.min_eq_right (Nat.zero_le a)]
    · simp only [hmk]
      rfl
  have hE0 :=
    led_eqG (fun s => some (L.mkS s)) _ (FoNums.S h).scEnd (degs_endS E (FoNums.S h))
        (FoNums.S h).pEnd
    (fun a => some (L.mkS ((FoNums.S h).pEnd (Ent.clamp (FoNums.S h).scEnd (.shown a))))) fun _ =>
        rfl
  have hE : (ledOf _ (forA E h L).wE fun _ => (forA E h L).cB) =
      _root_.Fo.ledMap (placeOf mk pl) (_root_.Fo.numsF (K := E) h lm jLK θ).ledE := by
    refine (congrArg₂ (fun a b => (⟨a, b, fun _ => (fun s => some (L.mkS s))
        ((FoNums.S h).pBit (.shown 0))⟩ : Led (Option J₀)))
      (congrArg Led.pw hE0) (congrArg Led.c0 hE0)).trans ?_
    simp only [hmk]
    rfl
  unfold _root_.Fo.noKey numsOf _root_.Fo.numsMap
  simp only []
  rw [hoK, hoT, hoE, hoB, hTie, hK, hT, hE, hB, hbA]
  rfl

/-- The hypotheses are met: the layout that is made from the two maps meets them by definition, at
every lawful shape. -/
theorem numsOf_forA_made (K : St₀ → (J₀ → E) → ℕ → ℕ → E) (lm jLK : ℕ) (mk : ℕ → J₀)
    (pl : ℕ → ℕ → J₀)
    (H : FoNums.ok h = true) (st : St₀) (θ : E)
    (kAt : ℕ → (forA E h ⟨K, fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1
        (FoNums.cellRC h lm (t, c, j)).2,
      fun s => mk (jLK + s)⟩).J ⊕ E) :
    _root_.Fo.noKey (numsOf (forA E h ⟨K, fun t c j => pl (FoNums.cellRC h lm (t, c, j)).1
        (FoNums.cellRC h lm (t, c, j)).2,
        fun s => mk (jLK + s)⟩) (st, θ) kAt) =
      _root_.Fo.noKey (_root_.Fo.numsMap (placeOf mk pl) (_root_.Fo.numsF h lm jLK θ)) :=
  numsOf_forA E h _ lm jLK mk pl (ok_parts H).1.1 (fun _ => rfl) (fun _ _ _ _ => rfl) st θ kAt

/-- Every row that the lookup's verifier hands on, but the keys', is the flat function's row at
the trace of the last state, its places renamed, spread. -/
theorem forA_rows16 (lm jLK : ℕ) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (hd : 10 ≤ h.dT)
    (hmk : ∀ s, L.mkS s = mk (jLK + s))
    (hbc : ∀ t c j, c < h.NC → L.bc t c j = pl (FoNums.cellRC h lm (t, c, j)).1
        (FoNums.cellRC h lm (t, c, j)).2)
    (o : (forA E h L).XB) :
    ((forA E h L).rd o).2.2 =
      ((_root_.Fo.r16 (_root_.Fo.numsF h lm jLK ((forA E h L).rd o).1.2)
          (traceOf (forA E h L) o)).map
        (_root_.Fo.rowMap (placeOf mk pl))).map toRow := by
  rw [rows16_eq (forA E h L) (fun _ => .inr 0) o, ← _root_.Fo.r16_eq, ← _root_.Fo.r16_noKey,
      ← _root_.Fo.r16_map,
    ← _root_.Fo.r16_noKey (_root_.Fo.numsMap _ _)]
  exact congrArg (fun N => (_root_.Fo.r16 N (traceOf (forA E h L) o)).map toRow)
    (numsOf_forA E h L lm jLK mk pl hd hmk hbc ((forA E h L).rd o).1.1 ((forA E h L).rd o).1.2 _)

end
end Cb.Fo.NumsEq
