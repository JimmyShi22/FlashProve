-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoWalksAt.lean: what the two walks of the lookup routine hand on, in
the flat function's own terms,
and the slot that is free behind each walk.

The record Walked (OnBytes/Tie/Pv/Lookup/Forest/FoDescent.lean) speaks of the levels from any level
l on, so at l = 0 its terms
read «fun i => o (0 + i)», «g + 0». Here they are written without the zero.

 - Walked.flat0, Walked.rows0, Walked.rho0, Walked.form0: the four fields at l = 0 in the terms
   lvGo o n 0 .., lvRowsR led g .., pntTop o .., incTop led ...
 - walkSlots_tel: the slots of n levels are the way from the first level's first slot to the first
   slot behind the last.
 - keys_slots, table_slots: at a forest: from the key side's first slot to the table side's; from
   the table side's first slot to the first slot of the sumcheck over the leaves.
 - keys_next, table_next: the slot that is free behind each walk. Premise: the walk began at its
   side's first slot.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoWalks

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

theorem zero_fun {α : Type} (f : ℕ → α) : (fun i => f (0 + i)) = f := by
  funext i
  rw [Nat.zero_add]

section
variable {K : Type} [CommRing K] {ρ : Reading K} {o : ℕ → List ℕ} {led : ℕ → Led Pl} {g n : ℕ}
  {s s' : Forest.Descent} {F G : Fork} {c c' : Ctx} {pt : List K} {tg : K} {inc : List (Pl × K)}
  {ev : List Ev} {lv : List (Sc K × K)} {rows : List Aff}

theorem Walked.flat0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows)
    (rest : Rounds K) :
    lvGo o n 0 tg pt (flEv ρ ev ++ rest) =
      (lv, tgTop tg lv.reverse, pntTop o pt lv.reverse, rest) := by
  have h := W.flat rest
  rwa [zero_fun o] at h

theorem Walked.rows0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    List.Forall₂ (RowIs ρ G) rows (lvRowsR led g inc lv.reverse).reverse := by
  have h := W.rowsAre
  rwa [zero_fun led] at h

theorem Walked.rho0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    rdA ρ s'.rho = (pntTop o pt lv.reverse).reverse := by
  have h := W.rho
  rwa [zero_fun o] at h

theorem Walked.form0 (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    FormIs ρ G s'.form (tgTop tg lv.reverse) (incTop led inc lv.reverse) := by
  have h := W.form
  rwa [zero_fun led] at h

theorem Walked.next (W : Walked ρ o led g n 0 s s' F G c c' pt tg inc ev lv rows) :
    G.next = F.next + walkSlots g n 0 := W.same.next

end

/-- The slots of n levels, from the steps between the levels' first slots. -/
theorem walkSlots_tel (g N : ℕ) (first : ℕ → ℕ)
    (hStep : ∀ l < N, first (l + 1) = first l + (1 + 2 * (g + l) + 4)) :
    ∀ n l, l + n ≤ N → first (l + n) = first l + walkSlots g n l
  | 0, _, _ => rfl
  | n + 1, l, h => by
    have e := walkSlots_tel g N first hStep n (l + 1) (by omega)
    rw [show l + (n + 1) = l + 1 + n by omega, e, hStep l (by omega)]
    show _ = first l + ((1 + 2 * (g + l) + 4) + walkSlots g n (l + 1))
    omega

/-- From the key side's first slot to the table side's. -/
theorem keys_slots (h : FoNums.Sh) :
    (FoNums.S h).fTab 0 = (FoNums.S h).fKey 0 + walkSlots 0 h.v 0 := by
  have e := walkSlots_tel 0 h.v (fun l => (FoNums.S h).fKey l)
    (fun l hl => by
      show (FoNums.S h).fKey (l + 1) = (FoNums.S h).fKey l + (1 + 2 * (0 + l) + 4)
      rw [Cb.Fo.Walk.first_key h l hl]
      simp only [layerSlots, sumcheckSlots, roundValues]
      omega) h.v 0 (by omega)
  rw [Nat.zero_add] at e
  exact (Cb.Fo.Walk.first_tab0 h).trans e

/-- From the table side's first slot to the first slot of the sumcheck over the leaves. -/
theorem table_slots (h : FoNums.Sh) :
    (FoNums.S h).fEnd = (FoNums.S h).fTab 0 + walkSlots 5 h.d 0 := by
  have e := walkSlots_tel 5 h.d (fun l => (FoNums.S h).fTab l)
    (fun l hl => by
      show (FoNums.S h).fTab (l + 1) = (FoNums.S h).fTab l + (1 + 2 * (5 + l) + 4)
      rw [Cb.Fo.Walk.first_tab h l hl]
      simp only [layerSlots, sumcheckSlots, roundValues]
      omega) h.d 0 (by omega)
  rw [Nat.zero_add] at e
  exact (Cb.Fo.Walk.first_end h).trans e

section
variable {K : Type} [CommRing K] {ρ : Reading K} {o : ℕ → List ℕ} {led : ℕ → Led Pl}
  {s s' : Forest.Descent} {F G : Fork} {c c' : Ctx} {pt : List K} {tg : K} {inc : List (Pl × K)}
  {ev : List Ev} {lv : List (Sc K × K)} {rows : List Aff}

/-- Behind the key side the table side's first slot is free. -/
theorem keys_next (h : FoNums.Sh) (jLK : ℕ)
    (W : Walked ρ o led 0 h.v 0 s s' F G c c' pt tg inc ev lv rows)
    (hn : F.next = jLK + (FoNums.S h).fKey 0) : G.next = jLK + (FoNums.S h).fTab 0 := by
  rw [W.next, hn, keys_slots h, Nat.add_assoc]

/-- Behind the table side the first slot of the sumcheck over the leaves is free. -/
theorem table_next (h : FoNums.Sh) (jLK : ℕ)
    (W : Walked ρ o led 5 h.d 0 s s' F G c c' pt tg inc ev lv rows)
    (hn : F.next = jLK + (FoNums.S h).fTab 0) : G.next = jLK + (FoNums.S h).fEnd := by
  rw [W.next, hn, table_slots h, Nat.add_assoc]

end
end Fo
