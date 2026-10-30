-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoDescent.lean: the two walks down a product tree in the byte-level
verifier's lookup routine,
read as the flat function's levels.

Forest.pad walks down the key side and then the table side by folding Forest.level over the numbers
of the levels. LevelLaw (OnBytes/Tie/Pv/Lookup/Forest/FoLevel.lean) reads one level. Here the levels
are put together, by
induction on the number of levels from any level l on.

 - descent_from: if the fold over the levels l, .., l + n - 1 returns, then there are calls ev of
   the channel's routines that lead from the context before the run to the one after it (Evs), a row
   of whole rounds (that the run made these very calls is not said); on the rounds of these calls,
   whatever rounds
   follow, the flat function's lvGo takes exactly these n levels and hands the following rounds on;
   the claims pushed are, in the run's order, the flat function's rows of these levels; the point
   with which the walk ends is the flat function's point read backwards; the form with which it ends
   has the flat function's target as its public part, and its value is that target less the flat
   function's form at the mask row; the state is a later one, of the right sizes, with the levels'
   slots taken and filled, and what lies under every other slot as it was.
 - keys_descent, table_descent: the same of the two folds as Forest.pad writes them, at the orders
   FoNums.ordK h and FoNums.ordT.
 - LedsFrom: the premise on the places of the masks: each level's places are those of its own
   scalars, counted from the slot that is free when the level begins. ledsFrom_of: it follows from
   each level's places and the step from a level's first slot to the next level's. leds_key,
   leds_tab: it holds of the flat function's places at a forest.
 - incTop_snoc, tgTop_snoc, pntTop_snoc, lvRowsR_snoc: the flat function's readers of a list of
   levels, the newest first, at a list with one more level at its old end.

Further premises of descent_from: the fold's step is Forest.level at g + i variables and the order
o i; each order is a permutation of its variables; the state fits (Sized); the point at the start,
read, is a point of g + l coordinates reversed; the start form is compared (FormIs). keys_descent
asks 10 ≤ dT and an empty point at the start, table_descent a point of 5 coordinates.
LevelLaw is a hypothesis of descent_from, keys_descent and table_descent; levelLaw
(OnBytes/Tie/Pv/Lookup/Forest/FoLevelLaw.lean) proves it.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoLevel

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.PscRun

/-! ### the flat function's readers, with one more level at the old end -/
section
variable {P K : Type} [CommRing K]

theorem incTop_snoc (led : ℕ → Led P) (inc0 : List (P × K)) (s0 : Sc K × K) :
    ∀ X : List (Sc K × K), incTop led inc0 (X ++ [s0]) =
      incTop (fun i => led (i + 1)) (lineForm (led 0) s0.1 s0.2) X
  | [] => rfl
  | x :: X => by
    show lineForm (led (X ++ [s0]).length) x.1 x.2 = lineForm (led (X.length + 1)) x.1 x.2
    rw [List.length_append]
    rfl

theorem tgTop_snoc (tg0 : K) (s0 : Sc K × K) :
    ∀ X : List (Sc K × K), tgTop tg0 (X ++ [s0]) = tgTop (lineTg s0.1 s0.2) X
  | [] => rfl
  | _ :: _ => rfl

theorem pntTop_snoc (o : ℕ → List ℕ) (p0 : List K) (s0 : Sc K × K) :
    ∀ X : List (Sc K × K), pntTop o p0 (X ++ [s0]) =
      pntTop (fun i => o (i + 1)) (byVar (o 0) s0.1.xs ++ [s0.2]) X
  | [] => rfl
  | x :: X => by
    show byVar (o (X ++ [s0]).length) x.1.xs ++ [x.2] = byVar (o (X.length + 1)) x.1.xs ++ [x.2]
    rw [List.length_append]
    rfl

theorem lvRowsR_snoc (led : ℕ → Led P) (g : ℕ) (inc0 : List (P × K)) (s0 : Sc K × K) :
    ∀ X : List (Sc K × K), lvRowsR led g inc0 (X ++ [s0]) =
      lvRowsR (fun i => led (i + 1)) (g + 1) (lineForm (led 0) s0.1 s0.2) X ++
        [rowU (led 0) (List.replicate g 2 ++ [2]) s0.1 inc0 (s0.1.v 0 * s0.1.v 1)]
  | [] => rfl
  | x :: X => by
    show rowU (led (X ++ [s0]).length) (List.replicate (g + (X ++ [s0]).length) 2 ++ [2]) x.1
        (incTop led inc0 (X ++ [s0])) (x.1.v 0 * x.1.v 1) :: lvRowsR led g inc0 (X ++ [s0]) = _
    rw [lvRowsR_snoc led g inc0 s0 X, incTop_snoc, List.length_append,
      show g + (X.length + [s0].length) = g + 1 + X.length by simp; omega]
    rfl

end

/-! ### the state's side -/

private theorem same_took' {F G : Fork} (h : Same F G) (n : ℕ) : Same (took F n) (took G n) := by
  unfold Same at h ⊢
  rw [h]
  rfl

private theorem took_took' (F : Fork) (a b : ℕ) : took (took F a) b = took F (a + b) := by
  simp only [took, Nat.add_assoc]

/-- The slots of the n levels from level l on, in a tree whose level 0 has g variables. -/
def walkSlots (g : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | n + 1, l => (1 + 2 * (g + l) + 4) + walkSlots g n (l + 1)

/-- Each level's places of masks are those of its own scalars, from the slot that is free when the
level begins. -/
def LedsFrom (led : ℕ → Led Pl) (g : ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, _, _ => True
  | n + 1, l, first => LedAt (led l) first (List.replicate (g + l) 2 ++ [2]) 2 ∧
      LedsFrom led g n (l + 1) (first + (1 + 2 * (g + l) + 4))

/-- From each level's places and the step from a level's first slot to the next level's. -/
theorem ledsFrom_of (led : ℕ → Led Pl) (g N : ℕ) (first : ℕ → ℕ)
    (hAt : ∀ l < N, LedAt (led l) (first l) (List.replicate (g + l) 2 ++ [2]) 2)
    (hStep : ∀ l < N, first (l + 1) = first l + (1 + 2 * (g + l) + 4)) :
    ∀ n l, l + n ≤ N → LedsFrom led g n l (first l)
  | 0, _, _ => trivial
  | n + 1, l, h => ⟨hAt l (by omega), hStep l (by omega) ▸ ledsFrom_of led g N first hAt hStep n
      (l + 1) (by omega)⟩

/-- The premise holds of the key side's places, from the key side's first slot on. -/
theorem leds_key (h : FoNums.Sh) (jLK : ℕ) :
    LedsFrom (fun l => ledF jLK ((FoNums.S h).pKeyC l)) 0 h.v 0 (jLK + (FoNums.S h).fKey 0) :=
  ledsFrom_of _ 0 h.v (fun l => jLK + (FoNums.S h).fKey l)
    (fun l hl => by rw [Nat.zero_add]; exact ledAt_key h jLK l hl)
    (fun l hl => by
      show jLK + (FoNums.S h).fKey (l + 1) = jLK + (FoNums.S h).fKey l + (1 + 2 * (0 + l) + 4)
      rw [Cb.Fo.Walk.first_key h l hl]
      simp only [layerSlots, sumcheckSlots, roundValues]
      omega) h.v 0 (by omega)

/-- The premise holds of the table side's places, from the table side's first slot on. -/
theorem leds_tab (h : FoNums.Sh) (jLK : ℕ) :
    LedsFrom (fun l => ledF jLK ((FoNums.S h).pTabC l)) 5 h.d 0 (jLK + (FoNums.S h).fTab 0) :=
  ledsFrom_of _ 5 h.d (fun l => jLK + (FoNums.S h).fTab l) (fun l hl => ledAt_tab h jLK l hl)
    (fun l hl => by
      show jLK + (FoNums.S h).fTab (l + 1) = jLK + (FoNums.S h).fTab l + (1 + 2 * (5 + l) + 4)
      rw [Cb.Fo.Walk.first_tab h l hl]
      simp only [layerSlots, sumcheckSlots, roundValues]
      omega) h.d 0 (by omega)

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What a walk over the levels l, .., l + n - 1 leaves. -/
structure Walked (o : ℕ → List ℕ) (led : ℕ → Led Pl) (g n l : ℕ) (s s' : Forest.Descent)
    (F G : Fork) (c c' : Ctx) (pt : List K) (tg : K) (inc : List (Pl × K)) (ev : List Ev)
    (lv : List (Sc K × K)) (rows : List Aff) : Prop where
  evs : Evs ev c c'
  rds : Rds ev
  closed : Closed ρ ev
  later : Later F G
  sized : Sized G
  same : Same (took F (walkSlots g n l)) G
  filled : ∀ j, Filled G j ↔ Filled F j ∨ (F.next ≤ j ∧ j < F.next + walkSlots g n l)
  out : ∀ j, (j < F.next ∨ F.next + walkSlots g n l ≤ j) →
    G.vp.getD j zeroE = F.vp.getD j zeroE ∧ G.mf.getD j zeroE = F.mf.getD j zeroE
  flat : ∀ rest, lvGo o n l tg pt (flEv ρ ev ++ rest) =
    (lv, tgTop tg lv.reverse, pntTop (fun i => o (l + i)) pt lv.reverse, rest)
  len : lv.length = n
  pushed : s'.rows.toList = s.rows.toList ++ rows
  rowsAre : List.Forall₂ (RowIs ρ G) rows
    (lvRowsR (fun i => led (l + i)) (g + l) inc lv.reverse).reverse
  rho : rdA ρ s'.rho = (pntTop (fun i => o (l + i)) pt lv.reverse).reverse
  form : FormIs ρ G s'.form (tgTop tg lv.reverse) (incTop (fun i => led (l + i)) inc lv.reverse)

theorem shift_fun {α : Type} (f : ℕ → α) (l : ℕ) :
    (fun i => f (l + (i + 1))) = fun i => f (l + 1 + i) := by
  funext i
  rw [show l + (i + 1) = l + 1 + i by omega]

/-- The walk, from any level on. -/
theorem descent_from (hL : LevelLaw ρ) (o : ℕ → List ℕ) (led : ℕ → Led Pl) (g : ℕ)
    (f : Forest.Descent → ℕ → SubM Forest.Descent)
    (hf : ∀ s i, f s i = Forest.level s (g + i) (o i)) :
    ∀ (n l : ℕ) (s s' : Forest.Descent) (F G : Fork) (c c' : Ctx) (pt : List K) (tg : K)
      (inc : List (Pl × K)),
      ((List.range' l n).foldlM f s) F c = .ok ((s', G), c') →
      (∀ i, l ≤ i → i < l + n → (o i).Perm (List.range (g + i))) →
      Sized F → pt.length = g + l → rdA ρ s.rho = pt.reverse → FormIs ρ F s.form tg inc →
      LedsFrom led g n l F.next →
      ∃ ev lv rows, Walked ρ o led g n l s s' F G c c' pt tg inc ev lv rows
  | 0, l, s, s', F, G, c, c', pt, tg, inc, h, _, hS, _, hr, hF, _ => by
    have e := (foldlM_nil_ok f s F c ((s', G), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ G = F) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨[], [], [],
      { evs := rfl, rds := Rds.nil, closed := Closed.nil ρ, later := Later.refl _,
          sized := hS,
        same := Same.refl _,
        filled := fun j => ⟨Or.inl, fun h => h.elim id fun h => by
          have h2 : j < _ + 0 := h.2
          omega⟩,
        out := fun _ _ => ⟨rfl, rfl⟩, flat := fun _ => rfl, len := rfl, pushed :=
            (List.append_nil _).symm,
        rowsAre := List.Forall₂.nil, rho := hr, form := hF }⟩
  | n + 1, l, s, s', F, G, c, c', pt, tg, inc, h, hp, hS, hl, hr, hF, hLed => by
    rw [List.range'_succ] at h
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s l _ F c ((s', G), c')).1 h
    rw [hf] at h1
    obtain ⟨l₁, sc, τ, row, a1, aR, a2, a3, a4, a5, aF, aO, a6, a7, a8, a9, a10⟩ :=
      hL s s₁ (g + l) (o l) F F₁ c c₁ pt tg inc (led l) h1 (hp l (le_refl _) (by omega)) hS hl hr
        hF hLed.1
    have hn : F₁.next = F.next + (1 + 2 * (g + l) + 4) := a5.next
    have hl' : (byVar (o l) sc.xs ++ [τ]).length = g + (l + 1) := by
      have := (hp l (le_refl _) (by omega)).length_eq
      rw [List.length_range] at this
      simp [byVar, this, Nat.add_assoc]
    obtain ⟨ev, lv, rows, W⟩ := descent_from hL o led g f hf n (l + 1) s₁ s' F₁ G c₁ c'
      (byVar (o l) sc.xs ++ [τ]) (lineTg sc τ) (lineForm (led l) sc τ) h2
      (fun i h1 h2 => hp i (by omega) (by omega)) a4 hl' a9 a10 (hn ▸ hLed.2)
    have eo := shift_fun o l
    have el := shift_fun led l
    refine ⟨l₁ ++ ev, (sc, τ) :: lv, row :: rows,
      { evs := (evs_append _ _ _ _).2 ⟨c₁, a1, W.evs⟩, rds := aR.append W.rds,
        closed := a2.append ρ W.closed,
        later := a3.trans W.later, sized := W.sized, same := ?_,
        filled := fun j => ?_, out := fun j hj => ?_, flat := fun rest => ?_,
        len := by rw [List.length_cons, W.len], pushed := ?_, rowsAre := ?_, rho := ?_,
        form := ?_ }⟩
    · have := (same_took' a5 (walkSlots g n (l + 1))).trans W.same
      rwa [took_took'] at this
    · have e : walkSlots g (n + 1) l = (1 + 2 * (g + l) + 4) + walkSlots g n (l + 1) := rfl
      rw [W.filled j, aF j, hn, e]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr ⟨h.1, by omega⟩
        · exact Or.inr ⟨by omega, by omega⟩
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · by_cases hj : j < F.next + (1 + 2 * (g + l) + 4)
          · exact Or.inl (Or.inr ⟨h.1, hj⟩)
          · exact Or.inr ⟨by omega, by omega⟩
    · have e : walkSlots g (n + 1) l = (1 + 2 * (g + l) + 4) + walkSlots g n (l + 1) := rfl
      rw [e] at hj
      have o2 := W.out j (by rw [hn]; omega)
      have o1 := aO j (by omega)
      exact ⟨o2.1.trans o1.1, o2.2.trans o1.2⟩
    · rw [flEv_app ρ a2, List.append_assoc]
      show (let a := takeSc (flEv ρ l₁ ++ (flEv ρ ev ++ rest)) tg (inRounds (o l) pt ++ [0]) true
        let rho := (a.2.headD ([], [])).2.headD 0
        let b := lvGo o n (l + 1) (lineTg a.1 rho) (byVar (o l) a.1.xs ++ [rho]) a.2.tail
        (((a.1, rho) :: b.1, b.2) : List (Sc K × K) × K × List K × Rounds K)) = _
      rw [a6 (flEv ρ ev ++ rest)]
      show ((sc, τ) :: (lvGo o n (l + 1) (lineTg sc τ) (byVar (o l) sc.xs ++ [τ])
        (flEv ρ ev ++ rest)).1, (lvGo o n (l + 1) (lineTg sc τ) (byVar (o l) sc.xs ++ [τ])
        (flEv ρ ev ++ rest)).2) = _
      rw [W.flat rest, List.reverse_cons, tgTop_snoc, pntTop_snoc, eo]
      rfl
    · rw [W.pushed, a7, Array.toList_push, List.append_assoc]
      rfl
    · rw [List.reverse_cons, lvRowsR_snoc, List.reverse_append, el]
      exact List.Forall₂.cons (a8.later ρ W.later) W.rowsAre
    · rw [W.rho, List.reverse_cons, pntTop_snoc, eo]
      rfl
    · rw [List.reverse_cons, tgTop_snoc, incTop_snoc, el]
      exact W.form


/-- The orders of the key levels name each variable once. -/
theorem ordK_perm (h : FoNums.Sh) (hd : 10 ≤ h.dT) (i : ℕ) :
    (FoNums.ordK h i).Perm (List.range (0 + i)) := by
  rw [Nat.zero_add]
  unfold FoNums.ordK
  by_cases e : i + 1 = h.v
  · rw [if_pos e]
    have hv : h.v = h.dT + h.rK := rfl
    exact E3.lastList_perm (by omega)
  · rw [if_neg e]
    exact E3.defaultList_perm i

/-- The key side, as Forest.pad writes it. -/
theorem keys_descent (hL : LevelLaw ρ) (h : FoNums.Sh) (hd : 10 ≤ h.dT) (led : ℕ → Led Pl)
    (s s' : Forest.Descent) (F G : Fork) (c c' : Ctx) (tg : K) (inc : List (Pl × K))
    (hrun : ((List.range h.v).foldlM
      (fun (s : Forest.Descent) mu =>
        Forest.level s mu
          (if mu + 1 = h.v then Forest.orderForestRange mu h.rK else orderDefault mu)) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hr : s.rho = #[]) (hF : FormIs ρ F s.form tg inc)
    (hLed : LedsFrom led 0 h.v 0 F.next) :
    ∃ ev lv rows, Walked ρ (FoNums.ordK h) led 0 h.v 0 s s' F G c c' [] tg inc ev lv rows := by
  rw [List.range_eq_range'] at hrun
  exact descent_from ρ hL (FoNums.ordK h) led 0 _ (fun s i => by rw [Nat.zero_add]; rfl) h.v 0 s s'
    F G c c' [] tg inc hrun (fun i _ _ => ordK_perm h hd i) hS rfl (by rw [hr]; rfl) hF hLed

/-- The table side, as Forest.pad writes it. pt: the point that joins the planes' roots, by
coordinate. -/
theorem table_descent (hL : LevelLaw ρ) (h : FoNums.Sh) (led : ℕ → Led Pl)
    (s s' : Forest.Descent) (F G : Fork) (c c' : Ctx) (pt : List K) (tg : K)
    (inc : List (Pl × K))
    (hrun : ((List.range h.d).foldlM
      (fun (s : Forest.Descent) l => Forest.level s (5 + l) (orderDefault (5 + l))) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hl : pt.length = 5) (hr : rdA ρ s.rho = pt.reverse)
    (hF : FormIs ρ F s.form tg inc) (hLed : LedsFrom led 5 h.d 0 F.next) :
    ∃ ev lv rows, Walked ρ FoNums.ordT led 5 h.d 0 s s' F G c c' pt tg inc ev lv rows := by
  rw [List.range_eq_range'] at hrun
  exact descent_from ρ hL FoNums.ordT led 5 _ (fun _ _ => rfl) h.d 0 s s' F G c c' pt tg inc hrun
    (fun i _ _ => E3.defaultList_perm (5 + i)) hS hl hr hF hLed

end
end Fo
