-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/FlPort/FoDescent.lean: a carried copy, made by a program, not typed by hand.

Of which file: OnBytes/Tie/Pv/Lookup/Forest/FoDescent.lean, as it lies in this library.
What is carried: those of its declarations that depend on a context of the verifier program's
channel, and no other:
  Walked, descent_from, keys_descent, table_descent
and, because the library keeps them private to that file, copies of:
  same_took', took_took'
How: by one swap of names throughout: a context becomes a tape; a routine
of the program becomes the library's flat function of the same text (OnBytes/K/Kc/Flat.lean,
OnBytes/K/Kc/FlatHear.lean). The laws on "returns" are those of Johnson/Top/H/FlPort/Kit.lean. Every
other name is the library's own: plain records, pure functions and lemmas on them, used from where
they lie. Those of OnBytes/Tie/Pv/ that the text names, as far as a program sees them:
  Closed, Closed.nil, Filled, FormIs, Later, Later.refl, LedsFrom, RowIs, Same, Same.refl, Sized,
  flEv, flEv_app, incTop_snoc, lvRowsR_snoc, ordK, ordK_perm, ordT, pntTop_snoc, shift_fun,
  tgTop_snoc, took, walkSlots
The comments on the declarations are the library's, under the same swap: where they say "run" or
"view", read: on a tape.

Limits. What is proved here is proved of the flat functions alone, and a flat function tests less of
the plan than the program's routine (the paragraph "Not claimed" in the head of
OnBytes/K/Kc/Flat.lean). Nothing is said where a function refuses. A tie: it has no error term. If
the source file turns, this copy does not follow by itself. In the list of names a use by dot
notation on a hypothesis is not seen, and a short name may stand once too often. That no routine
in a context is reached from a statement or a proof here is meant, and is not shown in this
library.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoDescent
import Johnson.Top.H.FlPort.Kit
import Johnson.Top.H.FlPort.PscWhole
import Johnson.Top.H.FlPort.PscRun
import Johnson.Top.H.FlPort.FoLevel
import Johnson.Top.H.FlPort.FoRds
import Johnson.Top.H.FlPort.FoHeard
import Johnson.Top.H.FlPort.FoLevelRun

set_option autoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV OnBytes OnBytes.Model OnBytes.PscRun

section
variable {P K : Type} [CommRing K]

end

private theorem same_took' {F G : Fork} (h : Same F G) (n : ℕ) : Same (took F n) (took G n) := by
  unfold Same at h ⊢
  rw [h]
  rfl

private theorem took_took' (F : Fork) (a b : ℕ) : took (took F a) b = took F (a + b) := by
  simp only [took, Nat.add_assoc]

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What a walk over the levels l, .., l + n - 1 leaves. -/
structure Walked (o : ℕ → List ℕ) (led : ℕ → Led Pl) (g n l : ℕ) (s s' : Forest.Descent)
    (F G : Fork) (c c' : Tape) (pt : List K) (tg : K) (inc : List (Pl × K)) (ev : List Ev)
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

/-- The walk, from any level on. -/
theorem descent_from (hL : LevelLaw ρ) (o : ℕ → List ℕ) (led : ℕ → Led Pl) (g : ℕ)
    (f : Forest.Descent → ℕ → Fl Forest.Descent)
    (hf : ∀ s i, f s i = lkLevel s (g + i) (o i)) :
    ∀ (n l : ℕ) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape) (pt : List K) (tg : K)
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

/-- The key side, as lkPad writes it. -/
theorem keys_descent (hL : LevelLaw ρ) (h : FoNums.Sh) (hd : 10 ≤ h.dT) (led : ℕ → Led Pl)
    (s s' : Forest.Descent) (F G : Fork) (c c' : Tape) (tg : K) (inc : List (Pl × K))
    (hrun : ((List.range h.v).foldlM
      (fun (s : Forest.Descent) mu =>
        lkLevel s mu
          (if mu + 1 = h.v then Forest.orderForestRange mu h.rK else orderDefault mu)) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hr : s.rho = #[]) (hF : FormIs ρ F s.form tg inc)
    (hLed : LedsFrom led 0 h.v 0 F.next) :
    ∃ ev lv rows, Walked ρ (FoNums.ordK h) led 0 h.v 0 s s' F G c c' [] tg inc ev lv rows := by
  rw [List.range_eq_range'] at hrun
  exact descent_from ρ hL (FoNums.ordK h) led 0 _ (fun s i => by rw [Nat.zero_add]; rfl) h.v 0 s s'
    F G c c' [] tg inc hrun (fun i _ _ => ordK_perm h hd i) hS rfl (by rw [hr]; rfl) hF hLed

/-- The table side, as lkPad writes it. pt: the point that joins the planes' roots, by
coordinate. -/
theorem table_descent (hL : LevelLaw ρ) (h : FoNums.Sh) (led : ℕ → Led Pl)
    (s s' : Forest.Descent) (F G : Fork) (c c' : Tape) (pt : List K) (tg : K)
    (inc : List (Pl × K))
    (hrun : ((List.range h.d).foldlM
      (fun (s : Forest.Descent) l => lkLevel s (5 + l) (orderDefault (5 + l))) s) F c =
        .ok ((s', G), c'))
    (hS : Sized F) (hl : pt.length = 5) (hr : rdA ρ s.rho = pt.reverse)
    (hF : FormIs ρ F s.form tg inc) (hLed : LedsFrom led 5 h.d 0 F.next) :
    ∃ ev lv rows, Walked ρ FoNums.ordT led 5 h.d 0 s s' F G c c' pt tg inc ev lv rows := by
  rw [List.range_eq_range'] at hrun
  exact descent_from ρ hL FoNums.ordT led 5 _ (fun _ _ => rfl) h.d 0 s s' F G c c' pt tg inc hrun
    (fun i _ _ => E3.defaultList_perm (5 + i)) hS hl hr hF hLed

end

end Fo.Tp
