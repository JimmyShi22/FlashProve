--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Keep/CEndPoint.lean: THE LOOKUP: EVERY COORDINATE OF THE KEY SIDE's POINT IS A DRAW
OF THE TAPE: at a tape whose every drawn element has a property Q, behind a return of the flat
lkPad: every element of g.zx and of g.zy has Q. And: the key side always has a level. Statements
and proofs.

OBJECT: the flat lkPad (OnBytes/K/Kc/FlatHear.lean): the fields zx, zy and shape of the record g
  that it returns.
USER: Johnson/Top/H/Ret/RetSteerPoint.lean.
LETTERS: calls, pub, lid, F, t, Q free.
  No statement here names Block's, State's or K3's text; its imports' closure holds all
  three.

Main names:
  stored_all: where the order names each variable once, every place of the array of challenges
    behind the rounds holds one of the rounds' challenges.
  level_point: behind a level every coordinate of the point that it hands down has Q.
  fold_point, pad_point, lkPad_point.
  lkPad_level: behind every return g.shape.v is not 0 (the library's bounds on a shape: 10 ≤ dT, and
    v is dT + rK): SO THE PREMISE "the key side has a level" of CEndWorth.lean, CEndTurns.lean,
    CEndSlots.lean and CEndSteer.lean IS PAID BY THE RETURN ITSELF.

Limits. On what the tape draws alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.CEndSteer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc

variable {Q : E → Prop}

/-- Every place holds one of the rounds' challenges. -/
theorem stored_all {α : Type} {P : α → Prop} (mu : ℕ) (order : List ℕ)
    (hp : order.Perm (List.range mu)) (xs : List α) (hx : xs.length = mu) (r0 : Array α)
    (h0 : r0.size = mu) (hP : ∀ x ∈ xs, P x) : ∀ y ∈ (stored mu order xs r0).toList, P y := by
  have hlen : order.length = mu := by rw [hp.length_eq, List.length_range]
  have hn : order.Nodup := hp.symm.nodup List.nodup_range
  have hv : ∀ v ∈ order, v < mu := fun v h => List.mem_range.mp (hp.subset h)
  intro y hy
  rw [stored_toList] at hy
  obtain ⟨i, hi, e⟩ := List.getElem_of_mem hy
  have hi' : i < mu := by
    rw [storedL_length] at hi
    simpa [h0] using hi
  have hm : mu - 1 - i ∈ order := hp.symm.subset (List.mem_range.mpr (by omega))
  have hg := storedL_get mu order xs r0.toList hn hv (by omega) (by simpa using h0) i hi'
  rw [if_pos hm, List.getElem?_eq_getElem hi, e] at hg
  exact hP y (List.mem_of_getElem? hg.symm)

/-- **Behind a level.** -/
theorem level_point (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hp : order.Perm (List.range mu))
    (hc : AllD Q c) : AllD Q c' ∧ ∀ x ∈ s'.rho.toList, Q x := by
  obtain ⟨o, ho, _, e2, _⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', hlen, _, _, hrs, _, _, _, _, hEv, _, _,
    _, _, _, _, _, hr, _, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  obtain ⟨d1, d2, _, _⟩ := evs_d _ _ _ hEv hc
  refine ⟨d1, fun x hx => ?_⟩
  rw [e2] at hx
  have hx' : x = o.tau ∨ x ∈ o.r.toList := by simpa using hx
  rcases hx' with rfl | hx'
  · exact d2 .line o.tau (by simp [levelEv])
  · rw [hr] at hx'
    refine stored_all mu order hp (rs.map (·.2)) (by rw [List.length_map, hrs, hlen]) _
      (by simp) (fun y hy => ?_) x hx'
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
    refine d2 .pscRound q.2 ?_
    unfold levelEv lvEv
    simp only [List.mem_append, List.mem_flatMap]
    exact Or.inr (Or.inl ⟨q, hq, by simp⟩)

/-- **Behind a walk of at least one level.** -/
theorem fold_point {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order ∧ order.Perm (List.range mu)) :
    ∀ (l : List α) (s s' : Forest.Descent) (A B : Fork) (c c' : Tape), l ≠ [] →
      (l.foldlM f s) A c = .ok ((s', B), c') → AllD Q c → ∀ x ∈ s'.rho.toList, Q x
  | [], _, _, _, _, _, _, hne, _, _ => absurd rfl hne
  | x :: l, s, s', A, B, c, c', _, h, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s x l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e, hp⟩ := hf s x
    rw [e] at h1
    obtain ⟨i1, x1⟩ := level_point s s₁ mu order A F₁ c c₁ h1 hp hc
    cases l with
    | nil =>
      have e2 := (foldlM_nil_ok f s₁ F₁ c₁ ((s', B), c')).1 h2
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s₁ ∧ B = F₁) ∧ c' = c₁ := by simpa [Prod.ext_iff] using e2
      exact x1
    | cons y l' => exact fold_point f hf (y :: l') s₁ s' F₁ B c₁ c' (by simp) h2 i1

/-! ## The tie keeps the draws' property -/

theorem tieFold_d (a : E) : ∀ (l : List ℕ) (s s' : Forest.TieStep) (A B : Fork) (c c' : Tape),
    (l.foldlM (lkTieStep a) s) A c = .ok ((s', B), c') → AllD Q c → AllD Q c'
  | [], s, s', A, B, c, c', h, hc => by
    have e := (foldlM_nil_ok (lkTieStep a) s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact hc
  | j :: l, s, s', A, B, c, c', h, hc => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok (lkTieStep a) s j l A c ((s', B), c')).1 h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hE, _⟩ := tieStep_ok a s j A F₁ c c₁ s₁ h1
    exact tieFold_d a l s₁ s' F₁ B c₁ c' h2 (evs_d _ _ _ hE hc).1

theorem tie_d (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie)
    (h : lkTie a F c = .ok ((T, G), c')) (hc : AllD Q c) : AllD Q c' := by
  obtain ⟨s, c1, pt, h1, hE, _⟩ := tie_ok a F G c c' T h
  exact (evs_d _ _ _ hE (tieFold_d a _ _ _ _ _ _ _ h1 hc)).1

theorem mem_extract {α : Type} {a : Array α} {i j : ℕ} {x : α}
    (h : x ∈ (a.extract i j).toList) : x ∈ a.toList := by
  rw [Array.toList_extract] at h
  have h' : x ∈ (a.toList.drop i).take (j - i) := h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h')

theorem pad_point {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M)
    (H : FoNums.ok (M.h pub) = true) (hc : AllD Q c) :
    (∀ x ∈ g.zx.toList, Q x) ∧ ∀ x ∈ g.zy.toList, Q x := by
  obtain ⟨_, hE4, _⟩ := head_cut P
  have hd : 10 ≤ (M.h pub).dT := (Cb.Fo.ok_parts H).1.1
  have hv : (M.h pub).v ≠ 0 := by
    have e : (M.h pub).v = (M.h pub).dT + (M.h pub).rK := rfl
    omega
  have i5 : AllD Q M.c5 := tie_d M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie (evs_d _ _ _ hE4 hc).1
  have hr : ∀ x ∈ M.keys.rho.toList, Q x :=
    fold_point _ (fun s mu => ⟨mu, _, rfl, by
      have := ordK_perm (M.h pub) hd mu
      rwa [Nat.zero_add] at this⟩) _ _ _ _ _ _ _
      (by
        intro e
        exact hv (by simpa using congrArg List.length e)) P.keys i5
  rw [P.heard]
  exact ⟨fun x hx => hr x (mem_extract hx), fun x hx => hr x (mem_extract hx)⟩

/-- **Of the library's flat copy.** -/
theorem lkPad_point (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (ht : AllD Q t) :
    (∀ x ∈ g.zx.toList, Q x) ∧ ∀ x ∈ g.zy.toList, Q x := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  exact pad_point P (Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)) ht

/-- **The key side always has a level.** -/
theorem lkPad_level (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) : g.shape.v ≠ 0 := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  have H : FoNums.ok (M.h pub) = true := Cb.Fo.shape_ok P.shape (_root_.Fo.ask_ok P.ask)
  have hd : 10 ≤ (M.h pub).dT := (Cb.Fo.ok_parts H).1.1
  have e : (M.h pub).v = (M.h pub).dT + (M.h pub).rK := rfl
  rw [pad_shape P]
  omega

end Fo.Tp

#print axioms Fo.Tp.stored_all
#print axioms Fo.Tp.level_point
#print axioms Fo.Tp.lkPad_point
#print axioms Fo.Tp.lkPad_level
