-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/PadSizes.lean: The kind "lookup" (K3): A LOOKUP's HEARING TURNS NO ARRAY's
LENGTH: the ledger that it leaves has the number of slots of the ledger in front, and its three
arrays have the lengths that they had: WITHOUT ANY PREMISE ON THE LEDGER IN FRONT. So: if the
ledger behind has its sizes, the ledger in front had them. At the library's flat copy of the
routine, and at an accept of K3.block's decide at any seat. Statements and proofs, along the chain
of Johnson/Top/H/Keep/PadNamed.lean.

OBJECT: Fork.hide, Fork.hideRun; lkPad; K3.block's decide.
Used by Johnson/Desc/First/Link/Law/SizesDigits.lean and Johnson/Desc/First/Link/Law/K4AtFront.lean.
LETTERS: all free.
Compiled with the whole library.

Why. Fork.hide writes by set! alone; taking slots moves "next"; entering an owed claim lengthens
"owed".

Main names:
  Len F G: G.ns = F.ns, and the three arrays' lengths are the same. Len.refl, Len.trans,
  Len.sizedBack.
  hide_len, hideSteps_len, hideRun_len. tieStep_len, tieFold_len, tie_lens, level_len, fold_len,
  pad_lens, lkPad_len.
  decide_sameLen: THE END. decide_sizedBack: its corollary.

Limits. None on the ledger. Nothing is said of what the arrays hold.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc

/-- The number of slots and the three arrays' lengths are the same. -/
def Len (F G : Fork) : Prop :=
  G.ns = F.ns ∧ G.vp.size = F.vp.size ∧ G.mf.size = F.mf.size ∧ G.gotF.size = F.gotF.size

theorem Len.refl (F : Fork) : Len F F := ⟨rfl, rfl, rfl, rfl⟩

theorem Len.trans {F G H : Fork} (a : Len F G) (b : Len G H) : Len F H :=
  ⟨b.1.trans a.1, b.2.1.trans a.2.1, b.2.2.1.trans a.2.2.1, b.2.2.2.trans a.2.2.2⟩

/-- **Sizes behind give sizes in front.** -/
theorem Len.sizedBack {F G : Fork} (a : Len F G) (h : Sized G) : Sized F :=
  ⟨by rw [← a.2.1, ← a.1]; exact h.1, by rw [← a.2.2.1, ← a.1]; exact h.2.1,
    by rw [← a.2.2.2, ← a.1]; exact h.2.2⟩

theorem took_len (F : Fork) (n : ℕ) : Len F (took F n) := ⟨rfl, rfl, rfl, rfl⟩

theorem owed3_len (F : Fork) : Len F (owed3 F) := ⟨rfl, rfl, rfl, rfl⟩

/-- One value put under a slot. -/
theorem hide_len {F G : Fork} {j : ℕ} {y factor : E} (h : F.hide j y factor = some G) :
    Len F G := by
  unfold Fork.hide at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, by simp, by simp, by simp⟩
  · simp at h

/-- The steps of a run of values. -/
theorem hideSteps_len (factor : E) : ∀ (l : List E) (first : ℕ) (F : Fork) (x : ℕ × Fork),
    l.foldlM (Fork.hideStep factor) (first, F) = some x → Len F x.2
  | [], first, A, x, h => by
    have hx : (first, A) = x := by simpa using h
    subst hx
    exact Len.refl A
  | y :: l, first, A, x, h => by
    rw [List.foldlM_cons] at h
    cases hq : Fork.hideStep factor (first, A) y with
    | none => simp [hq] at h
    | some s =>
      rw [hq] at h
      have h2 : l.foldlM (Fork.hideStep factor) s = some x := by simpa using h
      simp only [Fork.hideStep] at hq
      cases hh : A.hide first y factor with
      | none => simp [hh] at hq
      | some H =>
        rw [hh] at hq
        obtain rfl : (first + 1, H) = s := by simpa using hq
        exact (hide_len hh).trans (hideSteps_len factor l _ _ _ h2)

/-- A run of values put under slots. -/
theorem hideRun_len {F G : Fork} {first : ℕ} {v : Array E} {factor : E}
    (h : F.hideRun first v factor = some G) : Len F G := by
  unfold Fork.hideRun at h
  split at h
  · rename_i x hx
    obtain rfl := Option.some.inj h
    rw [← Array.foldlM_toList] at hx
    exact hideSteps_len factor _ _ _ _ hx
  · simp at h

/-! ## The tie -/

theorem tieStep_len (a : E) (s s' : Forest.TieStep) (j : ℕ) (F G : Fork) (c c' : Tape)
    (h : lkTieStep a s j F c = .ok ((s', G), c')) : Len F G := by
  obtain ⟨target, mu, eps, sent, beta, v, G1, vP, vG, summand, _, _, _, hv, hG1, _, _, _, hG,
    rfl⟩ := tieStep_ok a s j F G c c' s' h
  exact (((took_len F 1).trans (took_len _ _)).trans (hideRun_len hG1)).trans (hideRun_len hG)

theorem tieFold_len (a : E) : ∀ (n k : ℕ) (s s' : Forest.TieStep) (F G : Fork) (c c' : Tape),
    ((List.range' k n).foldlM (lkTieStep a) s) F c = .ok ((s', G), c') → Len F G
  | 0, k, s, s', A, B, c, c', h => by
    have e := (foldlM_nil_ok (lkTieStep a) s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact Len.refl _
  | n + 1, k, s, s', A, B, c, c', h => by
    rw [List.range'_succ] at h
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok (lkTieStep a) s k _ A c ((s', B), c')).1 h
    exact (tieStep_len a s s₁ k A F₁ c c₁ h1).trans
      (tieFold_len a n (k + 1) s₁ s' F₁ B c₁ c' h2)

theorem tie_lens (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie)
    (h : lkTie a F c = .ok ((T, G), c')) : Len F G := by
  obtain ⟨s, c1, pt, h1, _, rfl⟩ := tie_ok a F G c c' T h
  rw [List.range_eq_range'] at h1
  exact tieFold_len a 31 0 {} s F G c c1 h1

/-! ## A level; a walk of levels -/

theorem level_len (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) : Len F G := by
  obtain ⟨o, ho, e1, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, hst, _, _, _, _, hv2, _, hR, _,
    hsR, hH3, _, _, hHG, _, hrow, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  exact ((took_len F _).trans (hideRun_len hH3)).trans (hideRun_len hHG)

theorem fold_len {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape),
      (l.foldlM f s) F c = .ok ((s', G), c') → Len F G
  | [], s, s', A, B, c, c', h => by
    have e := (foldlM_nil_ok f s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact Len.refl _
  | a :: l, s, s', A, B, c, c', h => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s a
    rw [e] at h1
    exact (level_len s s₁ mu order A F₁ c c₁ h1).trans (fold_len f hf l s₁ s' F₁ B c₁ c' h2)

/-! ## The whole hearing -/

/-- From the chain of the runs of the routines that lkPad calls. -/
theorem pad_lens {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) : Len F F' := by
  have h4 : M.F4 = owed3 F := (head_cut P).1
  have l4 : Len F M.F4 := h4 ▸ owed3_len F
  have l5 : Len M.F4 M.F5 := tie_lens M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie
  have l6 : Len M.F5 M.F6 := fold_len _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.keys
  have l7 : Len M.F6 M.F7 := fold_len _ (fun s l => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.table
  obtain ⟨tgL, muL, epsL, _, _, g1, hlv0⟩ := pscBegin_ok _ _ _ _ _ _ P.l1
  obtain ⟨_, _, _, _, g2, _, hst, _, _, _, _⟩ :=
    ran_roundsIn eqForm_eq (hlv0 ▸ ran_begin M.table.form tgL muL epsL M.F7.next) _ _ _ _ _ _ _ P.l2
  obtain ⟨_, g3⟩ := (point_ok _ _ _ _ _ _ _).1 P.l3
  obtain ⟨tgB, muB, epsB, _, _, g4, hb0⟩ := pscBegin_ok _ _ _ _ _ _ P.l4
  obtain ⟨_, _, _, _, g5, _, hsB1, _, _, _, hR1⟩ :=
    ran_roundsIn eqForm_eq2 (hb0 ▸ ran_begin (Aff.ofConst zeroE) tgB muB epsB M.G3.next) _ _ _ _ _
      _ _ P.l5
  obtain ⟨sentY, beta, v, _, hv, _, hsb, hH6, _, hsB2, _, _, _, hR2⟩ :=
    ran_ends hR1 _ _ _ _ _ _ _ _ P.l6
  obtain ⟨_, _, e7⟩ := (shown_ok _ _ _ _).1 P.l7
  have g7 : M.G7 = M.G6 := congrArg (fun x : (E × Fork) × Tape => x.1.2) e7
  obtain ⟨-, -, -, -, -, hH8, hrow, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ P.l8
  have lG5 : Len M.F7 M.G5 := by
    rw [g5, g4, g3, g2, g1]
    exact (((took_len _ _).trans (took_len _ _)).trans (took_len _ _)).trans (took_len _ _)
  rw [g7] at hH8
  rw [P.fork]
  exact (((l4.trans l5).trans l6).trans l7).trans
    (((lG5.trans (took_len _ _)).trans (hideRun_len hH6)).trans (hideRun_len hH8))

/-- **Of the library's flat copy.** -/
theorem lkPad_len (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) : Len F F' := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  exact pad_lens P

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide: the hearing turns no array's length.** -/
theorem decide_sameLen {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ s' = seat.put s x.1 x.2 ∧
      x.2.ns = F.ns ∧ x.2.vp.size = F.vp.size ∧ x.2.mf.size = F.mf.size ∧
      x.2.gotF.size = F.gotF.size := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, rfl, ?_⟩
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := messagesCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      exact _root_.Fo.Tp.lkPad_len p.calls p.pub p.lid F x.2 t [] x.1 hl
    · exact absurd hx (by simp)

/-- **So: sizes behind give sizes in front.** -/
theorem decide_sizedBack {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ s' = seat.put s x.1 x.2 ∧
      (Sized x.2 → Sized F) := by
  obtain ⟨F, x, hF, e, L⟩ := decide_sameLen seat piece laid before p guests s s' rs cols hd
  exact ⟨F, x, hF, e, _root_.Fo.Tp.Len.sizedBack L⟩

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.Len.refl
#print axioms Fo.Tp.Len.trans
#print axioms Fo.Tp.Len.sizedBack
#print axioms Fo.Tp.took_len
#print axioms Fo.Tp.owed3_len
#print axioms Fo.Tp.hide_len
#print axioms Fo.Tp.hideSteps_len
#print axioms Fo.Tp.hideRun_len
#print axioms Fo.Tp.tieStep_len
#print axioms Fo.Tp.tieFold_len
#print axioms Fo.Tp.tie_lens
#print axioms Fo.Tp.level_len
#print axioms Fo.Tp.fold_len
#print axioms Fo.Tp.pad_lens
#print axioms Fo.Tp.lkPad_len
#print axioms VerifiableInference.OnPublicFiles.decide_sameLen
#print axioms VerifiableInference.OnPublicFiles.decide_sizedBack
