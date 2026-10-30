-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/PadNamed.lean: THE LOOKUP: WHAT THE FORMS THAT A HEARING KEEPS NAME: no entry of
a virtual row, and slots alone that are there and FILLED in the ledger behind the hearing. Of the
library's flat copy lkPad (OnBytes/K/Kc/), wherever it returns from a ledger that has its sizes.
Definitions, statements and proofs.

Why. The library's record HeardIs says what these forms are WORTH at every later ledger. A test on a
form's text ("each slot that it names is filled or will be filled by this run; each entry is there")
wants the text. For the routine in a context the library has the first half
(OnBytes/Tie/Pv/Led/LedRowsLook.lean: gives_pad); its rules on forms are spent here as they lie.

Main names:
  In F j: slot j is below F's number of slots and filled in F.
  Named F f: f names no entry (the library's Bare) and every slot that it names is In F (the
    library's FilledA: Named.filledA). NamedAll F rows: every member.
  hide_new: what a run of values under slots leaves: a later ledger, its sizes, these slots filled.
  named_rowForm: the claim that a sumcheck leaves, where its own slots are filled.
  tieStep_named, tie_named: the tie. level_named, fold_named: a level; a walk of levels.
  PadNames g F': what a hearing keeps: every row, the key side's end form, the form of the slot of
    the bits' shown value and the leaves' start form are Named at F'.
  pad_named (from the chain of runs), lkPad_named.
  bare_ents: a form that is Bare has no entry at all.

Limits. From a return alone. The leaves' ROW is not among these: the run "planes" makes it, and
fills its slots. Nothing on the forms that a calling kind hands in.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Road.K4.Slots.SlotsIn
import Johnson.Top.H.Keep.PadExact
import OnBytes.Tie.Pv.Led.LedRowsLook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc
open OnBytes.Road.Rows (Bare bare_ofConst bare_slot bare_addMul bare_add bare_scale bare_rowForm
  bare_foldl)
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_ofConst slotsIn_slot slotsIn_empty
  slotsIn_addMul slotsIn_scale slotsIn_add slotsIn_foldl_mem slotsIn_rowForm)

/-- Slot j is below the ledger's number of slots, and filled. -/
def In (F : Fork) (j : ℕ) : Prop := j < F.ns ∧ Filled F j

theorem In.later {F G : Fork} {j : ℕ} (h : In F j) (hL : Later F G) : In G j :=
  ⟨by rw [hL.ns]; exact h.1, (hL.keep j h.2).1⟩

/-- The form names no entry, and slots alone that are there and filled. -/
def Named (F : Fork) (f : Aff) : Prop := Bare f ∧ SlotsIn (In F) f

/-- The second half is the library's FilledA. -/
theorem Named.filledA {F : Fork} {f : Aff} (h : Named F f) : FilledA F f := h.2

def NamedAll (F : Fork) (rows : Array Aff) : Prop := ∀ f ∈ rows.toList, Named F f

theorem Named.later {F G : Fork} {f : Aff} (h : Named F f) (hL : Later F G) : Named G f :=
  ⟨h.1, slotsIn_mono (fun _ hj => In.later hj hL) h.2⟩

theorem NamedAll.later {F G : Fork} {rows : Array Aff} (h : NamedAll F rows) (hL : Later F G) :
    NamedAll G rows := fun f hf => (h f hf).later hL

theorem namedAll_empty (F : Fork) : NamedAll F #[] := fun f hf => by simp at hf

theorem namedAll_push {F : Fork} {rows : Array Aff} {f : Aff} (h : NamedAll F rows)
    (hf : Named F f) : NamedAll F (rows.push f) := fun x hx => by
  rw [Array.toList_push, List.mem_append] at hx
  rcases hx with hx | hx
  · exact h x hx
  · rw [List.mem_singleton.1 hx]
    exact hf

theorem named_ofConst (F : Fork) (v : E) : Named F (Aff.ofConst v) :=
  ⟨bare_ofConst v, slotsIn_ofConst v⟩

theorem named_slot {F : Fork} {j : ℕ} (h : j < F.ns ∧ Filled F j) : Named F (Aff.slot j) :=
  ⟨bare_slot j, slotsIn_slot (S := In F) h⟩

theorem named_addMul {F : Fork} {a b : Aff} (k : E) (ha : Named F a) (hb : Named F b) :
    Named F (Aff.addMul a b k) := ⟨bare_addMul k ha.1 hb.1, slotsIn_addMul k ha.2 hb.2⟩

theorem named_add {F : Fork} {a b : Aff} (ha : Named F a) (hb : Named F b) : Named F (a + b) :=
  ⟨bare_add ha.1 hb.1, slotsIn_add ha.2 hb.2⟩

theorem named_scale {F : Fork} {a : Aff} (k : E) (ha : Named F a) : Named F (Aff.scale a k) :=
  ⟨bare_scale k ha.1, slotsIn_scale k ha.2⟩

/-- The claim that a sumcheck leaves, where its own slots are filled. -/
theorem named_rowForm {G : Fork} (p : Psc) (S0 : E) (hs : Named G p.start)
    (hw : ∀ i, i < p.walk.1.length → p.first + i < G.ns ∧ Filled G (p.first + i)) :
    Named G (p.rowForm S0 {}) :=
  ⟨bare_rowForm p S0 hs.1, slotsIn_rowForm p S0 hw hs.2 slotsIn_empty⟩

/-- A form that is Bare has no entry at all. -/
theorem bare_ents {f : Aff} (h : Bare f) : f.ents = #[] := by
  have h0 : f.ents.toList = [] :=
    List.eq_nil_iff_forall_not_mem.2 fun y hy => h (fun _ _ => False) y hy
  exact Array.toList_eq_nil_iff.1 h0

/-- What a run of values under slots leaves. -/
theorem hide_new {F G : Fork} {first : ℕ} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) :
    Later F G ∧ Sized G ∧ ∀ i, i < v.size → first + i < G.ns ∧ Filled G (first + i) := by
  obtain ⟨hS, hG, hnew, _⟩ := hideRun_ok F G first v f hF h
  exact ⟨hideRun_later hF h, hG, fun i hi => ⟨by rw [hS.ns]; exact (hnew i hi).1,
    (hnew i hi).2.2.1⟩⟩

/-! ## The tie -/

/-- What rides along the tie's steps. n: how many steps have run. -/
structure TieOk (F : Fork) (s : Forest.TieStep) (n : ℕ) : Prop where
  rows : NamedAll F s.rows
  sP : 0 < n → s.sP < F.ns ∧ Filled F s.sP
  sZ : 0 < n → s.sZ < F.ns ∧ Filled F s.sZ
  sG : ∀ j ∈ s.sG.toList, j < F.ns ∧ Filled F j
  size : s.sG.size = n

theorem tieStep_named (a : E) (s s' : Forest.TieStep) (j : ℕ) (F G : Fork) (c c' : Tape)
    (h : lkTieStep a s j F c = .ok ((s', G), c')) (hF : Sized F) (hs : TieOk F s j) :
    Later F G ∧ Sized G ∧ TieOk G s' (j + 1) := by
  obtain ⟨target, mu, eps, sent, beta, v, G1, vP, vG, summand, _, _, _, hv, hG1, _, _, _, hG,
    rfl⟩ := tieStep_ok a s j F G c c' s' h
  have hT : Sized (took (took F 1) (3 + if j = 0 then 3 else 2)) :=
    took_sized _ (took_sized _ hF)
  obtain ⟨l1, s1, n1⟩ := hide_new hT hG1
  obtain ⟨l2, s2, n2⟩ := hide_new s1 hG
  have L1 : Later F G1 := ((took_later F 1).trans (took_later _ _)).trans l1
  have L : Later F G := L1.trans l2
  have at1 : ∀ i, i < v.size → F.next + 1 + 3 + i < G.ns ∧ Filled G (F.next + 1 + 3 + i) :=
    fun i hi => ⟨by rw [l2.ns]; exact (n1 i hi).1, (l2.keep _ (n1 i hi).2).1⟩
  have hstart : Named G (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP) := by
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact named_ofConst G _
    · rw [if_neg hj]
      exact (named_slot (hs.sP (Nat.pos_of_ne_zero hj))).later L
  refine ⟨L, s2, ⟨namedAll_push (hs.rows.later L) (named_rowForm _ _ hstart fun i hi => ?_),
    fun _ => ?_, fun _ => ?_, fun x hx => ?_, by rw [Array.size_push, hs.size]⟩⟩
  · exact n2 i (by simpa using hi)
  · by_cases hj : j = 0
    · simp only [if_pos hj] at hv ⊢
      exact at1 1 (by omega)
    · simp only [if_neg hj] at hv ⊢
      exact at1 0 (by omega)
  · by_cases hj : j = 0
    · simp only [if_pos hj] at hv ⊢
      exact at1 0 (by omega)
    · simp only [if_neg hj]
      have := hs.sZ (Nat.pos_of_ne_zero hj)
      exact ⟨by rw [L.ns]; exact this.1, (L.keep _ this.2).1⟩
  · rw [Array.toList_push, List.mem_append] at hx
    rcases hx with hx | hx
    · have := hs.sG x hx
      exact ⟨by rw [L.ns]; exact this.1, (L.keep _ this.2).1⟩
    · rw [List.mem_singleton.1 hx]
      by_cases hj : j = 0
      · simp only [if_pos hj] at hv ⊢
        exact at1 2 (by omega)
      · simp only [if_neg hj] at hv ⊢
        exact at1 1 (by omega)

theorem tieFold_named (a : E) : ∀ (n k : ℕ) (s s' : Forest.TieStep) (F G : Fork) (c c' : Tape),
    ((List.range' k n).foldlM (lkTieStep a) s) F c = .ok ((s', G), c') → Sized F → TieOk F s k →
    Later F G ∧ Sized G ∧ TieOk G s' (k + n)
  | 0, k, s, s', A, B, c, c', h, hF, hs => by
    have e := (foldlM_nil_ok (lkTieStep a) s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨Later.refl _, hF, hs⟩
  | n + 1, k, s, s', A, B, c, c', h, hF, hs => by
    rw [List.range'_succ] at h
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok (lkTieStep a) s k _ A c ((s', B), c')).1 h
    obtain ⟨l1, z1, t1⟩ := tieStep_named a s s₁ k A F₁ c c₁ h1 hF hs
    obtain ⟨l2, z2, t2⟩ := tieFold_named a n (k + 1) s₁ s' F₁ B c₁ c' h2 z1 t1
    exact ⟨l1.trans l2, z2, by rw [show k + (n + 1) = k + 1 + n by omega]; exact t2⟩

/-- **The tie.** -/
theorem tie_named (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie)
    (h : lkTie a F c = .ok ((T, G), c')) (hF : Sized F) :
    Later F G ∧ Sized G ∧ NamedAll G T.rows ∧ Named G (Aff.slot T.sZ) ∧ Named G T.cT := by
  obtain ⟨s, c1, pt, h1, _, rfl⟩ := tie_ok a F G c c' T h
  rw [List.range_eq_range'] at h1
  obtain ⟨L, z, t⟩ := tieFold_named a 31 0 {} s F G c c1 h1 hF
    ⟨namedAll_empty F, fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun j hj => by simp at hj, rfl⟩
  have hall : ∀ j ∈ (s.sG.push s.sP).toList, j < G.ns ∧ Filled G j := fun j hj => by
    rw [Array.toList_push, List.mem_append] at hj
    rcases hj with hj | hj
    · exact t.sG j hj
    · rw [List.mem_singleton.1 hj]
      exact t.sP (by omega)
  have hsz : (s.sG.push s.sP).size = 32 := by rw [Array.size_push, t.size]
  have hget : ∀ j, j < 32 → (s.sG.push s.sP).getD j 0 < G.ns ∧
      Filled G ((s.sG.push s.sP).getD j 0) := fun j hj => by
    have hj' : j < (s.sG.push s.sP).size := by rw [hsz]; exact hj
    have e : (s.sG.push s.sP).getD j 0 = (s.sG.push s.sP)[j] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj']
      rfl
    rw [e]
    exact hall _ (Array.mem_def.1 (Array.getElem_mem hj'))
  refine ⟨L, z, t.rows, named_slot (t.sZ (by omega)), ?_, ?_⟩
  · exact bare_foldl _ (fun f j hf => bare_addMul _ hf (bare_slot _)) _ _ (bare_ofConst _)
  · show SlotsIn (In G) (tieCT (s.sG.push s.sP) (eqTab pt.reverse))
    unfold tieCT
    exact slotsIn_foldl_mem (S := In G) _ (List.range 32)
      (fun f j hj hf => slotsIn_addMul _ hf (slotsIn_slot (hget j (List.mem_range.1 hj))))
      (Aff.ofConst zeroE) (slotsIn_ofConst _)

/-! ## A level; a walk of levels -/

theorem level_named (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork) (c c' : Tape)
    (h : lkLevel s mu order F c = .ok ((s', G), c')) (hF : Sized F) (hr : NamedAll F s.rows)
    (hf : Named F s.form) : Later F G ∧ Sized G ∧ NamedAll G s'.rows ∧ Named G s'.form := by
  obtain ⟨o, ho, e1, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, hst, _, _, _, _, hv2, _, hR, _,
    hsR, hH3, _, _, hHG, _, hrow, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  obtain ⟨l3, s3, n3⟩ := hide_new (took_sized _ hF) hH3
  obtain ⟨lG, sG, nG⟩ := hide_new s3 hHG
  have L : Later F G := ((took_later F _).trans l3).trans lG
  have atL : ∀ i, i < 2 → o.sL + i < G.ns ∧ Filled G (o.sL + i) := fun i hi => by
    have := n3 i (by rw [hv2]; exact hi)
    exact ⟨by rw [lG.ns]; exact this.1, (lG.keep _ this.2).1⟩
  refine ⟨L, sG, ?_, ?_⟩
  · rw [e1, hrow]
    refine namedAll_push (hr.later L) (named_rowForm p _ (by rw [hst]; exact hf.later L)
      fun i hi => ?_)
    rw [hR.first_eq]
    exact nG i (by simpa using hi)
  · rw [e3, hsR]
    exact named_add (named_scale _ (named_slot (atL 0 (by omega))))
      (named_scale _ (named_slot (atL 1 (by omega))))

theorem fold_named {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape),
      (l.foldlM f s) F c = .ok ((s', G), c') → Sized F → NamedAll F s.rows → Named F s.form →
      Later F G ∧ Sized G ∧ NamedAll G s'.rows ∧ Named G s'.form
  | [], s, s', A, B, c, c', h, hF, hr, hm => by
    have e := (foldlM_nil_ok f s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨Later.refl _, hF, hr, hm⟩
  | a :: l, s, s', A, B, c, c', h, hF, hr, hm => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s a
    rw [e] at h1
    obtain ⟨l1, z1, r1, m1⟩ := level_named s s₁ mu order A F₁ c c₁ h1 hF hr hm
    obtain ⟨l2, z2, r2, m2⟩ := fold_named f hf l s₁ s' F₁ B c₁ c' h2 z1 r1 m1
    exact ⟨l1.trans l2, z2, r2, m2⟩

/-! ## The whole hearing -/

/-- **What the forms that a hearing keeps name.** -/
structure PadNames (g : Forest.Heard) (F' : Fork) : Prop where
  rows : NamedAll F' g.rows
  cEnd : Named F' g.cEnd
  sBit : Named F' (Aff.slot g.sBit)
  start : Named F' g.leaves.start

/-- From the chain of the runs of the routines that lkPad calls. -/
theorem pad_named {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F) :
    PadNames g F' := by
  have h4 : M.F4 = owed3 F := (head_cut P).1
  have z4 : Sized M.F4 := h4 ▸ owed3_sized hF
  obtain ⟨_, z5, r5, mZ, mT⟩ := tie_named M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie z4
  obtain ⟨l6, z6, r6, m6⟩ := fold_named _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.keys z5 r5 mZ
  obtain ⟨l7, z7, r7, m7⟩ := fold_named _ (fun s l => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.table z6 r6
    (mT.later l6)
  -- the leaves' sumcheck: begun; its rounds
  obtain ⟨tgL, muL, epsL, _, _, g1, hlv0⟩ := pscBegin_ok _ _ _ _ _ _ P.l1
  obtain ⟨_, _, _, _, g2, _, hst, _, _, _, _⟩ :=
    ran_roundsIn eqForm_eq (hlv0 ▸ ran_begin M.table.form tgL muL epsL M.F7.next) _ _ _ _ _ _ _ P.l2
  obtain ⟨_, g3⟩ := (point_ok _ _ _ _ _ _ _).1 P.l3
  -- the bits' sumcheck
  obtain ⟨tgB, muB, epsB, _, _, g4, hb0⟩ := pscBegin_ok _ _ _ _ _ _ P.l4
  obtain ⟨_, _, _, _, g5, _, hsB1, _, _, _, hR1⟩ :=
    ran_roundsIn eqForm_eq2 (hb0 ▸ ran_begin (Aff.ofConst zeroE) tgB muB epsB M.G3.next) _ _ _ _ _
      _ _ P.l5
  obtain ⟨sentY, beta, v, _, hv, _, hsb, hH6, _, hsB2, _, _, _, hR2⟩ :=
    ran_ends hR1 _ _ _ _ _ _ _ _ P.l6
  obtain ⟨_, _, e7⟩ := (shown_ok _ _ _ _).1 P.l7
  have g7 : M.G7 = M.G6 := congrArg (fun x : (E × Fork) × Tape => x.1.2) e7
  obtain ⟨-, -, -, -, -, hH8, hrow, -⟩ := pscRow_ok _ _ _ _ _ _ _ _ _ P.l8
  have zG5 : Sized M.G5 := by
    rw [g5, g4, g3, g2, g1]
    exact took_sized _ (took_sized _ (took_sized _ (took_sized _ z7)))
  have lG5 : Later M.F7 M.G5 := by
    rw [g5, g4, g3, g2, g1]
    exact (((took_later _ _).trans (took_later _ _)).trans (took_later _ _)).trans (took_later _ _)
  obtain ⟨l6', z6', n6⟩ := hide_new (took_sized _ zG5) hH6
  rw [g7] at hH8
  obtain ⟨l8, z8, n8⟩ := hide_new z6' hH8
  have L78 : Later M.F7 M.G8 := ((lG5.trans (took_later _ _)).trans l6').trans l8
  have hb0s : M.b0.start = Aff.ofConst zeroE := by rw [hb0]
  have hlv0s : M.lv0.start = M.table.form := by rw [hlv0]
  rw [P.heard, P.fork]
  refine ⟨?_, (m6.later l7).later L78, ?_, ?_⟩
  · show NamedAll M.G8 (M.table.rows.push M.row)
    rw [hrow]
    refine namedAll_push (r7.later L78) (named_rowForm _ _ ?_ fun i hi => ?_)
    · rw [hsB2, hsB1, hb0s]
      exact named_ofConst _ _
    · exact n8 i (by simpa using hi)
  · show Named M.G8 (Aff.slot M.sBit)
    have := n6 0 (by rw [hv]; exact Nat.one_pos)
    exact named_slot ⟨by rw [l8.ns]; exact this.1, (l8.keep _ this.2).1⟩
  · show Named M.G8 M.lv.start
    rw [hst, hlv0s]
    exact m7.later L78

/-- **Of the library's flat copy.** -/
theorem lkPad_named (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F) :
    PadNames g F' := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  exact pad_named P hF

end Fo.Tp

#print axioms Fo.Tp.tie_named
#print axioms Fo.Tp.level_named
#print axioms Fo.Tp.pad_named
#print axioms Fo.Tp.lkPad_named
#print axioms Fo.Tp.bare_ents
