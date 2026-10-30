-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place is shown at which all premises hold together.
Johnson/Top/H/Keep/PadFresh.lean: The kind "lookup" (K3): EVERY SLOT THAT A FORM WHICH A LOOKUP's
HEARING KEEPS NAMES (its kept rows; the form left for the join; the slot of the bits' sumcheck; the
starting form of the sumcheck over the leaves) LIES AT OR ABOVE THE NEXT SLOT OF THE LEDGER IN
FRONT: the hearing takes no slot from outside. At the library's flat copy of the routine, and at an
accept of K3.block's decide at any seat. Statements and proofs. THE SISTER OF
Johnson/Top/H/Keep/PadNamed.lean ("there and filled"), along the same chain of the runs of the
routines that lkPad calls.

OBJECT: lkPad; K3.block's decide.
Used by Johnson/Top/H/Keep/MergeApart.lean.
LETTERS: F0: the ledger in front of the hearing, fixed along the chain.
Compiled with the whole library.

How. Off F0 j: slot j is free in F0. A run of values under slots (Fork.hideRun) refuses at a filled
slot, and what is filled stays filled: so every slot that the hearing fills was free in F0. Every
slot that a kept form names is one that the hearing has filled: so it is Off F0 (the chain:
tieStep_off … pad_off). It is also filled behind (PadNames), and behind a hearing a slot is filled
just if it was filled in front or lies in the hearing's own room (PadExact.marks): so it lies in
that room: at or above F0.next.

Main names:
  Off, off_of_hide. TieOff, tieStep_off, tieFold_off, tie_off, level_off, fold_off. PadOff, pad_off,
  lkPad_off.
  fresh_of_off: the last step.
  decide_fresh: THE END: at an accept of K3.block's decide, at any seat.

Limits. Sized F is a premise.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Tp
open OnBytes.K.Kc
open TwV FoNums OnBytes OnBytes.Model OnBytes.PscRun OnBytes.PscTie OnBytes.Psc
open OnBytes.Desc.First.K4.Slots (SlotsIn slotsIn_mono slotsIn_ofConst slotsIn_slot slotsIn_empty
  slotsIn_addMul slotsIn_scale slotsIn_add slotsIn_foldl_mem slotsIn_rowForm)

/-- Slot j is free in the ledger F0. -/
def Off (F0 : Fork) (j : ℕ) : Prop := ¬ Filled F0 j

/-- Every form of the array names slots alone that are free in F0. -/
def OffAll (F0 : Fork) (rows : Array Aff) : Prop := ∀ f ∈ rows.toList, SlotsIn (Off F0) f

theorem offAll_empty (F0 : Fork) : OffAll F0 #[] := fun f hf => by simp at hf

theorem offAll_push {F0 : Fork} {rows : Array Aff} {f : Aff} (h : OffAll F0 rows)
    (hf : SlotsIn (Off F0) f) : OffAll F0 (rows.push f) := fun x hx => by
  rw [Array.toList_push, List.mem_append] at hx
  rcases hx with hx | hx
  · exact h x hx
  · rw [List.mem_singleton.1 hx]
    exact hf

/-- What a run of values under slots fills was free in every earlier ledger. -/
theorem off_of_hide {F0 F G : Fork} {first : ℕ} {v : Array E} {f : E} (h0 : Later F0 F)
    (hF : Sized F) (h : F.hideRun first v f = some G) : ∀ i, i < v.size → Off F0 (first + i) :=
  fun i hi hc => ((hideRun_ok F G first v f hF h).2.2.1 i hi).2.1 (h0.keep _ hc).1

/-! ## The tie -/

/-- What rides along the tie's steps. n: how many steps have run. -/
structure TieOff (F0 : Fork) (s : Forest.TieStep) (n : ℕ) : Prop where
  rows : OffAll F0 s.rows
  sP : 0 < n → Off F0 s.sP
  sZ : 0 < n → Off F0 s.sZ
  sG : ∀ j ∈ s.sG.toList, Off F0 j
  size : s.sG.size = n

theorem tieStep_off (F0 : Fork) (a : E) (s s' : Forest.TieStep) (j : ℕ) (F G : Fork) (c c' : Tape)
    (h : lkTieStep a s j F c = .ok ((s', G), c')) (h0 : Later F0 F) (hF : Sized F)
    (hs : TieOff F0 s j) : Later F G ∧ Sized G ∧ TieOff F0 s' (j + 1) := by
  obtain ⟨target, mu, eps, sent, beta, v, G1, vP, vG, summand, _, _, _, hv, hG1, _, _, _, hG,
    rfl⟩ := tieStep_ok a s j F G c c' s' h
  have hT : Sized (took (took F 1) (3 + if j = 0 then 3 else 2)) :=
    took_sized _ (took_sized _ hF)
  have LT : Later F (took (took F 1) (3 + if j = 0 then 3 else 2)) :=
    (took_later F 1).trans (took_later _ _)
  obtain ⟨l1, s1, _⟩ := hide_new hT hG1
  obtain ⟨l2, s2, _⟩ := hide_new s1 hG
  have L1 : Later F G1 := LT.trans l1
  have L : Later F G := L1.trans l2
  have n1 := off_of_hide (h0.trans LT) hT hG1
  have n2 := off_of_hide (h0.trans L1) s1 hG
  have at1 : ∀ i, i < v.size → Off F0 (F.next + 1 + 3 + i) := fun i hi => n1 i hi
  have hstart : SlotsIn (Off F0) (if j = 0 then Aff.ofConst zeroE else Aff.slot s.sP) := by
    by_cases hj : j = 0
    · rw [if_pos hj]
      exact slotsIn_ofConst _
    · rw [if_neg hj]
      exact slotsIn_slot (S := Off F0) (hs.sP (Nat.pos_of_ne_zero hj))
  refine ⟨L, s2, ⟨offAll_push hs.rows
    (slotsIn_rowForm _ _ (fun i hi => ?_) hstart slotsIn_empty),
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
      exact hs.sZ (Nat.pos_of_ne_zero hj)
  · rw [Array.toList_push, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hs.sG x hx
    · rw [List.mem_singleton.1 hx]
      by_cases hj : j = 0
      · simp only [if_pos hj] at hv ⊢
        exact at1 2 (by omega)
      · simp only [if_neg hj] at hv ⊢
        exact at1 1 (by omega)

theorem tieFold_off (F0 : Fork) (a : E) :
    ∀ (n k : ℕ) (s s' : Forest.TieStep) (F G : Fork) (c c' : Tape),
    ((List.range' k n).foldlM (lkTieStep a) s) F c = .ok ((s', G), c') → Later F0 F → Sized F →
    TieOff F0 s k → Later F G ∧ Sized G ∧ TieOff F0 s' (k + n)
  | 0, k, s, s', A, B, c, c', h, _, hF, hs => by
    have e := (foldlM_nil_ok (lkTieStep a) s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨Later.refl _, hF, hs⟩
  | n + 1, k, s, s', A, B, c, c', h, h0, hF, hs => by
    rw [List.range'_succ] at h
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok (lkTieStep a) s k _ A c ((s', B), c')).1 h
    obtain ⟨l1, z1, t1⟩ := tieStep_off F0 a s s₁ k A F₁ c c₁ h1 h0 hF hs
    obtain ⟨l2, z2, t2⟩ := tieFold_off F0 a n (k + 1) s₁ s' F₁ B c₁ c' h2 (h0.trans l1) z1 t1
    exact ⟨l1.trans l2, z2, by rw [show k + (n + 1) = k + 1 + n by omega]; exact t2⟩

/-- **The tie.** -/
theorem tie_off (F0 : Fork) (a : E) (F G : Fork) (c c' : Tape) (T : Forest.Tie)
    (h : lkTie a F c = .ok ((T, G), c')) (h0 : Later F0 F) (hF : Sized F) :
    Later F G ∧ Sized G ∧ OffAll F0 T.rows ∧ SlotsIn (Off F0) (Aff.slot T.sZ) ∧
      SlotsIn (Off F0) T.cT := by
  obtain ⟨s, c1, pt, h1, _, rfl⟩ := tie_ok a F G c c' T h
  rw [List.range_eq_range'] at h1
  obtain ⟨L, z, t⟩ := tieFold_off F0 a 31 0 {} s F G c c1 h1 h0 hF
    ⟨offAll_empty F0, fun h => absurd h (by omega), fun h => absurd h (by omega),
      fun j hj => by simp at hj, rfl⟩
  have hall : ∀ j ∈ (s.sG.push s.sP).toList, Off F0 j := fun j hj => by
    rw [Array.toList_push, List.mem_append] at hj
    rcases hj with hj | hj
    · exact t.sG j hj
    · rw [List.mem_singleton.1 hj]
      exact t.sP (by omega)
  have hsz : (s.sG.push s.sP).size = 32 := by rw [Array.size_push, t.size]
  have hget : ∀ j, j < 32 → Off F0 ((s.sG.push s.sP).getD j 0) := fun j hj => by
    have hj' : j < (s.sG.push s.sP).size := by rw [hsz]; exact hj
    have e : (s.sG.push s.sP).getD j 0 = (s.sG.push s.sP)[j] := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hj']
      rfl
    rw [e]
    exact hall _ (Array.mem_def.1 (Array.getElem_mem hj'))
  refine ⟨L, z, t.rows, slotsIn_slot (S := Off F0) (t.sZ (by omega)), ?_⟩
  show SlotsIn (Off F0) (tieCT (s.sG.push s.sP) (eqTab pt.reverse))
  unfold tieCT
  exact slotsIn_foldl_mem (S := Off F0) _ (List.range 32)
    (fun f j hj hf => slotsIn_addMul _ hf (slotsIn_slot (hget j (List.mem_range.1 hj))))
    (Aff.ofConst zeroE) (slotsIn_ofConst _)

/-! ## A level; a walk of levels -/

theorem level_off (F0 : Fork) (s s' : Forest.Descent) (mu : ℕ) (order : List ℕ) (F G : Fork)
    (c c' : Tape) (h : lkLevel s mu order F c = .ok ((s', G), c')) (h0 : Later F0 F)
    (hF : Sized F) (hr : OffAll F0 s.rows) (hf : SlotsIn (Off F0) s.form) :
    Later F G ∧ Sized G ∧ OffAll F0 s'.rows ∧ SlotsIn (Off F0) s'.form := by
  obtain ⟨o, ho, e1, _, e3⟩ := level_ok s mu order F G c c' s' h
  obtain ⟨p, m0, eps, rs, sentY, beta, vals, vL, vR, F3, p', _, _, hst, _, _, _, _, hv2, _, hR, _,
    hsR, hH3, _, _, hHG, _, hrow, _⟩ := levelIn_ran mu s.rho s.form order F G c c' o ho
  obtain ⟨l3, s3, _⟩ := hide_new (took_sized _ hF) hH3
  obtain ⟨lG, sG, _⟩ := hide_new s3 hHG
  have L3 : Later F F3 := (took_later F _).trans l3
  have L : Later F G := L3.trans lG
  have n3 := off_of_hide (h0.trans (took_later F _)) (took_sized _ hF) hH3
  have nG := off_of_hide (h0.trans L3) s3 hHG
  have atL : ∀ i, i < 2 → Off F0 (o.sL + i) := fun i hi => n3 i (by rw [hv2]; exact hi)
  refine ⟨L, sG, ?_, ?_⟩
  · rw [e1, hrow]
    refine offAll_push hr (slotsIn_rowForm p _ (fun i hi => ?_) (by rw [hst]; exact hf)
      slotsIn_empty)
    rw [hR.first_eq]
    exact nG i (by simpa using hi)
  · rw [e3, hsR]
    exact slotsIn_add (slotsIn_scale _ (slotsIn_slot (S := Off F0) (atL 0 (by omega))))
      (slotsIn_scale _ (slotsIn_slot (S := Off F0) (atL 1 (by omega))))

theorem fold_off (F0 : Fork) {α : Type} (f : Forest.Descent → α → Fl Forest.Descent)
    (hf : ∀ s a, ∃ mu order, f s a = lkLevel s mu order) :
    ∀ (l : List α) (s s' : Forest.Descent) (F G : Fork) (c c' : Tape),
      (l.foldlM f s) F c = .ok ((s', G), c') → Later F0 F → Sized F → OffAll F0 s.rows →
      SlotsIn (Off F0) s.form →
      Later F G ∧ Sized G ∧ OffAll F0 s'.rows ∧ SlotsIn (Off F0) s'.form
  | [], s, s', A, B, c, c', h, _, hF, hr, hm => by
    have e := (foldlM_nil_ok f s A c ((s', B), c')).1 h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ : (s' = s ∧ B = A) ∧ c' = c := by simpa [Prod.ext_iff] using e
    exact ⟨Later.refl _, hF, hr, hm⟩
  | a :: l, s, s', A, B, c, c', h, h0, hF, hr, hm => by
    obtain ⟨s₁, F₁, c₁, h1, h2⟩ := (foldlM_cons_ok f s a l A c ((s', B), c')).1 h
    obtain ⟨mu, order, e⟩ := hf s a
    rw [e] at h1
    obtain ⟨l1, z1, r1, m1⟩ := level_off F0 s s₁ mu order A F₁ c c₁ h1 h0 hF hr hm
    obtain ⟨l2, z2, r2, m2⟩ := fold_off F0 f hf l s₁ s' F₁ B c₁ c' h2 (h0.trans l1) z1 r1 m1
    exact ⟨l1.trans l2, z2, r2, m2⟩

/-! ## The whole hearing -/

/-- **The forms that a hearing keeps name slots alone that were free in front.** -/
structure PadOff (F0 : Fork) (g : Forest.Heard) : Prop where
  rows : OffAll F0 g.rows
  cEnd : SlotsIn (Off F0) g.cEnd
  sBit : SlotsIn (Off F0) (Aff.slot g.sBit)
  start : SlotsIn (Off F0) g.leaves.start

/-- From the chain of the runs of the routines that lkPad calls. -/
theorem pad_off {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Tape}
    {g : Forest.Heard} {M : PadMid} (P : PadCut calls pub lid F c g F' c' M) (hF : Sized F) :
    PadOff F g := by
  have h4 : M.F4 = owed3 F := (head_cut P).1
  have z4 : Sized M.F4 := h4 ▸ owed3_sized hF
  have l4 : Later F M.F4 := h4 ▸ owed3_later F
  obtain ⟨l5, z5, r5, mZ, mT⟩ := tie_off F M.a M.F4 M.F5 M.c4 M.c5 M.t P.tie l4 z4
  have L5 : Later F M.F5 := l4.trans l5
  obtain ⟨l6, z6, r6, m6⟩ :=
    fold_off F _ (fun s mu => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.keys L5 z5 r5 mZ
  have L6 : Later F M.F6 := L5.trans l6
  obtain ⟨l7, z7, r7, m7⟩ :=
    fold_off F _ (fun s l => ⟨_, _, rfl⟩) _ _ _ _ _ _ _ P.table L6 z6 r6 mT
  have L7 : Later F M.F7 := L6.trans l7
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
  obtain ⟨l6', z6', _⟩ := hide_new (took_sized _ zG5) hH6
  have n6 := off_of_hide ((L7.trans lG5).trans (took_later _ _)) (took_sized _ zG5) hH6
  rw [g7] at hH8
  have n8 := off_of_hide (((L7.trans lG5).trans (took_later _ _)).trans l6') z6' hH8
  have hb0s : M.b0.start = Aff.ofConst zeroE := by rw [hb0]
  have hlv0s : M.lv0.start = M.table.form := by rw [hlv0]
  rw [P.heard]
  refine ⟨?_, m6, ?_, ?_⟩
  · show OffAll F (M.table.rows.push M.row)
    rw [hrow]
    refine offAll_push r7 (slotsIn_rowForm _ _ (fun i hi => ?_) ?_ slotsIn_empty)
    · exact n8 i (by simpa using hi)
    · rw [hsB2, hsB1, hb0s]
      exact slotsIn_ofConst _
  · show SlotsIn (Off F) (Aff.slot M.sBit)
    exact slotsIn_slot (S := Off F) (n6 0 (by rw [hv]; exact Nat.one_pos))
  · show SlotsIn (Off F) M.lv.start
    rw [hst, hlv0s]
    exact m7

/-- **Of the library's flat copy.** -/
theorem lkPad_off (calls : Array Call) (pub : Array Nat) (lid : ℕ) (F F' : Fork) (t u : Tape)
    (g : Forest.Heard) (h : lkPad calls pub lid F t = some (g, F', u)) (hF : Sized F) :
    PadOff F g := by
  have h' : lkPad calls pub lid F t = .ok ((g, F'), u) := h
  obtain ⟨M, P⟩ := pad_cut calls pub lid F F' t u g h'
  exact pad_off P hF

/-- **The last step**: free in front, filled behind: so in the hearing's own room. -/
theorem fresh_of_off {h : Forest.Shape} {F F' : Fork} {g : Forest.Heard} (X : PadExact h F F' g)
    {f : Aff} (ho : SlotsIn (Off F) f) (hn : SlotsIn (In F') f) :
    ∀ x ∈ f.slots.toList, F.next ≤ x.1 := fun x hx =>
  ((X.marks x.1).1 (hn x hx).2).elim (fun hc => absurd hc (ho x hx)) fun y => y.1

end Fo.Tp

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc.First.Tape (flRun flRun_holds)

/-- **Of K3.block's decide: every slot that a kept form names lies at or above the next slot of the
ledger in front.** -/
theorem decide_fresh {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (hd : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ (F : Fork) (x : Forest.Heard × Fork), seat.fork s = some F ∧ seat.heard s = none ∧
      s' = seat.put s x.1 x.2 ∧
      (Sized F → (∀ f ∈ x.1.rows.toList, ∀ y ∈ f.slots.toList, F.next ≤ y.1) ∧
        (∀ y ∈ x.1.cEnd.slots.toList, F.next ≤ y.1) ∧ F.next ≤ x.1.sBit ∧
        ∀ y ∈ x.1.leaves.start.slots.toList, F.next ≤ y.1) := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hd
  refine ⟨F, x, hF, hn, rfl, fun hS => ?_⟩
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
      have O := _root_.Fo.Tp.lkPad_off p.calls p.pub p.lid F x.2 t [] x.1 hl hS
      have N := _root_.Fo.Tp.lkPad_named p.calls p.pub p.lid F x.2 t [] x.1 hl hS
      have X := _root_.Fo.Tp.lkPad_exact p.calls p.pub p.lid F x.2 t [] x.1 hl hS
      refine ⟨fun f hf => _root_.Fo.Tp.fresh_of_off X (O.rows f hf) (N.rows f hf).2,
        _root_.Fo.Tp.fresh_of_off X O.cEnd N.cEnd.2, ?_,
        _root_.Fo.Tp.fresh_of_off X O.start N.start.2⟩
      exact _root_.Fo.Tp.fresh_of_off X O.sBit N.sBit.2 (x.1.sBit, oneE) (by simp [Aff.slot])
    · exact absurd hx (by simp)

end VerifiableInference.OnPublicFiles

#print axioms Fo.Tp.off_of_hide
#print axioms Fo.Tp.offAll_empty
#print axioms Fo.Tp.offAll_push
#print axioms Fo.Tp.tieStep_off
#print axioms Fo.Tp.tieFold_off
#print axioms Fo.Tp.tie_off
#print axioms Fo.Tp.level_off
#print axioms Fo.Tp.fold_off
#print axioms Fo.Tp.pad_off
#print axioms Fo.Tp.lkPad_off
#print axioms Fo.Tp.fresh_of_off
#print axioms VerifiableInference.OnPublicFiles.decide_fresh
