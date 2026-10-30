-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Slots/RunsFwd.lean: K4's TWO LISTINGS OF CLAIMS GO FORWARD TO A LATER LEDGER IN
WHICH THEIR WINDOWS ARE STILL FREE: they return there too, with the same forms, and the slots that
they fill late are the same, with the same values. The twin, THE OTHER WAY ROUND, of
Johnson/Road/K4/Slots/RunsSpare.lean, whose statements all begin at a return. Statements with their
proofs.

  `hide_returns` | `steps_return` | `run_returns`: a run of values is taken where the ledger has
    arrays of the right sizes and every slot of the run is there and free.
  `run_fwd`: where a run is taken from F, it is taken from a later F' in which its slots are still
    free.
  `shown_later` | `shownAll_later`: what is shown under a slot in F is shown in a later F'.
  `LateSame F G F' G'`: at every slot: "free in front and filled behind" holds of (F, G) and of (F',
  G') alike, and then with the same shown value and factor. `late_eq`: so the two lists of late
  slots (`K9.lateOf`, Johnson/Desc/First/Batch/ReaderOf.lean) are one.
  **`formsBack_fwd`** | **`formsFront_fwd`**: Sized F · Later F F' · the windows free in F' · the
  listing returns (fs, G) from F ⟹ it returns (fs, G') from F' for some G', G'.ns = G.ns, and
  K9.lateOf F' G' = K9.lateOf F G.

Limits. ON THE TWO LISTINGS AND THE LEDGER ALONE: that the block's runs "front" and "back" are these
listings, and the reader's own test on the entries, are not called here. THAT THE WINDOWS ARE STILL
FREE IN F' IS A PREMISE. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.
-/
import Johnson.Road.K4.Slots.RunsSpare
import Johnson.Desc.First.Batch.ReaderOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Slots

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.PscRun (Sized Filled Later Same hide_ok hideRun_ok hideRun_keeps)
open VerifiableInference.Desc (K9.lateOf)

/-! ## A run of values is taken -/

theorem hide_returns {F : Fork} {j : ℕ} (y k : E) (hF : Sized F) (hj : j < F.ns)
    (hf : ¬ Filled F j) : ∃ G, F.hide j y k = some G := by
  have hs : j < F.gotF.size := by rw [hF.2.2]; exact hj
  have e : F.gotF.getD j true = F.gotF.getD j false := by simp [Array.getD, hs]
  have e2 : F.gotF.getD j false = false := by
    unfold Filled at hf
    simpa using hf
  have c : (decide (j < F.ns) && F.gotF.size == F.ns && !F.gotF.getD j true) = true := by
    simp [hj, hF.2.2, e, e2]
  unfold Fork.hide
  rw [if_pos c]
  exact ⟨_, rfl⟩

theorem steps_return (k : E) : ∀ (l : List E) (first : ℕ) (F : Fork), Sized F →
    (∀ i, i < l.length → first + i < F.ns ∧ ¬ Filled F (first + i)) →
    ∃ x, l.foldlM (Fork.hideStep k) (first, F) = some x
  | [], first, F, _, _ => ⟨(first, F), rfl⟩
  | y :: l, first, F, hF, h => by
    obtain ⟨h0, h1⟩ := h 0 (by simp)
    obtain ⟨G, hG⟩ := hide_returns y k hF h0 h1
    obtain ⟨_, _, sm, sG, _, _, _, rest⟩ := hide_ok F G (first + 0) y k hF hG
    have ns : G.ns = F.ns := by rw [sm]
    obtain ⟨x, hx⟩ := steps_return k l (first + 1) G sG fun i hi => by
      obtain ⟨a, b⟩ := h (i + 1) (by simpa using hi)
      have e : first + 1 + i = first + (i + 1) := by omega
      rw [e, ns]
      exact ⟨a, fun c => b (((rest _ (by omega)).2.2).1 c)⟩
    refine ⟨x, ?_⟩
    rw [List.foldlM_cons]
    show (Fork.hideStep k (first, F) y).bind _ = _
    have e : Fork.hideStep k (first, F) y = some (first + 1, G) := by
      show (F.hide first y k).map _ = _
      rw [show first = first + 0 from rfl, hG]
      rfl
    rw [e]
    exact hx

theorem run_returns {F : Fork} {first : ℕ} {v : Array E} (k : E) (hF : Sized F)
    (h : ∀ i, i < v.size → first + i < F.ns ∧ ¬ Filled F (first + i)) :
    ∃ G, F.hideRun first v k = some G := by
  obtain ⟨x, hx⟩ := steps_return k v.toList first F hF (by simpa using h)
  refine ⟨x.2, ?_⟩
  unfold Fork.hideRun
  rw [← Array.foldlM_toList, hx]

/-- **A run that is taken from F is taken from a later ledger in which its slots are still free.**
-/
theorem run_fwd {F F' G : Fork} {first : ℕ} {v : Array E} {k : E} (hF : Sized F) (L : Later F F')
    (hfree : ∀ i, i < v.size → ¬ Filled F' (first + i)) (h : F.hideRun first v k = some G) :
    ∃ G', F'.hideRun first v k = some G' := by
  obtain ⟨_, _, a, _⟩ := hideRun_ok F G first v k hF h
  exact run_returns k (L.sized hF) fun i hi => ⟨by rw [L.ns]; exact (a i hi).1, hfree i hi⟩

/-! ## What is shown stays shown -/

theorem shown_later {F F' : Fork} (L : Later F F') {j : ℕ} {e : E} (h : F.shown j = some e) :
    F'.shown j = some e := by
  unfold Fork.shown at h ⊢
  split at h
  · rename_i c
    rw [Bool.and_eq_true, decide_eq_true_eq] at c
    obtain ⟨k1, k2, _⟩ := L.keep j c.2
    rw [if_pos (by rw [Bool.and_eq_true, decide_eq_true_eq, L.ns]; exact ⟨c.1, k1⟩), k2]
    exact h
  · cases h

theorem mapM_fwd {α β : Type} (f f' : α → Option β) (hf : ∀ a b, f a = some b → f' a = some b) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → l.mapM f' = some r
  | [], r, h => h
  | a :: l, r, h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨b, hb, h1⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨bs, hbs, h2⟩ := Option.bind_eq_some_iff.mp h1
    show (f' a).bind _ = _
    rw [hf a b hb]
    show (l.mapM f').bind _ = _
    rw [mapM_fwd f f' hf l bs hbs]
    exact h2

theorem shownAll_later {F F' : Fork} (L : Later F F') (a : Array ℕ) (g : ℕ → ℕ) {sh : Array E}
    (h : (a.mapM fun i => F.shown (g i)) = some sh) :
    (a.mapM fun i => F'.shown (g i)) = some sh := by
  rw [Array.mapM_eq_mapM_toList] at h ⊢
  obtain ⟨r, hr, e⟩ := Option.map_eq_some_iff.mp h
  rw [mapM_fwd _ (fun i => F'.shown (g i)) (fun i b hb => shown_later L hb) _ r hr]
  exact e ▸ rfl

/-! ## The late slots -/

/-- At every slot: "free in front and filled behind" holds of (F, G) and of (F', G') alike, and then
with the same shown value and factor. -/
def LateSame (F G F' G' : Fork) : Prop :=
  ∀ j, ((¬ Filled F' j ∧ Filled G' j) ↔ (¬ Filled F j ∧ Filled G j)) ∧
    (¬ Filled F j → Filled G j →
      G'.vp.getD j zeroE = G.vp.getD j zeroE ∧ G'.mf.getD j zeroE = G.mf.getD j zeroE)

theorem late_eq {F G F' G' : Fork} (hns : G'.ns = G.ns) (h : LateSame F G F' G') :
    K9.lateOf F' G' = K9.lateOf F G := by
  unfold K9.lateOf
  rw [hns]
  refine List.filterMap_congr fun j _ => ?_
  obtain ⟨a, b⟩ := h j
  unfold Filled at a b
  by_cases c : ¬ F.gotF.getD j false = true ∧ G.gotF.getD j false = true
  · have c' := a.2 c
    obtain ⟨e1, e2⟩ := b c.1 c.2
    have k : (!(F.gotF.getD j false) && G.gotF.getD j false) = true := by simp [c.1, c.2]
    have k' : (!(F'.gotF.getD j false) && G'.gotF.getD j false) = true := by simp [c'.1, c'.2]
    rw [if_pos k, if_pos k', e1, e2]
  · have c' : ¬ (¬ F'.gotF.getD j false = true ∧ G'.gotF.getD j false = true) := fun q => c (a.1 q)
    have k : ¬ (!(F.gotF.getD j false) && G.gotF.getD j false) = true := by
      intro q
      rw [Bool.and_eq_true, Bool.not_eq_true'] at q
      exact c ⟨by rw [q.1]; decide, q.2⟩
    have k' : ¬ (!(F'.gotF.getD j false) && G'.gotF.getD j false) = true := by
      intro q
      rw [Bool.and_eq_true, Bool.not_eq_true'] at q
      exact c' ⟨by rw [q.1]; decide, q.2⟩
    rw [if_neg k, if_neg k']

/-- One run, taken from F and from F'. -/
theorem run_late {F G F' G' : Fork} {first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (hF' : Sized F') (h : F.hideRun first v k = some G) (h' : F'.hideRun first v k = some G') :
    LateSame F G F' G' := by
  obtain ⟨_, _, a, r⟩ := hideRun_ok F G first v k hF h
  obtain ⟨_, _, a', r'⟩ := hideRun_ok F' G' first v k hF' h'
  intro j
  by_cases hj : j < first ∨ first + v.size ≤ j
  · obtain ⟨_, _, q⟩ := r j hj
    obtain ⟨_, _, q'⟩ := r' j hj
    exact ⟨⟨fun x => absurd (q'.1 x.2) x.1, fun x => absurd (q.1 x.2) x.1⟩,
      fun x y => absurd (q.1 y) x⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = first + i := ⟨j - first, by omega⟩
    have hi : i < v.size := by omega
    obtain ⟨_, b1, b2, b3, b4⟩ := a i hi
    obtain ⟨_, c1, c2, c3, c4⟩ := a' i hi
    exact ⟨⟨fun _ => ⟨b1, b2⟩, fun _ => ⟨c1, c2⟩⟩, fun _ _ => ⟨c3.trans b3.symm, c4.trans b4.symm⟩⟩

/-- Two stretches, one behind the other. -/
theorem LateSame.trans {F G H F' G' H' : Fork} (L1 : Later F G) (L2 : Later G H)
    (L1' : Later F' G') (L2' : Later G' H') (a : LateSame F G F' G') (b : LateSame G H G' H') :
    LateSame F H F' H' := by
  intro j
  obtain ⟨a1, a2⟩ := a j
  obtain ⟨b1, b2⟩ := b j
  refine ⟨⟨fun x => ?_, fun x => ?_⟩, fun x y => ?_⟩
  · by_cases c : Filled G' j
    · obtain ⟨p, q⟩ := a1.1 ⟨x.1, c⟩
      exact ⟨p, (L2.keep j q).1⟩
    · obtain ⟨p, q⟩ := b1.1 ⟨c, x.2⟩
      exact ⟨fun z => p (L1.keep j z).1, q⟩
  · by_cases c : Filled G j
    · obtain ⟨p, q⟩ := a1.2 ⟨x.1, c⟩
      exact ⟨p, (L2'.keep j q).1⟩
    · obtain ⟨p, q⟩ := b1.2 ⟨c, x.2⟩
      exact ⟨fun z => p (L1'.keep j z).1, q⟩
  · by_cases c : Filled G j
    · obtain ⟨e1, e2⟩ := a2 x c
      obtain ⟨_, k1, k2⟩ := L2.keep j c
      obtain ⟨_, k1', k2'⟩ := L2'.keep j (a1.2 ⟨x, c⟩).2
      exact ⟨k1'.trans (e1.trans k1.symm), k2'.trans (e2.trans k2.symm)⟩
    · exact b2 c y

/-! ## The two listings go forward -/

theorem ownClaim_of {p : Psc} {S0 : E} {kept : Aff} {F G : Fork}
    (hb : (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size) = true)
    (h : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    ownClaim p S0 kept F = some (p.rowForm S0 kept, G) := by
  unfold ownClaim
  show (Fl.andThen
      (Fl.must (!p.rowMade && p.started && !p.vars.isEmpty && p.r.size == p.vars.size))
      (fun _ => Fl.andThen
        (Fl.change (·.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE)))
        (fun _ => Fl.ret (p.rowForm S0 kept, { p with rowMade := true }))) F []).map _ = _
  unfold Fl.andThen Fl.must
  rw [if_pos hb]
  simp only [Fl.change, Fl.ret, h, Option.map_some]

/-- A window that is free. -/
def WinFree (p : Psc) (F : Fork) : Prop := ∀ j, InWin p j → ¬ Filled F j

theorem win_fwd {p : Psc} {F F' G : Fork} (hF : Sized F) (L : Later F F') (W : WinFree p F')
    (h : F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G) :
    ∃ G', F'.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G' :=
  run_fwd hF L (fun i hi => W _ ⟨by omega, by rw [Array.size_replicate] at hi; omega⟩) h

/-- **The listing "back" goes forward.** -/
theorem formsBack_fwd {o : Own} {F F' G : Fork} {fs : Array Aff} (hF : Sized F) (L : Later F F')
    (W : WinFree o.wo.toWsMerged.p F') (h : formsBack o F = some (fs, G)) :
    ∃ G', formsBack o F' = some (fs, G') ∧ G'.ns = G.ns ∧ K9.lateOf F' G' = K9.lateOf F G := by
  have h0 := h
  unfold formsBack at h0
  obtain ⟨⟨rowM, F1⟩, a1, h1⟩ := Option.bind_eq_some_iff.mp h0
  dsimp only at h1
  obtain ⟨e1, hb, r1⟩ := ownClaim_some a1
  obtain ⟨F1', r1'⟩ := win_fwd hF L W r1
  have e := Option.some.inj h1
  have eG : G = F1.paid o.H.fo.owedJoin := (congrArg Prod.snd e).symm
  have efs : fs = (back o rowM).toArray := (congrArg Prod.fst e).symm
  refine ⟨F1'.paid o.H.fo.owedJoin, ?_, ?_, ?_⟩
  · unfold formsBack
    rw [ownClaim_of hb r1', efs, e1]
    rfl
  · rw [eG]
    show F1'.ns = F1.ns
    rw [(hideRun_keeps r1').ns, (hideRun_keeps r1).ns, L.ns]
  · rw [eG]
    refine late_eq ?_ (show LateSame F (F1.paid _) F' (F1'.paid _) from
      (run_late hF (L.sized hF) r1 r1' : LateSame F F1 F' F1'))
    show F1'.ns = F1.ns
    rw [(hideRun_keeps r1').ns, (hideRun_keeps r1).ns, L.ns]

/-- One run, taken from F and from a later F': the ledgers behind are again one later than the other;
and a slot that is free behind the first and free in F' is free behind the second. -/
theorem run_step {F F' G G' : Fork} {first : ℕ} {v : Array E} {k : E} (hF : Sized F)
    (L : Later F F') (h : F.hideRun first v k = some G) (h' : F'.hideRun first v k = some G') :
    Later G G' ∧ ∀ j, ¬ Filled G j → ¬ Filled F' j → ¬ Filled G' j := by
  obtain ⟨_, sG, a, r⟩ := hideRun_ok F G first v k hF h
  obtain ⟨_, sG', a', r'⟩ := hideRun_ok F' G' first v k (L.sized hF) h'
  obtain ⟨_, n, _⟩ := run_same hF h
  obtain ⟨_, n', _⟩ := run_same (L.sized hF) h'
  refine ⟨⟨by rw [n, n']; exact L.next,
    by rw [(hideRun_keeps h').ns, (hideRun_keeps h).ns, L.ns], fun _ => sG', fun j hj => ?_⟩,
    fun j f1 f2 => ?_⟩
  · by_cases c : j < first ∨ first + v.size ≤ j
    · obtain ⟨q1, q2, q3⟩ := r j c
      obtain ⟨p1, p2, p3⟩ := r' j c
      obtain ⟨k0, k1, k2⟩ := L.keep j (q3.1 hj)
      exact ⟨p3.2 k0, p1.trans (k1.trans q1.symm), p2.trans (k2.trans q2.symm)⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = first + i := ⟨j - first, by omega⟩
      have hi : i < v.size := by omega
      obtain ⟨_, _, _, b3, b4⟩ := a i hi
      obtain ⟨_, _, c2, c3, c4⟩ := a' i hi
      exact ⟨c2, c3.trans b3.symm, c4.trans b4.symm⟩
  · by_cases c : j < first ∨ first + v.size ≤ j
    · exact fun z => f2 ((r' j c).2.2.1 z)
    · obtain ⟨i, rfl⟩ : ∃ i, j = first + i := ⟨j - first, by omega⟩
      exact absurd (a i (by omega)).2.2.1 f1

/-- **The listing "front" goes forward.** -/
theorem formsFront_fwd {rows : Bool} {P : Pub} {g : ℕ} {o : Own} {F F' G : Fork} {fs : Array Aff}
    (hF : Sized F) (L : Later F F') (W1 : WinFree o.H.tV.p F') (W2 : WinFree o.H.fo.leaves F')
    (h : formsFrontWith rows P g o F = some (fs, G)) :
    ∃ G', formsFrontWith rows P g o F' = some (fs, G') ∧ G'.ns = G.ns ∧
      K9.lateOf F' G' = K9.lateOf F G := by
  have h0 := h
  unfold formsFrontWith at h0
  obtain ⟨sh, a1, h1⟩ := Option.bind_eq_some_iff.mp h0
  obtain ⟨⟨rowV, F1⟩, a2, h2⟩ := Option.bind_eq_some_iff.mp h1
  dsimp only at h2
  obtain ⟨pp, a3, h3⟩ := Option.bind_eq_some_iff.mp h2
  obtain ⟨⟨rowL, F2⟩, a4, h4⟩ := Option.bind_eq_some_iff.mp h3
  dsimp only at h4
  obtain ⟨l, a5, h5⟩ := Option.bind_eq_some_iff.mp h4
  obtain ⟨e2, hb2, r2⟩ := ownClaim_some a2
  obtain ⟨e4, hb4, r4⟩ := ownClaim_some a4
  have e := Option.some.inj h5
  obtain ⟨F1', r2'⟩ := win_fwd hF L W1 r2
  obtain ⟨L1, fr⟩ := run_step hF L r2 r2'
  obtain ⟨s1, _, _⟩ := run_same hF r2
  obtain ⟨_, _, af, _⟩ := hideRun_ok F1 F2 _ _ _ s1 r4
  have W2' : WinFree o.H.fo.leaves F1' := by
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = o.H.fo.leaves.first + i := ⟨j - o.H.fo.leaves.first, by
      have := hj.1
      omega⟩
    refine fr _ (af i ?_).2.1 (W2 _ hj)
    rw [Array.size_replicate]
    have := hj.2
    omega
  obtain ⟨F2', r4'⟩ := win_fwd s1 L1 W2' r4
  have a1' := shownAll_later L (Array.range (4 * P.y.NI)) (fun i => o.H.tV.sEnd + i) a1
  have c2 := ownClaim_of (S0 := rowsSummand P.y o.H sh) (kept := {}) hb2 r2'
  have c4 := ownClaim_of (S0 := oneE) (kept := pp.1) hb4 r4'
  rw [e2, e4] at a5
  have nsE : F2'.ns = F2.ns := by
    rw [(hideRun_keeps r4').ns, (hideRun_keeps r4).ns, (hideRun_keeps r2').ns,
      (hideRun_keeps r2).ns, L.ns]
  have LS : LateSame F F2 F' F2' :=
    LateSame.trans (hideRun_keeps r2) (hideRun_keeps r4) (hideRun_keeps r2') (hideRun_keeps r4')
      (run_late hF (L.sized hF) r2 r2') (run_late s1 (L1.sized s1) r4 r4')
  have eG : G = (if rows then F2.paid o.H.fo.owedObjects else F2).paid o.H.fo.owedPlanes :=
    (congrArg Prod.snd e).symm
  have efs : fs = l.toArray := (congrArg Prod.fst e).symm
  refine ⟨(if rows then F2'.paid o.H.fo.owedObjects else F2').paid o.H.fo.owedPlanes, ?_, ?_, ?_⟩
  · unfold formsFrontWith
    simp only [Option.bind_eq_bind, Option.pure_def, a1', Option.bind_some, c2, a3, c4, a5, efs]
  · rw [eG]
    cases rows <;> exact nsE
  · rw [eG]
    cases rows
    · exact late_eq nsE (show LateSame F (F2.paid _) F' (F2'.paid _) from LS)
    · exact late_eq nsE (show LateSame F ((F2.paid _).paid _) F' ((F2'.paid _).paid _) from LS)

end OnBytes.Desc.First.K4.Slots

#print axioms OnBytes.Desc.First.K4.Slots.run_step
#print axioms OnBytes.Desc.First.K4.Slots.formsFront_fwd
#print axioms OnBytes.Desc.First.K4.Slots.late_eq
#print axioms OnBytes.Desc.First.K4.Slots.run_late
#print axioms OnBytes.Desc.First.K4.Slots.LateSame.trans
#print axioms OnBytes.Desc.First.K4.Slots.ownClaim_of
#print axioms OnBytes.Desc.First.K4.Slots.formsBack_fwd
#print axioms OnBytes.Desc.First.K4.Slots.hide_returns
#print axioms OnBytes.Desc.First.K4.Slots.steps_return
#print axioms OnBytes.Desc.First.K4.Slots.run_returns
#print axioms OnBytes.Desc.First.K4.Slots.run_fwd
#print axioms OnBytes.Desc.First.K4.Slots.shown_later
#print axioms OnBytes.Desc.First.K4.Slots.shownAll_later
