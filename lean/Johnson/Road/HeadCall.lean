-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadCall.lean: what the form of a lookup call's key vector is worth, in its parts.

For each lookup call of the output head's sub-proof the verifier builds one form (keyForm in
OnBytes/Model/HeadForms.lean): the padding key times the weight of the columns that no segment
lists, the forms of the call's segments, and, in the call with the segment NF, the first slot of a
sumcheck. This file takes that routine apart.

Main definitions: padSum (the weight of the columns that no segment lists).
Main theorems: ok_forIn_pre (a rule with an invariant for a loop over a list); keyForm_value.

What is not claimed. What a segment's form is worth is a hypothesis here
(Johnson/Road/HeadLines.lean and the files beside it show it, family by family). Nothing is said
about the counts of padding keys that the routine also returns. The theorem begins "if the routine
succeeds". The program does not import this file.
-/
import Johnson.Road.HeadLines
import OnBytes.Iop.RowLaws

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)

/-- A rule for a loop over the members of a list l0. I pre b F C says what holds when the members
pre have been dealt with, of the loop's value b, the state and the context. If every step that
succeeds goes on and keeps I, a loop that succeeds ends with I at the whole list. -/
theorem ok_forIn_pre {α β : Type} (f : α → β → SubM (ForInStep β)) (l0 : List α)
    (I : List α → β → Fork → Ctx → Prop)
    (step : ∀ pre a b F1 C1 r F2 C2, (∃ post, l0 = pre ++ a :: post) → I pre b F1 C1 →
      Ok (f a b) F1 C1 r F2 C2 → ∃ b', r = ForInStep.yield b' ∧ I (pre ++ [a]) b' F2 C2) :
    ∀ (l pre : List α) (b : β) (F : Fork) (C : Ctx) (b' : β) (G : Fork) (D : Ctx),
      l0 = pre ++ l → I pre b F C → Ok (forIn l b f) F C b' G D → I l0 b' G D
  | [], pre, b, F, C, b', G, D, e, h0, h => by
    rw [List.forIn_nil, ok_pure] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rw [e, List.append_nil]
    exact h0
  | a :: l, pre, b, F, C, b', G, D, e, h0, h => by
    rw [List.forIn_cons, ok_bind] at h
    obtain ⟨r, F1, C1, h1, h2⟩ := h
    obtain ⟨b1, rfl, hI⟩ := step pre a b F C r F1 C1 ⟨l, e⟩ h0 h1
    exact ok_forIn_pre f l0 I step l (pre ++ [a]) b1 F1 C1 b' G D (by rw [e]; simp) hI h2

section Call

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- The sum of the weights e of the columns below J that bear the mark 0. -/
def padSum (e : Array E) (weighed : Array ℕ) (J : ℕ) : K :=
  ∑ j ∈ range J, if weighed.getD j 0 = 0 then ρ.val (e.getD j zeroE) else 0

variable {ρ W}

/-- The form of call number q's key vector, in its parts. val g is what the form of the segment g
is worth. The marks are those that the segments' lists of columns leave. -/
theorem keyForm_value {R : Model.Head.Run} {q : ℕ} {laid : Array ℕ} {F G : Fork} {C D : Ctx}
    {x : Aff × Array ℕ} (val : Model.Seg → K)
    (hLine : ∀ g ∈ (R.L.calls.getD q default).segs, ∀ a G' D',
      Ok (Model.Head.LINE R g.name) F C a G' D' → G' = F ∧ D' = C ∧ a.value ρ W = val g)
    (h : Ok (Model.Head.keyForm R q laid) F C x G D) :
    G = F ∧ D = C ∧ ∃ weighed,
      (R.L.calls.getD q default).segs.foldlM (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some weighed ∧
      x.1.value ρ W =
        ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0)) *
            padSum ρ (Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)) weighed
              (R.L.calls.getD q default).J +
          (if q = R.x.qN then W.slot R.x.tN.sCl else 0) +
          ((R.L.calls.getD q default).segs.map fun g => val g).sum := by
  unfold Model.Head.keyForm at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨⟨lines, weighed⟩, F1, C1, h1, h2⟩ := h
  have i1 := ok_forIn_pre _ (R.L.calls.getD q default).segs
    (fun pre (b : MProd Aff (Array ℕ)) F' C' => F' = F ∧ C' = C ∧
      b.1.value ρ W = (pre.map fun g => val g).sum ∧
      pre.foldlM (fun w g => Model.Head.markColumns R w g)
        (Array.replicate (R.L.calls.getD q default).J 0) = some b.2)
    (by
      rintro pre g ⟨ln, wd⟩ F2 C2 r F3 C3 ⟨post, hpost⟩ ⟨rfl, rfl, hv, hm⟩ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨a, F4, C4, h3, h4⟩ := hr
      obtain ⟨rfl, rfl, ha⟩ := hLine g (by rw [hpost]; simp) a F4 C4 h3
      rw [ok_bind] at h4
      obtain ⟨w', F5, C5, h5, h6⟩ := h4
      rw [ok_lift, getAs_ok] at h5
      obtain ⟨⟨hw, rfl⟩, rfl⟩ := h5
      rw [ok_bind] at h6
      obtain ⟨_, F6, C6, h7, h8⟩ := h6
      rw [ok_pure] at h7 h8
      obtain ⟨_, rfl, rfl⟩ := h7
      obtain ⟨rfl, rfl, rfl⟩ := h8
      refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
      · show (ln + a).value ρ W = _
        rw [Aff.value_add, hv, ha, List.map_append, List.sum_append]
        simp
      · show (pre ++ [g]).foldlM _ _ = some w'
        rw [List.foldlM_append, hm]
        simpa using hw)
    (R.L.calls.getD q default).segs [] ⟨{}, Array.replicate (R.L.calls.getD q default).J 0⟩ F C
    ⟨lines, weighed⟩ F1 C1 rfl ⟨rfl, rfl, by simp [Aff.value_empty], rfl⟩ h1
  obtain ⟨rfl, rfl, hlines, hmarks⟩ := i1
  dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨⟨laid', padW⟩, F2, C2, h3, h4⟩ := h2
  have i2 := ok_forIn_range (R.L.calls.getD q default).J _
    (fun j (b : MProd (Array ℕ) E) F' C' => F' = F1 ∧ C' = C1 ∧
      ρ.val b.2 = padSum ρ (Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)) weighed j)
    (by
      rintro j ⟨ld, pw⟩ F3 C3 r F4 C4 _ ⟨rfl, rfl, hp⟩ hr
      try dsimp only at hr
      have tail : ∀ (ld : Array ℕ) (p : E) (r : ForInStep (MProd (Array ℕ) E)) (F5 : Fork)
          (C5 : Ctx),
          Ok (if (weighed.getD j 0 != 1) = true then
              (liftM (Model.mustAs "internal-h-join-place"
                (decide (R.x.g1.shape.first.getD q 0 +
                  j / 2 ^ (R.x.g1.shape.dT - R.h.lt) < ld.size))) : SubM Unit) >>= fun _ =>
                (pure PUnit.unit : SubM PUnit) >>= fun _ =>
                  pure (ForInStep.yield (⟨ld.modify (R.x.g1.shape.first.getD q 0 +
                    j / 2 ^ (R.x.g1.shape.dT - R.h.lt)) fun x => x + R.h.T, p⟩ :
                      MProd (Array ℕ) E))
            else (pure PUnit.unit : SubM PUnit) >>= fun _ =>
              pure (ForInStep.yield (⟨ld, p⟩ : MProd (Array ℕ) E))) F3 C3 r F5 C5 →
          F5 = F3 ∧ C5 = C3 ∧ ∃ ld', r = ForInStep.yield ⟨ld', p⟩ := by
        intro ld p r F5 C5 ht
        split at ht
        · rw [ok_bind] at ht
          obtain ⟨_, F6, C6, t1, t2⟩ := ht
          rw [ok_lift, mustAs_ok] at t1
          obtain ⟨⟨_, rfl⟩, rfl⟩ := t1
          rw [ok_bind] at t2
          obtain ⟨_, F7, C7, t3, t4⟩ := t2
          rw [ok_pure] at t3 t4
          obtain ⟨_, rfl, rfl⟩ := t3
          obtain ⟨rfl, rfl, rfl⟩ := t4
          exact ⟨rfl, rfl, _, rfl⟩
        · rw [ok_bind] at ht
          obtain ⟨_, F6, C6, t1, t2⟩ := ht
          rw [ok_pure] at t1 t2
          obtain ⟨_, rfl, rfl⟩ := t1
          obtain ⟨rfl, rfl, rfl⟩ := t2
          exact ⟨rfl, rfl, _, rfl⟩
      split at hr
      · rename_i hz
        rw [ok_bind] at hr
        obtain ⟨_, F6, C6, t1, t2⟩ := hr
        rw [ok_pure] at t1
        obtain ⟨_, rfl, rfl⟩ := t1
        obtain ⟨rfl, rfl, ld', rfl⟩ := tail _ _ _ _ _ t2
        refine ⟨_, rfl, rfl, rfl, ?_⟩
        show ρ.val (addE pw _) = _
        have hz' : weighed.getD j 0 = 0 := by simpa using hz
        unfold padSum at hp ⊢
        rw [ρ.add, hp, Finset.sum_range_succ, if_pos hz']
      · rename_i hz
        rw [ok_bind] at hr
        obtain ⟨_, F6, C6, t1, t2⟩ := hr
        rw [ok_pure] at t1
        obtain ⟨_, rfl, rfl⟩ := t1
        obtain ⟨rfl, rfl, ld', rfl⟩ := tail _ _ _ _ _ t2
        refine ⟨_, rfl, rfl, rfl, ?_⟩
        show ρ.val pw = _
        have hz' : ¬ weighed.getD j 0 = 0 := by simpa using hz
        unfold padSum at hp ⊢
        rw [hp, Finset.sum_range_succ, if_neg hz', add_zero])
    (b := ⟨laid, zeroE⟩) ⟨rfl, rfl, by simp [padSum, ρ.zero]⟩ h3
  obtain ⟨rfl, rfl, hpad⟩ := i2
  dsimp only at h4
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  refine ⟨rfl, rfl, weighed, hmarks, ?_⟩
  show (_ + lines).value ρ W = _
  rw [Aff.value_add, hlines]
  congr 1
  by_cases hq : q = R.x.qN
  · have hb : (q == R.x.qN) = true := by simpa using hq
    rw [if_pos hb, if_pos hq, Aff.value_add, Aff.value_ofConst, Aff.value_slot, scaleE_val, hpad]
  · have hb : ¬ (q == R.x.qN) = true := by simpa using hq
    rw [if_neg hb, if_neg hq, Aff.value_ofConst, scaleE_val, hpad, add_zero]

end Call

#print axioms ok_forIn_pre
#print axioms keyForm_value

end OnBytes.Road.Hd
