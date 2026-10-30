-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Psc/Run/PscRow.lean: scalars that are received before mu as a prefix of the first
round's message; pscRow on a run; the row that it leaves, in the fields of what Psc.run hands on.

Scalars that stand before mu in the message of the round PSC epsilon are called riders here.

Main names:
  `recvEs_add`: a elements received, then b more, are a + b elements received.
  `hearOne_riders`: k riders received, then the round PSC epsilon heard with the one scalar that is
    left, are that round heard whole, with k + 1 scalars, mu the last.
  `pscRow_ok`: pscRow (OnBytes/Model/Psc.lean) hears nothing. It fills the slots from p.first on,
    one for each coefficient of p.walk, with 0 shown and the factor -1, and returns Psc.rowForm.
  `run_fields`: the fields of what the block's Psc.run hands on that the row is made of.
  `rowForm_of_run`: the model's row written with these fields.
Limits: whether the context from which the riders are received stands at the start of a message is
the caller's to know. One direction only, from a success of the model's routine. Nothing is said on
hiding.
-/
import OnBytes.Tie.Pv.Psc.Run.PscLoops

namespace OnBytes.Model.Road
open OnBytes.Psc (Weight hearOne hearMany hear claimAfter polyAt hidingWalk)

/-! ## (a) The riders -/

theorem recvEsInto_acc : ∀ (n : Nat) (acc out : Array E) (c c' : Ctx),
    (Blk.recvEsInto n acc).Yields c out c' →
    ∃ l : List E, out = acc ++ l.toArray ∧ ∀ acc' : Array E,
      (Blk.recvEsInto n acc').Yields c (acc' ++ l.toArray) c'
  | 0, acc, out, c, c', h => by
    simp only [Blk.recvEsInto] at h
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h
    refine ⟨[], by simp [e1], fun acc' => ?_⟩
    simp only [Blk.recvEsInto]
    exact (Blk.yields_pure _ _ _ _).2 ⟨by simp, e2⟩
  | n + 1, acc, out, c, c', h => by
    simp only [Blk.recvEsInto] at h
    obtain ⟨x, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h
    obtain ⟨l, e1, f⟩ := recvEsInto_acc n _ _ _ _ k1
    refine ⟨x :: l, by rw [e1]; simp, fun acc' => ?_⟩
    simp only [Blk.recvEsInto]
    refine (Blk.yields_bind _ _ _ _ _).2 ⟨x, c1, h1, ?_⟩
    have := f (acc'.push x)
    simpa using this

theorem recvEsInto_add : ∀ (a b : Nat) (acc mid out : Array E) (c c1 c' : Ctx),
    (Blk.recvEsInto a acc).Yields c mid c1 → (Blk.recvEsInto b mid).Yields c1 out c' →
    (Blk.recvEsInto (a + b) acc).Yields c out c'
  | 0, b, acc, mid, out, c, c1, c', h1, h2 => by
    simp only [Blk.recvEsInto] at h1
    obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h1
    rw [e1, e2] at h2
    rw [Nat.zero_add]
    exact h2
  | a + 1, b, acc, mid, out, c, c1, c', h1, h2 => by
    simp only [Blk.recvEsInto] at h1
    obtain ⟨x, c0, h0, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [Blk.recvEsInto]
    exact (Blk.yields_bind _ _ _ _ _).2 ⟨x, c0, h0, recvEsInto_add a b _ mid out c0 c1 c' k1 h2⟩

/-- a elements, then b more: a + b elements. -/
theorem recvEs_add (a b : Nat) (l l' : List E) (c c1 c' : Ctx) (h1 : (Blk.recvEs a).Yields c l c1)
    (h2 : (Blk.recvEs b).Yields c1 l' c') : (Blk.recvEs (a + b)).Yields c (l ++ l') c' := by
  unfold Blk.recvEs at h1 h2 ⊢
  obtain ⟨o1, d1, y1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k1
  obtain ⟨o2, d2, y2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 h2
  obtain ⟨e3, e4⟩ := (Blk.yields_pure _ _ _ _).1 k2
  obtain ⟨t, e5, f⟩ := recvEsInto_acc b _ _ _ _ y2
  rw [e2] at y2 f
  refine (Blk.yields_bind _ _ _ _ _).2 ⟨o1 ++ t.toArray, d2, recvEsInto_add a b _ o1 _ c d1 d2 y1 (f
      o1),
    (Blk.yields_pure _ _ _ _).2 ⟨?_, e4⟩⟩
  rw [e1, e3, e5]
  simp

/-- The riders as a prefix: k scalars received, then the round heard with the one scalar that was
left, are the round "PSC epsilon" heard whole. Its scalars are the riders and then mu. -/
theorem hearOne_riders (k : Nat) (riders : List E) (mu eps : E) (c c1 c' : Ctx)
    (h1 : (Blk.recvEs k).Yields c riders c1)
    (h2 : (hearOne "PSC epsilon" .join 1 0).Yields c1 ([mu], eps) c') :
    (hearOne "PSC epsilon" .join (k + 1) 0).Yields c (riders ++ [mu], eps) c' := by
  unfold hearOne at h2
  obtain ⟨q, d1, y1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 h2
  obtain ⟨g, d2, y2, k2⟩ := (Blk.yields_bind _ _ _ _ _).1 k1
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k2
  obtain ⟨e3, e4⟩ := Prod.mk.inj e1
  rw [← e3] at y1
  rw [← e4, ← e2] at y2
  exact hearOne_of _ _ _ _ _ _ _ _ _ (recvEs_add k 1 riders [mu] c c1 d1 h1 y1) y2

/-! ## (b) pscRow on a run -/

/-- pscRow hears nothing. It puts the coefficients of the hiding polynomial under the slots from
p.first on
(shown 0, factor -1) and returns the form Psc.rowForm. -/
theorem pscRow_ok (p p' : Psc) (S0 : E) (kept row : Aff) (F G : Fork) (c c' : Ctx)
    (h : pscRow p S0 kept F c = .ok (((row, p'), G), c')) :
    c' = c ∧ row = p.rowForm S0 kept ∧ p' = { p with rowMade := true } ∧
      p.rowMade = false ∧ p.started = true ∧ p.vars.isEmpty = false ∧ p.r.size = p.vars.size ∧
      F.hideRun p.first (Array.replicate p.walk.1.length zeroE) (subE zeroE oneE) = some G := by
  unfold pscRow at h
  obtain ⟨_, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨b1, e1, e2⟩ := (must_ok _ _ _ _ _ _).1 h1
  obtain ⟨_, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨b2, e3⟩ := (change_ok _ _ _ _ _ _).1 h2
  obtain ⟨e4, e5, e6⟩ := (pure_ok _ _ _ _ _ _).1 k2
  obtain ⟨e7, e8⟩ := Prod.mk.inj e4
  simp only [Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at b1
  rw [e1, ← e5] at b2
  exact ⟨by rw [e6, e3, e2], e7, e8, b1.1.1.1, b1.1.1.2, b1.1.2, b1.2, b2⟩

/-! ## (c) The row, in the words of what the block hands on -/

/-- The fields of what Psc.run hands on that the row is made of. -/
theorem run_fields (cl : OnBytes.Psc.Claim) (S : OnBytes.Psc.Summand) (fresh : List Slot)
    (h : OnBytes.Psc.Heard) (o : OnBytes.Psc.Out) (ho : OnBytes.Psc.run cl S fresh h = some o) :
    o.rowTarget = subE (claimAfter (OnBytes.Psc.varsOf cl S) h.rounds (addE h.mu (mulE h.eps
        cl.target)))
        (mulE h.eps ((S.coeffs ((h.rounds.map (·.2)).take cl.vars.length) h.values).headD zeroE)) ∧
      o.rowMasks = fresh.zip (hidingWalk ((OnBytes.Psc.varsOf cl S).zip (h.rounds.map (·.2)))).1 ++
        OnBytes.Psc.scaleForm
          (mulE h.eps (hidingWalk ((OnBytes.Psc.varsOf cl S).zip (h.rounds.map (·.2)))).2) cl.masks
              ∧
      o.rowMaps = ((S.coeffs ((h.rounds.map (·.2)).take cl.vars.length) h.values).drop 1).map
        (fun x => mulE h.eps x) ∧
      o.eps = h.eps ∧ o.point = (h.rounds.map (·.2)).take cl.vars.length := by
  unfold OnBytes.Psc.run at ho
  simp only [] at ho
  split at ho
  · have e := Option.some.inj ho
    rw [← e]
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · cases ho

/-- The model's row is made of the block's fields. If S0 is the summand's first coefficient at the
point and the end values, the constant of Psc.rowForm is minus the block's row target, and the
coefficients on the slots from p.first on are those of the block's fresh mask entries. -/
theorem rowForm_of_run (p : Psc) (cl : OnBytes.Psc.Claim) (S : OnBytes.Psc.Summand) (fresh :
    List Slot)
    (h : OnBytes.Psc.Heard) (o : OnBytes.Psc.Out) (kept : Aff)
    (ho : OnBytes.Psc.run cl S fresh h = some o)
    (hc : p.claim = claimAfter (OnBytes.Psc.varsOf cl S) h.rounds (addE h.mu (mulE h.eps
        cl.target)))
    (hw : p.walk = hidingWalk ((OnBytes.Psc.varsOf cl S).zip (h.rounds.map (·.2))))
    (he : p.eps = h.eps) :
    p.rowForm ((S.coeffs o.point h.values).headD zeroE) kept =
      Aff.addMul
        (Aff.addMul
          (addSlots (Aff.ofConst (subE zeroE o.rowTarget)) p.first
            (hidingWalk ((OnBytes.Psc.varsOf cl S).zip (h.rounds.map (·.2)))).1.toArray)
          (Aff.ofConst p.target - p.start)
          (mulE o.eps (hidingWalk ((OnBytes.Psc.varsOf cl S).zip (h.rounds.map (·.2)))).2))
        kept o.eps := by
  obtain ⟨f1, _, _, f4, f5⟩ := run_fields cl S fresh h o ho
  unfold Psc.rowForm
  simp only []
  rw [f1, f4, f5, hc, hw, he]

#print axioms hearOne_riders
#print axioms pscRow_ok
#print axioms rowForm_of_run

end OnBytes.Model.Road
