-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearL.lean: what the verifier's routines for a layers' sub-proof's own messages
have heard where they succeed: the kinds of stages, and the calls of which the routines are made.

As OnBytes/Tie/Pv/Att/HearStages.lean for attention. A layers' sub-proof has three kinds of steps
more: a point that is drawn under another round's name (JOIN); the one element that a product layer
draws last (LINE); and steps that hear nothing and close nothing but may write into the context
beside the channel (a kept intermediate value; the mark of a failed test on values).

Main names:
  `StageL`: one stage: a sumcheck with its riders, its weights and its degree in the further
    variable; a round that batches rows, with scalars of its own or none; a round that draws a
    point, with its name; the round LINE; an idle step.
  `HeardL stages c c'`: the stages were heard one after the other from the context c to c', each by
    the block's own listeners. At an idle step nothing of the context has turned but the kept values
    and the mark of a failed test (`Still`).
  `HeardL.append`.
  `pointR_ok`: SubM.point r n, for any round's name r: one stage, in which n elements are drawn.
  `Still`, `note_still`, `check_still`, `Still.heard`: a kept value and a test on values are idle
    steps.
  `LevelSaid`, `level_heard`: one product layer (levelIn, OnBytes/Model/Psc.lean): two stages, a
    sumcheck without riders and LINE; with the sizes of what was heard, the record's five fields and
    the state.
  `batch_heardL`: a round that batches rows, behind scalars that are still open.

Limits: one direction: from a call's success, from a state whose arrays on slots have their length.
On a view and in the dry run alike. A routine's success does not say that its tests on values held:
a failed one is marked in the context and the routine goes on; of that mark it is said here only
that an idle step neither wipes nor replaces it (`Still`); OnBytes/Tie/Pv/Lay/HearMark.lean carries
"no mark" back along the stages. The typed side is not named here.
-/
import OnBytes.Tie.Pv.Att.HearStages
import OnBytes.Tie.Pv.Att.HearPoint
import OnBytes.Tie.Pv.Psc.Run.PscLayer
import OnBytes.Model.Layer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH batch_ok claimsIn_said closeAs_elems)

/-- One stage. -/
inductive StageL where
  | sum (riders : List E) (ws : List Weight) (dY : Nat) (H : PscH)
  | bat (sent : List E) (rows : Nat) (x : E)
  | point (r : RoundName) (d : Fmt.Drawn)
  | line (tau : E)
  | idle

/-- The second context is the first but for the kept values and the mark of a failed test; and a
mark that stood stands as it was: it is neither wiped nor replaced. -/
def Still (c c' : Ctx) : Prop :=
  ∃ n f, c' = { c with notes := n, failed := f } ∧ (c.failed.isSome → f = c.failed)

theorem Still.refl (c : Ctx) : Still c c := ⟨c.notes, c.failed, rfl, fun _ => rfl⟩

theorem Still.trans {c c1 c2 : Ctx} (h : Still c c1) (h' : Still c1 c2) : Still c c2 := by
  obtain ⟨n, f, rfl, k⟩ := h
  obtain ⟨n', f', rfl, k'⟩ := h'
  refine ⟨n', f', rfl, fun hs => ?_⟩
  have e : f = c.failed := k hs
  have e' : f' = f := k' (by rw [e]; exact hs)
  rw [e', e]

theorem Still.ch {c c1 : Ctx} (h : Still c c1) : c1.ch = c.ch := by
  obtain ⟨n, f, rfl, _⟩ := h
  rfl

/-- No mark behind: none before. -/
theorem Still.mark {c c1 : Ctx} (h : Still c c1) (h1 : c1.failed = none) : c.failed = none := by
  obtain ⟨n, f, rfl, k⟩ := h
  cases hc : c.failed with
  | none => rfl
  | some s =>
    have e : f = c.failed := k (by rw [hc]; rfl)
    have e1 : f = none := h1
    rw [e1, hc] at e
    cases e

/-- The stages were heard one after the other. -/
def HeardL : List StageL → Ctx → Ctx → Prop
  | [], c, c' => c' = c
  | .sum riders ws dY H :: l, c, c' =>
    ∃ c1 c2, Parts c c1 c2 riders H.mu H.eps ws H.rs dY H.sentY H.beta H.v ∧ HeardL l c2 c'
  | .bat sent rows x :: l, c, c' =>
    ∃ c1 c2 c3, (Blk.recvEs sent.length).Yields c sent c1 ∧
      (Blk.closeOne RoundName.batSigma.name .elems 0).Yields c1 x c2 ∧
      (Blk.requireRows rows).Yields c2 () c3 ∧ HeardL l c3 c'
  | .point r d :: l, c, c' =>
    ∃ c1, (Blk.close r.name .elems 0).Yields c d c1 ∧ HeardL l c1 c'
  | .line tau :: l, c, c' =>
    ∃ c1, (Blk.closeOne "LINE" .elems 0).Yields c tau c1 ∧ HeardL l c1 c'
  | .idle :: l, c, c' => ∃ c1, Still c c1 ∧ HeardL l c1 c'

theorem HeardL.append : ∀ (l l' : List StageL) (c c1 c' : Ctx), HeardL l c c1 →
    HeardL l' c1 c' → HeardL (l ++ l') c c'
  | [], _, _, _, _, h, h' => by
    rw [show _ = _ from h] at h'
    exact h'
  | .sum _ _ _ _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, b, h1, h2⟩ := h
    exact ⟨a, b, h1, HeardL.append l l' _ c1 c' h2 h'⟩
  | .bat _ _ _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, b, d, h1, h2, h3, h4⟩ := h
    exact ⟨a, b, d, h1, h2, h3, HeardL.append l l' _ c1 c' h4 h'⟩
  | .point _ _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, h1, h2⟩ := h
    exact ⟨a, h1, HeardL.append l l' _ c1 c' h2 h'⟩
  | .line _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, h1, h2⟩ := h
    exact ⟨a, h1, HeardL.append l l' _ c1 c' h2 h'⟩
  | .idle :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, h1, h2⟩ := h
    exact ⟨a, h1, HeardL.append l l' _ c1 c' h2 h'⟩

/-- The round that draws a point, under any name. -/
theorem pointR_ok (r : RoundName) (n : Nat) (F G : Fork) (c c' : Ctx) (pts : Array E)
    (h : SubM.point r n F c = .ok ((pts, G), c')) :
    G = F ∧ ∃ d : Fmt.Drawn, HeardL [.point r d] c c' ∧
      pts = (d.elems.map E.ofTriple).toArray ∧ d.elems.length = n := by
  unfold SubM.point at h
  obtain ⟨y, e⟩ := (liftY_ok _ _ _ _ _ _).1 h
  unfold trPoint at y
  obtain ⟨_, c0, h0, k0⟩ := (Blk.yields_bind _ _ _ _ _).1 y
  obtain ⟨_, m2⟩ := (mustAs_ok _ _ _ _ _).1 ((Blk.yields_iff _ _ _ _).1 h0)
  obtain ⟨d, c1, h1, k1⟩ := (Blk.yields_bind _ _ _ _ _).1 k0
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 k1
  rw [m2] at h1
  refine ⟨e, d, ⟨c', ?_, rfl⟩, e1, closeAs_elems _ _ _ _ _ _ _ _ h1⟩
  rw [e2]
  exact closeAs_close _ _ _ _ _ _ _ _ h1

/-- A kept intermediate value. -/
theorem note_still (what : String) (x : E) (F G : Fork) (c c' : Ctx) (u : Unit)
    (h : note what x F c = .ok ((u, G), c')) : G = F ∧ Still c c' := by
  obtain ⟨h1, e⟩ := (lift_ok _ _ _ _ _ _).1 h
  refine ⟨e, ?_⟩
  unfold Blk.note at h1
  have e2 := (Prod.mk.inj (Except.ok.inj h1)).2
  rw [← e2]
  split
  · exact ⟨_, c.failed, rfl, fun _ => rfl⟩
  · exact Still.refl c

/-- A test on values: the routine goes on. -/
theorem check_still (name : String) (b : Bool) (F G : Fork) (c c' : Ctx) (u : Unit)
    (h : (liftM (Blk.check name b) : SubM Unit) F c = .ok ((u, G), c')) : G = F ∧ Still c c' := by
  obtain ⟨h1, e⟩ := (lift_ok _ _ _ _ _ _).1 h
  refine ⟨e, ?_⟩
  unfold Blk.check at h1
  split at h1
  · rw [← (Prod.mk.inj (Except.ok.inj h1)).2]
    exact Still.refl c
  · rename_i hb
    rw [← (Prod.mk.inj (Except.ok.inj h1)).2]
    exact ⟨c.notes, _, rfl, fun hs => absurd (by simp [hs]) hb⟩

/-- An idle step. -/
theorem Still.heard {c c' : Ctx} (h : Still c c') : HeardL [.idle] c c' := ⟨c', h, rfl⟩

/-- What one product layer has said: the sizes of what was heard, the record, the state. -/
structure LevelSaid (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) (F G : Fork)
    (o : Level) (H : PscH) : Prop where
  len : order.length = mu
  vars : ∀ v ∈ order, v < mu ∧ mu - 1 - v < rho.size
  rounds : H.rs.length = mu
  two : ∀ x ∈ H.rs, x.1.length = 2
  sentY : H.sentY.length = 2
  vals : H.v.length = 2
  /-- the challenges, each at the place of its variable -/
  r : o.r = placed mu (Array.replicate mu zeroE) order (H.rs.map (·.2))
  sL : o.sL = F.next + (1 + 2 * mu + 2)
  sR : o.sR = o.sL + 1
  /-- the sumcheck's record, with the public part of the start form -/
  psc : ∃ (τ : E) (p : Psc), F.publicPart C = some τ ∧
    Ended p C τ H.mu H.eps F.next (levelWeights mu rho order) H.rs 2 H.sentY H.beta ∧
    o.row = p.rowForm (mulE (H.v.getD 0 zeroE) (H.v.getD 1 zeroE)) {}
  /-- the end values stand under the two slots, with the factor beta; some number of zeros under
  the sumcheck's own slots, with the factor -1 -/
  ends : ∃ (F1 : Fork) (n : Nat), Filled (taken F (1 + 2 * mu + 2 + 2)) F1 o.sL H.v H.beta ∧
    Filled F1 G F.next (List.replicate n zeroE) (subE zeroE oneE)
  sized : Sized G

/-- One product layer. -/
theorem level_heard (mu : Nat) (rho : Array E) (C : Aff) (order : List Nat) (F G : Fork)
    (c c' : Ctx) (o : Level) (h : levelIn mu rho C order F c = .ok ((o, G), c')) (hs : Sized F) :
    ∃ H : PscH, HeardL [.sum [] (levelWeights mu rho order) 2 H, .line o.tau] c c' ∧
      LevelSaid mu rho C order F G o H := by
  obtain ⟨τ, m, eps, rs, sentY, beta, vL, vR, cL, p, F1, a1, a2, a3, a4, a5, a6, a7, _, a9, a10,
    a11, a12, a13, a14, a15, a16⟩ := levelIn_seam mu rho C order F G c c' o h hs
  have hw : (levelWeights mu rho order).length = mu := by
    rw [← a3]
    simp [levelWeights]
  refine ⟨⟨m, eps, rs, sentY, beta, [vL, vR]⟩, ⟨c, cL, a1, c', a2, rfl⟩,
    ⟨a3, a4, a6.trans hw, ?_, a10, rfl, a11, a13, a14, ⟨τ, p, a5, a9, a12⟩, ⟨F1, _, a15, a16⟩,
        a16.sized⟩⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hi' : i < (levelWeights mu rho order).length := by rw [← a6]; exact hi
  have hz : i < ((levelWeights mu rho order).zip rs).length := by
    rw [List.length_zip]
    exact lt_min hi' hi
  have hm := List.getElem_mem hz
  rw [List.getElem_zip] at hm
  have h1 := a7 _ hm
  have h2 : ((levelWeights mu rho order)[i]).d = 3 := by
    simp only [levelWeights, List.getElem_map]
    rfl
  rw [h2] at h1
  exact Nat.succ.inj h1

/-- A round that batches rows, behind scalars that are still open. -/
theorem batch_heardL (n : Nat) (F G : Fork) (c c' : Ctx) (w : Array E)
    (h : SubM.batch n F c = .ok ((w, G), c')) (pre : List E) (c0 : Ctx)
    (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    G = F ∧ ∃ x : E, HeardL [.bat pre n x] c0 c' ∧ w = powers x n := by
  obtain ⟨_, e, x, c1, a1, a2, a3⟩ := batch_ok n F G c c' w h
  exact ⟨e, x, ⟨c, c1, c', h0, a1, a2, rfl⟩, a3⟩

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.pointR_ok
#print axioms OnBytes.Tie.Pv.Lay.note_still
#print axioms OnBytes.Tie.Pv.Lay.check_still
#print axioms OnBytes.Tie.Pv.Lay.level_heard
#print axioms OnBytes.Tie.Pv.Lay.batch_heardL
