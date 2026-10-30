-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoDoorRows.lean.
Where doorH n returns on a view, the entry of the round that was closed last counts
F.planClaimsF + n rows. n is the number that the caller passes: any number here.

doorH (OnBytes/Model/Trees.lean) is called when all claims of a sub-proof have been added. This file
says what a call of it that returns has tested, in terms of the state F and the context c from which
it was called.

Main names:
  `doorH_rows`: if doorH n L F c = .ok r, then F.planClaimsF is not 0; F.nClaim = F.planClaimsF;
    the state that is left is F with the door's mark set; and Blk.requireRows (F.nClaim + n) has
    returned from the very context c.
  `requireRows_view`: on a view, where Blk.requireRows rows returns, the entry of the round that was
    closed last counts that many rows.
  `doorH_view`: the two together: on a view there is an entry e with c.ch.last = some e and
    e.rows = F.planClaimsF + n.
  `lbind_ok`, `sub_ok`, `linkMustAs_ok`, `linkFork_ok`, `linkCall_fork`: when a link's routine
    returns.
Does not say: that the round closed last before the call is the round of the batching element; that
F.planClaimsF is the plan's number of claims; that n is the number that the plan has added, or the
number of indices that the smallness test's equations take; anything on the equation (terms,
coefficients on the mask row, target) that doorH passes to the chain. Nothing on the dry run's
entry.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoHushLink
import OnBytes.Tie.Pv.Lookup.Ends.FoTallyDoor

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α β : Type}

theorem lbind_ok (x : LinkM α) (f : α → LinkM β) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((β × LinkCtx) × Fork) × Ctx) :
    (x >>= f) L F c = .ok r ↔
      ∃ a L1 F1 c1, x L F c = .ok (((a, L1), F1), c1) ∧ f a L1 F1 c1 = .ok r := by
  show (x L >>= fun p => f p.1 p.2) F c = .ok r ↔ _
  rw [bind_ok]
  constructor
  · rintro ⟨⟨a, L1⟩, F1, c1, h1, h2⟩
    exact ⟨a, L1, F1, c1, h1, h2⟩
  · rintro ⟨a, L1, F1, c1, h1, h2⟩
    exact ⟨(a, L1), F1, c1, h1, h2⟩

theorem HushL.of {x : LinkM α} (hx : HushL x) {L L1 : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x L F c = .ok (((a, L1), G), c')) : G = F ∧ c' = c := hx L F c (a, L1) G c' h

theorem sub_ok (x : SubM α) (L L1 : LinkCtx) (F G : Fork) (c c' : Ctx) (a : α)
    (h : LinkM.sub x L F c = .ok (((a, L1), G), c')) : x F c = .ok ((a, G), c') := by
  have h' : (x >>= fun b => (Pure.pure (b, L) : SubM (α × LinkCtx))) F c = _ := h
  rw [bind_ok] at h'
  obtain ⟨b, F1, c1, h1, h2⟩ := h'
  rw [pure_ok] at h2
  obtain ⟨⟨⟨rfl, -⟩, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h2
  exact h1

end

/-- A public condition in a link's routine: where it returns, the condition holds. -/
theorem linkMustAs_ok {name : String} {b : Bool} {L L1 : LinkCtx} {F G : Fork} {c c' : Ctx}
    {u : Unit} (h : LinkM.mustAs name b L F c = .ok (((u, L1), G), c')) : b = true := by
  have h1 := sub_ok _ _ _ _ _ _ _ _ h
  have h2 : (StateT.lift (mustAs name b) : SubM Unit) F c = .ok ((u, G), c') := h1
  rw [lift_ok] at h2
  obtain ⟨_, _, h3, -⟩ := h2
  unfold OnBytes.Model.mustAs at h3
  split at h3
  · assumption
  · cases h3

/-- The question for the state gives the state. -/
theorem linkFork_ok {L L1 : LinkCtx} {F G A : Fork} {c c' : Ctx}
    (h : LinkM.fork L F c = .ok (((A, L1), G), c')) : A = F := by
  have h1 := sub_ok _ _ _ _ _ _ _ _ h
  rw [ask_ok] at h1
  obtain ⟨a', ha, e⟩ := h1
  obtain rfl := Option.some.inj ha
  exact (congrArg (fun x : (Fork × Fork) × Ctx => x.1.1) e)

/-- A call of the chain's check leaves the sub-proof's state. -/
theorem linkCall_fork {f : ChainCheck → Blk ChainCheck} {L L1 : LinkCtx} {F G : Fork} {c c' : Ctx}
    {u : Unit} (h : LinkM.call f L F c = .ok (((u, L1), G), c')) : G = F := by
  have h' : (SubM.must (L.link == L.check.link) >>= fun _ =>
      (liftM (f L.check) : SubM ChainCheck) >>= fun check =>
        (Pure.pure ((), { L with check := check }) : SubM (Unit × LinkCtx))) F c = _ := h
  rw [bind_ok] at h'
  obtain ⟨_, F1, c1, h1, h'⟩ := h'
  obtain ⟨rfl, rfl⟩ := Hush.must _ _ _ _ _ _ h1
  rw [bind_ok] at h'
  obtain ⟨_, F2, c2, h2, h'⟩ := h'
  have h2' : (StateT.lift (f L.check) : SubM ChainCheck) F1 c1 = _ := h2
  rw [lift_ok] at h2'
  obtain ⟨_, _, -, e⟩ := h2'
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using e
  rw [pure_ok] at h'
  obtain ⟨⟨-, rfl⟩, -⟩ := by simpa [Prod.ext_iff] using h'
  rfl

theorem doorH_rows (n : Nat) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((Unit × LinkCtx) × Fork) × Ctx) (h : doorH n L F c = .ok r) :
    F.planClaimsF ≠ 0 ∧ F.nClaim = F.planClaimsF ∧ r.1.2 = { F with doorShutF := true } ∧
      ∃ c1, Blk.requireRows (F.nClaim + n) c = .ok ((), c1) := by
  obtain ⟨⟨⟨u, Lr⟩, Gr⟩, cr⟩ := r
  unfold doorH at h
  rw [lbind_ok] at h
  obtain ⟨L0, L1, F1, c1, h1, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h1
  rw [lbind_ok] at h
  obtain ⟨_, L2, F2, c2, h2, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h2
  rw [lbind_ok] at h
  obtain ⟨_, L3, F3, c3, h3, h⟩ := h
  have h3' := sub_ok _ _ _ _ _ _ _ _ h3
  rw [change_ok] at h3'
  obtain ⟨G', hG, e3⟩ := h3'
  obtain rfl := Option.some.inj hG
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  rw [lbind_ok] at h
  obtain ⟨_, L4, F4, c4, h4, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h4
  rw [lbind_ok] at h
  obtain ⟨A, L5, F5, c5, h5, h⟩ := h
  obtain rfl := linkFork_ok h5
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h5
  rw [lbind_ok] at h
  obtain ⟨_, L6, F6, c6, h6, h⟩ := h
  have hb := linkMustAs_ok h6
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h6
  rw [lbind_ok] at h
  obtain ⟨_, L7, F7, c7, h7, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h7
  rw [lbind_ok] at h
  obtain ⟨_, L8, F8, c8, h8, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h8
  rw [lbind_ok] at h
  obtain ⟨_, L9, F9, c9, h9, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h9
  rw [lbind_ok] at h
  obtain ⟨_, L10, F10, c10, h10, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h10
  rw [lbind_ok] at h
  obtain ⟨_, L11, F11, c11, h11, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h11
  rw [lbind_ok] at h
  obtain ⟨⟨onMasks, constant⟩, L12, F12, c12, h12, h⟩ := h
  obtain ⟨rfl, rfl⟩ := HushL.of (by hush) h12
  rw [lbind_ok] at h
  obtain ⟨_, L13, F13, c13, h13, h⟩ := h
  have h13' : (StateT.lift (Blk.requireRows _) : SubM Unit) _ _ = _ := sub_ok _ _ _ _ _ _ _ _ h13
  rw [lift_ok] at h13'
  obtain ⟨_, c13', hq, e13⟩ := h13'
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e13
  rw [lbind_ok] at h
  obtain ⟨_, L14, F14, c14, h14, h⟩ := h
  obtain rfl := linkCall_fork h14
  obtain ⟨e15, -⟩ := HushL.of (by hush) h
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hb
  exact ⟨hb.1, hb.2, e15, _, hq⟩

/-- On a view the entry of the round that was closed last counts that many rows. -/
theorem requireRows_view {rows : Nat} {c c1 : Ctx} (h : Blk.requireRows rows c = .ok ((), c1))
    (hv : c.ch.dry = false) : ∃ e, c.ch.last = some e ∧ e.rows = rows := by
  unfold Blk.requireRows at h
  split at h
  · rename_i e he
    rw [hv] at h
    split at h
    · rename_i hb
      exact ⟨e, he, by simpa using hb⟩
    · cases h
  · cases h

theorem doorH_view (n : Nat) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((Unit × LinkCtx) × Fork) × Ctx) (h : doorH n L F c = .ok r) (hv : c.ch.dry = false) :
    ∃ e, c.ch.last = some e ∧ e.rows = F.planClaimsF + n := by
  obtain ⟨-, h2, -, c1, h4⟩ := doorH_rows n L F c r h
  rw [h2] at h4
  exact requireRows_view h4 hv

end Fo
