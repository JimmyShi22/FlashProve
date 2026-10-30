-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSite.lean.
Where the byte-level verifier calls a sub-proof's lookup: the state's arrays have their sizes, and
no message of the prover is open.

The statement on the lookup's routine (OnBytes.Model.Forest.pad) has two premises on the caller: the
three arrays of the sub-proof's state have one entry for each slot (`Sized F`), and the run is on a
view with no message open (`Clean c`). The routine is called at four places. This file gives the
ways to take a link's routine apart, and the place in the smallness test.

 * `bindL_ok`, `subL_ok`, `liftL_ok`: "the run returns" for a link's routine: bind, and a
   sub-proof's routine used inside a link.
 * `sized_slots`: behind `Fork.slots` the arrays have their sizes.
 * `stepL`: one line of a link's routine that keeps what lies under the filled slots and stays on
   the view: if it returns from a state with `Sized F` and from a context on a view, it leaves a
   later state whose arrays have their sizes, and a context on a view.
 * `mustAsL_ok`, `slotL_ok`, `fixedBefore_ok`: three lines that leave the link's state, the
   sub-proof's state and the context as they are.
 * `site_Z`: the lookup on the digits (`HTailF2.transcriptF`). If that routine returns r from (L, F,
   c), with `Sized F` and c on a view, then: the draw of the matrix has run from (F, c) itself; the
   commitment (`rootInH`) from where that draw ended, and from L; the lookup's routine from where
   the commitment ended, (F1, c1), to the state and the context of r itself; the record in r is the
   one that the draw returned, with the count of draws, the two slots and the lookup's record filled
   in. And `Sized F1`, `Later F F1`, `Clean c1`: the commitment leaves no message open. Each witness
   is fixed by a run equation whose start is named.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoChanUp
import OnBytes.Tie.Pv.Lookup.Ends.FoKeepsLink
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α β : Type}

theorem bindL_ok (x : LinkM α) (f : α → LinkM β) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((β × LinkCtx) × Fork) × Ctx) :
    (x >>= f) L F c = .ok r ↔
      ∃ a L1 F1 c1, x L F c = .ok (((a, L1), F1), c1) ∧ f a L1 F1 c1 = .ok r := by
  have k := bind_ok (x L) (fun p => f p.1 p.2) F c r
  constructor
  · intro h
    obtain ⟨⟨a, L1⟩, G, c1, h1, h2⟩ := k.1 h
    exact ⟨a, L1, G, c1, h1, h2⟩
  · rintro ⟨a, L1, G, c1, h1, h2⟩
    exact k.2 ⟨(a, L1), G, c1, h1, h2⟩

theorem subL_ok (x : SubM α) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((α × LinkCtx) × Fork) × Ctx) :
    LinkM.sub x L F c = .ok r ↔ ∃ a G c1, x F c = .ok ((a, G), c1) ∧ r = (((a, L), G), c1) := by
  have k := bind_ok x (fun a => (Pure.pure (a, L) : SubM (α × LinkCtx))) F c r
  constructor
  · intro h
    obtain ⟨a, G, c1, h1, h2⟩ := k.1 h
    exact ⟨a, G, c1, h1, (pure_ok _ _ _ _).1 h2⟩
  · rintro ⟨a, G, c1, h1, h2⟩
    exact k.2 ⟨a, G, c1, h1, (pure_ok _ _ _ _).2 h2⟩

theorem liftL_ok (x : SubM α) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((α × LinkCtx) × Fork) × Ctx) :
    (MonadLiftT.monadLift x : LinkM α) L F c = .ok r ↔
      ∃ a G c1, x F c = .ok ((a, G), c1) ∧ r = (((a, L), G), c1) := subL_ok x L F c r

/-- One line of a link's routine. -/
theorem stepL {x : LinkM α} (hk : KeepsL x) (hd : DryL x) {L L' : LinkCtx} {F G : Fork}
    {c c' : Ctx} {a : α} (h : x L F c = .ok (((a, L'), G), c')) (hF : Sized F)
    (hc : c.ch.dry = false) : Sized G ∧ Later F G ∧ c'.ch.dry = false :=
  ⟨(hk L F c (a, L') G c' h hF).2, (hk L F c (a, L') G c' h hF).1,
    (hd L F).out c ((a, L'), G) c' h hc⟩

end

theorem sized_slots (F : Fork) (n : ℕ) : Sized (F.slots n) := by
  simp [Sized, Fork.slots]

/-! ### the lines of the smallness test before its lookup -/

theorem dry_closeAs (name : String) (kind : Fmt.Kind) (a b e : Nat) :
    Dry (closeAs name kind a b e) := by unfold closeAs; dry
theorem dry_trTrits (a b : Nat) : Dry (trTrits a b) := by
  unfold trTrits
  exact Dry.bind (calm_must _ _).dry fun _ => Dry.bind (dry_closeAs _ _ _ _ _) fun _ => Dry.pure _

theorem dryS_drawMatrixF (tl : HTailF2) : DryS tl.drawMatrixF := by
  unfold HTailF2.drawMatrixF
  exact DryS.bind (CalmS.lift (calm_must _ _)).dry fun _ =>
    DryS.bind (DryS.lift (dry_trTrits _ _)) fun _ => (CalmS.pure _).dry

theorem calmL_fixedBefore (tl : HTailF2) : CalmL tl.fixedBeforeTheMatrixF := by
  unfold HTailF2.fixedBeforeTheMatrixF
  exact CalmL.bind CalmL.get fun _ =>
    CalmL.bind (CalmL.sub (CalmS.lift calm_statement)) fun _ => calmL_mustAs _ _

theorem keepsL_mustAs (name : String) (b : Bool) : KeepsL (LinkM.mustAs name b) := by keeps
theorem keepsL_fixedBefore (tl : HTailF2) : KeepsL tl.fixedBeforeTheMatrixF := by keeps
theorem keeps_drawMatrixF (tl : HTailF2) : Keeps tl.drawMatrixF := by keeps

theorem DryL.sub {α : Type} {x : SubM α} (h : DryS x) : DryL (LinkM.sub x) := fun L =>
  DryS.bind (f := fun a => Pure.pure (a, L)) h fun _ => (CalmS.pure _).dry

/-! ### lines that leave the three states as they are -/

theorem mustAsL_ok (name : String) (b : Bool) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((Unit × LinkCtx) × Fork) × Ctx) (h : LinkM.mustAs name b L F c = .ok r) :
    r = ((((), L), F), c) := by
  obtain ⟨_, G, c1, h1, rfl⟩ := (subL_ok _ _ _ _ _).1 h
  cases ((Fo.mustAs_ok name b F c _).1 h1).2.symm
  rfl

theorem slotL_ok (L : LinkCtx) (F : Fork) (c : Ctx) (r : ((Nat × LinkCtx) × Fork) × Ctx)
    (h : LinkM.sub SubM.slot L F c = .ok r) : r = (((F.next, L), F), c) := by
  obtain ⟨a, G, c1, h1, rfl⟩ := (subL_ok _ _ _ _ _).1 h
  obtain ⟨a', e1, e2⟩ := (ask_ok _ _ _ _).1 h1
  cases Option.some.inj e1
  cases e2.symm
  rfl

theorem fixedBefore_ok (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((Unit × LinkCtx) × Fork) × Ctx) (h : tl.fixedBeforeTheMatrixF L F c = .ok r) :
    r = ((((), L), F), c) := by
  unfold HTailF2.fixedBeforeTheMatrixF at h
  obtain ⟨_, L1, F1, c1, h1, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  cases (Except.ok.inj h1 : (((L, L), F), c) = _)
  obtain ⟨_, L2, F2, c2, h2, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨_, G, d, k1, e⟩ := (subL_ok _ _ _ _ _).1 h2
  obtain ⟨_, d', k2, e'⟩ := (lift_ok _ _ _ _).1 k1
  cases (Except.ok.inj k2 : (c.st, c) = _)
  cases e'.symm
  cases e.symm
  exact mustAsL_ok _ _ _ _ _ _ h

/-- The lookup on the digits. The run of the smallness test's messages is taken apart: the draw of
the matrix from the routine's own start; the commitment behind it; the lookup behind that, which
ends in the routine's own end; and the record that the routine returns. -/
theorem site_Z (tl : HTailF2) (L : LinkCtx) (F : Fork) (c : Ctx)
    (r : ((HTailF2 × LinkCtx) × Fork) × Ctx) (h : tl.transcriptF L F c = .ok r) (hF : Sized F)
    (hd : c.ch.dry = false) :
    ∃ (tl' : HTailF2) (F5 F1 : Fork) (c5 c1 : Ctx) (L6 : LinkCtx) (g : Forest.Heard),
      tl.drawMatrixF F c = .ok ((tl', F5), c5) ∧
      rootInH [tl'.ix.ZZ, tl'.ix.BZ] L F5 c5 = .ok ((((), L6), F1), c1) ∧
      Forest.pad #[tl'.z1.call, tl'.z2.call] tl'.f9.pub tl'.lidb F1 c1 = .ok ((g, r.1.2), r.2) ∧
      r.1.1 = ({ tl' with foldDrawn := tl'.foldDrawn + 1, slotA := F.next, slotB := r.1.2.next,
                          heard := some g }, L6) ∧
      Sized F1 ∧ Later F F1 ∧ Clean c1 := by
  unfold HTailF2.transcriptF at h
  obtain ⟨_, L1, F1, c1, h1, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  cases (mustAsL_ok _ _ _ _ _ _ h1).symm
  obtain ⟨_, L2, F2, c2, h2, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  cases (mustAsL_ok _ _ _ _ _ _ h2).symm
  obtain ⟨sA, L3, F3, c3, h3, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  cases (slotL_ok _ _ _ _ h3).symm
  obtain ⟨_, L4, F4, c4, h4, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  cases (fixedBefore_ok _ _ _ _ _ h4).symm
  obtain ⟨tl', L5, F5, c5, h5, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨tl2, G5, d5, k5, e5⟩ := (subL_ok _ _ _ _ _).1 h5
  cases e5
  obtain ⟨_, L6, F6, c6, h6, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨g, L7, F7, c7, h7, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨g', G7, d7, k7, e7⟩ := (subL_ok _ _ _ _ _).1 h7
  cases e7
  obtain ⟨sB, L8, F8, c8, h8, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  cases (slotL_ok _ _ _ _ h8).symm
  cases (pure_ok _ _ _ _).1 h
  obtain ⟨s5, l5, d5'⟩ :=
    stepL (KeepsL.sub (keeps_drawMatrixF _)) (DryL.sub (dryS_drawMatrixF _)) h5 hF hd
  obtain ⟨s6, l6, _⟩ := stepL (KeepsL.rootInH _) (shutL_rootInH _).dry h6 s5 d5'
  have k6 : Clean c6 := (shutL_rootInH _ _ _).out _ _ c6 h6 d5'
  exact ⟨_, _, _, _, _, _, _, k5, h6, k7, rfl, s6, l5.trans l6, k6⟩

end Fo
