-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTiedLook.lean.
The callers' own routines around the lookup's routines, with the lookup's starts written out.

Each statement: if the caller's routine returns from the state F and the context c, then the
lookup's routine has returned, from a state and a context that are written out as terms of F and c.
* `a_hear_exact`, `g_look_exact`, `h_hear_exact`: Forest.pad in Attention.hear (from F, c), in
  Layer.hearLook (from F, c; it ends where hearLook ends) and in Head.hear (from F.slots hp.ns, c).
  From the state that pad left to the routine's own end state every property that the steps keep
  passes on (`Passes`, OnBytes/Tie/Pv/Lookup/Ends/FoPass.lean).
* `planeLins_exact`: Forest.planeLins is Forest.planeClaims, then the adding of its forms and the
  mark, each from where the one before ended.
* `g_planes_exact`, `h_planes_exact`: in Layer.claimsPlanes and Head.claimPlanes Forest.planeLins
  runs from F, c themselves; the three tables' starts are what the caller's list of tables gives
  under their names.
* `g_own_fo`: the record of the lookup that Layer.hearOwn keeps is the one that it was given.
* `z_objects_exact`: in objectsF of the smallness test Forest.objects runs from F, c, for the record
  that the test keeps; linJoin9 from where it ended; linBits9 from where linJoin9 ended.
Not tied: in the first group the context in which the routine ends; in the last the rest of objectsF
behind linBits9, of which only Passes is said: the record that objectsF returns and the context in
which it ends are tied to nothing here (z_objects_whole, OnBytes/Tie/Pv/Lookup/Ends/FoTiedZ2.lean,
ties them).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTiedG
import OnBytes.Tie.Pv.Lookup.Port.FoReads

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

theorem a_hear_exact (P : Attention.Plan) (F G : Fork) (c c' : Ctx) (f : Attention.First)
    (h : Attention.hear P F c = .ok ((f, G), c')) :
    ∃ (F' : Fork) (c1 : Ctx),
      Forest.pad (P.S.calls.map (·.call)) P.fs.pub P.lid F c = .ok ((f.g, F'), c1) ∧
      Passes F' G := by
  unfold Attention.hear at h
  rw [bind_ok] at h
  obtain ⟨g, F', c1, hp, h⟩ := h
  have hg : f.g = g := by
    refine (?_ : Yields _ fun a : Attention.First => a.g = g) _ _ _ _ _ h
    repeat' first
      | exact Yields.pure rfl
      | (refine Yields.bind fun _ => ?_)
  exact ⟨F', c1, hg ▸ hp, Passes.of h (fun I _ => by inv)⟩

theorem g_look_exact (y : Layer.Lay) (g : ℕ) (F G : Fork) (c c' : Ctx) (fo : Forest.Heard)
    (h : Layer.hearLook y g F c = .ok ((fo, G), c')) :
    Forest.pad y.cl y.fo.pub y.h.lidb F c = .ok ((fo, G), c') := by
  unfold Layer.hearLook at h
  rw [bind_ok] at h
  obtain ⟨fo', F', c1, hp, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨_, F2, c2, h2, h⟩ := h
  obtain ⟨e1, e2⟩ := IdleS.lift (IdleB.mustAs _ _) _ _ _ h2
  rw [pure_ok] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using h
  simp only at e1 e2
  subst e1 e2
  exact hp

theorem h_hear_exact (h : Head.Shape) (L : Head.HL) (hp : Head.HPlanH2) (cov : Head.Covered)
    (plain : Array E) (F G : Fork) (c c' : Ctx) (x : Head.Heard)
    (hr : Head.hear h L hp cov plain F c = .ok ((x, G), c')) :
    ∃ (F' : Fork) (c1 : Ctx),
      Forest.pad L.cl L.fs.pub h.LIDB (F.slots hp.ns) c = .ok ((x.g1, F'), c1) ∧ Passes F' G := by
  unfold Head.hear at hr
  rw [bind_ok] at hr
  obtain ⟨yTok, A1, d1, h1, hr⟩ := hr
  have i1 : IdleS (Head.replyToken plain h.V) := by
    unfold Head.replyToken
    exact IdleS.bind (IdleS.lift (IdleB.mustAs _ _)) fun _ =>
      IdleS.bind (IdleS.lift (IdleB.testAs _ _)) fun _ => IdleS.pure _
  obtain ⟨e1, e2⟩ := i1 _ _ _ h1
  simp only at e1 e2
  subst e1 e2
  rw [bind_ok] at hr
  obtain ⟨_, A2, d2, h2, hr⟩ := hr
  obtain ⟨_, hG, e⟩ := (change_ok _ _ _ _).1 h2
  obtain ⟨⟨-, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  obtain rfl := Option.some.inj hG
  rw [bind_ok] at hr
  obtain ⟨g1, F', c1, hp', hr⟩ := hr
  have hy : x.g1 = g1 := by
    refine (?_ : Yields _ fun a : Head.Heard => a.g1 = g1) _ _ _ _ _ hr
    repeat' first
      | exact Yields.pure rfl
      | (refine Yields.bind fun _ => ?_)
  exact ⟨F', c1, hy ▸ hp', Passes.of hr (fun I _ => by inv)⟩

theorem planeLins_exact (g : Forest.Heard) (lm : ℕ) (bit : ℕ → ℕ → SubM Aff) (pin : ℕ → SubM Aff)
    (F G : Fork) (c c' : Ctx) (h : Forest.planeLins g lm bit pin F c = .ok (((), G), c')) :
    ∃ (planes : Array Aff) (G1 : Fork) (c1 : Ctx) (G2 : Fork) (c2 : Ctx),
      Forest.planeClaims g lm bit pin F c = .ok ((planes, G1), c1) ∧
      (planes.forM SubM.lin : SubM PUnit) G1 c1 = .ok (((), G2), c2) ∧
      Forest.planesAdded g G2 c2 = .ok (((), G), c') := by
  unfold Forest.planeLins at h
  rw [bind_ok] at h
  obtain ⟨planes, G1, c1, h1, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨_, G2, c2, h2, h⟩ := h
  exact ⟨planes, G1, c1, G2, c2, h1, h2, h⟩

theorem g_planes_exact (v : Layer.Env) (fo : Forest.Heard) (F G : Fork) (c c' : Ctx)
    (h : Layer.claimsPlanes v fo F c = .ok (((), G), c')) :
    ∃ tB0 tB1 tP : ℕ, v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧
      v.tabAt "b-pin" = some tP ∧
      Forest.planeLins fo v.y.h.lmb (bitLayer v tB0 tB1) (pinLayer v tP) F c =
        .ok (((), G), c') := by
  rw [claimsPlanes_eq, bind_ok] at h
  obtain ⟨tB0, A1, d1, h1, h⟩ := h
  obtain ⟨_, g1, e1⟩ := (get_ok _ _ _ _).1 h1
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e1
  rw [bind_ok] at h
  obtain ⟨tB1, A2, d2, h2, h⟩ := h
  obtain ⟨_, g2, e2⟩ := (get_ok _ _ _ _).1 h2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e2
  rw [bind_ok] at h
  obtain ⟨tP, A3, d3, h3, h⟩ := h
  obtain ⟨_, g3, e3⟩ := (get_ok _ _ _ _).1 h3
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e3
  exact ⟨_, _, _, g1, g2, g3, h⟩

/-- The start of the head's table of the given name. -/
def hTab (R : Head.Run) (n : String) : Option ℕ := (R.t.tab.find? fun e => e.1 == n).map (·.2.1)

theorem tabAt_exact (R : Head.Run) (n : String) (F G : Fork) (c c' : Ctx) (a : ℕ)
    (h : Head.tabAt R n F c = .ok ((a, G), c')) : hTab R n = some a ∧ G = F ∧ c' = c := by
  unfold Head.tabAt at h
  obtain ⟨a', c1, h1, e⟩ := (lift_ok _ _ _ _).1 h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e
  exact ⟨getAs_some h1, rfl, IdleB.getAs _ _ _ _ h1⟩

theorem h_planes_exact (R : Head.Run) (F G : Fork) (c c' : Ctx)
    (h : Head.claimPlanes R F c = .ok (((), G), c')) :
    ∃ tB0 tB1 tP : ℕ, hTab R "bH-bits-0" = some tB0 ∧ hTab R "bH-bits-1" = some tB1 ∧
      hTab R "bH-pin" = some tP ∧
      Forest.planeLins R.x.g1 R.h.lmbH (bitHead R tB0 tB1) (colHead R tP) F c =
        .ok (((), G), c') := by
  rw [claimPlanes_eq, bind_ok] at h
  obtain ⟨tB0, A1, d1, h1, h⟩ := h
  obtain ⟨g1, rfl, rfl⟩ := tabAt_exact _ _ _ _ _ _ _ h1
  rw [bind_ok] at h
  obtain ⟨tB1, A2, d2, h2, h⟩ := h
  obtain ⟨g2, rfl, rfl⟩ := tabAt_exact _ _ _ _ _ _ _ h2
  rw [bind_ok] at h
  obtain ⟨tP, A3, d3, h3, h⟩ := h
  obtain ⟨g3, rfl, rfl⟩ := tabAt_exact _ _ _ _ _ _ _ h3
  exact ⟨_, _, _, g1, g2, g3, h⟩

theorem Yields.bind2 {α β : Type} {x : SubM α} {f : α → SubM β} {p : α → Prop} {q : β → Prop}
    (hx : Yields x p) (hf : ∀ a, p a → Yields (f a) q) : Yields (x >>= f) q := by
  intro F c b G c' hr
  rw [bind_ok] at hr
  obtain ⟨a, F1, c1, h1, h2⟩ := hr
  exact hf a (hx _ _ _ _ _ h1) _ _ _ _ _ h2

theorem g_norms_fo (P : Layer.Pub) (g : ℕ) (fo : Forest.Heard) :
    Yields (Layer.hearNorms P g fo) fun H => H.fo = fo := by
  unfold Layer.hearNorms
  repeat' first
    | exact Yields.pure rfl
    | (refine Yields.bind fun _ => ?_)
    | split

theorem g_terms_fo (P : Layer.Pub) (H0 : Layer.Heard) :
    Yields (Layer.hearTerms P H0) fun H => H.fo = H0.fo := by
  unfold Layer.hearTerms
  repeat' first
    | exact Yields.pure rfl
    | (refine Yields.bind fun _ => ?_)
    | split

/-- The record of the lookup that hearOwn keeps is the one that it was given. -/
theorem g_own_fo (P : Layer.Pub) (hp : Layer.HPlan2) (g : ℕ) (fo : Forest.Heard) :
    Yields (Layer.hearOwn P hp g fo) fun o => o.H.fo = fo := by
  unfold Layer.hearOwn
  simp only []
  refine Yields.bind fun _ => ?_
  refine Yields.bind2 (g_norms_fo P g fo) fun H0 h0 => ?_
  refine Yields.bind2 (g_terms_fo P H0) fun H h1 => ?_
  have e : H.fo = fo := h1.trans h0
  repeat' first
    | exact Yields.pure e
    | (refine Yields.bind fun _ => ?_)
    | split

theorem IdleS.of {α : Type} {x : SubM α} (hx : IdleS x) {F G : Fork} {c c' : Ctx} {a : α}
    (h : x F c = .ok ((a, G), c')) : G = F ∧ c' = c := hx F c _ h

theorem z_objects_exact (tl tl9 : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl9, G), c')) :
    ∃ (g : Forest.Heard) (Fa : Fork) (ca : Ctx) (tl1 : HTailF2) (G1 : Fork) (c1 : Ctx)
      (tl2 : HTailF2) (G2 : Fork) (c2 : Ctx),
      tl.heard = some g ∧ Forest.objects g F c = .ok (((), Fa), ca) ∧
      tl.linJoin9 Fa ca = .ok ((tl1, G1), c1) ∧ tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2) ∧
      Passes G2 G := by
  unfold HTailF2.objectsF at h
  rw [bind_ok] at h
  obtain ⟨_, _, _, h1, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.lift (IdleB.mustAs _ _)) h1
  rw [bind_ok] at h
  obtain ⟨_, _, _, h2, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.lift (IdleB.mustAs _ _)) h2
  rw [bind_ok] at h
  obtain ⟨_, _, _, h3, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.ask _) h3
  rw [bind_ok] at h
  obtain ⟨_, _, _, h4, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.lift (IdleB.testAs _ _)) h4
  rw [bind_ok] at h
  obtain ⟨g, _, _, h5, h⟩ := h
  obtain ⟨_, g5, e5⟩ := (get_ok _ _ _ _).1 h5
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := by simpa [Prod.ext_iff] using e5
  rw [bind_ok] at h
  obtain ⟨_, _, _, h6, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.ask _) h6
  rw [bind_ok] at h
  obtain ⟨_, Fa, ca, h7, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨_, _, _, h8, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.ask _) h8
  rw [bind_ok] at h
  obtain ⟨_, _, _, h9, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.lift (IdleB.mustAs _ _)) h9
  rw [bind_ok] at h
  obtain ⟨_, _, _, h10, h⟩ := h
  obtain ⟨rfl, rfl⟩ := IdleS.of (IdleS.ask _) h10
  rw [bind_ok] at h
  obtain ⟨tl1, G1, c1, h11, h⟩ := h
  rw [bind_ok] at h
  obtain ⟨tl2, G2, c2, h12, h⟩ := h
  exact ⟨_, _, _, tl1, G1, c1, tl2, G2, c2, g5, h7, h11, h12, Passes.of h (fun I _ => by inv)⟩

end Fo
