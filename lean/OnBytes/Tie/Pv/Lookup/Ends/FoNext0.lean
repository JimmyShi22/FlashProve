-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoNext0.lean.
The planned state of a group of layers and of an attention sub-proof has taken no slot.

A sub-proof numbers the scalars that it is sent: Fork.next is the first free slot. A plan makes its
state from the empty state by HTailF2.addTreesF, which does not move Fork.next (of what else it
writes nothing is said here). So the planned state's next is 0, and the calls' lookup, whose
messages are a sub-proof's first, begins at slot 0.

Main names:
  `t2AddN_next`, `t2AddP_next`, `addTreesF_next`: these routines do not move Fork.next.
  `planG_next0`, `planA_next0`: where Layer.planG returns hp: hp.Fp.next = 0; where Attention.plan
    returns a: a.seam.Fp.next = 0.
  `planned_next0`: where Verify.publicOf returns X: so at every member of X.G and of X.A.
  `planned_door0`: so the state (Fp.fillL.slots ns) has next = 0 (by Fo.slots_next,
    OnBytes/Tie/Pv/Lookup/Ends/FoDoors.lean). That a run of such a sub-proof calls its first lookup
    from that state is not said here: the doors of that file have it.
At the groups of layers and at attention. At the head the like is Fo.slots_nextH, by unfolding. On
the first lookup of a sub-proof alone: nothing on the slot at which the smallness test's begins.
The walks of addTreesF and of the plans follow OnBytes/Tie/Pv/Lookup/Ends/FoAddTrees.lean's and
OnBytes/Tie/Pv/Lookup/Ends/FoPlanSize.lean's.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import OnBytes.Tie.Pv.Lookup.Ends.FoPlanSize
import OnBytes.Tie.Pv.Lookup.Ends.FoDoors

set_option autoImplicit false

namespace Fo.Next0
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 Fo.Pub
open Fo.BatRows (bindE_ok ite_ok)

theorem jp0 {c : Prop} [Decidable c] {e : String} {β : Type}
    {jp : PUnit.{1} → Except String β} {y : β}
    (h : (if c then (throw e >>= jp) else (pure PUnit.unit >>= jp)) = .ok y) :
    jp PUnit.unit = .ok y := by
  by_cases hc : c
  · rw [if_pos hc] at h
    have h' : (Except.error e : Except String β) = .ok y := h
    cases h'
  · rw [if_neg hc] at h
    exact h

theorem forIn0 {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (I : σ → Prop)
    (step : ∀ a s s', I s → f a s = .ok s' → ∃ t, s' = .yield t ∧ I t) :
    ∀ (l : List α) (s r : σ), I s → forIn l s f = .ok r → I r
  | [], s, r, hI, h => by
    rw [List.forIn_nil] at h
    have hr : s = r := Except.ok.inj h
    rw [← hr]
    exact hI
  | a :: l, s, r, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := bindE_ok h
    obtain ⟨t, rfl, hI'⟩ := step a s s' hI hs
    exact forIn0 f I step l t r hI' h

theorem t2AddN_next {F : Fork} {T : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddN F T name R K ec a foreign nv = .ok (got, F', T')) : F'.next = F.next := by
  unfold t2AddN at h
  split at h
  · cases h
  · obtain ⟨_, e2⟩ := Prod.mk.inj (Except.ok.inj h)
    obtain ⟨e2, _⟩ := Prod.mk.inj e2
    subst e2
    rfl

theorem t2AddP_next {F : Fork} {T : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} {F' : Fork} {T' : Tail2}
    (h : t2AddP F T name m k w a foreign = .ok (got, F', T')) : F'.next = F.next := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain ⟨_, e2⟩ := Prod.mk.inj (Except.ok.inj h)
      obtain ⟨e2, _⟩ := Prod.mk.inj e2
      subst e2
      rfl

/-- The routine that lays the arrays does not move the first free slot. -/
theorem addTreesF_next {tl tl' : HTailF2} {F G : Fork} {T T' : Tail2} {nU aTX : Array Nat}
    {hb hbLine : Nat} (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', G, T')) :
    G.next = F.next := by
  unfold addTreesF at h
  have h := jp0 h
  have h := jp0 h
  have h := jp0 h
  have h := jp0 h
  obtain ⟨⟨F1, T1⟩, h1, h⟩ := bindE_ok h
  obtain ⟨⟨F2, T2⟩, h2, h⟩ := bindE_ok h
  obtain ⟨⟨F3, T3⟩, h3, h⟩ := bindE_ok h
  obtain ⟨⟨gotZ, FZ, TZ⟩, hZ, h⟩ := bindE_ok h
  have h := jp0 h
  obtain ⟨⟨gotB, FB, TB⟩, hB, h⟩ := bindE_ok h
  have h := jp0 h
  obtain ⟨⟨F4, T4⟩, h4, h⟩ := bindE_ok h
  have h := jp0 h
  obtain ⟨_, e2⟩ := Prod.mk.inj (Except.ok.inj h)
  obtain ⟨e2, _⟩ := Prod.mk.inj e2
  subst e2
  have K1 : F1.next = F.next := forIn0 _ (fun s : MProd Fork Tail2 => s.1.next = F.next)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      dsimp only at hs
      split at hs
      · obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindE_ok hs
        have hs := jp0 hs
        exact ⟨_, (Except.ok.inj hs).symm, (t2AddN_next hP).trans hI⟩
      · exact ⟨_, (Except.ok.inj hs).symm, hI⟩)
    _ _ _ rfl h1
  have K2 : F2.next = F1.next := forIn0 _ (fun s : MProd Fork Tail2 => s.1.next = F1.next)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindE_ok hs
      have hs := jp0 hs
      exact ⟨_, (Except.ok.inj hs).symm, (t2AddP_next hP).trans hI⟩)
    _ _ _ rfl h2
  have K3 : F3.next = F2.next := forIn0 _ (fun s : MProd Fork Tail2 => s.1.next = F2.next)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindE_ok hs
      have hs := jp0 hs
      exact ⟨_, (Except.ok.inj hs).symm, (t2AddP_next hP).trans hI⟩)
    _ _ _ rfl h3
  have K4 : F4.next = FB.next := forIn0 _ (fun s : MProd Fork Tail2 => s.1.next = FB.next)
    (fun a s s' hI hs => by
      obtain ⟨Fs, Ts⟩ := s
      obtain ⟨⟨got, F', T''⟩, hP, hs⟩ := bindE_ok hs
      have hs := jp0 hs
      exact ⟨_, (Except.ok.inj hs).symm, (t2AddP_next hP).trans hI⟩)
    _ _ _ rfl h4
  rw [K4, t2AddN_next hB, t2AddN_next hZ, K3, K2, K1]

/-! ### the plans -/

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

set_option hygiene false in
/-- Takes the branch of a test in which nothing is thrown. -/
local macro "alive" : tactic => `(tactic|
  (rcases ite_ok e with ⟨_, e⟩ | ⟨_, e⟩; (· dead); obtain ⟨_, _, e⟩ := bindE_ok e))

theorem trimL_next (F : Fork) : F.trimL.next = F.next := rfl

theorem planG_next0 (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : hp.Fp.next = 0 := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  have k : Fp.next = 0 := addTreesF_next hA
  obtain ⟨Tp1, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    obtain ⟨y, hy, h⟩ := bindE_ok h
    obtain ⟨_, _, h⟩ := bindE_ok h
    cases h
    exact k
  · split at h
    · repeat obtain ⟨_, _, h⟩ := bindE_ok h
      cases h
      exact k
    · obtain ⟨_, hx, _⟩ := bindE_ok h
      cases hx

theorem seamPlan_next0 {s s' : Attention.Seam} {nU3 hb hbLine : Nat}
    (e : s.plan nU3 hb hbLine = .ok s') : s'.Fp.next = 0 := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl1, Fp, T⟩, hA, e⟩ := bindE_ok e
  have k : Fp.next = 0 := addTreesF_next hA
  alive
  obtain ⟨_, _, e⟩ := bindE_ok e
  cases e
  exact k

theorem planA_next0 (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (a : Attention.Plan) (e : Attention.plan settings i cf = .ok a) : a.seam.Fp.next = 0 := by
  obtain ⟨seam0, -, h1, -⟩ := BatRows.planA_rows0 settings i cf a e
  exact seamPlan_next0 h1

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **The planned states of the layers' groups and of attention have taken no slot.** -/
theorem planned_next0 (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → hp.Fp.next = 0) ∧
      ∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → a.seam.Fp.next = 0 := by
  refine ⟨fun g hp hg => planG_next0 X.layers g _ hp (public_G h g hp hg), fun g a hg => ?_⟩
  obtain ⟨sc, lines, cf, a0, -, -, -, m2, e3, -, -⟩ := public_A h g a hg
  rw [e3]
  exact planA_next0 _ _ cf a0 m2

/-- So the state from which a run calls the lookup begins at slot 0. -/
theorem planned_door0 (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → (hp.Fp.fillL.slots hp.ns).next = 0) ∧
      ∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a →
        (a.seam.Fp.fillL.slots a.ns).next = 0 :=
  ⟨fun g hp hg => (slots_next hp.Fp hp.ns).trans ((planned_next0 h).1 g hp hg),
    fun g a hg => (slots_next a.seam.Fp a.ns).trans ((planned_next0 h).2 g a hg)⟩

end

end Fo.Next0
