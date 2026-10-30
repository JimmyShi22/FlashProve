-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoBoxSlots.lean.
The slots of the calls' lookup lie inside the plan's number of slots; so its mask entries are one to
one.

A plan counts the scalars that its sub-proof is sent. The first term of each of the three counts
(Layer.slotsOf, Attention.ownScalars, Head.slotsH) is Forest.elems of the calls' lookup's record,
the number of scalars of that lookup.

Main names:
  `planG_elems`, `planA_elems`, `planH2_elems`: where the plan's routine returns: Forest.elems of
    the lookup's record is at most the plan's number of slots.
  `public_elems`: so at the members of X.G and X.A and at X.H, where Verify.publicOf returns X.
  `mkA_inj`, `mkH_inj`: at attention's and the head's records with the bounds written
    (Fo.Pub2.lookPubA1, lookPubH1, OnBytes/Tie/Pv/Lookup/Ends/FoBoxAH.lean), where Verify.publicOf
    returns X: the layout's mask entries of two slots below Forest.elems are equal only if the slots
    are.
Does not say: that the lookup reads the mask entries of the slots below Forest.elems alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoBoxAH
import OnBytes.Tie.Pv.Lookup.Ends.FoNext0

set_option autoImplicit false

namespace Fo.Pub2
open Cb Cb.Fo OnBytes OnBytes.Model OnBytes.Ends Fo.Pub
open Fo.BatRows (bindE_ok ite_ok)

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (cases e; done)
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

theorem planG_elems (P : Layer.Pub) (g : Nat) (O : Option Layer.HPlan2) (hp : Layer.HPlan2)
    (h : Layer.planG P g O = .ok hp) : Forest.elems P.y.fo ≤ hp.ns := by
  unfold Layer.planG at h
  obtain ⟨⟨mats, txOf, ft⟩, _, h⟩ := bindE_ok h
  obtain ⟨tl, hS, h⟩ := bindE_ok h
  obtain ⟨⟨tl1, Fp, Tp⟩, hA, h⟩ := bindE_ok h
  have k : Forest.elems P.y.fo ≤ Layer.slotsOf P.y P.rd g P.wsLay.lk tl.smallElems := by
    unfold Layer.slotsOf
    dsimp only
    omega
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

theorem planA_elems (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (a : Attention.Plan) (e : Attention.plan settings i cf = .ok a) :
    Forest.elems a.fs ≤ a.ns := by
  unfold Attention.plan at e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨⟨S, fs⟩, hS, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam0, h0, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  split at e
  · dead
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨seam, h1, e⟩ := bindE_ok e
  cases e
  show Forest.elems fs ≤ Attention.ownScalars S fs (Attention.Counts.of S) + seam0.smallElems
  unfold Attention.ownScalars
  dsimp only
  omega

theorem planH2_elems (g : Settings) (h : Head.Shape) (L : Head.HL) (b : Head.Border)
    (O : Head.Owner) (NGr lkW : Nat) (hp : Head.HPlanH2)
    (e : Head.planH2 g h L b O NGr lkW = .ok hp) : Forest.elems L.fs ≤ hp.ns := by
  unfold Head.planH2 at e
  repeat obtain ⟨_, _, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl, hS, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨⟨tl1, Fp, Tp⟩, hA, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    obtain ⟨tl2, hO, e⟩ := bindE_ok e
    obtain ⟨_, _, e⟩ := bindE_ok e
    cases e
    show Forest.elems L.fs ≤ Head.slotsH h L tl lkW
    unfold Head.slotsH
    omega
  · obtain ⟨_, hx, _⟩ := bindE_ok e
    cases hx

section
variable {M₀ : Type} {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_elems (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → Forest.elems X.layers.y.fo ≤ hp.ns) ∧
      (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → Forest.elems a.fs ≤ a.ns) ∧
      Forest.elems X.HLy.fs ≤ X.H.ns := by
  refine ⟨fun g hp hg => planG_elems X.layers g _ hp (public_G h g hp hg), fun g a hg => ?_, ?_⟩
  · obtain ⟨sc, lines, cf, a0, -, -, -, m2, e3, -, -⟩ := public_A h g a hg
    rw [e3]
    exact planA_elems _ _ cf a0 m2
  · obtain ⟨H0, h0, e⟩ := public_H h
    rw [e]
    exact planH2_elems _ _ _ _ _ _ _ H0 h0

theorem mkA_inj (rdA : M₀ → IxA → Cb.Gl.E) (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ)
    (a : Attention.Plan) (hg : X.A[g]? = some a) (St : Type) {s s' : ℕ}
    (hs : s < Forest.elems a.fs) (hs' : s' < Forest.elems a.fs)
    (e : (lookPubA1 rdA a St).L.mkS s = (lookPubA1 rdA a St).L.mkS s') : s = s' := by
  have k := (public_elems h).2.1 g a hg
  have n0 := (Fo.Next0.planned_next0 h).2 g a hg
  have := maskJ_inj (j := a.seam.Fp.next + s) (j' := a.seam.Fp.next + s') (by omega) (by omega) e
  omega

theorem mkH_inj (rdH : M₀ → IxH → Cb.Gl.E) (h : Verify.publicOf pol KL layout = .ok X)
    {St : Type} (rq : St → Head.Covered × Array ℕ) (wR wC : ℕ) {s s' : ℕ}
    (hs : s < Forest.elems X.HLy.fs) (hs' : s' < Forest.elems X.HLy.fs)
    (e : (lookPubH1 rdH X rq wR wC).L.mkS s = (lookPubH1 rdH X rq wR wC).L.mkS s') : s = s' := by
  have k := (public_elems h).2.2
  have := maskH_inj (j := 0 + s) (j' := 0 + s') (by omega) (by omega) e
  omega

end

end Fo.Pub2
