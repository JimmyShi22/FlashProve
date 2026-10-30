-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoMadePublic.lean: at every record of a lookup's numbers in what
Verify.publicOf returns, the record is what Forest.shape makes of the calls that lie beside it, but
for its numbers of padding keys, which are left as they are (Fo.Made,
OnBytes/Tie/Pv/Lookup/Ends/FoShapes.lean). That the checks pass these calls to the lookup is not
said here: it stands at the doors (OnBytes/Tie/Pv/Lookup/Ends/FoDoorsPlan.lean).

 - planA_shapeHid, planA_made: Attention.plan keeps what shapeHid returns, at the settings' cap.
 - ownerPlace_zkeep, zkeep_trans, ZKept, ownerPlaces_zkeep, owners_zkeep: Verify.attentionOwners,
   which writes into the records of attention's smallness tests, keeps z1, z2, lidb and f9.
 - public_made_G, public_made_tG, public_made_A, public_made_tA, public_made_H, public_made_tH: the
   six kinds of records.
 - public_made: all six, in the words of shapesB_parts
   (OnBytes/Tie/Pv/Lookup/Ends/FoDoorsPlan.lean): from
   Verify.publicOf pol KL layout = .ok X alone.
On publicOf_cut, public_G, public_A, public_H (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean,
OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean) and
publicOf_headLayout (OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean). The walk of attentionOwners' loop
follows OnBytes/Tie/Pv/Lookup/Ends/FoPublicANm.lean's.

Not claimed: that publicOf returns; anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoMadeTail
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

set_option hygiene false in
/-- Closes a goal whose hypothesis e says that a routine which throws has returned. -/
local macro "dead" : tactic => `(tactic| first
  | (obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done)
  | (obtain ⟨_, _, e⟩ := bindE_ok e; obtain ⟨_, e1, _⟩ := bindE_ok e; cases e1; done))

/-- Attention's plan holds what shapeHid returns. -/
theorem planA_shapeHid (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    Attention.shapeHid settings.lidb cf = .ok (P.S, P.fs) ∧ P.settings = settings := by
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
  exact ⟨hS, rfl⟩

theorem planA_made (settings : Settings) (i : Attention.In) (cf : Attention.Cfg)
    (P : Attention.Plan) (e : Attention.plan settings i cf = .ok P) :
    Made (P.S.calls.map (·.call)) P.lid P.fs := by
  obtain ⟨h1, h2⟩ := planA_shapeHid settings i cf P e
  unfold Attention.Plan.lid
  rw [h2]
  exact made_shapeHid h1

/-! ### attentionOwners keeps the smallness test's lookup -/

theorem ownerPlace_zkeep {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : ZKeep X.tl X'.tl := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_zkeep h1

theorem zkeep_trans {a b c : HTailF2} (h1 : ZKeep a b) (h2 : ZKeep b c) : ZKeep a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

/-- What the loop keeps. -/
def ZKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ ZKeep s0.tl s.tl

theorem ownerPlaces_zkeep (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), ZKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → ZKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_zkeep G A l out1 r ?_ h
    split at h1
    · rename_i O X hO hX
      obtain ⟨X', h2, h1⟩ := bindE_ok h1
      obtain rfl := Except.ok.inj h1
      intro i s hi
      by_cases hig : i = g
      · subst hig
        obtain ⟨s0, e0, a0⟩ := hk i X hX
        have hlt : i < out.size := by
          obtain ⟨hl, _⟩ := Array.getElem?_eq_some_iff.1 hX
          exact hl
        have e : (out.set! i X')[i]? = some X' := by
          simp [Array.set!, hlt]
        rw [e] at hi
        obtain rfl := Option.some.inj hi
        exact ⟨s0, e0, zkeep_trans a0 (ownerPlace_zkeep h2)⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_zkeep {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : ZKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_zkeep G A _ A r (fun i s hi => ⟨s, hi, rfl, rfl, rfl, rfl⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, rfl, rfl, rfl, rfl⟩

/-! ### the six kinds of records of X -/

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_made_G (h : Verify.publicOf pol KL layout = .ok X) :
    Made X.y.cl X.y.h.lidb X.y.fo := by
  have e := (publicOf_cut pol KL layout X h).1
  unfold Verify.polLayout at e
  obtain ⟨P, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨y, hy, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨_, e2⟩ := Prod.mk.inj (Except.ok.inj e)
  show Made X.layers.y.cl X.layers.y.h.lidb X.layers.y.fo
  rw [← e2]
  exact made_layout hy

theorem public_made_tG (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) : MadeZ hp.tl :=
  planG_madeZ _ _ _ hp (public_G h g hp hg)

theorem public_made_H (h : Verify.publicOf pol KL layout = .ok X) :
    Made X.HLy.cl X.hS.LIDB X.HLy.fs :=
  made_headLayout (publicOf_headLayout h)

theorem public_made_tH (h : Verify.publicOf pol KL layout = .ok X) : MadeZ X.H.tl := by
  obtain ⟨H0, h1, h2⟩ := public_H h
  rw [h2]
  exact planH2_madeZ _ _ _ _ _ _ _ H0 h1

theorem public_made_A (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) :
    Made (a.S.calls.map (·.call)) a.lid a.fs := by
  obtain ⟨_, _, cf, a0, _, _, _, m2, e, _, _⟩ := public_A h g a hg
  have k := planA_made _ _ cf a0 m2
  rw [e]
  exact k

theorem public_made_tA (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : MadeZ a.seam.tl := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_zkeep k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    show MadeZ s.tl
    rw [f3] at f2
    exact f2.made (planA_madeZ _ _ _ a0 m2)
  · simp at e1

/-- **At every record of a lookup's numbers in what publicOf returns: it is what Forest.shape makes
of the calls beside it, but for its numbers of padding keys.** -/
theorem public_made (h : Verify.publicOf pol KL layout = .ok X) :
    Made X.y.cl X.y.h.lidb X.y.fo ∧
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp →
      Made #[hp.tl.z1.call, hp.tl.z2.call] hp.tl.lidb hp.tl.f9) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a →
      Made (a.S.calls.map (·.call)) a.lid a.fs ∧
      Made #[a.seam.tl.z1.call, a.seam.tl.z2.call] a.seam.tl.lidb a.seam.tl.f9) ∧
    Made X.HLy.cl X.hS.LIDB X.HLy.fs ∧
    Made #[X.H.tl.z1.call, X.H.tl.z2.call] X.H.tl.lidb X.H.tl.f9 :=
  ⟨public_made_G h, fun g hp e => public_made_tG h g hp e,
    fun g a e => ⟨public_made_A h g a e, public_made_tA h g a e⟩, public_made_H h,
    public_made_tH h⟩

end
end Fo.Pub
