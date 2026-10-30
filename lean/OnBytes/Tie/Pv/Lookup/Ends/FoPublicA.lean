-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean.
The plans of the attention sub-proofs in the byte-level verifier's record of public numbers.

OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean cuts a run of Verify.publicOf. The members of X.A are not
the plans that Attention.plan returns as they are: publicOf first lets Verify.attentionOwners fill,
in each plan's smallness test, the record of the one array that the sub-proof reads of a layer's,
and puts that smallness test into the plan. This file says that a member of X.A is such a plan but
for its smallness test, and that the filling keeps what the number of the smallness test's
equations reads. What is filled in is not stated.

* mapM_at: member number i of what List.mapM returns.
* config_at, group_plan: member number g of the plans of Attention.config is what Attention.plan
  returns at arguments that are named.
* borderMeans_keeps, ownerPlace_keeps, ownerPlaces_fold, owners_keeps: each member of what
  attentionOwners returns stands at the number of a member of what it was given, and has that
  member's matrices and number of combinations of the smallness test (OwnersKept, AlikeTl). That
  it returns as many plans as it was given is not stated.
* public_A: a member a of X.A is a0 but for its smallness test a.seam.tl, where a0 is what
  Attention.plan returns, at arguments named in X's own fields; a.seam.tl has a0's matrices and
  number of combinations. Not handed on: what else attentionOwners wrote into a.seam.tl.
* public_A_rows: so the number of rows of its batching round is its field nLin plus the smallness
  test's equationsF (planA_rows, OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic

set_option autoImplicit false

namespace Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

/-- Member number i of what mapM returns. -/
theorem mapM_at {ε α β : Type} (f : α → Except ε β) : ∀ (l : List α) (r : List β),
    l.mapM f = .ok r → ∀ (i : Nat) (b : β), r[i]? = some b → ∃ x, l[i]? = some x ∧ f x = .ok b
  | [], r, h, i, b, hi => by
    rw [List.mapM_nil] at h
    obtain rfl : [] = r := Except.ok.inj h
    cases hi
  | x :: l, r, h, i, b, hi => by
    rw [List.mapM_cons] at h
    obtain ⟨y, h1, h⟩ := bindE_ok h
    obtain ⟨r', h2, h⟩ := bindE_ok h
    obtain rfl : y :: r' = r := Except.ok.inj h
    cases i with
    | zero =>
      obtain rfl : y = b := Option.some.inj hi
      exact ⟨x, rfl, h1⟩
    | succ j => exact mapM_at f l r' h2 j b hi

/-- A group's plan is what Attention.plan returns. -/
theorem group_plan {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : Nat → Nat}
    {lines : List Attention.Line} {g : Nat} {a : Attention.Plan}
    (h : Attention.group P y s mq lines g = .ok a) :
    ∃ cf, Attention.fill P y s lines g = .ok cf ∧
      Attention.plan P.settings (Attention.inOf P.settings y (mq g) g) cf = .ok a := by
  unfold Attention.group at h
  obtain ⟨cf, h1, h⟩ := bindE_ok h
  obtain ⟨X, h2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl : X = a := Except.ok.inj h
  exact ⟨cf, h1, h2⟩

/-- Member number g of the plans of config. -/
theorem config_at {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : Nat → Nat}
    {c : Attention.Config} (h : Attention.config P y s mq = .ok c) :
    ∃ lines, Attention.readLines P.polCallsA = .ok lines ∧
      ∀ (g : Nat) (a : Attention.Plan), c.plans[g]? = some a →
        Attention.group P y s mq lines g = .ok a := by
  unfold Attention.config at h
  obtain ⟨lines, h1, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨plans, h2, h⟩ := bindE_ok h
  refine ⟨lines, h1, fun g a hg => ?_⟩
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨_, _, h⟩ := bindE_ok h
    obtain rfl := Except.ok.inj h
    obtain ⟨x, hx, hf⟩ := mapM_at _ _ _ h2 g a (by simpa using hg)
    have hx' : x = g := by
      obtain ⟨_, e⟩ := List.getElem?_eq_some_iff.1 hx
      rw [List.getElem_range] at e
      exact e.symm
    rw [hx'] at hf
    exact hf

/-! ### attentionOwners keeps what the number of equations reads -/

/-- The two plans' smallness tests have the same matrices and number of combinations. -/
def AlikeTl (s s0 : Verify.SubPlan) : Prop := s.tl.mats = s0.tl.mats ∧ s.tl.tau = s0.tl.tau

theorem borderMeans_keeps {tl tl' : HTailF2} {iF o i : Nat}
    (h : tl.borderMeans iF o i = .ok tl') : tl'.mats = tl.mats ∧ tl'.tau = tl.tau := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · obtain rfl := Except.ok.inj h
      exact ⟨rfl, rfl⟩

theorem ownerPlace_keeps {g : Nat} {O X X' : Verify.SubPlan}
    (h : Verify.attentionOwnerPlace g O X = .ok X') : AlikeTl X' X := by
  unfold Verify.attentionOwnerPlace at h
  obtain ⟨tl, h1, h⟩ := bindE_ok h
  obtain ⟨own, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Except.ok.inj h
    exact borderMeans_keeps h1

/-- What the loop keeps. -/
def OwnersKept (A out : Array Verify.SubPlan) : Prop :=
  ∀ (i : Nat) (s : Verify.SubPlan), out[i]? = some s → ∃ s0, A[i]? = some s0 ∧ AlikeTl s s0

theorem ownerPlaces_fold (G A : Array Verify.SubPlan) : ∀ (l : List Nat)
    (out r : Array Verify.SubPlan), OwnersKept A out →
    l.foldlM (fun (out : Array Verify.SubPlan) g =>
      match G[g]?, out[g]? with
      | some O, some X => do pure (out.set! g (← Verify.attentionOwnerPlace g O X))
      | _, _ => throw "internal-a-owner-shape") out = .ok r → OwnersKept A r
  | [], out, r, hk, h => by
    obtain rfl : out = r := Except.ok.inj h
    exact hk
  | g :: l, out, r, hk, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨out1, h1, h⟩ := bindE_ok h
    refine ownerPlaces_fold G A l out1 r ?_ h
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
        have a1 := ownerPlace_keeps h2
        exact ⟨s0, e0, a1.1.trans a0.1, a1.2.trans a0.2⟩
      · have e : (out.set! g X')[i]? = out[i]? := by
          simp [Array.set!, Ne.symm hig]
        rw [e] at hi
        exact hk i s hi
    · cases h1

theorem owners_keeps {p4 : Bool} {NGr : Nat} {G A r : Array Verify.SubPlan}
    (h : Verify.attentionOwners p4 NGr G A = .ok r) : OwnersKept A r := by
  unfold Verify.attentionOwners at h
  split at h
  · obtain ⟨_, _, h⟩ := bindE_ok h
    exact ownerPlaces_fold G A _ A r (fun i s hi => ⟨s, hi, rfl, rfl⟩) h
  · obtain rfl : A = r := Except.ok.inj h
    exact fun i s hi => ⟨s, hi, rfl, rfl⟩

/-! ### the members of X.A -/

/-- A member of X.A. -/
theorem public_A {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    ∃ (sc : Layer.Scales) (lines : List Attention.Line) (cf : Attention.Cfg)
      (a0 : Attention.Plan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      Attention.readLines X.P.polCallsA = .ok lines ∧
      Attention.fill X.P X.layers.y sc lines g = .ok cf ∧
      Attention.plan X.P.settings
        (Attention.inOf X.P.settings X.layers.y (midQ X.layers.y g) g) cf = .ok a0 ∧
      a = { a0 with seam := { a0.seam with tl := a.seam.tl } } ∧
      a.seam.tl.mats = a0.seam.tl.mats ∧ a.seam.tl.tau = a0.seam.tl.tau := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := publicOf_cut pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_keeps k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := config_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    refine ⟨sc, lines, cf, a0, k2, l1, m1, m2, rfl, ?_, ?_⟩
    · show s.tl.mats = _
      rw [f2.1, f3]
    · show s.tl.tau = _
      rw [f2.2, f3]
  · simp at e1

/-- So the rows of an attention's batching round. -/
theorem public_A_rows {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : Nat) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    a.own.rows = a.nLin +
      a.seam.tl.equationsF (Attention.tableReads a.S (Attention.Counts.of a.S)) := by
  obtain ⟨_, _, cf, a0, _, _, _, m2, e, hm, ht⟩ := public_A h g a hg
  have e1 : a.own = a0.own := by rw [e]
  have e2 : a.nLin = a0.nLin := by rw [e]
  have e3 : a.S = a0.S := by rw [e]
  rw [e1, e2, e3, equationsF_congr hm ht]
  exact planA_rows _ _ cf a0 m2

end Fo.Pub
