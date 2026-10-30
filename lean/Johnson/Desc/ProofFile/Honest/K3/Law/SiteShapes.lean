-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SiteShapes.lean: at each sort of lookup of a public part, the
plan's own structure of the shape, the number lm and the row's sort of lookup (`whoOf`) are the
terms at which keys and bits are shown honest. Theorems.

Terms. Honest/K3/GLOSSARY.md ("keys and bits are honest", "site", "sort"). In this file: `fsOf`
(Honest/K3/LotPublic.lean) is the plan's structure of the shape at a site; `whoOf`
(Honest/K3/LotRow.lean) gives a site's sort of lookup as a value of `Who`.

What is shown, by the file's sections.
  1. `lookAt_calls`, `lookAt_digits`: what `lookAt` gives as fs and lm, by whose link it is.
  2. `site_look`, `sites_look`: the parameters of a site that `siteAt` makes come from `lookAt` at
     the site's own link. `who_calls`: on the calls no round is named.
  3. `site_layers`, `site_attention`, `site_head`, `site_digits`: the four sorts: at each, `fsOf`,
     lm and `whoOf` are the terms named under Users.

Hypotheses that remain. In the four theorems of section 3: that the site is one of the public part's
(`hs`), with its sort and caller (`hd`, `hc`); there is no other. In `lookAt_calls`,
`lookAt_digits`: `h`: `lookAt` returns. In `site_look`: `hs`: `siteAt` returns the site. In
`who_calls`: `hr`: a round is named just where the site is on the digits.

How the proof goes. Both sides go back to one text, the verifier's own split of the links (`lookAt`,
Johnson/Desc/First/Look/LookAt.lean), which this file unfolds.

Users. Honest/K3/Law/MeetsSite.lean [not in this library] asks `L.Meets fs s.p.lm` at fs := `fsOf`
at the site. Honest/K3/WitFill.lean and
Honest/K3/WitDigits.lean show `Meets` at terms that name the caller: X.y.fo and X.y.h.lmb (a group's
layers); fsAt X g and (Hd.shapeA X g).cf.lmb (its attention); X.HLy.fs and X.hS.lmbH (the head);
tl.f9 and 5 (the digits of a link's smallness test, tl its structure). Honest/K3/Law/SiteThere.lean
[not in this library] calls `site_attention`; Honest/K3/Law/Thread/LeftAtCalls.lean calls
`site_layers`; Honest/K3/Law/SiteLawful.lean [not in this library] imports this file.

Limits. Public numbers alone. Nothing is said on keys, bits or summands.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotPublic
import Johnson.Desc.ProofFile.Honest.K3.LotLaw
import Johnson.Desc.ProofFile.Honest.K3.LotRow
import Johnson.Desc.ProofFile.Honest.K3.WitDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Spec
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First.Look (lookAt placeAt)
open OnBytes.HonestTrace (fsAt)
open OnBytes.Road (Hd.shapeA)

/-! ## 1 What lookAt gives -/

/-- On a link's calls: the shape and lm, by whose link it is. -/
theorem lookAt_calls (X : OnBytes.Model.Verify.Public) (i : Nat)
    (pl : VerifiableInference.Desc.First.Look.Place) (h : lookAt X i false = some pl) :
    ((callerOf X.p4 X.NGr i).1 = .head → pl.fs = X.HLy.fs ∧ pl.lm = X.hS.lmbH) ∧
    ((callerOf X.p4 X.NGr i).1 = .layers → pl.fs = X.y.fo ∧ pl.lm = X.y.h.lmb) ∧
    ((callerOf X.p4 X.NGr i).1 = .attention →
      pl.fs = fsAt X (callerOf X.p4 X.NGr i).2 ∧
        pl.lm = (Hd.shapeA X (callerOf X.p4 X.NGr i).2).cf.lmb) := by
  unfold lookAt at h
  unfold callerOf
  dsimp only at h ⊢
  by_cases h1 : (i == (if X.p4 = true then 2 else 1) * X.NGr) = true
  · rw [if_pos h1] at h ⊢
    simp only [Bool.false_eq_true, if_false] at h
    obtain rfl := Option.some.inj h
    exact ⟨fun _ => ⟨rfl, rfl⟩, (fun e => Caller.noConfusion e), (fun e => Caller.noConfusion e)⟩
  · rw [if_neg h1] at h ⊢
    by_cases h2 : (i % (if X.p4 = true then 2 else 1) == 0) = true
    · rw [if_pos h2] at h ⊢
      obtain ⟨hp, _, h⟩ := Option.bind_eq_some_iff.1 h
      simp only [Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      exact ⟨(fun e => Caller.noConfusion e), fun _ => ⟨rfl, rfl⟩,
        (fun e => Caller.noConfusion e)⟩
    · rw [if_neg h2] at h ⊢
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      simp only [Bool.false_eq_true, if_false] at h
      obtain rfl := Option.some.inj h
      refine ⟨(fun e => Caller.noConfusion e), (fun e => Caller.noConfusion e),
        fun _ => ⟨?_, ?_⟩⟩
      · show a.fs = ((X.A[i / (if X.p4 = true then 2 else 1)]?).map (·.fs)).getD default
        rw [ha]
        rfl
      · show a.S.cf.lmb = (Hd.shapeA X (i / (if X.p4 = true then 2 else 1))).cf.lmb
        unfold OnBytes.Road.Hd.shapeA
        rw [ha]
        rfl

/-- On the digits of a link's smallness test: the shape is that of the test's structure; lm is 5. -/
theorem lookAt_digits (X : OnBytes.Model.Verify.Public) (i : Nat)
    (pl : VerifiableInference.Desc.First.Look.Place) (h : lookAt X i true = some pl) :
    pl.fs = (tlOf X i).f9 ∧ pl.lm = 5 := by
  unfold lookAt at h
  unfold tlOf linkH stepOf
  dsimp only at h
  by_cases h1 : (i == (if X.p4 = true then 2 else 1) * X.NGr) = true
  · rw [if_pos h1] at h ⊢
    simp only [if_true] at h
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨rfl, rfl⟩
  · rw [if_neg h1] at h ⊢
    by_cases h2 : (i % (if X.p4 = true then 2 else 1) == 0) = true
    · rw [if_pos h2] at h ⊢
      obtain ⟨hp, hh, h⟩ := Option.bind_eq_some_iff.1 h
      simp only [if_true] at h
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [hh]
      exact ⟨rfl, rfl⟩
    · rw [if_neg h2] at h ⊢
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.1 h
      simp only [if_true] at h
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h
      rw [ha]
      exact ⟨rfl, rfl⟩

/-! ## 2 A site's parameters come from lookAt -/

theorem site_look (X : OnBytes.Model.Verify.Public) (ps : List Spot) (x : Nat × Bool × Place)
    (s : Site) (hs : siteAt X ps x = some s) :
    ∃ pl, lookAt X s.link s.digits = some pl ∧ s.p.lm = pl.lm ∧
      s.caller = (callerOf X.p4 X.NGr s.link).1 ∧ s.group = (callerOf X.p4 X.NGr s.link).2 ∧
      s.rng.isSome = s.digits := by
  have hr := (siteAt_rng X ps x s hs).1
  unfold siteAt at hs
  obtain ⟨p, hp, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.1 hs
  unfold placeAt at hp
  obtain ⟨pl, hpl, rfl⟩ := Option.map_eq_some_iff.1 hp
  dsimp only at hs
  split at hs
  · obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 hs
    exact ⟨pl, hpl, rfl, rfl, rfl, hr⟩
  · obtain rfl := Option.some.inj hs
    exact ⟨pl, hpl, rfl, rfl, rfl, hr⟩

theorem sites_look (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) :
    ∃ pl, lookAt Z.p.X s.link s.digits = some pl ∧ s.p.lm = pl.lm ∧
      s.caller = (callerOf Z.p.X.p4 Z.p.X.NGr s.link).1 ∧
      s.group = (callerOf Z.p.X.p4 Z.p.X.NGr s.link).2 ∧ s.rng.isSome = s.digits := by
  unfold lookSites at hs
  obtain ⟨x, _, hx⟩ := List.mem_filterMap.1 hs
  exact site_look _ _ x s hx

/-! ## 3 The four sorts -/

theorem who_calls (s : Site) (hr : s.rng.isSome = s.digits) (hd : s.digits = false) :
    s.rng = none := by
  rw [hd] at hr
  cases h : s.rng with
  | none => rfl
  | some r => rw [h] at hr; exact absurd hr (by simp)

/-- **A group's layers.** -/
theorem site_layers (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .layers) :
    fsOf Z.p.X s = some Z.p.X.y.fo ∧ s.p.lm = Z.p.X.y.h.lmb ∧ whoOf s = .layers s.group := by
  obtain ⟨pl, h1, h2, h3, _, h5⟩ := sites_look Z s hs
  rw [hd] at h1
  obtain ⟨e1, e2⟩ := (lookAt_calls _ _ pl h1).2.1 (h3.symm.trans hc)
  refine ⟨?_, by rw [h2, e2], ?_⟩
  · unfold fsOf
    rw [hd, h1, ← e1]
    rfl
  · unfold whoOf
    rw [who_calls s h5 hd, hc]

/-- **A group's attention.** -/
theorem site_attention (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .attention) :
    fsOf Z.p.X s = some (fsAt Z.p.X s.group) ∧ s.p.lm = (Hd.shapeA Z.p.X s.group).cf.lmb ∧
      whoOf s = .attention s.group := by
  obtain ⟨pl, h1, h2, h3, h4, h5⟩ := sites_look Z s hs
  rw [hd] at h1
  obtain ⟨e1, e2⟩ := (lookAt_calls _ _ pl h1).2.2 (h3.symm.trans hc)
  refine ⟨?_, by rw [h2, e2, h4], ?_⟩
  · unfold fsOf
    rw [hd, h1, h4, ← e1]
    rfl
  · unfold whoOf
    rw [who_calls s h5 hd, hc]

/-- **The head.** -/
theorem site_head (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = false)
    (hc : s.caller = .head) :
    fsOf Z.p.X s = some Z.p.X.HLy.fs ∧ s.p.lm = Z.p.X.hS.lmbH ∧ whoOf s = .head := by
  obtain ⟨pl, h1, h2, h3, _, h5⟩ := sites_look Z s hs
  rw [hd] at h1
  obtain ⟨e1, e2⟩ := (lookAt_calls _ _ pl h1).1 (h3.symm.trans hc)
  refine ⟨?_, by rw [h2, e2], ?_⟩
  · unfold fsOf
    rw [hd, h1, ← e1]
    rfl
  · unfold whoOf
    rw [who_calls s h5 hd, hc]

/-- **The digits of a link's smallness test.** -/
theorem site_digits (Z : Pub) (s : Site) (hs : s ∈ lookSites Z) (hd : s.digits = true) :
    ∃ r, s.rng = some r ∧ fsOf Z.p.X s = some (tlOf Z.p.X s.link).f9 ∧ s.p.lm = 5 ∧
      whoOf s = .digits s.link r := by
  obtain ⟨pl, h1, h2, _, _, h5⟩ := sites_look Z s hs
  rw [hd] at h1 h5
  obtain ⟨e1, e2⟩ := lookAt_digits _ _ pl h1
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h5
  refine ⟨r, hr, ?_, by rw [h2, e2], ?_⟩
  · unfold fsOf
    rw [hd, h1, ← e1]
    rfl
  · unfold whoOf
    rw [hr]

end ProofFile.Honest.K3.Law.Spec

#print axioms ProofFile.Honest.K3.Law.Spec.lookAt_calls
#print axioms ProofFile.Honest.K3.Law.Spec.lookAt_digits
#print axioms ProofFile.Honest.K3.Law.Spec.site_look
#print axioms ProofFile.Honest.K3.Law.Spec.sites_look
#print axioms ProofFile.Honest.K3.Law.Spec.who_calls
#print axioms ProofFile.Honest.K3.Law.Spec.site_layers
#print axioms ProofFile.Honest.K3.Law.Spec.site_attention
#print axioms ProofFile.Honest.K3.Law.Spec.site_head
#print axioms ProofFile.Honest.K3.Law.Spec.site_digits
