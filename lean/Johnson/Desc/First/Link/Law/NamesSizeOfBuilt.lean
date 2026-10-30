-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/NamesSizeOfBuilt.lean: A BUILT SEGMENT's LIST OF NAMES HAS AS MANY
ENTRIES AS ITS LIST OF ARRAYS: a law of a text that the verifier runs: a return of `buildLinksH`
(OnBytes/Model/StagesLinks.lean). Six theorems. In the make of Law/NamedOfBuilt.lean beside this
file, whose cuts it calls. No text already in the library turns.
Why. `declareOwn` begins the list as `Array.replicate X.Tp.nt.size …`; `own` and `foreign` turn it
by `namesH` alone, which sets one entry. So its size stays.
  `ownNames_size`, `foreignNames_size`: one step keeps the size. `declareOwn_size`: behind it the
  size is `X.Tp.nt.size`.
  `declareLinks_size`: at every segment that it returns: `X.arrayOf.size = X.Tp.nt.size`.
  `names_size_of_buildLinks`: **the same at a return of `buildLinksH`**, general in what it is
  handed. `names_size_of_built`: at a return of `Verify.builtOf`.
Limits. A size alone: which array bears which name is not said. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Link.Law.NamedOfBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)

theorem ownNames_size {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') : d'.arrayOf.size = d.arrayOf.size := by
  obtain ⟨_, _, _, _, _, _, e, _, _⟩ := own_cut2 h
  rw [e, Array.size_setIfInBounds]

theorem foreignNames_size {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') : s'.1.size = s.1.size := by
  obtain ⟨_, _, _, _, _, hn, _, _, _⟩ := foreign_cut2 h
  rw [(namesH_cut hn).1, Array.size_setIfInBounds]

/-- Behind `declareOwn` the list has as many entries as the list of arrays. -/
theorem declareOwn_size {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    d.arrayOf.size = X.Tp.nt.size := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have I0 : ({ arrayOf := Array.replicate X.Tp.nt.size (noLink, ""), moment := #[#[]] } :
      Declaring).arrayOf.size = X.Tp.nt.size := Array.size_replicate
  have stepOwn : ∀ (done : List (Nat × Nat)) (a : Nat × Nat) (s : Declaring)
      (s' : ForInStep Declaring), s.arrayOf.size = X.Tp.nt.size →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ t.arrayOf.size = X.Tp.nt.size := by
    intro _ a s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    exact ⟨r, (Except.ok.inj e).symm, (ownNames_size e1).trans I⟩
  have I1 : d1.arrayOf.size = X.Tp.nt.size :=
    forIn_done _ (fun _ s => s.arrayOf.size = X.Tp.nt.size) stepOwn _ [] _ _ I0 h1
  have I2 : d2.arrayOf.size = X.Tp.nt.size :=
    forIn_done _ (fun _ s => s.arrayOf.size = X.Tp.nt.size) stepOwn _ [] _ _ I1 h2
  have I3 : d3.arrayOf.size = X.Tp.nt.size := forIn_done _
    (fun (_ : List (Option Nat × Nat)) (s : Declaring) => s.arrayOf.size = X.Tp.nt.size)
    (fun done a s s' I e => by
      split at e
      · obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨r, (Except.ok.inj e).symm, (ownNames_size e1).trans I⟩
      · obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨s, (Except.ok.inj e).symm, I⟩)
    _ [] _ _ I2 h3
  exact (ownNames_size h5).trans ((ownNames_size h4).trans I3)

/-- **At every segment that `declareLinks` returns.** -/
theorem declareLinks_size {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) :
    ∀ (l : Nat) (X : LinkH), named[l]? = some X → X.arrayOf.size = X.Tp.nt.size := by
  unfold declareLinks at h
  dsimp only at h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain rfl : r.snd = named := congrArg Prod.fst (Except.ok.inj h)
  exact forIn_done _
    (fun (_ : List (LinkH × Nat)) (s : MProd (Array FrameLink) (Array LinkH)) =>
      ∀ (l : Nat) (X : LinkH), s.snd[l]? = some X → X.arrayOf.size = X.Tp.nt.size)
    (fun done x s s' I e => by
      obtain ⟨d, hd, e⟩ := exc_bind e
      obtain ⟨s1, h1, e⟩ := exc_bind e
      replace e := exc_guard e
      obtain ⟨_, _, e⟩ := exc_bind e
      refine ⟨_, (Except.ok.inj e).symm, ?_⟩
      have J : s1.1.size = x.1.Tp.nt.size :=
        forIn_done _
          (fun (_ : List (Nat × PlaceF)) (q : Array (Nat × String) × Array FrameLink) =>
            q.1.size = x.1.Tp.nt.size)
          (fun _ y q q' Iq eq => by
            obtain ⟨q1, e1, eq⟩ := exc_bind eq
            obtain ⟨_, _, eq⟩ := exc_bind eq
            exact ⟨q1, (Except.ok.inj eq).symm, (foreignNames_size e1).trans Iq⟩)
          _ [] _ _ (declareOwn_size hd) h1
      intro j Y hY
      have hY' : (s.snd.push { x.1 with arrayOf := s1.1 })[j]? = some Y := hY
      by_cases hj : j < s.snd.size
      · rw [Array.getElem?_push_lt hj, ← Array.getElem?_eq_getElem hj] at hY'
        exact I j Y hY'
      · have hj' : j = s.snd.size := by
          have := (Array.getElem?_eq_some_iff.1 hY').1
          rw [Array.size_push] at this
          omega
        subst hj'
        rw [Array.getElem?_push_size] at hY'
        obtain rfl := Option.some.inj hY'
        exact J)
    links.toList.zipIdx [] ⟨#[], #[]⟩ r (fun l X hX => by simp at hX) hr

/-- **At the maker's own text.** -/
theorem names_size_of_buildLinks {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH), B.links[l]? = some X → X.arrayOf.size = X.Tp.nt.size := by
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨named, declared⟩, h3, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  exact declareLinks_size h3

/-- At a return of `Verify.builtOf`. -/
theorem names_size_of_built {W : Verify.Public} {ch : Verify.Chains} {Bt : LinksH}
    (h : Verify.builtOf W ch = .ok Bt) :
    ∀ (l : Nat) (X : LinkH), Bt.links[l]? = some X → X.arrayOf.size = X.Tp.nt.size := by
  unfold Verify.builtOf at h
  obtain ⟨l0, _, h⟩ := exc_bind h
  exact names_size_of_buildLinks h

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.ownNames_size
#print axioms VerifiableInference.Desc.LinkJoin.foreignNames_size
#print axioms VerifiableInference.Desc.LinkJoin.declareOwn_size
#print axioms VerifiableInference.Desc.LinkJoin.declareLinks_size
#print axioms VerifiableInference.Desc.LinkJoin.names_size_of_buildLinks
#print axioms VerifiableInference.Desc.LinkJoin.names_size_of_built
