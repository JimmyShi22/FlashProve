-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8UNamed.lean: WHICH ARRAY OF A BUILT SEGMENT's LIST OF NAMES BEARS THE NAME OF A VECTOR OF READS: at each n < 4: the array number tree, where tl.ix.U[n]? = some (some tree), bears the segment's own number and the name "U" ++ toString (n + 1), AT EVERY BUILT SEGMENT. A law of a text that the verifier runs: a return of declareLinks (OnBytes/Model/StagesLinks.lean). At every o; no scope; no pin. Five theorems.
  Why. The walk over a segment's arrays (Named.arrays, Johnson/Desc/First/K8/Named.lean: the matrices' trees, then the vectors' over List.range 4) wants the name at every vector, not at the third alone (Johnson/P5J/K8U3Named.lean).
  declareOwn_un     behind declareOwn X l: that file's own invariant over the maker's third loop, read at n. n < 4 IS THE MAKER's "take 4": beyond the fourth it declares nothing.
  un_of_declared    the walk over declareLinks IS CALLED: declareLinks_of_own (Johnson/IMR/ZzNamed.lean).
  un_of_buildLinks · un_of_made · **un_at_ground**: ZzNamed.lean's three proofs (zz_of_buildLinks · zz_of_made · zz_at_ground), word for word, at this sentence.
IS IT IDLE? Where U has no entry at n the law says nothing. By a file of evaluations, which is not named here, the third vector alone stands in the full size's lists: then the law works at n = 2 and is idle at the other three: harmless under a "for all n".
Five of K8U3Named.lean's six theorems are the instances n := 2 of these; no file derives them so.
Limits. That declareLinks, buildLinksH or pub returns at any files is not said. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K8U3Named

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J.K8N

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)
open IM.Own (Keeps own_keeps declareLinks_of_own)

/-- **Behind declareOwn each vector of reads' array bears the segment's number and the vector's name.** -/
theorem declareOwn_un {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    ∀ n tree, n < 4 → X.tl.ix.U[n]? = some (some tree) →
      d.arrayOf[tree]? = some (l, "U" ++ toString (n + 1)) := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have I3 := forIn_done _
    (fun (done : List (Option Nat × Nat)) (s : Declaring) =>
      ∀ p ∈ done, ∀ tree, p.1 = some tree →
        s.arrayOf[tree]? = some (l, "U" ++ toString (p.2 + 1)))
    (fun done a s s' I e => by
      obtain ⟨u, n⟩ := a
      cases u with
      | some tr =>
        obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        obtain ⟨k1, k2⟩ := own_keeps e1
        refine ⟨r, (Except.ok.inj e).symm, fun p hp tree hpt => ?_⟩
        rcases List.mem_append.1 hp with hp | hp
        · exact k1 _ _ _ (I p hp tree hpt) (uName_ne _)
        · obtain rfl := List.mem_singleton.1 hp
          obtain rfl : tr = tree := Option.some.inj hpt
          exact k2
      | none =>
        obtain ⟨_, _, e⟩ := exc_bind e
        refine ⟨s, (Except.ok.inj e).symm, fun p hp tree hpt => ?_⟩
        rcases List.mem_append.1 hp with hp | hp
        · exact I p hp tree hpt
        · obtain rfl := List.mem_singleton.1 hp
          cases hpt)
    _ [] _ _ (fun p hp => by cases hp) h3
  intro n tree hn ht
  have hm : ((some tree, n) : Option Nat × Nat) ∈ [] ++ (X.tl.ix.U.toList.take 4).zipIdx := by
    rw [List.nil_append, List.mk_mem_zipIdx_iff_getElem?, List.getElem?_take_of_lt hn,
      Array.getElem?_toList]
    exact ht
  have e3 : d3.arrayOf[tree]? = some (l, "U" ++ toString (n + 1)) := I3 _ hm tree rfl
  exact (own_keeps h5).1 _ _ _ ((own_keeps h4).1 _ _ _ e3 (uName_ne n)) (uName_ne n)

theorem un_of_declared {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) :
    ∀ (l : Nat) (Y : LinkH), named[l]? = some Y →
      ∀ n tree, n < 4 → Y.tl.ix.U[n]? = some (some tree) →
        Y.arrayOf[tree]? = some (l, "U" ++ toString (n + 1)) :=
  declareLinks_of_own
    (Φ := fun l tl A => ∀ n tree, n < 4 → tl.ix.U[n]? = some (some tree) →
      A[tree]? = some (l, "U" ++ toString (n + 1)))
    (fun _ _ _ hd => declareOwn_un hd)
    (fun _ _ _ _ k e n tree hn ht => k _ _ _ (e n tree hn ht) (uName_ne n)) h

theorem un_of_buildLinks {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH), B.links[l]? = some X →
      ∀ n tree, n < 4 → X.tl.ix.U[n]? = some (some tree) →
        X.arrayOf[tree]? = some (l, "U" ++ toString (n + 1)) := by
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
  intro l X hX
  exact un_of_declared h3 l X hX

theorem un_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH), Z.p.built.links[l]? = some X →
      ∀ n tree, n < 4 → X.tl.ix.U[n]? = some (some tree) →
        X.arrayOf[tree]? = some (l, "U" ++ toString (n + 1)) := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  unfold Verify.builtOf at hb
  obtain ⟨l0, _, hb⟩ := exc_bind hb
  intro l X hX
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact un_of_buildLinks hb l Y hY

/-- **AT THE GROUND's LINKS.** -/
theorem un_at_ground {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : Nat} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    ∀ n tree, n < 4 → Xl.tl.ix.U[n]? = some (some tree) →
      Xl.arrayOf[tree]? = some (l, "U" ++ toString (n + 1)) := by
  obtain ⟨links, e⟩ := Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact un_of_made h l (Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

end P5J.K8N

#print axioms P5J.K8N.declareOwn_un
#print axioms P5J.K8N.un_of_declared
#print axioms P5J.K8N.un_of_buildLinks
#print axioms P5J.K8N.un_of_made
#print axioms P5J.K8N.un_at_ground
