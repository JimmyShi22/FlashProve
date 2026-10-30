-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K8U3Named.lean: WHICH ARRAY OF A BUILT SEGMENT's LEDGER BEARS THE NAME "U3": the array of the third vector of reads (number tree, where tl.ix.U[2]? = some (some tree)) bears the segment's own number and the name "U3", AT EVERY BUILT SEGMENT. A law of a text that the verifier runs: a return of declareLinks (OnBytes/Model/StagesLinks.lean). At every o; no scope; no pin. Six theorems.
  Why. The named test on sizes of the smallness test (K9.smallSizesB, Johnson/Desc/First/Batch/SmallSizesPlan.lean) reads a built segment's list of names at three sorts of index: the matrices' trees · ZZ's · the third vector's. The first has the names' tie; the second zz_at_ground (Johnson/IMR/ZzNamed.lean); this is the third.
  uName_ne          a vector's name is not empty.
  declareOwn_u3     behind declareOwn X l: its third loop lays (l, "U" ++ toString (n + 1)) at the tree of vector n; the loop's later steps and the two "own" behind it (ZZ, BZ) KEEP it: Keeps (Johnson/IMR/OwnNames.lean) hands on every entry whose name is not empty: namesH REFUSES to write over a named entry: so no premise "the trees are different" is wanted.
  u3_of_declared    THE WALK OVER declareLinks IS CALLED, NOT TYPED ANEW: declareLinks_of_own (Johnson/IMR/ZzNamed.lean) at this sentence.
  u3_of_buildLinks · u3_of_made · **u3_at_ground**: zz_of_buildLinks | zz_of_made | zz_at_ground's proofs, word for word, at this sentence (these three are not general in the sentence).
Is the premise met? tl.ix.U[2]? = some (some _) is the third clause of planFitsB (Johnson/Desc/First/K8/PlanFits.lean), asked at all 25 segments' plans by planFitsAllB: a conjunct of the kind's frozen condition; evaluated true there by others' runs. Where U has no third entry the law is idle.
Limits. That declareLinks, buildLinksH or pub returns at any files is not said. Nothing on the other vectors (the loop's invariant has them; the statements are cut to the third). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.IMR.ZzNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J.K8N

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)
open IM.Own (Keeps own_keeps declareLinks_of_own)

theorem uName_ne (n : Nat) : ("U" ++ toString (n + 1)).isEmpty = false := by
  cases h : ("U" ++ toString (n + 1)).isEmpty with
  | false => rfl
  | true => simp at h

/-- **Behind declareOwn the third vector of reads' array bears the link's number and the name "U3".** -/
theorem declareOwn_u3 {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    ∀ tree, X.tl.ix.U[2]? = some (some tree) → d.arrayOf[tree]? = some (l, "U3") := by
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
  intro tree ht
  have hm : ((some tree, 2) : Option Nat × Nat) ∈ [] ++ (X.tl.ix.U.toList.take 4).zipIdx := by
    rw [List.nil_append, List.mk_mem_zipIdx_iff_getElem?, List.getElem?_take_of_lt (by decide),
      Array.getElem?_toList]
    exact ht
  have eN : "U" ++ toString (2 + 1 : Nat) = "U3" := by decide
  have e3 : d3.arrayOf[tree]? = some (l, "U" ++ toString (2 + 1 : Nat)) := I3 _ hm tree rfl
  rw [eN] at e3
  exact (own_keeps h5).1 _ _ _ ((own_keeps h4).1 _ _ _ e3 (by decide)) (by decide)

theorem u3_of_declared {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) :
    ∀ (l : Nat) (Y : LinkH), named[l]? = some Y →
      ∀ tree, Y.tl.ix.U[2]? = some (some tree) → Y.arrayOf[tree]? = some (l, "U3") :=
  declareLinks_of_own
    (Φ := fun l tl A => ∀ tree, tl.ix.U[2]? = some (some tree) → A[tree]? = some (l, "U3"))
    (fun _ _ _ hd => declareOwn_u3 hd)
    (fun _ _ _ _ k e tree ht => k _ _ _ (e tree ht) (by decide)) h

theorem u3_of_buildLinks {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH), B.links[l]? = some X →
      ∀ tree, X.tl.ix.U[2]? = some (some tree) → X.arrayOf[tree]? = some (l, "U3") := by
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
  exact u3_of_declared h3 l X hX

theorem u3_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH), Z.p.built.links[l]? = some X →
      ∀ tree, X.tl.ix.U[2]? = some (some tree) → X.arrayOf[tree]? = some (l, "U3") := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  unfold Verify.builtOf at hb
  obtain ⟨l0, _, hb⟩ := exc_bind hb
  intro l X hX
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact u3_of_buildLinks hb l Y hY

/-- **AT THE GROUND's LINKS.** -/
theorem u3_at_ground {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : Nat} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    ∀ tree, Xl.tl.ix.U[2]? = some (some tree) → Xl.arrayOf[tree]? = some (l, "U3") := by
  obtain ⟨links, e⟩ := Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact u3_of_made h l (Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

end P5J.K8N

#print axioms P5J.K8N.uName_ne
#print axioms P5J.K8N.declareOwn_u3
#print axioms P5J.K8N.u3_of_declared
#print axioms P5J.K8N.u3_of_buildLinks
#print axioms P5J.K8N.u3_of_made
#print axioms P5J.K8N.u3_at_ground
