-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ZzNamed.lean: WHICH ARRAY OF A BUILT LINK's LEDGER BEARS THE NAME "ZZ": the array
of the smallness test's digits (number tl.ix.ZZ of the link's list) bears the link's own number and
the name "ZZ", AT EVERY BUILT LINK. A law of a text that the verifier runs: a return of
declareLinks (OnBytes/Model/StagesLinks.lean). At every o; no scope; no pin. Theorems, proved.

Compiled with the whole library.

  declareLinks_of_own   THE WALK, ONCE, GENERAL IN WHAT IS KEPT: for every sentence Φ l tl A that
    declareOwn's return gives at (l, X.tl, d.arrayOf), and that Keeps hands on
      (Johnson/IMR/OwnNames.lean: an
    entry that bears a name that is not empty stays): Φ l Y.tl Y.arrayOf at EVERY link Y, number l,
    of declareLinks' return. It is declareLinks_names' own walk (Johnson/IMR/OwnNames.lean) with a
      letter in
    NamedIn's place.
  declareOwn_zz   behind declareOwn X l: arrayOf[X.tl.ix.ZZ]? = some (l, "ZZ"): "own" lays it, and
    the one "own" behind it (at BZ) keeps it.
  zz_of_declared · zz_of_buildLinks · **zz_of_made**   so at every built link: where the proof
    file's public part Z is made: at Z.p.built.links.
  **zz_at_ground**   and at the ground's links (ProofFile.blankBy's value): they are the built ones but
    for their routines (blank_built, Johnson/IMR/OwnSeat.lean).

OBJECT: no block's text: the maker's. USER: Johnson/IMR/NearAtDraw.lean. LETTERS: none.

What is not claimed. That buildLinksH or pub returns at any files. WHICH number tl.ix.ZZ is. Nothing
on another name ("BZ", "U1" to "U4": each would be one more instance of the walk). No soundness.

-/
import Johnson.IMR.OwnNames
import Johnson.IMR.OwnSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Own

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)

/-- **THE WALK OF declareLinks, GENERAL IN WHAT IS KEPT.** -/
theorem declareLinks_of_own {Φ : Nat → HTailF2 → Array (Nat × String) → Prop}
    (hown : ∀ (X : LinkH) (l : Nat) (d : Declaring), declareOwn X l = .ok d → Φ l X.tl d.arrayOf)
    (hk : ∀ (l : Nat) (tl : HTailF2) (A A' : Array (Nat × String)), Keeps A A' → Φ l tl A →
      Φ l tl A')
    {links named : Array LinkH} {NGr : Nat} {p4 : Bool} {declared : Array FrameLink}
    (h : declareLinks links NGr p4 = .ok (named, declared)) :
    ∀ (l : Nat) (Y : LinkH), named[l]? = some Y → Φ l Y.tl Y.arrayOf := by
  unfold declareLinks at h
  dsimp only at h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain rfl : r.snd = named := congrArg Prod.fst (Except.ok.inj h)
  have key := forIn_done _
    (fun (done : List (LinkH × Nat)) (s : MProd (Array FrameLink) (Array LinkH)) =>
      (∀ (j : Nat) (x : LinkH × Nat), done[j]? = some x → x.2 = j) →
        s.snd.size = done.length ∧
          ∀ (l : Nat) (Y : LinkH), s.snd[l]? = some Y → Φ l Y.tl Y.arrayOf)
    (fun done x s s' I e => by
      obtain ⟨d, hd, e⟩ := exc_bind e
      obtain ⟨s1, h1, e⟩ := exc_bind e
      replace e := exc_guard e
      obtain ⟨_, _, e⟩ := exc_bind e
      refine ⟨_, (Except.ok.inj e).symm, fun hidx => ?_⟩
      have hx2 : x.2 = done.length := hidx done.length x (by
        rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl)
      obtain ⟨z2, z3⟩ := I fun j y hy => hidx j y (by
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hy).1]
        exact hy)
      have J : Keeps d.arrayOf s1.1 :=
        forIn_done _
          (fun (_ : List (Nat × PlaceF)) (q : Array (Nat × String) × Array FrameLink) =>
            Keeps d.arrayOf q.1)
          (fun _ y q q' Iq eq => by
            obtain ⟨q1, e1, eq⟩ := exc_bind eq
            obtain ⟨_, _, eq⟩ := exc_bind eq
            exact ⟨q1, (Except.ok.inj eq).symm, Iq.trans (foreign_keeps e1)⟩)
          _ [] _ _ (Keeps.refl _) h1
      refine ⟨by
          show (s.snd.push _).size = (done ++ [x]).length
          rw [Array.size_push, z2, List.length_append]
          rfl, ?_⟩
      intro j Y hY
      have hY' : (s.snd.push { x.1 with arrayOf := s1.1 })[j]? = some Y := hY
      by_cases hj : j < s.snd.size
      · rw [Array.getElem?_push_lt hj, ← Array.getElem?_eq_getElem hj] at hY'
        exact z3 j Y hY'
      · have hj' : j = s.snd.size := by
          have := (Array.getElem?_eq_some_iff.1 hY').1
          rw [Array.size_push] at this
          omega
        subst hj'
        rw [Array.getElem?_push_size] at hY'
        obtain rfl := Option.some.inj hY'
        have hl : s.snd.size = x.2 := by rw [z2, hx2]
        rw [hl]
        exact hk x.2 x.1.tl d.arrayOf s1.1 J (hown x.1 x.2 d hd))
    links.toList.zipIdx [] ⟨#[], #[]⟩ r
    (fun _ => ⟨rfl, fun l Y hY => by simp at hY⟩) hr
  exact (key fun j x hx => by
    rw [List.nil_append, List.getElem?_zipIdx] at hx
    obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    simp).2

/-- **Behind declareOwn the digits' array bears the link's number and the name "ZZ".** -/
theorem declareOwn_zz {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    d.arrayOf[X.tl.ix.ZZ]? = some (l, "ZZ") := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  exact (own_keeps h5).1 _ _ _ (own_keeps h4).2 (by decide)

theorem zz_of_declared {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) :
    ∀ (l : Nat) (Y : LinkH), named[l]? = some Y → Y.arrayOf[Y.tl.ix.ZZ]? = some (l, "ZZ") :=
  declareLinks_of_own (Φ := fun l tl A => A[tl.ix.ZZ]? = some (l, "ZZ"))
    (fun _ _ _ hd => declareOwn_zz hd) (fun _ _ _ _ k e => k _ _ _ e (by decide)) h

/-- At the maker's own text. -/
theorem zz_of_buildLinks {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH), B.links[l]? = some X → X.arrayOf[X.tl.ix.ZZ]? = some (l, "ZZ") := by
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
  exact zz_of_declared h3 l X hX

/-- **WHERE THE PROOF FILE's PUBLIC PART IS MADE.** At every o. -/
theorem zz_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH), Z.p.built.links[l]? = some X →
      X.arrayOf[X.tl.ix.ZZ]? = some (l, "ZZ") := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  unfold Verify.builtOf at hb
  obtain ⟨l0, _, hb⟩ := exc_bind hb
  intro l X hX
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact zz_of_buildLinks hb l Y hY

/-- **AT THE GROUND's LINKS.** -/
theorem zz_at_ground {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : Nat} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    Xl.arrayOf[Xl.tl.ix.ZZ]? = some (l, "ZZ") := by
  obtain ⟨links, e⟩ := Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact zz_of_made h l (Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

end IM.Own

#print axioms IM.Own.declareLinks_of_own
#print axioms IM.Own.declareOwn_zz
#print axioms IM.Own.zz_of_declared
#print axioms IM.Own.zz_of_buildLinks
#print axioms IM.Own.zz_of_made
#print axioms IM.Own.zz_at_ground
