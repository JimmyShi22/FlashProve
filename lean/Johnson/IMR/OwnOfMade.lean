--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OwnOfMade.lean: WHAT declareOwn LAYS INTO A LINK's LIST OF NAMES, AND
WHAT NO LATER STEP WRITES OVER, HOLDS AT EVERY BUILT LINK: declareLinks_of_own CARRIED
TO THE THREE PLACES WHERE IT IS SPENT, ONCE, GENERAL IN THE SENTENCE Φ. A law of a text that the
verifier runs. At every o; no scope; no pin. Theorems, proved.



Φ l tl A: a sentence on a link's number, the plan of its closing part, and its list of names. THE
TWO PREMISES ARE declareLinks_of_own's OWN: hown: declareOwn's return gives Φ l X.tl d.arrayOf;
hk: Keeps (an entry that bears a name that is not empty stays) hands Φ on.
  of_buildLinks   at buildLinksH's return: at every link of B.links.
  of_made         where the proof file's public part Z is made: at Z.p.built.links.
  at_ground       at the ground's links (ProofFile.blankBy's value).
THE PROOFS ARE zz_of_buildLinks', zz_of_made's AND zz_at_ground's (ZzNamed.lean), TOKEN FOR
TOKEN, with declareLinks_of_own hown hk in zz_of_declared's place. That file's bytes do not turn:
so these lines stand twice; the three examples at the foot are the calls that its three
theorems become at the clean-up.

OBJECT: no block's text: the maker's. USER: part 5's names "U1" to "U4". LETTERS: Φ.

What is not claimed. That buildLinksH or pub returns at any files. Anything for a sentence that
reads another field of the link than tl and arrayOf (of_made passes through ProofFile.Law.blank, and
at_ground through a change of the routine: both leave these two). No soundness.
-/
import Johnson.IMR.ZzNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Own

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages

variable {Φ : Nat → HTailF2 → Array (Nat × String) → Prop}

/-- **At the maker's own text.** -/
theorem of_buildLinks
    (hown : ∀ (X : LinkH) (l : Nat) (d : Declaring), declareOwn X l = .ok d → Φ l X.tl d.arrayOf)
    (hk : ∀ (l : Nat) (tl : HTailF2) (A A' : Array (Nat × String)), Keeps A A' → Φ l tl A →
      Φ l tl A')
    {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay} {p : Params.First}
    {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH), B.links[l]? = some X → Φ l X.tl X.arrayOf := by
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
  exact declareLinks_of_own hown hk h3 l X hX

/-- **WHERE THE PROOF FILE's PUBLIC PART IS MADE.** At every o. -/
theorem of_made
    (hown : ∀ (X : LinkH) (l : Nat) (d : Declaring), declareOwn X l = .ok d → Φ l X.tl d.arrayOf)
    (hk : ∀ (l : Nat) (tl : HTailF2) (A A' : Array (Nat × String)), Keeps A A' → Φ l tl A →
      Φ l tl A')
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH), Z.p.built.links[l]? = some X → Φ l X.tl X.arrayOf := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  unfold Verify.builtOf at hb
  obtain ⟨l0, _, hb⟩ := exc_bind hb
  intro l X hX
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact of_buildLinks hown hk hb l Y hY

/-- **AT THE GROUND's LINKS.** -/
theorem at_ground
    (hown : ∀ (X : LinkH) (l : Nat) (d : Declaring), declareOwn X l = .ok d → Φ l X.tl d.arrayOf)
    (hk : ∀ (l : Nat) (tl : HTailF2) (A A' : Array (Nat × String)), Keeps A A' → Φ l tl A →
      Φ l tl A')
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : Nat} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    Φ l Xl.tl Xl.arrayOf := by
  obtain ⟨links, e⟩ := Meaning.K2.blank_built hG
  rw [e] at e3
  obtain ⟨hl, e'⟩ := Array.getElem?_eq_some_iff.1 e3
  have hl1 : l < Z.p.built.links.size := by
    rw [Array.size_zipWith] at hl
    omega
  rw [Array.getElem_zipWith] at e'
  rw [← e']
  exact of_made hown hk h l (Z.p.built.links[l]'hl1) (Array.getElem?_eq_getElem hl1)

/-! ### The three sentences on "ZZ" (Johnson/IMR/ZzNamed.lean) as calls -/

example {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay} {p : Params.First}
    {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH), B.links[l]? = some X → X.arrayOf[X.tl.ix.ZZ]? = some (l, "ZZ") :=
  of_buildLinks (Φ := fun l tl A => A[tl.ix.ZZ]? = some (l, "ZZ"))
    (fun _ _ _ hd => declareOwn_zz hd) (fun _ _ _ _ k e => k _ _ _ e (by decide)) h

example {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH), Z.p.built.links[l]? = some X →
      X.arrayOf[X.tl.ix.ZZ]? = some (l, "ZZ") :=
  of_made (Φ := fun l tl A => A[tl.ix.ZZ]? = some (l, "ZZ"))
    (fun _ _ _ hd => declareOwn_zz hd) (fun _ _ _ _ k e => k _ _ _ e (by decide)) h

example {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {mk : ProofFile.LinksBy} {G : ProofFile.Ground}
    (hG : ProofFile.blankBy mk Z = some G) {l : Nat} {Xl : LinkH} (e3 : G.built[l]? = some Xl) :
    Xl.arrayOf[Xl.tl.ix.ZZ]? = some (l, "ZZ") :=
  at_ground (Φ := fun l tl A => A[tl.ix.ZZ]? = some (l, "ZZ"))
    (fun _ _ _ hd => declareOwn_zz hd) (fun _ _ _ _ k e => k _ _ _ e (by decide)) h hG e3

end IM.Own

#print axioms IM.Own.of_buildLinks
#print axioms IM.Own.of_made
#print axioms IM.Own.at_ground
