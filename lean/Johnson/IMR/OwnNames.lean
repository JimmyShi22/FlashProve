-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/OwnNames.lean: WHICH ARRAY OF A BUILT LINK's LEDGER BEARS WHICH OWN MATRIX's NAME; AND
SO: «THE DESCRIPTION IS MADE ⟹ namedThere», WITHOUT A PIN. A law of a text that the verifier runs: a
return of buildLinksH (OnBytes/Model/StagesLinks.lean). Statements and proofs. It stands over
Johnson/Desc/First/Link/Law/NamedOfBuilt.lean, whose head says: "WHICH array of a link's ledger
bears WHICH name is not said": here it is said, for the link's own matrices; that file's namesH_cut,
get_set and foreign_cut2 are called.

  Keeps A A'          an entry of A that bears a name that is not empty stands in A' as it was
  namesH_keeps · own_keeps · foreign_keeps   each step keeps, and lays its own entry
  matrixName_ne       a matrix's name is not empty
  ownPairs tl · NamedIn l L A · NamedIn.keep · AllNamed   the letters
  declareOwn_names    behind declareOwn X l: at every pair (tree, mu) of the two lists of own matrices: arrayOf[tree]? = some (l, matrixName mu)
  declareLinks_names · **names_of_buildLinks** · **names_of_made**   so at every built link
  **ownHeld_of_made** OwnHeld (Johnson/IMR/NamedOfHeld.lean) where the public part Z is made: with
    that file's named_of_made
  **namedThere_of_made**   in the goals' scope, at `secondHashFunction`: namedThere from "Z is made" alone

What is not claimed. That buildLinksH or pub returns at any files. Nothing on an array of another link's. Nothing on seatsNamedC. No soundness.

-/
import Johnson.Desc.First.Link.Law.NamedOfBuilt
import Johnson.IMR.NamedOfHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM.Own

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)
open VerifiableInference.Desc.LinkJoin (namesH_cut get_set foreign_cut2 named_of_made)

/-- An entry that bears a name that is not empty stays. -/
def Keeps (A A' : Array (Nat × String)) : Prop :=
  ∀ (τ b : Nat) (nm : String), A[τ]? = some (b, nm) → nm.isEmpty = false → A'[τ]? = some (b, nm)

theorem Keeps.refl (A : Array (Nat × String)) : Keeps A A := fun _ _ _ h _ => h

theorem Keeps.trans {A B C : Array (Nat × String)} (h : Keeps A B) (k : Keeps B C) : Keeps A C :=
  fun τ b nm x e => k τ b nm (h τ b nm x e) e

theorem namesH_keeps {A A' : Array (Nat × String)} {tree born : Nat} {name : String}
    (h : namesH A tree born name = .ok A') : Keeps A A' ∧ A'[tree]? = some (born, name) := by
  obtain ⟨e, hlt, he⟩ := namesH_cut h
  refine ⟨fun τ b nm hx hn => ?_, ?_⟩
  · rw [e, get_set _ _ _ _ hlt]
    by_cases ht : tree = τ
    · subst ht
      have q : nm.isEmpty = true := he _ hx
      rw [hn] at q
      cases q
    · rw [if_neg ht]
      exact hx
  · rw [e, get_set _ _ _ _ hlt, if_pos rfl]

theorem own_keeps {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') :
    Keeps d.arrayOf d'.arrayOf ∧ d'.arrayOf[tree]? = some (l, name) := by
  unfold own at h
  obtain ⟨arrayOf, hn, h⟩ := exc_bind h
  split at h
  · obtain rfl := Except.ok.inj h
    exact namesH_keeps hn
  · cases h

theorem foreign_keeps {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') : Keeps s.1 s'.1 := by
  obtain ⟨born, D, D', name, -, hn, -, -, -⟩ := foreign_cut2 h
  exact (namesH_keeps hn).1

theorem matrixName_ne (mu : Nat) : (matrixName mu).isEmpty = false := by
  unfold matrixName
  cases h : ("M" ++ toString mu).isEmpty with
  | false => rfl
  | true => simp at h

/-- The pairs (array, matrix) of a record's two lists of own matrices. -/
def ownPairs (tl : HTailF2) : List (Nat × Nat) :=
  zipT tl.ix.PK.toList tl.pkMat.toList ++ zipT tl.ix.TX.toList tl.pxMat.toList

/-- Each pair of L bears link l's name for its matrix. -/
def NamedIn (l : Nat) (L : List (Nat × Nat)) (A : Array (Nat × String)) : Prop :=
  ∀ p ∈ L, A[p.1]? = some (l, matrixName p.2)

theorem NamedIn.keep {l : Nat} {L : List (Nat × Nat)} {A A' : Array (Nat × String)}
    (H : NamedIn l L A) (k : Keeps A A') : NamedIn l L A' :=
  fun p hp => k _ _ _ (H p hp) (matrixName_ne _)

/-- **Behind declareOwn each own matrix's array bears the link's number and the matrix's name.** -/
theorem declareOwn_names {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    NamedIn l (ownPairs X.tl) d.arrayOf := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have stepOwn : ∀ (pre done : List (Nat × Nat)) (a : Nat × Nat) (s : Declaring)
      (s' : ForInStep Declaring), NamedIn l (pre ++ done) s.arrayOf →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ NamedIn l (pre ++ (done ++ [a])) t.arrayOf := by
    intro pre done a s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    obtain ⟨k1, k2⟩ := own_keeps e1
    refine ⟨r, (Except.ok.inj e).symm, fun p hp => ?_⟩
    rw [← List.append_assoc] at hp
    rcases List.mem_append.1 hp with hp | hp
    · exact I.keep k1 p hp
    · obtain rfl := List.mem_singleton.1 hp
      exact k2
  have I1 := forIn_done _ (fun done (s : Declaring) => NamedIn l ([] ++ done) s.arrayOf)
    (stepOwn []) _ [] _ _ (fun p hp => by cases hp) h1
  have I2 := forIn_done _
    (fun done (s : Declaring) =>
      NamedIn l (zipT X.tl.ix.PK.toList X.tl.pkMat.toList ++ done) s.arrayOf)
    (stepOwn _) _ [] _ _ (fun p hp => I1 p (by simpa using hp)) h2
  have I2' : NamedIn l (ownPairs X.tl) d2.arrayOf := fun p hp => I2 p (by simpa [ownPairs] using hp)
  have I3 : NamedIn l (ownPairs X.tl) d3.arrayOf := forIn_done _
    (fun (_ : List (Option Nat × Nat)) (s : Declaring) => NamedIn l (ownPairs X.tl) s.arrayOf)
    (fun done a s s' I e => by
      split at e
      · obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨r, (Except.ok.inj e).symm, NamedIn.keep (A := s.arrayOf) I (own_keeps e1).1⟩
      · obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨s, (Except.ok.inj e).symm, I⟩)
    _ [] _ _ I2' h3
  exact (NamedIn.keep (A := d3.arrayOf) I3 (own_keeps h4).1).keep (own_keeps h5).1

/-- At every link of the list: each own matrix's array bears that link's number and the matrix's
name. -/
def AllNamed (named : Array LinkH) : Prop :=
  ∀ (l : Nat) (Y : LinkH), named[l]? = some Y → NamedIn l (ownPairs Y.tl) Y.arrayOf

theorem declareLinks_names {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) :
    AllNamed named := by
  unfold declareLinks at h
  dsimp only at h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain rfl : r.snd = named := congrArg Prod.fst (Except.ok.inj h)
  have key := forIn_done _
    (fun (done : List (LinkH × Nat)) (s : MProd (Array FrameLink) (Array LinkH)) =>
      (∀ (j : Nat) (x : LinkH × Nat), done[j]? = some x → x.2 = j) →
        s.snd.size = done.length ∧ AllNamed s.snd)
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
        exact (declareOwn_names hd).keep J)
    links.toList.zipIdx [] ⟨#[], #[]⟩ r
    (fun _ => ⟨rfl, fun l Y hY => by simp at hY⟩) hr
  exact (key fun j x hx => by
    rw [List.nil_append, List.getElem?_zipIdx] at hx
    obtain ⟨y, _, rfl⟩ := Option.map_eq_some_iff.1 hx
    simp).2

/-- **(a), AT THE MAKER's OWN TEXT.** -/
theorem names_of_buildLinks {links0 : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links0 NGr p4 wsLay p = .ok B) :
    ∀ (l : Nat) (X : LinkH) (tree mu : Nat), B.links[l]? = some X →
      (tree, mu) ∈ zipT X.tl.ix.PK.toList X.tl.pkMat.toList ++
        zipT X.tl.ix.TX.toList X.tl.pxMat.toList →
      X.arrayOf[tree]? = some (l, matrixName mu) := by
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
  intro l X tree mu hX hm
  exact declareLinks_names h3 l X hX (tree, mu) hm

/-- **(a), WHERE THE PROOF FILE's PUBLIC PART IS MADE.** At every o. -/
theorem names_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) :
    ∀ (l : Nat) (X : LinkH) (tree mu : Nat), Z.p.built.links[l]? = some X →
      (tree, mu) ∈ zipT X.tl.ix.PK.toList X.tl.pkMat.toList ++
        zipT X.tl.ix.TX.toList X.tl.pxMat.toList →
      X.arrayOf[tree]? = some (l, matrixName mu) := by
  obtain ⟨b, hb, e⟩ := ProofFile.Law.pub_builtOf h
  unfold Verify.builtOf at hb
  obtain ⟨l0, _, hb⟩ := exc_bind hb
  intro l X tree mu hX hm
  rw [← e] at hX
  have hX' : (b.links.map ProofFile.Law.blank)[l]? = some X := hX
  rw [Array.getElem?_map] at hX'
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1 hX'
  exact names_of_buildLinks hb l Y tree mu hY hm

/-- **OwnHeld, where the public part is made.** At every o. -/
theorem ownHeld_of_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) : OwnHeld Z.first.layout Z.p.built.links := by
  intro l Y tree mu hY hm
  obtain ⟨-, A, L, m, hA, -, -, -, -, hs⟩ :=
    named_of_made h l Y tree l (matrixName mu) hY (names_of_made h l Y tree mu hY hm)
  obtain ⟨tr, t1, t2, t3⟩ := hs rfl
  exact ⟨A, tr, hA, t1, t2, t3⟩

/-- **namedThere FROM «THE DESCRIPTION IS MADE» ALONE.** In the goals' scope, at the second hash
function. No pin. -/
theorem namedThere_of_made {W : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (hR : VerifierAndGoals.readFiles W = .ok pp)
    (h : ProofFile.pureRoad.pub OnBytes.secondHashFunction W.pol W.lay W.KL = .ok Z) :
    Meaning.namedThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true :=
  namedThere_of_held hW hR h (ownHeld_of_made h)

end IM.Own

#print axioms IM.Own.declareOwn_names
#print axioms IM.Own.names_of_buildLinks
#print axioms IM.Own.names_of_made
#print axioms IM.Own.ownHeld_of_made
#print axioms IM.Own.namedThere_of_made
