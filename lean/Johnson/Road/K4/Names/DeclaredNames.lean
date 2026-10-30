-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Names/DeclaredNames.lean: WHAT THE LIST arrayOf OF A BUILT SEGMENT HOLDS AT THE
TREES OF ITS MATRICES: where declareLinks (OnBytes/Model/StagesLinks.lean) returns, the field
arrayOf that it fills at link l says, at each tree of a symbol array of the link's own, the link's
number l and the name of the matrix; and at each tree of a matrix that an earlier sub-proof has
committed to, the owner's link and the name of the matrix in the owner's list. No scope is asked.


  `Has a t b n`: entry t of a is (b, n), and n is not empty. `Stays a a'`: what a has, a' has.
  `matrixName_ne`: a matrix's name is not empty.
  `namesH_cut`: where namesH returns: what was named stays, and the entry is laid. Why: namesH
    refuses to write over a name that is not empty.
  `own_names`, `declareOwn_names`, `foreign_names`: the same along the three makers.
  `Named links p4 X l ar`: the three sentences on ar, over the three zipped lists of X's plan.
  **`declared_names`**: declareLinks links NGr p4 = .ok (named, declared) and links[l]? = some X
    give ar with named[l]? = some { X with arrayOf := ar } and Named links p4 X l ar.
The walks are those of declareOwn_moments, foreign_cut
(OnBytes/Tie/Pv/Lookup/Ends/FoDeclMoments.lean) and declareLinks_at
(OnBytes/Tie/Pv/Keeps/LinksBuilt.lean), with another invariant.
Limits. Nothing on which tree is which matrix's (the plan's side). K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import OnBytes.Tie.Pv.Lookup.Ends.FoDeclMoments
import OnBytes.Tie.Pv.Keeps.LinksBuilt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Names
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)
open OnBytes.L5.LinksOrder (forIn_chain)

/-- Entry t of a is (b, n), and n is not empty. -/
def Has (a : Array (Nat × String)) (t b : Nat) (n : String) : Prop :=
  a[t]? = some (b, n) ∧ n.isEmpty = false

/-- What a has, a' has. -/
def Stays (a a' : Array (Nat × String)) : Prop := ∀ t b n, Has a t b n → Has a' t b n

theorem Stays.refl (a : Array (Nat × String)) : Stays a a := fun _ _ _ h => h

theorem Stays.trans {a b c : Array (Nat × String)} (h : Stays a b) (k : Stays b c) : Stays a c :=
  fun t x n e => k t x n (h t x n e)

/-- A matrix's name is not empty. -/
theorem matrixName_ne (mu : Nat) : (matrixName mu).isEmpty = false := by
  unfold matrixName
  have h : 0 < ("M" ++ toString mu).utf8ByteSize := by
    rw [String.utf8ByteSize_append]
    exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  exact beq_false_of_ne (Nat.ne_of_gt h)

/-- Where namesH returns: what was named stays, and the entry is laid. -/
theorem namesH_cut {a a' : Array (Nat × String)} {t b : Nat} {n : String}
    (h : namesH a t b n = .ok a') : Stays a a' ∧ a'[t]? = some (b, n) := by
  unfold namesH at h
  split at h
  · rename_i x hx
    split at h
    · rename_i he
      obtain rfl := Except.ok.inj h
      have ht : t < a.size := (Array.getElem?_eq_some_iff.1 hx).1
      refine ⟨fun t' b' n' e => ?_, ?_⟩
      · by_cases hc : t = t'
        · subst hc
          have ex : x = (b', n') := Option.some.inj (hx.symm.trans e.1)
          rw [ex] at he
          exact absurd he (by rw [e.2]; exact Bool.false_ne_true)
        · refine ⟨?_, e.2⟩
          show (a.setIfInBounds t (b, n))[t']? = some (b', n')
          rw [Array.getElem?_setIfInBounds_ne hc]
          exact e.1
      · show (a.setIfInBounds t (b, n))[t]? = some (b, n)
        rw [Array.getElem?_setIfInBounds, if_pos rfl, if_pos ht]
    · cases h
  · cases h

theorem own_names {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') :
    Stays d.arrayOf d'.arrayOf ∧ d'.arrayOf[tree]? = some (l, name) := by
  unfold own at h
  obtain ⟨arrayOf, hn, h⟩ := exc_bind h
  split at h
  · obtain rfl := Except.ok.inj h
    exact namesH_cut hn
  · cases h

/-- The invariant of a loop that names matrices: what the start had stays, and every pair done so
far is named. -/
def OwnInv (l : Nat) (s0 : Declaring) (done : List (Nat × Nat)) (s : Declaring) : Prop :=
  Stays s0.arrayOf s.arrayOf ∧ ∀ p ∈ done, Has s.arrayOf p.1 l (matrixName p.2)

theorem declareOwn_names {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d) :
    (∀ p ∈ zipT X.tl.ix.PK.toList X.tl.pkMat.toList, Has d.arrayOf p.1 l (matrixName p.2)) ∧
      ∀ p ∈ zipT X.tl.ix.TX.toList X.tl.pxMat.toList, Has d.arrayOf p.1 l (matrixName p.2) := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have stepOwn : ∀ (s0 : Declaring) (done : List (Nat × Nat)) (a : Nat × Nat) (s : Declaring)
      (s' : ForInStep Declaring), OwnInv l s0 done s →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ OwnInv l s0 (done ++ [a]) t := by
    intro s0 done a s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    obtain ⟨k1, k2⟩ := own_names e1
    refine ⟨r, (Except.ok.inj e).symm, I.1.trans k1, fun p hp => ?_⟩
    rcases List.mem_append.1 hp with hp | hp
    · exact k1 _ _ _ (I.2 p hp)
    · obtain rfl : p = a := by simpa using hp
      exact ⟨k2, matrixName_ne _⟩
  have I1 := forIn_done _ (OwnInv l _) (stepOwn _) _ [] _ _
    ⟨Stays.refl _, fun _ hp => by cases hp⟩ h1
  have I2 := forIn_done _ (OwnInv l d1) (stepOwn d1) _ [] _ _
    ⟨Stays.refl _, fun _ hp => by cases hp⟩ h2
  have I3 : Stays d2.arrayOf d3.arrayOf := forIn_done _
    (fun (_ : List (Option Nat × Nat)) s => Stays d2.arrayOf s.arrayOf)
    (fun done a s s' I e => by
      split at e
      · obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨r, (Except.ok.inj e).symm, I.trans (own_names e1).1⟩
      · obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨s, (Except.ok.inj e).symm, I⟩)
    _ [] _ _ (Stays.refl _) h3
  have I4 : Stays d3.arrayOf d4.arrayOf := (own_names h4).1
  have I5 : Stays d4.arrayOf d5.arrayOf := (own_names h5).1
  have T25 : Stays d2.arrayOf d5.arrayOf := (I3.trans I4).trans I5
  rw [List.nil_append] at I1 I2
  exact ⟨fun p hp => T25 _ _ _ (I2.1 _ _ _ (I1.2 p hp)), fun p hp => T25 _ _ _ (I2.2 p hp)⟩

/-- What foreign says of the reader's entry pl (a value of the structure PlaceF), and lays at entry
tree of ar. -/
def ForeignAt (links : Array LinkH) (p4 : Bool) (ar : Array (Nat × String)) (tree : Nat)
    (pl : PlaceF) : Prop :=
  ∃ owner rootIndex Y mu, pl.owner = some owner ∧ pl.rootIndex = some rootIndex ∧
    links[layersLink p4 owner]? = some Y ∧ Y.tl.pxMat[rootIndex - Y.tl.pkMat.size]? = some mu ∧
    ar[tree]? = some (layersLink p4 owner, matrixName mu)

theorem ForeignAt.stays {links : Array LinkH} {p4 : Bool} {ar ar' : Array (Nat × String)}
    {tree : Nat} {pl : PlaceF} (h : ForeignAt links p4 ar tree pl) (k : Stays ar ar') :
    ForeignAt links p4 ar' tree pl := by
  obtain ⟨owner, ri, Y, mu, a1, a2, a3, a4, a5⟩ := h
  exact ⟨owner, ri, Y, mu, a1, a2, a3, a4, (k _ _ _ ⟨a5, matrixName_ne mu⟩).1⟩

theorem foreign_names {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    Stays s.1 s'.1 ∧ ForeignAt links p4 s'.1 tree pl := by
  unfold foreign at h
  dsimp only at h
  split at h
  · rename_i owner ho
    replace h := exc_guard h
    split at h
    · rename_i Y hY
      split at h
      · rename_i ri hri
        replace h := exc_guard h
        split at h
        · rename_i mu hmu
          split at h
          · split at h
            · replace h := exc_guard h
              obtain ⟨arrayOf, hn, h⟩ := exc_bind h
              split at h
              · obtain ⟨D', _, h⟩ := exc_bind h
                obtain rfl := Except.ok.inj h
                obtain ⟨k1, k2⟩ := namesH_cut hn
                exact ⟨k1, owner, ri, Y, mu, ho, hri, hY, hmu, k2⟩
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- The three sentences on the list ar that is laid at link l, which is X. -/
def Named (links : Array LinkH) (p4 : Bool) (X : LinkH) (l : Nat) (ar : Array (Nat × String)) :
    Prop :=
  (∀ p ∈ zipT X.tl.ix.PK.toList X.tl.pkMat.toList, ar[p.1]? = some (l, matrixName p.2)) ∧
    (∀ p ∈ zipT X.tl.ix.TX.toList X.tl.pxMat.toList, ar[p.1]? = some (l, matrixName p.2)) ∧
    ∀ p ∈ zipT X.tl.ix.FT.toList X.tl.plFor.toList, ForeignAt links p4 ar p.1 p.2

/-- One step of declareLinks: a link is added that is the given one with arrayOf filled, and the
list that is laid is named. -/
def StepN (links : Array LinkH) (p4 : Bool) (x : LinkH × Nat)
    (b b' : MProd (Array FrameLink) (Array LinkH)) : Prop :=
  ∃ ar, b'.snd = b.snd.push { x.1 with arrayOf := ar } ∧ Named links p4 x.1 x.2 ar

theorem chain_named (links : Array LinkH) (p4 : Bool) :
    ∀ (l : List (LinkH × Nat)) (b r : MProd (Array FrameLink) (Array LinkH)),
    OnBytes.L5.LinksOrder.Chain (StepN links p4) l b r →
    (∀ j, j < b.snd.size → r.snd[j]? = b.snd[j]?) ∧
      ∀ j x, l[j]? = some x → ∃ ar, r.snd[b.snd.size + j]? = some { x.1 with arrayOf := ar } ∧
        Named links p4 x.1 x.2 ar
  | [], b, r, h => by
    have e : r = b := h
    rw [e]
    exact ⟨fun _ _ => rfl, fun j x hx => by simp at hx⟩
  | a :: l, b, r, h => by
    obtain ⟨b', ⟨ar, hb', hN⟩, hc⟩ := h
    obtain ⟨i2, i3⟩ := chain_named links p4 l b' r hc
    have hs : b'.snd.size = b.snd.size + 1 := by rw [hb', Array.size_push]
    refine ⟨?_, ?_⟩
    · intro j hj
      rw [i2 j (by omega), hb', Array.getElem?_push_lt hj, Array.getElem?_eq_getElem hj]
    · intro j x hx
      cases j with
      | zero =>
        have e : a = x := by simpa using hx
        refine ⟨ar, ?_, e ▸ hN⟩
        rw [Nat.add_zero, i2 _ (by omega), hb', Array.getElem?_push_size, e]
      | succ j =>
        obtain ⟨ar', h3, hN'⟩ := i3 j x (by simpa using hx)
        refine ⟨ar', ?_, hN'⟩
        rw [← h3, hs]
        congr 1
        omega

/-- **Where declareLinks returns: the list that it lays at link l is named.** -/
theorem declared_names {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) {l : Nat}
    {X : LinkH} (hX : links[l]? = some X) :
    ∃ ar, named[l]? = some { X with arrayOf := ar } ∧ Named links p4 X l ar := by
  unfold declareLinks at h
  obtain ⟨r, h1, h2⟩ := exc_bind h
  have hn : named = r.snd := by
    obtain ⟨d, n⟩ := r
    exact (congrArg Prod.fst (Except.ok.inj h2)).symm
  have hc := forIn_chain _ (StepN links p4) (fun x b s hs => by
    obtain ⟨Y, j⟩ := x
    obtain ⟨d, hd, k1⟩ := exc_bind hs
    obtain ⟨s1, hs1, k2⟩ := exc_bind k1
    dsimp only at k2
    split at k2
    · cases k2
    · obtain ⟨o1, o2⟩ := declareOwn_names hd
      have I := forIn_done _
        (fun (done : List (Nat × PlaceF)) (q : Array (Nat × String) × Array FrameLink) =>
          Stays d.arrayOf q.1 ∧ ∀ p ∈ done, ForeignAt links p4 q.1 p.1 p.2)
        (fun done a q q' Iq eq => by
          obtain ⟨q1, e1, eq⟩ := exc_bind eq
          obtain ⟨_, _, eq⟩ := exc_bind eq
          obtain ⟨k1, k2⟩ := foreign_names e1
          refine ⟨q1, (Except.ok.inj eq).symm, Iq.1.trans k1, fun p hp => ?_⟩
          rcases List.mem_append.1 hp with hp | hp
          · exact (Iq.2 p hp).stays k1
          · obtain rfl : p = a := by simpa using hp
            exact k2)
        _ [] _ _ ⟨Stays.refl _, fun _ hp => by cases hp⟩ hs1
      rw [List.nil_append] at I
      exact ⟨_, (Except.ok.inj k2).symm, s1.fst, rfl, fun p hp => (I.1 _ _ _ (o1 p hp)).1,
        fun p hp => (I.1 _ _ _ (o2 p hp)).1, I.2⟩) _ _ _ h1
  obtain ⟨_, i3⟩ := chain_named links p4 _ _ _ hc
  subst hn
  obtain ⟨ar, h3, hN⟩ := i3 l (X, l) (by
    rw [List.getElem?_zipIdx, Array.getElem?_toList, hX]
    simp)
  exact ⟨ar, by simpa using h3, hN⟩

end OnBytes.Road.K4.Names

#print axioms OnBytes.Road.K4.Names.matrixName_ne
#print axioms OnBytes.Road.K4.Names.namesH_cut
#print axioms OnBytes.Road.K4.Names.declareOwn_names
#print axioms OnBytes.Road.K4.Names.foreign_names
#print axioms OnBytes.Road.K4.Names.declared_names
