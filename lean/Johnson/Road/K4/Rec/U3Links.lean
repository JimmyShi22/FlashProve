-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/U3Links.lean: WHAT ALL SEGMENTS' DECLARATIONS HOLD OF ONE SEGMENT's ARRAY OF THE
READS (U3): where declareLinks (OnBytes/Model/StagesLinks.lean) returns (named, declared), at a
segment l whose given structure X has the list of the vectors' arrays #[none, none, some 0, none]:
entry 0 of named[l]'s list arrayOf is (l, "U3"), and declared[l]'s second moment (number 1) is
ONE array: "U3", with the rows and columns of array 0 of X's plan. Three definitions, eight
statements with their proofs.

  `SameM D D'`: two declarations have one second moment and as many moments. `SameL A B`: two
    lists of declarations are as long, and SameM entry by entry. Each with refl and trans.
  `keptUpTo_sameM`, `foreign_sameL`: a later segment's step foreign keeps an earlier declaration's
    second moment and its number of moments.
  `StepU`, `chain_u3`: one step of declareLinks; what a chain of steps leaves.
  **`declared_u3`**: see above. Premises: declareLinks returns · links[l]? = some X · hU.
The walk is that of declared_names (Johnson/Road/K4/Names/DeclaredNames.lean), with the list of
declarations carried beside the list of segments.
Limits. Nothing on the layout or the request's shape: that these hold what is declared is another
test of the maker's (heldAgainst). K04_law, the law of K4's sub-protocol itself, IS NOT PROVED.
Nothing on soundness.


-/
import Johnson.Road.K4.Rec.U3Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done foreign_cut getD_set)
open OnBytes.L5.LinksOrder (forIn_chain)
open OnBytes.Road.K4.Names (Has Stays foreign_names)

/-- Two declarations have one second moment, and as many moments. -/
def SameM (D D' : FrameLink) : Prop :=
  D'.moment.getD 1 #[] = D.moment.getD 1 #[] ∧ D'.moment.size = D.moment.size

theorem SameM.refl (D : FrameLink) : SameM D D := ⟨rfl, rfl⟩

theorem SameM.trans {A B C : FrameLink} (h : SameM A B) (k : SameM B C) : SameM A C :=
  ⟨k.1.trans h.1, k.2.trans h.2⟩

/-- Two lists of declarations are as long, and SameM entry by entry. -/
def SameL (A B : Array FrameLink) : Prop :=
  B.size = A.size ∧ ∀ j, SameM (A.getD j {}) (B.getD j {})

theorem SameL.refl (A : Array FrameLink) : SameL A A := ⟨rfl, fun _ => SameM.refl _⟩

theorem SameL.trans {A B C : Array FrameLink} (h : SameL A B) (k : SameL B C) : SameL A C :=
  ⟨k.1.trans h.1, fun j => (h.2 j).trans (k.2 j)⟩

/-- keptUpTo keeps the second moment and the number of moments. -/
theorem keptUpTo_sameM {D D' : FrameLink} {name : String} {life : Nat}
    (h : keptUpTo D name life = .ok D') : SameM D D' := by
  unfold keptUpTo at h
  dsimp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    refine ⟨?_, ?_⟩
    · show (D.moment.setIfInBounds 0 _).getD 1 #[] = _
      rw [getD_set, if_neg (by omega)]
    · show (D.moment.setIfInBounds 0 _).size = _
      rw [Array.size_setIfInBounds]
  · cases h

/-- The step foreign keeps every earlier declaration's second moment and number of moments. -/
theorem foreign_sameL {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') : SameL s.2 s'.2 := by
  obtain ⟨born, D, D', name, life, hD, hk, e⟩ := foreign_cut h
  have k := keptUpTo_sameM hk
  refine ⟨by rw [e, Array.size_setIfInBounds], fun j => ?_⟩
  rw [e, getD_set]
  split
  · rename_i hc
    obtain ⟨rfl, _⟩ := hc
    have eD : s.2.getD born {} = D := by
      rw [Array.getD_eq_getD_getElem?, hD]
      rfl
    rw [eD]
    exact k
  · exact SameM.refl _

/-- One step of declareLinks: a segment is added with arrayOf filled over what declareOwn laid; its
declaration is pushed behind the earlier ones, whose second moments stay. -/
def StepU (x : LinkH × Nat) (b b' : MProd (Array FrameLink) (Array LinkH)) : Prop :=
  ∃ ar d s2, declareOwn x.1 x.2 = .ok d ∧ Stays d.arrayOf ar ∧
    b'.snd = b.snd.push { x.1 with arrayOf := ar } ∧
    b'.fst = s2.push { name := x.1.name, moment := d.moment } ∧ SameL b.fst s2

/-- What a chain of steps leaves. -/
theorem chain_u3 : ∀ (l : List (LinkH × Nat)) (b r : MProd (Array FrameLink) (Array LinkH)),
    OnBytes.L5.LinksOrder.Chain StepU l b r → ∀ nf ns, b.fst.size = nf → b.snd.size = ns →
    (∀ j, j < nf → SameM (b.fst.getD j {}) (r.fst.getD j {})) ∧ nf ≤ r.fst.size ∧
      (∀ j, j < ns → r.snd[j]? = b.snd[j]?) ∧
      ∀ j x, l[j]? = some x → ∃ ar d, declareOwn x.1 x.2 = .ok d ∧ Stays d.arrayOf ar ∧
        r.snd[ns + j]? = some { x.1 with arrayOf := ar } ∧ nf + j < r.fst.size ∧
        (r.fst.getD (nf + j) {}).moment.getD 1 #[] = d.moment.getD 1 #[] ∧
        (r.fst.getD (nf + j) {}).moment.size = d.moment.size
  | [], b, r, h, nf, ns, ef, es => by
    have e : r = b := h
    rw [e]
    exact ⟨fun _ _ => SameM.refl _, Nat.le_of_eq ef.symm, fun _ _ => rfl,
      fun j x hx => by simp at hx⟩
  | a :: l, b, r, h, nf, ns, ef, es => by
    obtain ⟨b', ⟨ar, d, s2, hd, hst, hs, hf, hL⟩, hc⟩ := h
    have zs : b'.snd.size = ns + 1 := by rw [hs, Array.size_push, es]
    have zf : b'.fst.size = nf + 1 := by rw [hf, Array.size_push, hL.1, ef]
    have z2 : s2.size = nf := hL.1.trans ef
    obtain ⟨i1, i2, i3, i4⟩ := chain_u3 l b' r hc (nf + 1) (ns + 1) zf zs
    have g1 : ∀ j, j < nf → b'.fst.getD j {} = s2.getD j {} := by
      intro j hj
      have hj' : j < s2.size := by omega
      rw [hf, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hj',
        ← Array.getElem?_eq_getElem hj', ← Array.getD_eq_getD_getElem?]
    have g2 : b'.fst.getD nf {} = { name := a.1.name, moment := d.moment } := by
      rw [hf, ← z2, Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
      rfl
    refine ⟨?_, by omega, ?_, ?_⟩
    · intro j hj
      have a1 := i1 j (by omega)
      rw [g1 j hj] at a1
      exact (hL.2 j).trans a1
    · intro j hj
      have hj' : j < b.snd.size := by omega
      rw [i3 j (by omega), hs, Array.getElem?_push_lt hj', Array.getElem?_eq_getElem hj']
    · intro j x hx
      cases j with
      | zero =>
        have e : a = x := by simpa using hx
        subst e
        have a1 := i1 nf (by omega)
        rw [g2] at a1
        refine ⟨ar, d, hd, hst, ?_, by omega, a1.1, a1.2⟩
        rw [Nat.add_zero, i3 _ (by omega), hs, ← es, Array.getElem?_push_size]
      | succ j =>
        obtain ⟨ar', d', h1, h2, h3, h4, h5, h6⟩ := i4 j x (by simpa using hx)
        have e1 : ns + (j + 1) = ns + 1 + j := by omega
        have e2 : nf + (j + 1) = nf + 1 + j := by omega
        rw [e1, e2]
        exact ⟨ar', d', h1, h2, h3, h4, h5, h6⟩

/-- **Where declareLinks returns: the array of the reads of segment l, in both lists.** -/
theorem declared_u3 {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) {l : Nat}
    {X : LinkH} (hX : links[l]? = some X) (hU : X.tl.ix.U = #[none, none, some 0, none]) :
    ∃ ar t n, named[l]? = some { X with arrayOf := ar } ∧ ar[0]? = some (l, nameU3) ∧
      X.Fp.trees[0]? = some t ∧ X.Tp.nt[0]? = some n ∧ l < declared.size ∧
      1 < (declared.getD l {}).moment.size ∧
      (declared.getD l {}).moment.getD 1 #[] =
        #[{ name := nameU3, rows := t.R, columns := t.K, overE := n.ec == 3 }] := by
  unfold declareLinks at h
  obtain ⟨r, h1, h2⟩ := exc_bind h
  have hn : named = r.snd ∧ declared = r.fst := by
    obtain ⟨d, n⟩ := r
    have e := Except.ok.inj h2
    exact ⟨(congrArg Prod.fst e).symm, (congrArg Prod.snd e).symm⟩
  have hc := forIn_chain _ StepU (fun x b s hs => by
    obtain ⟨Y, j⟩ := x
    obtain ⟨d, hd, k1⟩ := exc_bind hs
    obtain ⟨s1, hs1, k2⟩ := exc_bind k1
    dsimp only at k2
    split at k2
    · cases k2
    · have I := forIn_done _
        (fun (_ : List (Nat × PlaceF)) (q : Array (Nat × String) × Array FrameLink) =>
          Stays d.arrayOf q.1 ∧ SameL b.fst q.2)
        (fun done a q q' Iq eq => by
          obtain ⟨q1, e1, eq⟩ := exc_bind eq
          obtain ⟨_, _, eq⟩ := exc_bind eq
          exact ⟨q1, (Except.ok.inj eq).symm, Iq.1.trans (foreign_names e1).1,
            Iq.2.trans (foreign_sameL e1)⟩)
        _ [] _ _ ⟨Stays.refl _, SameL.refl _⟩ hs1
      exact ⟨_, (Except.ok.inj k2).symm, s1.fst, d, s1.snd, hd, I.1, rfl, rfl, I.2⟩) _ _ _ h1
  obtain ⟨_, _, _, i4⟩ := chain_u3 _ _ _ hc 0 0 rfl rfl
  obtain ⟨ar, d, hd, hst, h3, h4, h5, h6⟩ := i4 l (X, l) (by
    rw [List.getElem?_zipIdx, Array.getElem?_toList, hX]
    simp)
  rw [Nat.zero_add] at h3 h4 h5 h6
  obtain ⟨t, n, ht, hn', hs, hm, hh⟩ := declareOwn_u3 hd hU
  rw [hn.1, hn.2]
  exact ⟨ar, t, n, h3, (hst _ _ _ hh).1, ht, hn', h4, by rw [h6]; exact hs, by rw [h5, hm]⟩

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.keptUpTo_sameM
#print axioms OnBytes.Road.K4.Rec.foreign_sameL
#print axioms OnBytes.Road.K4.Rec.chain_u3
#print axioms OnBytes.Road.K4.Rec.declared_u3
