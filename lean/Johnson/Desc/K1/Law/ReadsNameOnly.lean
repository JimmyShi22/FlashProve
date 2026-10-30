-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ReadsNameOnly.lean: IN THE LIST OF ARRAYS OF A BUILT SEGMENT (the field arrayOf
that declareLinks fills, OnBytes/Model/StagesLinks.lean) THE NAME "U3" STANDS AT THE NUMBER OF THE
SEGMENT's THIRD VECTOR ALONE. The converse of the laws that run from a tree to its entry
(`declared_names`, Johnson/Road/K4/Names/DeclaredNames.lean;
`reads_named_of_built`, Johnson/Desc/Kinds/Law/ReadsRoomOfBuilt.lean). General in the segments'
structures: no scope, no public part. Statements with their proofs; no routine is evaluated.

How. Every write into a list of arrays goes through namesH. The names that are written are
"M" ++ a number (own and foreign matrices), "U1" to "U4", "ZZ" and "BZ"; "U3" is written once, at
the third place of ix.U. ONE INVARIANT carries it along the walks of DeclaredNames.lean.

  `OnlyAt u a`   whatever entry of a bears the name "U3" sits at the number u
  `matrixName_no`, `uName`   a matrix's name is not "U3"; of "U1" to "U4" the third alone is
  `namesH_only`, `own_only`, `declareOwn_only`, `foreign_only`   the invariant along the makers
  `StepO`, `chain_only`   one step of declareLinks, and the chain of steps
  `declared_only`   **MAIN**: declareLinks links NGr p4 = .ok (named, declared) and
      links[l]? = some X give ar with named[l]? = some { X with arrayOf := ar } and
      OnlyAt (X.tl.ix.U.getD 2 none) ar

What is not claimed. That an entry bears the name "U3" at all. Nothing on the other names. Nothing
on soundness.

-/
import Johnson.Road.K4.Names.DeclaredNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1.Only

open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_mem)
open OnBytes.L5.LinksOrder (forIn_chain Chain)

/-- Whatever entry of a bears the name "U3" sits at the number u. -/
def OnlyAt (u : Option ℕ) (a : Array (ℕ × String)) : Prop :=
  ∀ t b, a[t]? = some (b, "U3") → u = some t

theorem matrixName_no (mu : ℕ) : matrixName mu ≠ "U3" := by
  intro h
  unfold matrixName at h
  have h2 := congrArg String.toList h
  simp at h2

theorem uName (k : ℕ) (hk : k < 4) (h : "U" ++ toString (k + 1) = "U3") : k = 2 := by
  interval_cases k
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl
  · exact absurd h (by decide)

theorem namesH_only {u : Option ℕ} {a a' : Array (ℕ × String)} {t b : ℕ} {n : String}
    (h : namesH a t b n = .ok a') (hn : n = "U3" → u = some t) (I : OnlyAt u a) :
    OnlyAt u a' := by
  unfold namesH at h
  split at h
  · split at h
    · obtain rfl := Except.ok.inj h
      intro t' b' e
      by_cases hc : t = t'
      · subst hc
        have e' : (a.setIfInBounds t (b, n))[t]? = some (b', "U3") := e
        rw [Array.getElem?_setIfInBounds, if_pos rfl] at e'
        split at e'
        · exact hn (congrArg Prod.snd (Option.some.inj e'))
        · cases e'
      · have e' : (a.setIfInBounds t (b, n))[t']? = some (b', "U3") := e
        rw [Array.getElem?_setIfInBounds_ne hc] at e'
        exact I t' b' e'
    · cases h
  · cases h

theorem own_only {u : Option ℕ} {X : LinkH} {l : ℕ} {d d' : Declaring} {tree : ℕ} {name : String}
    (h : own X l d tree name = .ok d') (hn : name = "U3" → u = some tree)
    (I : OnlyAt u d.arrayOf) : OnlyAt u d'.arrayOf := by
  unfold own at h
  obtain ⟨arrayOf, h1, h⟩ := exc_bind h
  split at h
  · obtain rfl := Except.ok.inj h
    exact namesH_only h1 hn I
  · cases h

theorem declareOwn_only {X : LinkH} {l : ℕ} {d : Declaring} (h : declareOwn X l = .ok d) :
    OnlyAt (X.tl.ix.U.getD 2 none) d.arrayOf := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have I0 : OnlyAt (X.tl.ix.U.getD 2 none)
      (Array.replicate X.Tp.nt.size (noLink, "") : Array (ℕ × String)) := by
    intro t b e
    rw [Array.getElem?_replicate] at e
    split at e
    · have e2 : ("" : String) = "U3" := congrArg Prod.snd (Option.some.inj e)
      exact absurd e2 (by decide)
    · cases e
  have stepOwn : ∀ (L : List (ℕ × ℕ)), ∀ a ∈ L, ∀ (s : Declaring) (s' : ForInStep Declaring),
      OnlyAt (X.tl.ix.U.getD 2 none) s.arrayOf →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ OnlyAt (X.tl.ix.U.getD 2 none) t.arrayOf := by
    intro L a _ s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    exact ⟨r, (Except.ok.inj e).symm, own_only e1 (fun hn => absurd hn (matrixName_no _)) I⟩
  have I1 := forIn_mem _ (fun s : Declaring => OnlyAt (X.tl.ix.U.getD 2 none) s.arrayOf) _
    (stepOwn _) _ _ _ (fun _ ha => ha) I0 h1
  have I2 := forIn_mem _ (fun s : Declaring => OnlyAt (X.tl.ix.U.getD 2 none) s.arrayOf) _
    (stepOwn _) _ _ _ (fun _ ha => ha) I1 h2
  have I3 := forIn_mem _ (fun s : Declaring => OnlyAt (X.tl.ix.U.getD 2 none) s.arrayOf)
    ((X.tl.ix.U.toList.take 4).zipIdx)
    (fun a ha s s' I e => by
      split at e
      · rename_i tree hu
        obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        refine ⟨r, (Except.ok.inj e).symm, own_only e1 (fun hn => ?_) I⟩
        have hm : (List.take 4 X.tl.ix.U.toList)[a.2]? = some a.1 :=
          List.mem_zipIdx_iff_getElem?.1 ha
        have hk : a.2 < 4 := by
          have h6 := (List.getElem?_eq_some_iff.1 hm).1
          have h7 := List.length_take_le 4 X.tl.ix.U.toList
          omega
        have e2 : a.2 = 2 := uName a.2 hk hn
        rw [e2, List.getElem?_take_of_lt (by omega), Array.getElem?_toList, hu] at hm
        rw [Array.getD_eq_getD_getElem?, hm]
        rfl
      · obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨s, (Except.ok.inj e).symm, I⟩)
    _ _ _ (fun _ ha => ha) I2 h3
  have I4 := own_only h4 (fun hn => absurd hn (by decide)) I3
  exact own_only h5 (fun hn => absurd hn (by decide)) I4

theorem foreign_only {u : Option ℕ} {links : Array LinkH} {NGr : ℕ} {p4 : Bool} {l : ℕ} {X : LinkH}
    {s s' : Array (ℕ × String) × Array FrameLink} {tree : ℕ} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') (I : OnlyAt u s.1) : OnlyAt u s'.1 := by
  unfold foreign at h
  dsimp only at h
  split at h
  · replace h := exc_guard h
    split at h
    · split at h
      · replace h := exc_guard h
        split at h
        · split at h
          · split at h
            · replace h := exc_guard h
              obtain ⟨arrayOf, hn, h⟩ := exc_bind h
              split at h
              · obtain ⟨D', _, h⟩ := exc_bind h
                obtain rfl := Except.ok.inj h
                exact namesH_only hn (fun e => absurd e (matrixName_no _)) I
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-- One step of declareLinks: a link is added that is the given one with arrayOf filled, and in the
list that is laid the name "U3" stands at the number of the link's third vector alone. -/
def StepO (x : LinkH × ℕ) (b b' : MProd (Array FrameLink) (Array LinkH)) : Prop :=
  ∃ ar, b'.snd = b.snd.push { x.1 with arrayOf := ar } ∧ OnlyAt (x.1.tl.ix.U.getD 2 none) ar

theorem chain_only :
    ∀ (l : List (LinkH × ℕ)) (b r : MProd (Array FrameLink) (Array LinkH)),
    Chain StepO l b r →
    (∀ j, j < b.snd.size → r.snd[j]? = b.snd[j]?) ∧
      ∀ j x, l[j]? = some x → ∃ ar, r.snd[b.snd.size + j]? = some { x.1 with arrayOf := ar } ∧
        OnlyAt (x.1.tl.ix.U.getD 2 none) ar
  | [], b, r, h => by
    have e : r = b := h
    rw [e]
    exact ⟨fun _ _ => rfl, fun j x hx => by simp at hx⟩
  | a :: l, b, r, h => by
    obtain ⟨b', ⟨ar, hb', hN⟩, hc⟩ := h
    obtain ⟨i2, i3⟩ := chain_only l b' r hc
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

/-- **Where declareLinks returns: in the list that it lays at link l the name "U3" stands at the
number of the link's third vector alone.** -/
theorem declared_only {links named : Array LinkH} {NGr : ℕ} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared)) {l : ℕ}
    {X : LinkH} (hX : links[l]? = some X) :
    ∃ ar, named[l]? = some { X with arrayOf := ar } ∧ OnlyAt (X.tl.ix.U.getD 2 none) ar := by
  unfold declareLinks at h
  obtain ⟨r, h1, h2⟩ := exc_bind h
  have hn : named = r.snd := by
    obtain ⟨d, n⟩ := r
    exact (congrArg Prod.fst (Except.ok.inj h2)).symm
  have hc := forIn_chain _ StepO (fun x b s hs => by
    obtain ⟨Y, j⟩ := x
    obtain ⟨d, hd, k1⟩ := exc_bind hs
    obtain ⟨s1, hs1, k2⟩ := exc_bind k1
    dsimp only at k2
    split at k2
    · cases k2
    · have I := forIn_mem _
        (fun (q : Array (ℕ × String) × Array FrameLink) => OnlyAt (Y.tl.ix.U.getD 2 none) q.1) _
        (fun a _ q q' Iq eq => by
          obtain ⟨q1, e1, eq⟩ := exc_bind eq
          obtain ⟨_, _, eq⟩ := exc_bind eq
          exact ⟨q1, (Except.ok.inj eq).symm, foreign_only e1 Iq⟩)
        _ _ _ (fun _ ha => ha) (declareOwn_only hd) hs1
      exact ⟨_, (Except.ok.inj k2).symm, s1.fst, rfl, I⟩) _ _ _ h1
  obtain ⟨_, i3⟩ := chain_only _ _ _ hc
  subst hn
  obtain ⟨ar, h3, hN⟩ := i3 l (X, l) (by
    rw [List.getElem?_zipIdx, Array.getElem?_toList, hX]
    simp)
  exact ⟨ar, by simpa using h3, hN⟩

end VerifiableInference.Desc.K1.Only

#print axioms VerifiableInference.Desc.K1.Only.matrixName_no
#print axioms VerifiableInference.Desc.K1.Only.uName
#print axioms VerifiableInference.Desc.K1.Only.namesH_only
#print axioms VerifiableInference.Desc.K1.Only.declareOwn_only
#print axioms VerifiableInference.Desc.K1.Only.foreign_only
#print axioms VerifiableInference.Desc.K1.Only.declared_only
