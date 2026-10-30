-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoDeclMoments.lean.
The arrays that the links declare: where every link has one of the vectors U1 to U4, every declared
link has an array at moment 2, that is, at its third moment: moments are counted from 0.

declareLinks (OnBytes/Model/StagesLinks.lean) declares the arrays of all links. For each link
declareOwn opens a first moment for the symbol arrays, one moment for each vector U1 to U4 that the
sub-proof has, and a last one for the arrays ZZ and BZ. The step foreign then turns, in an earlier
link's first moment, how long an array is kept.

* forIn_done, forIn_mem: two laws on a loop in Except whose every step, if it returns, goes on.
* DOK d, own_cut, own_keep, own_next: there is a moment, and every moment from the second on has an
  array; the step own pushes one array onto the last moment; so it keeps DOK and the number of
  moments; behind nextMoment it keeps DOK with one moment more.
* declareOwn_moments: if declareOwn X l = .ok d and X has one of the four vectors, then d has an
  array at moment 2.
* QOK declared, keptUpTo_keep, foreign_cut, foreign_keep: every declared link has an array at moment
  2; foreign keeps that.
* declareLinks_moments: if declareLinks links NGr p4 = .ok (named, declared) and every link has one
  of the four vectors, then QOK declared.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoFrameFolds

set_option autoImplicit false

namespace Fo.ReqF
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages

/-- A loop in Except whose every step, if it returns, goes on. -/
theorem forIn_done {α σ : Type} (f : α → σ → Except String (ForInStep σ))
    (I : List α → σ → Prop)
    (step : ∀ done a s s', I done s → f a s = .ok s' → ∃ t, s' = .yield t ∧ I (done ++ [a]) t) :
    ∀ (l done : List α) (s r : σ), I done s → forIn l s f = .ok r → I (done ++ l) r
  | [], done, s, r, hI, h => by
    rw [List.forIn_nil] at h
    obtain rfl : s = r := Except.ok.inj h
    rwa [List.append_nil]
  | a :: l, done, s, r, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := exc_bind h
    obtain ⟨t, rfl, hI'⟩ := step done a s s' hI hs
    have := forIn_done f I step l (done ++ [a]) t r hI' h
    rwa [List.append_assoc] at this

/-- The same with an invariant of the state alone, where the steps are asked at the list's members.
-/
theorem forIn_mem {α σ : Type} (f : α → σ → Except String (ForInStep σ)) (I : σ → Prop)
    (L : List α)
    (step : ∀ a ∈ L, ∀ s s', I s → f a s = .ok s' → ∃ t, s' = .yield t ∧ I t) :
    ∀ (l : List α) (s r : σ), (∀ a ∈ l, a ∈ L) → I s → forIn l s f = .ok r → I r
  | [], s, r, _, hI, h => by
    rw [List.forIn_nil] at h
    obtain rfl : s = r := Except.ok.inj h
    exact hI
  | a :: l, s, r, hl, hI, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s', hs, h⟩ := exc_bind h
    obtain ⟨t, rfl, hI'⟩ := step a (hl a List.mem_cons_self) s s' hI hs
    exact forIn_mem f I L step l t r (fun b hb => hl b (List.mem_cons_of_mem _ hb)) hI' h

/-- Every moment from the second on has an array. -/
def DOK (d : Declaring) : Prop :=
  1 ≤ d.moment.size ∧ ∀ t, 1 ≤ t → t < d.moment.size → 0 < (d.moment.getD t #[]).size

theorem own_cut {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') :
    ∃ a, d'.moment = d.moment.modify (d.moment.size - 1) (·.push a) := by
  unfold own at h
  obtain ⟨arrayOf, _, h⟩ := exc_bind h
  split at h
  · obtain rfl := Except.ok.inj h
    exact ⟨_, rfl⟩
  · cases h

theorem own_keep {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (I : DOK d) (h : own X l d tree name = .ok d') :
    DOK d' ∧ d'.moment.size = d.moment.size := by
  obtain ⟨a, e⟩ := own_cut h
  have es : d'.moment.size = d.moment.size := by rw [e, Array.size_modify]
  refine ⟨⟨es ▸ I.1, fun t h1 h2 => ?_⟩, es⟩
  rw [e, Fo.getD_modify]
  split
  · rw [Array.size_push]
    omega
  · exact I.2 t h1 (es ▸ h2)

theorem own_next {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (I : DOK d) (h : own X l d.nextMoment tree name = .ok d') :
    DOK d' ∧ d'.moment.size = d.moment.size + 1 := by
  obtain ⟨a, e⟩ := own_cut h
  have en : d.nextMoment.moment = d.moment.push #[] := rfl
  have es : d'.moment.size = d.moment.size + 1 := by
    rw [e, Array.size_modify, en, Array.size_push]
  refine ⟨⟨by omega, fun t h1 h2 => ?_⟩, es⟩
  rw [e, Fo.getD_modify]
  split
  · rw [Array.size_push]
    omega
  · rename_i hc
    rw [en, Array.size_push] at hc
    have ht : t < d.moment.size := by
      by_contra hx
      exact hc ⟨by omega, by omega⟩
    rw [en, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt ht, ← Array.getElem?_eq_getElem ht,
      ← Array.getD_eq_getD_getElem?]
    exact I.2 t h1 ht

theorem declareOwn_moments {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d)
    (hU : ∃ u ∈ X.tl.ix.U.toList.take 4, u.isSome = true) :
    0 < (d.moment.getD 2 #[]).size := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have I0 : DOK { arrayOf := Array.replicate X.Tp.nt.size (noLink, ""), moment := #[#[]] } :=
    ⟨Nat.le_refl 1, fun t a b => absurd b (by
      show ¬ t < 1
      omega)⟩
  have stepOwn : ∀ (done : List (Nat × Nat)) (a : Nat × Nat) (s : Declaring)
      (s' : ForInStep Declaring), DOK s →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ DOK t := by
    intro _ a s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    exact ⟨r, (Except.ok.inj e).symm, (own_keep I e1).1⟩
  have I1 : DOK d1 := forIn_done _ (fun _ s => DOK s) stepOwn _ [] _ _ I0 h1
  have I2 : DOK d2 := forIn_done _ (fun _ s => DOK s) stepOwn _ [] _ _ I1 h2
  have I3 := forIn_done _
    (fun (done : List (Option Nat × Nat)) s => DOK s ∧
      ((∃ x ∈ done, x.1.isSome = true) → 2 ≤ s.moment.size))
    (fun done a s s' I e => by
      obtain ⟨Ia, Ib⟩ := I
      split at e
      · rename_i tree ha
        obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        obtain ⟨Ja, Jb⟩ := own_next Ia e1
        exact ⟨r, (Except.ok.inj e).symm, Ja, fun _ => by
          have := Ia.1
          omega⟩
      · rename_i hn
        obtain ⟨_, _, e⟩ := exc_bind e
        refine ⟨s, (Except.ok.inj e).symm, Ia, ?_⟩
        rintro ⟨x, hx, hs⟩
        rcases List.mem_append.1 hx with hx | hx
        · exact Ib ⟨x, hx, hs⟩
        · obtain rfl : x = a := by simpa using hx
          obtain ⟨tree, ht⟩ := Option.isSome_iff_exists.1 hs
          exact absurd ht (hn tree))
    _ [] _ _ ⟨I2, fun ⟨_, hx, _⟩ => by cases hx⟩ h3
  obtain ⟨I3a, I3b⟩ := I3
  have hs3 : 2 ≤ d3.moment.size := by
    obtain ⟨u, hu, hs⟩ := hU
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hu
    exact I3b ⟨(_, n), by
      rw [List.nil_append]
      exact List.mk_mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem hn), hs⟩
  obtain ⟨I4, s4⟩ := own_next I3a h4
  obtain ⟨I5, s5⟩ := own_keep I4 h5
  exact I5.2 2 (by omega) (by omega)

/-- Every declared link has an array at moment 2. -/
def QOK (declared : Array FrameLink) : Prop :=
  ∀ j, j < declared.size → 0 < ((declared.getD j {}).moment.getD 2 #[]).size

theorem keptUpTo_keep {D D' : FrameLink} {name : String} {life : Nat}
    (h : keptUpTo D name life = .ok D') : D'.moment.getD 2 #[] = D.moment.getD 2 #[] := by
  unfold keptUpTo at h
  dsimp only at h
  split at h
  · obtain rfl := Except.ok.inj h
    show (D.moment.setIfInBounds 0 _).getD 2 #[] = _
    rw [getD_set, if_neg (by omega)]
  · cases h

theorem foreign_cut {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF}
    (h : foreign links NGr p4 l X s tree pl = .ok s') :
    ∃ born D D' name life, s.2[born]? = some D ∧ keptUpTo D name life = .ok D' ∧
      s'.2 = s.2.setIfInBounds born D' := by
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
              obtain ⟨arrayOf, _, h⟩ := exc_bind h
              split at h
              · rename_i D hD
                obtain ⟨D', hk, h⟩ := exc_bind h
                obtain rfl := Except.ok.inj h
                exact ⟨_, D, D', _, _, hD, hk, rfl⟩
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

theorem foreign_keep {links : Array LinkH} {NGr : Nat} {p4 : Bool} {l : Nat} {X : LinkH}
    {s s' : Array (Nat × String) × Array FrameLink} {tree : Nat} {pl : PlaceF} (I : QOK s.2)
    (h : foreign links NGr p4 l X s tree pl = .ok s') : QOK s'.2 := by
  obtain ⟨born, D, D', name, life, hD, hk, e⟩ := foreign_cut h
  intro j hj
  rw [e, Array.size_setIfInBounds] at hj
  rw [e, getD_set]
  by_cases hc : born = j ∧ j < s.2.size
  · rw [if_pos hc]
    obtain rfl := hc.1
    have eD : s.2.getD born {} = D := by
      rw [Array.getD_eq_getD_getElem?, hD]
      rfl
    rw [keptUpTo_keep hk, ← eD]
    exact I born hj
  · rw [if_neg hc]
    exact I j hj

/-- **Where every link has a vector U, every declared link has an array at moment 2.** -/
theorem declareLinks_moments {links named : Array LinkH} {NGr : Nat} {p4 : Bool}
    {declared : Array FrameLink} (h : declareLinks links NGr p4 = .ok (named, declared))
    (hU : ∀ X ∈ links.toList, ∃ u ∈ X.tl.ix.U.toList.take 4, u.isSome = true) : QOK declared := by
  unfold declareLinks at h
  dsimp only at h
  obtain ⟨r, hr, h⟩ := exc_bind h
  obtain rfl : r.fst = declared := congrArg Prod.snd (Except.ok.inj h)
  have I0 : QOK (⟨#[], #[]⟩ : MProd (Array FrameLink) (Array LinkH)).fst :=
    fun j hj => absurd hj (Nat.not_lt_zero j)
  refine forIn_mem _ (fun (s : MProd (Array FrameLink) (Array LinkH)) => QOK s.fst)
    links.toList.zipIdx (fun x hx s s' I e => ?_) _ _ _ (fun _ ha => ha) I0 hr
  obtain ⟨d, hd, e⟩ := exc_bind e
  obtain ⟨s1, h1, e⟩ := exc_bind e
  replace e := exc_guard e
  obtain ⟨_, _, e⟩ := exc_bind e
  refine ⟨_, (Except.ok.inj e).symm, ?_⟩
  have I1 : QOK s1.2 := forIn_mem _
    (fun (q : Array (Nat × String) × Array FrameLink) => QOK q.2) _
    (fun y _ q q' Iq eq => by
      obtain ⟨q1, e1, eq⟩ := exc_bind eq
      obtain ⟨_, _, eq⟩ := exc_bind eq
      exact ⟨q1, (Except.ok.inj eq).symm, foreign_keep Iq e1⟩) _ _ _ (fun _ ha => ha) I h1
  have hX : x.1 ∈ links.toList := by
    have := List.mk_mem_zipIdx_iff_getElem?.1 (show (x.1, x.2) ∈ links.toList.zipIdx from hx)
    exact List.mem_of_getElem? this
  have hd2 := declareOwn_moments hd (hU x.1 hX)
  intro j hj
  show 0 < (((s1.2.push { name := x.1.name, moment := d.moment }).getD j {}).moment.getD 2 #[]).size
  have hj' : j < s1.2.size + 1 := by
    have : j < (s1.2.push { name := x.1.name, moment := d.moment }).size := hj
    rwa [Array.size_push] at this
  by_cases hlt : j < s1.2.size
  · have eJ : (s1.2.push { name := x.1.name, moment := d.moment }).getD j {} = s1.2.getD j {} := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hlt, Array.getD_eq_getD_getElem?,
        Array.getElem?_eq_getElem hlt]
    rw [eJ]
    exact I1 j hlt
  · obtain rfl : j = s1.2.size := by omega
    have eJ : (s1.2.push { name := x.1.name, moment := d.moment }).getD s1.2.size {} =
        { name := x.1.name, moment := d.moment } := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
      rfl
    rw [eJ]
    exact hd2

end Fo.ReqF
