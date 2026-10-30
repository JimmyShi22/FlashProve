-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/U3Declared.lean: WHAT A SEGMENT DECLARES OF ITS ARRAY OF THE READS (U3): where
declareOwn (OnBytes/Model/StagesLinks.lean) returns at a segment X whose list of the vectors'
arrays is #[none, none, some 0, none]: the segment's second moment (number 1) holds ONE array: its
name is "U3", its rows and columns are those of array 0 of X's plan; and entry 0 of the list
arrayOf is (l, "U3"). One definition, six statements with their proofs.

  `nameU3`, `nameU3_ne`: the name as the maker spells it; it is not empty.
  `own_full`: the step own: the array that it pushes onto the last moment (arrayOf: own_names).
  `own_next_keeps`, `own_last_keeps`: behind nextMoment the step own keeps every earlier moment;
    without it, every moment but the last.
  `push_one`: a new moment with one array pushed is that array alone.
  **`declareOwn_u3`**: see above. Premises: declareOwn returns · hU.
The walk is that of Fo.ReqF.declareOwn_moments (OnBytes/Tie/Pv/Lookup/Ends/FoDeclMoments.lean);
the loop over the four vectors is cut into its four steps (forIn_chain).
Limits. One segment's own declaration: what later segments turn in it (how long an array of its
FIRST moment is kept) is not touched here. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Names.DeclaredNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done own_cut)
open OnBytes.L5.LinksOrder (forIn_chain)
open OnBytes.Road.K4.Names (Has Stays own_names)

/-- The name of the array of the reads, as declareOwn spells it. -/
def nameU3 : String := "U" ++ toString (2 + 1)

theorem nameU3_ne : nameU3.isEmpty = false := by
  unfold nameU3
  have h : 0 < ("U" ++ toString (2 + 1)).utf8ByteSize := by
    rw [String.utf8ByteSize_append]
    exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
  exact beq_false_of_ne (Nat.ne_of_gt h)

/-- The step own: the array that it pushes onto the last moment (arrayOf: own_names). -/
theorem own_full {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') :
    ∃ t n, X.Fp.trees[tree]? = some t ∧ X.Tp.nt[tree]? = some n ∧
      d'.moment = d.moment.modify (d.moment.size - 1)
        (·.push { name := name, rows := t.R, columns := t.K, overE := n.ec == 3 }) := by
  unfold own at h
  obtain ⟨arrayOf, _, h⟩ := exc_bind h
  split at h
  · rename_i t n ht hn
    obtain rfl := Except.ok.inj h
    exact ⟨t, n, ht, hn, rfl⟩
  · cases h

/-- Behind nextMoment the step own keeps every earlier moment. -/
theorem own_next_keeps {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d.nextMoment tree name = .ok d') {j : Nat} (hj : j < d.moment.size) :
    d'.moment.getD j #[] = d.moment.getD j #[] ∧ d'.moment.size = d.moment.size + 1 := by
  obtain ⟨a, e⟩ := own_cut h
  have en : d.nextMoment.moment = d.moment.push #[] := rfl
  have hc : ¬ (d.nextMoment.moment.size - 1 = j ∧ j < d.nextMoment.moment.size) := by
    rw [en, Array.size_push]
    omega
  refine ⟨?_, by rw [e, Array.size_modify, en, Array.size_push]⟩
  rw [e, Fo.getD_modify, if_neg hc, en, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt hj,
    ← Array.getElem?_eq_getElem hj, ← Array.getD_eq_getD_getElem?]

/-- The step own keeps every moment but the last. -/
theorem own_last_keeps {X : LinkH} {l : Nat} {d d' : Declaring} {tree : Nat} {name : String}
    (h : own X l d tree name = .ok d') {j : Nat} (hj : j + 1 < d.moment.size) :
    d'.moment.getD j #[] = d.moment.getD j #[] ∧ d'.moment.size = d.moment.size := by
  obtain ⟨a, e⟩ := own_cut h
  have hc : ¬ (d.moment.size - 1 = j ∧ j < d.moment.size) := by omega
  exact ⟨by rw [e, Fo.getD_modify, if_neg hc], by rw [e, Array.size_modify]⟩

/-- A new moment with one array pushed is that array alone. -/
theorem push_one (M : Array (Array FrameArray)) (a : FrameArray) :
    ((M.push #[]).modify ((M.push #[]).size - 1) (·.push a)).getD M.size #[] = #[a] := by
  have hc : (M.push #[]).size - 1 = M.size ∧ M.size < (M.push #[]).size := by
    rw [Array.size_push]
    omega
  rw [Fo.getD_modify, if_pos hc, Array.getD_eq_getD_getElem?, Array.getElem?_push_size]
  rfl

/-- **What a segment declares of its array of the reads.** -/
theorem declareOwn_u3 {X : LinkH} {l : Nat} {d : Declaring} (h : declareOwn X l = .ok d)
    (hU : X.tl.ix.U = #[none, none, some 0, none]) :
    ∃ t n, X.Fp.trees[0]? = some t ∧ X.Tp.nt[0]? = some n ∧ 1 < d.moment.size ∧
      d.moment.getD 1 #[] =
        #[{ name := nameU3, rows := t.R, columns := t.K, overE := n.ec == 3 }] ∧
      Has d.arrayOf 0 l nameU3 := by
  unfold declareOwn at h
  dsimp only at h
  replace h := exc_guard h
  obtain ⟨d1, h1, h⟩ := exc_bind h
  obtain ⟨d2, h2, h⟩ := exc_bind h
  obtain ⟨d3, h3, h⟩ := exc_bind h
  obtain ⟨d4, h4, h⟩ := exc_bind h
  obtain ⟨d5, h5, h⟩ := exc_bind h
  obtain rfl := Except.ok.inj h
  have stepSz : ∀ (done : List (Nat × Nat)) (a : Nat × Nat) (s : Declaring)
      (s' : ForInStep Declaring), s.moment.size = 1 →
      (do
        let r ← own X l s a.1 (matrixName a.2)
        pure PUnit.unit
        pure (ForInStep.yield r) : Except String (ForInStep Declaring)) = .ok s' →
      ∃ t, s' = .yield t ∧ t.moment.size = 1 := by
    intro _ a s s' I e
    obtain ⟨r, e1, e⟩ := exc_bind e
    obtain ⟨_, _, e⟩ := exc_bind e
    obtain ⟨x, ex⟩ := own_cut e1
    exact ⟨r, (Except.ok.inj e).symm, by rw [ex, Array.size_modify]; exact I⟩
  have S1 : d1.moment.size = 1 :=
    forIn_done _ (fun _ s => s.moment.size = 1) stepSz _ [] _ _ rfl h1
  have S2 : d2.moment.size = 1 :=
    forIn_done _ (fun _ s => s.moment.size = 1) stepSz _ [] _ _ S1 h2
  have hc := forIn_chain _
    (fun (a : Option Nat × Nat) (b b' : Declaring) =>
      (b' = b ∧ ∀ tree, a.1 = some tree → False) ∨
        ∃ tree, a.1 = some tree ∧
          own X l b.nextMoment tree ("U" ++ toString (a.2 + 1)) = .ok b')
    (fun a b s e => by
      split at e
      · rename_i tree ha
        obtain ⟨r, e1, e⟩ := exc_bind e
        obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨r, (Except.ok.inj e).symm, Or.inr ⟨tree, ha, e1⟩⟩
      · rename_i hn
        obtain ⟨_, _, e⟩ := exc_bind e
        exact ⟨b, (Except.ok.inj e).symm, Or.inl ⟨rfl, hn⟩⟩) _ _ _ h3
  have eL : (X.tl.ix.U.toList.take 4).zipIdx =
      [(none, 0), (none, 1), (some 0, 2), (none, 3)] := by
    rw [hU]
    rfl
  rw [eL] at hc
  obtain ⟨b1, r1, b2, r2, b3, r3, b4, r4, e4⟩ := hc
  have q1 : b1 = d2 := by
    rcases r1 with ⟨e, _⟩ | ⟨_, e, _⟩
    · exact e
    · exact absurd e (by simp)
  have q2 : b2 = b1 := by
    rcases r2 with ⟨e, _⟩ | ⟨_, e, _⟩
    · exact e
    · exact absurd e (by simp)
  have q4 : b4 = b3 := by
    rcases r4 with ⟨e, _⟩ | ⟨_, e, _⟩
    · exact e
    · exact absurd e (by simp)
  have ho : own X l b2.nextMoment 0 nameU3 = .ok b3 := by
    rcases r3 with ⟨_, hn⟩ | ⟨tree, e, ho⟩
    · exact absurd rfl (hn 0)
    · obtain rfl : 0 = tree := Option.some.inj e
      exact ho
  have e3 : d3 = b3 := e4.trans q4
  rw [q2, q1] at ho
  rw [e3] at h4
  obtain ⟨t, n, ht, hn, em⟩ := own_full ho
  have en : d2.nextMoment.moment = d2.moment.push #[] := rfl
  have s3 : b3.moment.size = 2 := by
    rw [em, Array.size_modify, en, Array.size_push, S2]
  have m3 : b3.moment.getD 1 #[] =
      #[{ name := nameU3, rows := t.R, columns := t.K, overE := n.ec == 3 }] := by
    have p := push_one d2.moment
      { name := nameU3, rows := t.R, columns := t.K, overE := n.ec == 3 }
    rw [S2] at p
    rw [em, en]
    exact p
  obtain ⟨m4, s4⟩ := own_next_keeps h4 (j := 1) (by omega)
  obtain ⟨m5, s5⟩ := own_last_keeps h5 (j := 1) (by omega)
  refine ⟨t, n, ht, hn, by omega, by rw [m5, m4, m3], ?_⟩
  exact (own_names h5).1 _ _ _ ((own_names h4).1 _ _ _ ⟨(own_names ho).2, nameU3_ne⟩)

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.nameU3_ne
#print axioms OnBytes.Road.K4.Rec.own_full
#print axioms OnBytes.Road.K4.Rec.own_next_keeps
#print axioms OnBytes.Road.K4.Rec.own_last_keeps
#print axioms OnBytes.Road.K4.Rec.push_one
#print axioms OnBytes.Road.K4.Rec.declareOwn_u3
