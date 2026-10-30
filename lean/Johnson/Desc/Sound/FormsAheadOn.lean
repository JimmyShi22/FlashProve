-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FormsAheadOn.lean: THE PUBLIC TEST `formsInA`
(Johnson/Desc/First/Batch/Ahead.lean) RIDES FORWARD, ALSO ACROSS
THE SENDING OF WHAT WAS AHEAD. Theorems.

Why. The table ties a public item to every open item on a run's forms: a block that the item rides
past owes "the test holds behind me". `formsIn_on` (Johnson/Desc/Sound/FormsOn.lean) does it for
`formsIn`. Across the sending of an array that was ahead an entry goes from the arm "ahead" to the
arm
"there".
  `Comes sent own a b`: what the later part b owes for what was ahead at a: each such array is still
    ahead at b, with the same array of the layout, OR IS THERE at b (`arrayIn`), the same array.
  `entInA_on`, `affInA_on`, `formsInA_on`: each test at a gives the test at b.
Limits: `Comes` is a premise: at the sending's own block its second arm is what
`cellA_meets` (Johnson/Desc/Sound/FormsAhead.lean) asks too: the frame finds the message, and the
book
holds it at a seat of own. One answer of the reader, `Rides`, `Grows`, `lateOk` behind: premises, as
in
`formsIn_on`. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.FormsOn
import Johnson.Desc.Sound.FormsAhead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt? lateOk slotIn arrayIn entIn Read Readers mergeOf Ahead
  aheadIn entInA entInA_of_entIn affInA formsInA)

section
variable (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ))

/-- What was ahead is still ahead, or has come. -/
def Comes (a b : K9.Part) : Prop :=
  ∀ (t : ℕ) (c : ℕ × String) (q : Ahead), a.L.arrayOf[t]? = some c →
    aheadIn sent own a c = some q →
      (∃ q', aheadIn sent own b c = some q' ∧ q'.A = q.A) ∨ arrayIn own b t = some q.A

theorem entInA_on (a b : K9.Part) (h : Rides own a b) (hc : Comes sent own a b) (x : Ent)
    (e : entInA sent own a x = true) : entInA sent own b x = true := by
  unfold entInA at e
  rcases Eq.mp (Bool.or_eq_true _ _) e with e | e
  · exact entInA_of_entIn sent own b x (entIn_on own a b h x e)
  · cases e1 : a.L.arrayOf[x.tree]? with
    | none =>
      rw [e1] at e
      exact nomatch e
    | some c =>
      rw [e1] at e
      cases e2 : aheadIn sent own a c with
      | none =>
        have e' : (match (some c : Option (ℕ × String)).bind (aheadIn sent own a) with
          | some q => decide (x.row < q.A.sizeI) && decide (x.idx < q.A.sizeC)
          | none => false) = true := e
        rw [Option.bind_some, e2] at e'
        exact nomatch e'
      | some q =>
        have e' : (match (some c : Option (ℕ × String)).bind (aheadIn sent own a) with
          | some q => decide (x.row < q.A.sizeI) && decide (x.idx < q.A.sizeC)
          | none => false) = true := e
        rw [Option.bind_some, e2] at e'
        have e3 : (decide (x.row < q.A.sizeI) && decide (x.idx < q.A.sizeC)) = true := e'
        rcases hc x.tree c q e1 e2 with ⟨q', h1, h2⟩ | h1
        · unfold entInA
          refine Eq.mpr (Bool.or_eq_true _ _) (Or.inr ?_)
          rw [h.arrays, e1, Option.bind_some, h1]
          show (decide (x.row < q'.A.sizeI) && decide (x.idx < q'.A.sizeC)) = true
          rw [h2]
          exact e3
        · refine entInA_of_entIn sent own b x ?_
          unfold entIn
          rw [h1]
          exact e3

theorem affInA_on (free : Option ℕ) (late : List (ℕ × E × E)) (a b : K9.Part) (h : Rides own a b)
    (g : Grows a b) (hc : Comes sent own a b) (f : Aff)
    (e : affInA sent own free late a f = true) : affInA sent own free late b f = true := by
  unfold affInA at e ⊢
  obtain ⟨e1, e2⟩ := Eq.mp (Bool.and_eq_true _ _) e
  refine Eq.mpr (Bool.and_eq_true _ _) ⟨?_, ?_⟩
  · exact List.all_eq_true.2 fun x hx =>
      entInA_on sent own a b h hc x (List.all_eq_true.1 e1 x hx)
  · exact List.all_eq_true.2 fun x hx =>
      slotIn_on own free late a b h g x.1 (List.all_eq_true.1 e2 x hx)

/-- **The public test rides forward, also across the sending of what was ahead.** -/
theorem formsInA_on (Rd : Readers) (piece : ℕ) (run : String) (s s' : S) (a b : K9.Part) (R : Read)
    (ha : segAt? s = some a) (hb : segAt? s' = some b) (hs : Rd.forms piece run s = some R)
    (hs' : Rd.forms piece run s' = some R) (hm : mergeOf s' = mergeOf s) (h : Rides own a b)
    (g : Grows a b) (hc : Comes sent own a b) (hl : lateOk R.late b = true)
    (hin : formsInA Rd sent own piece run s = true) :
    formsInA Rd sent own piece run s' = true := by
  unfold formsInA at hin ⊢
  rw [ha, hs] at hin
  rw [hb, hs', hm]
  obtain ⟨_, e⟩ := Eq.mp (Bool.and_eq_true _ _) hin
  exact Eq.mpr (Bool.and_eq_true _ _) ⟨hl, List.all_eq_true.2 fun f hf =>
    affInA_on sent own (mergeOf s) R.late a b h g hc f (List.all_eq_true.1 e f hf)⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.entInA_on
#print axioms VerifiableInference.Desc.Sound.affInA_on
#print axioms VerifiableInference.Desc.Sound.formsInA_on
