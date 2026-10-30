-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ChainOfPromisesR.lean: THE CHAIN OF PROMISES WITH A CONDITION THAT EVERY
ACCEPTING STEP HANDS ON, BESIDE THE TABLE's PROMISE. A second form of the two definitions and three
theorems of Johnson/Desc/Sound/ChainOfPromises.lean. A RULE OVER LETTERS. A file BESIDE the table of
joints: it turns nothing of it.

Why. What is owed at a sub-protocol (`TiedAt`) is asked at EVERY statement that meets the table's
promise at the border in front of it. A theorem that is proved along the verifier's run from the
state at the start ("the state at this border is what the sub-protocols in front made of some rounds
and columns") cannot be spent there: the promise does not say where the state came from. Let Rch k
be any family of conditions, a border a member, that is handed on wherever a sub-protocol accepts.
Then it may stand beside the promise at every border, and each tie may take it as a premise. It
costs no error: it is shown of every accepting transcript.

What is said. `onR k`: the table's promise at border k, and Rch k. `TiedAtR k q`: the clauses of
`TiedAt`, each of the five ties with ONE PREMISE MORE: Rch k a. `HandsOn k q`: Rch k in front, and
the piece accepts: then Rch (k + 1) behind. `tiedAtR_of_tiedAt`: every tie of the first form is one
of the second, for nothing. `EachTiedR`: both at every member of a list. `goodIn_of_tiedR`: a
sub-protocol's law between `onR k` and `onR (k + 1)`, at the table's relations. `chainOfPromisesR`:
so `EachGoodIn` at `onR` and the table's relations. `eachTiedR_of_eachTied`: the first form's list,
with the hand-on at each member, is the second's.

Limits. (1) A RULE OVER LETTERS: Rch is a letter; at Rch := never every tie is free and the
conclusion says nothing: whoever calls the rule for a file owes Rch 0 at the state at the start.
(2) A witness inside Rch ("there are rounds and columns") is not the run's own: a law that spends
Rch may conclude nothing on the run's transcript from it. (3) The Limits of the first form stand.
(4) Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ChainOfPromises

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound

open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers start)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop)

/-- The table's promise at border k, and the condition beside it. -/
abbrev onR (k : ℕ) (a : A × Fr.E.Str) : Prop := onQ N Mg links ps get k a ∧ Rch k a

/-- **What is owed at sub-protocol number k, with Rch k in hand in each tie.** -/
def TiedAtR (k : ℕ) (q : Piece C Fr A Cl W) : Prop :=
  ∃ (o o' : A × Fr.E.Str → Prop) (R R' : A × Fr.E.Str → W → Prop),
    q.GoodIn o o' R R' ∧
    (∀ a, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none → o a) ∧
    (∀ a τ b, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → onQ N Mg links ps get (k + 1) b) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R' b w) ∧
    (∀ a τ b w, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → o' b → relAt (meansQ N Mg get) (outsQ links ps k) b w →
      R a (q.ext a τ w) → relAt (meansQ N Mg get) (insQ links ps k) a (q.ext a τ w)) ∧
    (∀ a τ b w i, onQ N Mg links ps get k a → Rch k a → ¬ (get a.1).2.failed ≠ none →
      q.ior.red.out a τ = some b → onQ N Mg links ps get (k + 1) b →
      relQ N Mg links ps get (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg get i a (q.ext a τ w)) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → (get a.1).2.failed ≠ none →
      (get b.1).2.failed ≠ none) ∧
    (∀ a τ b, q.ior.red.out a τ = some b → Mg.decodes (get a.1) (strsOf Fr a.2) →
      Mg.decodes (get b.1) (strsOf Fr b.2))

/-- Where the piece accepts, the condition is handed on. -/
def HandsOn (k : ℕ) (q : Piece C Fr A Cl W) : Prop :=
  ∀ a τ b, Rch k a → q.ior.red.out a τ = some b → Rch (k + 1) b

/-- **Every tie of the first form is one of the second.** -/
theorem tiedAtR_of_tiedAt (k : ℕ) (q : Piece C Fr A Cl W) (h : TiedAt N Mg links ps get k q) :
    TiedAtR N Mg links ps get Rch k q := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  exact ⟨o, o', R, R', hl, fun a ha _ => t1 a ha, fun a τ b ha _ => t2 a τ b ha,
    fun a τ b w ha _ => t3 a τ b w ha, fun a τ b w ha _ => t4 a τ b w ha,
    fun a τ b w i ha _ => t5 a τ b w i ha, hMark, hDec⟩

/-- Both at every member of a list; the first has the number k. -/
def EachTiedR : ℕ → List (Piece C Fr A Cl W) → Prop
  | _, [] => True
  | k, q :: l =>
    TiedAtR N Mg links ps get Rch k q ∧ HandsOn Rch k q ∧ EachTiedR (k + 1) l

/-- A tied sub-protocol's law between the two conditions and the table's relations at its two
borders. -/
theorem goodIn_of_tiedR (k : ℕ) (q : Piece C Fr A Cl W)
    (h : TiedAtR N Mg links ps get Rch k q) (hs : HandsOn Rch k q) :
    q.GoodIn (onR N Mg links ps get Rch k) (onR N Mg links ps get Rch (k + 1))
      (relQ N Mg links ps get k) (relQ N Mg links ps get (k + 1)) := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  refine spineStepIn q _ _ (meansQ N Mg get) _ (insQ links ps k) (outsQ links ps k)
    (ownOfGoodInWide A Cl W Item C Fr q _ _ _ _ _ (fun a => (get a.1).2.failed ≠ none) o o' R R' hl
      (fun a ha hm => t1 a ha.1 ha.2 hm)
      (fun a τ b ha hm hb ho => ⟨t2 a τ b ha.1 ha.2 hm hb ho, hs a τ b ha.2 hb⟩)
      (fun a τ b w ha hm hb ho hO => t3 a τ b w ha.1 ha.2 hm hb ho hO)
      (fun a τ b w ha hm hb ho hO hR => t4 a τ b w ha.1 ha.2 hm hb ho hO hR) ?_) ?_
  · intro a τ b ha hm hb
    refine ⟨⟨⟨hDec a τ b hb ha.1.1, Or.inl (hMark a τ b hb hm)⟩, hs a τ b ha.2 hb⟩,
      fun w hw => ?_⟩
    have hu : meansQ (Fr := Fr) N Mg get .unmarked b w :=
      hw .unmarked (List.mem_append_right _ (List.mem_singleton.2 rfl))
    exact hMark a τ b hb hm hu
  · intro a τ b w i ha hb hon hall hi hin
    refine t5 a τ b w i ha.1 ha.2 ?_ hb hon.1 hall hi hin
    intro hm
    have hu : meansQ (Fr := Fr) N Mg get .unmarked b w :=
      hall .unmarked (Or.inr (List.mem_append_right _ (List.mem_singleton.2 rfl)))
    exact hMark a τ b hb hm hu

/-- **THE CHAIN OF PROMISES, SECOND FORM.** -/
theorem chainOfPromisesR (l : List (Piece C Fr A Cl W)) :
    ∀ k, EachTiedR N Mg links ps get Rch k l →
      EachGoodIn (onR N Mg links ps get Rch) (relQ N Mg links ps get) k l := by
  induction l with
  | nil => intro _ _; trivial
  | cons q l ih =>
    intro k h
    exact ⟨goodIn_of_tiedR N Mg links ps get Rch k q h.1 h.2.1, ih (k + 1) h.2.2⟩

/-- The hand-on at every member of a list. -/
def EachHandsOn : ℕ → List (Piece C Fr A Cl W) → Prop
  | _, [] => True
  | k, q :: l => HandsOn Rch k q ∧ EachHandsOn (k + 1) l

/-- **The first form's list, with the hand-on at each member, is the second's.** -/
theorem eachTiedR_of_eachTied (l : List (Piece C Fr A Cl W)) :
    ∀ k, EachTied N Mg links ps get k l → EachHandsOn Rch k l →
      EachTiedR N Mg links ps get Rch k l := by
  induction l with
  | nil => intro _ _ _; trivial
  | cons q l ih =>
    intro k h hs
    exact ⟨tiedAtR_of_tiedAt N Mg links ps get Rch k q h.1, hs.1, ih (k + 1) h.2 hs.2⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tiedAtR_of_tiedAt
#print axioms VerifiableInference.Desc.Sound.goodIn_of_tiedR
#print axioms VerifiableInference.Desc.Sound.chainOfPromisesR
#print axioms VerifiableInference.Desc.Sound.eachTiedR_of_eachTied
