-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PlusDoor.lean: A TIE THAT IS TYPED AT A WIDER FILLING OF THE TABLE's LETTERS
SERVES, IN THE SECOND FORM (`TiedAtR`, Johnson/Desc/Sound/ChainOfPromisesR.lean),
AT THE NARROWER ONE. Definitions, and statements with their proofs; free of any kind of
sub-protocol. Why. Ties have been typed at fillings whose door holds names that only carry a fact
on the verifier's state across many sub-protocols, and whose "in order" has conjuncts of that
sort. These leave the filling; the facts come from the condition Rch ("this state is reached")
instead. So that no tie is typed anew: a tie at the wider filling is carried to the narrower.
  `widen Mg M pub' io'`: the filling Mg with another door, other tests of the public items and
  another "in order". Nothing else turns: what an item says, "decodes", "held", "shown", "no
    collision" and what a public item says beside its test are Mg's, by the make.
  `onQ_down`: the promise at the wider filling gives the promise at the narrower, WHERE, at border
  k:
    every public item that is open at Mg's door is open at M; the wider "in order" gives Mg's; at
    each public item that is open at Mg's door or tied to an open item the wider test gives Mg's.
  `onQ_up`: the promise at the narrower gives the promise at the wider, WHERE, at a state without a
    mark: Mg's "in order" gives the wider; each public item that is open at M, or tied, passes the
    wider test; each that is open at M says what it says beside its test.
  `tiedAtR_of_wider`: **THE BRIDGE**: a tie at a filling Mp is a tie in the second form at Mg, WHERE
    the two say the same of every item and of "decodes"; the promise goes down at border k + 1; it
    goes up, under Rch, at borders k and k + 1; and Rch is handed on over the piece (`HandsOn`).
  `tiedAtR_of_widen`: so at `widen Mg M pub' io'`.
What is not claimed. The premises: that the facts hold at the states that Rch admits is the debt
that takes the place of a keeping at every sub-protocol. Nothing on soundness. Terms:
lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ChainOfPromisesR

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Pub More Meaning Numbers onAt pubSets pubHeld
  pubOfItems openSets start)

section
variable {A Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (M : More)
  (pub' : Pub → P × First.S → Bool) (io' : P × First.S → Bool) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S)

/-- The filling with another door, other tests of the public items and another "in order". -/
def widen (Mg : Meaning P W) (M : More) (pub' : Pub → P × First.S → Bool)
    (io' : P × First.S → Bool) : Meaning P W :=
  { Mg with more := M, pub := pub', inOrder := io' }

/-- **From the wider filling to the narrower.** -/
theorem onQ_down (k : ℕ) (a : A × Fr.E.Str)
    (hsub : ∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], q ∈ (pubSets M links ps)[k]?.getD [])
    (hio : io' (get a.1) = true → Mg.inOrder (get a.1) = true)
    (hpub : ∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [] ++
      pubOfItems ((openSets links ps (start links))[k]?.getD []),
      pub' q (get a.1) = true → Mg.pub q (get a.1) = true)
    (h : onQ N (widen Mg M pub' io') links ps get k a) : onQ N Mg links ps get k a := by
  obtain ⟨hd, hr⟩ := h
  refine ⟨hd, ?_⟩
  rcases hr with hm | ⟨hB, hS, hC, hP⟩
  · exact Or.inl hm
  · refine Or.inr ⟨?_, hS, hC, fun q hq => hP q (hsub q hq)⟩
    simp only [Bool.and_eq_true] at hB ⊢
    obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hB
    refine ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, hio b4⟩, ?_⟩, b6⟩
    have hall := List.all_eq_true.1 b5
    refine List.all_eq_true.2 fun q hq => hpub q hq ?_
    rcases List.mem_append.1 hq with hq | hq
    · exact hall q (List.mem_append_left _ (hsub q hq))
    · exact hall q (List.mem_append_right _ hq)

/-- **From the narrower filling to the wider.** -/
theorem onQ_up (k : ℕ) (a : A × Fr.E.Str)
    (hio : (get a.1).2.failed = none → Mg.inOrder (get a.1) = true → io' (get a.1) = true)
    (hpub : (get a.1).2.failed = none →
      (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [] ++
        pubOfItems ((openSets links ps (start links))[k]?.getD []), Mg.pub q (get a.1) = true) →
      ∀ q ∈ (pubSets M links ps)[k]?.getD [] ++
        pubOfItems ((openSets links ps (start links))[k]?.getD []), pub' q (get a.1) = true)
    (hP' : (get a.1).2.failed = none →
      (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (get a.1)) →
      ∀ q ∈ (pubSets M links ps)[k]?.getD [], Mg.pubP q (get a.1))
    (h : onQ N Mg links ps get k a) : onQ N (widen Mg M pub' io') links ps get k a := by
  obtain ⟨hd, hr⟩ := h
  refine ⟨hd, ?_⟩
  by_cases hm : (get a.1).2.failed = none
  swap
  · exact Or.inl hm
  obtain ⟨hB, hS, hC, hP⟩ := hr.resolve_left fun h => h hm
  refine Or.inr ⟨?_, hS, hC, hP' hm hP⟩
  simp only [Bool.and_eq_true] at hB ⊢
  obtain ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩ := hB
  exact ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, hio hm b4⟩,
    List.all_eq_true.2 (hpub hm (List.all_eq_true.1 b5))⟩, b6⟩

variable (Rch : ℕ → A × Fr.E.Str → Prop)

/-- **THE BRIDGE.** -/
theorem tiedAtR_of_wider (Mp : Meaning P W) (k : ℕ) (q : Piece C Fr A Cl W)
    (hmeans : meansQ (Fr := Fr) N Mp get = meansQ N Mg get) (hdec : Mp.decodes = Mg.decodes)
    (hdown : ∀ b : A × Fr.E.Str, onQ N Mp links ps get (k + 1) b → onQ N Mg links ps get (k + 1) b)
    (hup : ∀ a, Rch k a → onQ N Mg links ps get k a → onQ N Mp links ps get k a)
    (hup' : ∀ b, Rch (k + 1) b → onQ N Mg links ps get (k + 1) b →
      onQ N Mp links ps get (k + 1) b)
    (hs : HandsOn Rch k q) (h : TiedAt N Mp links ps get k q) :
    TiedAtR N Mg links ps get Rch k q := by
  obtain ⟨o, o', R, R', hl, t1, t2, t3, t4, t5, hMark, hDec⟩ := h
  have hrel : ∀ j, relQ (Fr := Fr) N Mp links ps get j = relQ N Mg links ps get j := fun j => by
    unfold relQ
    rw [hmeans]
  rw [hmeans] at t3 t4 t5
  rw [hdec] at hDec
  refine ⟨o, o', R, R', hl, fun a ha hr => t1 a (hup a hr ha),
    fun a τ b ha hr hm hb ho => hdown b (t2 a τ b (hup a hr ha) hm hb ho),
    fun a τ b w ha hr => t3 a τ b w (hup a hr ha), fun a τ b w ha hr => t4 a τ b w (hup a hr ha),
    fun a τ b w i ha hr hm hb hon hall => ?_, hMark, hDec⟩
  refine t5 a τ b w i (hup a hr ha) hm hb (hup' b (hs a τ b hr hb) hon) ?_
  rw [hrel]
  exact hall

/-- **The bridge at `widen`.** -/
theorem tiedAtR_of_widen (k : ℕ) (q : Piece C Fr A Cl W)
    (hdown : ∀ b : A × Fr.E.Str, onQ N (widen Mg M pub' io') links ps get (k + 1) b →
      onQ N Mg links ps get (k + 1) b)
    (hup : ∀ a, Rch k a → onQ N Mg links ps get k a →
      onQ N (widen Mg M pub' io') links ps get k a)
    (hup' : ∀ b, Rch (k + 1) b → onQ N Mg links ps get (k + 1) b →
      onQ N (widen Mg M pub' io') links ps get (k + 1) b)
    (hs : HandsOn Rch k q) (h : TiedAt N (widen Mg M pub' io') links ps get k q) :
    TiedAtR N Mg links ps get Rch k q :=
  tiedAtR_of_wider N Mg links ps get Rch (widen Mg M pub' io') k q
    (by
      funext i a w
      cases i <;> rfl)
    rfl hdown hup hup' hs h

end

end VerifiableInference.Desc.Sound
