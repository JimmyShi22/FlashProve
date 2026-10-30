-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/LotFind.lean: CONDITIONAL.

What is here. WHICH HALF K4's LOT's HONEST SIDE HOLDS AT A PLACE, AND WHAT A LIST OF FALLS THAT
HOLDS K4's OWN SAYS THERE. (1) Where x is a member of the lot's own list (`k4From`), `k4PubOf`
returns Q at its parameters and the test `k4TableFits` accepts Q, the FIRST half of `k4HLot` at the
place `k4Place Q` is `k4Half` at Q: in the form of the premise hg, "what my own list holds at the
place", of the frame's law on which half is found at a place (`firstOf_find`, Honest/FirstFind.lean;
not imported here). No earlier member can stand there: one member at most bears a given link's
number, x.2.link (the library's `k4From_link_inj`, Johnson/Desc/ProofFile/Lot/K4One.lean). (2) Where
`k4Fall Q` is among a list of falls and the falls at `k4Place Q`, as one (`fallOf`,
Honest/Side.lean), say nothing, the verifier's test on one sampled element, written as a function of
K4's own challenges (`k4CoinZero`), says nothing: the element is not seen to be 0; the test also
says nothing while that round's challenge has not been heard, and where that challenge holds no
element (it is read as 1 there). General in the public part, the ground and the lists. Statements
and proofs.

  `find_unique`   the first member of a list that passes a test, where all that pass are one.
  `k4PubOf_link`   the public data's link is the parameters'.
  `k4HLot_find`   **the lot's half at the place.**
  `coin_of_fallOf`   **the falls at the place say nothing: so does the test on the sampled
      element.**

Not shown here. That x is a member of the list at any ground; that `k4PubOf` returns; THAT
`k4TableFits` ACCEPTS ANYWHERE: three hypotheses of (1). hm: THAT `k4Fall Q`, AT THIS VERY Q, STANDS
IN ANY LIST OF FALLS: a hypothesis of (2); nothing here makes such a list. That the lot stands in
any prover's list of lots, and that no other lot has a half at the place. Nothing on what a half
plays. WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops,
unopened, at every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/ and at
every module whose name begins Cb.Bridge: it stopped at 2 modules under Johnson/Bridge/, the two at
which the walk from Honest/K4/Part.lean stops too; at none of the others; it saw no module whose
name holds RecCompile.

Kin. `find_unique`, a law on lists alone, IS IN THE LIBRARY ALREADY, under the same short name, up
to the letters, the brackets and the order of its arguments: `AtPublicFiles.Key.find_unique`
(E2E/KeyPlanesRead.lean). It is typed anew here because this file does not build on that one, which
would bring more than a thousand modules beneath it. Of the three others no twin is known to its
writers. `k4From_link_inj` (Johnson/Desc/ProofFile/Lot/K4One.lean), which `k4HLot_find` calls, is
the library's.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Part
import Johnson.Desc.ProofFile.Lot.K4One

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest

variable {W₀ Rc Tr X : Type}

/-- The first member of a list that passes a test, where all members that pass are one. -/
theorem find_unique {α : Type} {p : α → Bool} {a : α} {l : List α} (ha : a ∈ l) (hp : p a = true)
    (hu : ∀ b ∈ l, p b = true → b = a) : l.find? p = some a := by
  induction l with
  | nil => cases ha
  | cons b t ih =>
    by_cases hb : p b = true
    · have e := hu b (List.mem_cons.2 (Or.inl rfl)) hb
      simp only [List.find?_cons, e, hp]
    · have hb' : p b = false := Bool.eq_false_of_not_eq_true hb
      simp only [List.find?_cons, hb']
      refine ih ?_ fun c hc => hu c (List.mem_cons_of_mem _ hc)
      rcases List.mem_cons.1 ha with e | h'
      · exact absurd (e ▸ hp) hb
      · exact h'

/-- The public data's link is the parameters'. -/
theorem k4PubOf_link {Z : Pub} {p : OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (h : k4PubOf Z p = some Q) : Q.link = p.link := by
  unfold k4PubOf at h
  obtain ⟨r0, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- CONDITIONAL: on the three hypotheses. **THE LOT's HALF AT THE PLACE.** -/
theorem k4HLot_find (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) {Z : Pub}
    {G : Ground} {x : Bool × OnBytes.Desc.First.K4.Par} {Q : K4Pub}
    (hx : x ∈ k4From Z G G.built.toList 0 none) (hQ : k4PubOf Z x.2 = some Q)
    (hF : k4TableFits Q = true) :
    ((k4HLot (Rc := Rc) (X := X) cells weights look).halves Z G).find?
      (fun z => z.place == k4Place Q) =
      some (k4Half cells weights k4Tokens (look Z G) Q) := by
  refine find_unique ?_ (beq_self_eq_true (k4Place Q)) ?_
  · refine List.mem_filterMap.2 ⟨x, hx, ?_⟩
    rw [hQ]
    simp [Option.filter, hF]
  · intro b hb hp
    obtain ⟨y, hy, e⟩ := List.mem_filterMap.1 hb
    obtain ⟨Q', hQ', rfl⟩ := Option.map_eq_some_iff.1 e
    obtain ⟨hy', -⟩ := Option.filter_eq_some_iff.1 hQ'
    have ep : k4Place Q' = k4Place Q := eq_of_beq hp
    have el : (some Q'.link : Option Nat) = some Q.link :=
      congrArg VerifiableInference.Desc.Place.link ep
    have exy : y = x := k4From_link_inj Z G _ _ _ y x hy hx (by
      rw [← k4PubOf_link hy', ← k4PubOf_link hQ]
      exact Option.some.inj el)
    subst exy
    rw [Option.some.inj (hy'.symm.trans hQ)]

/-- **THE FALLS AT THE PLACE SAY NOTHING: SO DOES THE TEST ON THE SAMPLED ELEMENT.** -/
theorem coin_of_fallOf {S : Type} {fs : List (Fall S)} {Q : K4Pub} (hm : k4Fall Q ∈ fs) {s : S}
    {ds : List Fmt.Drawn} (h : fallOf fs (k4Place Q) s ds = none) : k4CoinZero Q ds = none := by
  unfold fallOf at h
  rw [List.findSome?_eq_none_iff] at h
  exact h (k4Fall Q) (List.mem_filter.2 ⟨hm, beq_self_eq_true (k4Place Q)⟩)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.find_unique
#print axioms ProofFile.Honest.K4.k4PubOf_link
#print axioms ProofFile.Honest.K4.k4HLot_find
#print axioms ProofFile.Honest.K4.coin_of_fallOf
