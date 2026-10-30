-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameRides.lean: the premise LettersRide of the frame's ties (FrameTied.lean),
cut down to what a filling of the table's letters truly owes.

  front_parts     what FrontAt holds, clause by clause
  StringsRide     what is asked of the letters that read the oracles' strings, at ONE record:
                  decodes, shown, noColl forward, every open item backward, over a step of the
                  strings that stays below base
  lettersRide_same   at "the record is handed on" ("laid", the chain's front), at a quiet row that
                  opens nothing, where the door's filling makes nothing: LettersRide FROM
                  StringsRide ALONE: all that reads the record alone comes of the promise in front

Limits. StringsRide is shown at no filling: its payer shows that each letter reads of the strings
the stored table's cells and the trees below base alone. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameTiedStep

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers Pub openSets pubSets rowOf onAt
  start sampledIn samplesHeld pubOfItems quietRow openSets_succ pubSets_succ sampledIn_step)

section
variable {P W : Type} {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place}
  {k : Nat}

/-- What FrontAt holds, clause by clause. -/
theorem front_parts {a : P × S} {y : Strs} (hu : a.2.failed = none)
    (h : FrontAt N Mg links ps k a y) :
    Mg.inOrder a = true ∧
      (∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.held x.1 x.2 a = true ∧ Mg.shown x.1 x.2 y ∧ Mg.noColl x.1 x.2 a y) ∧
      ∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q a := by
  unfold FrontAt onAt at h
  rcases h.2 with h' | ⟨h1, h2, h3, h4⟩
  · exact absurd hu h'
  · simp only [Bool.and_eq_true] at h1
    unfold samplesHeld at h2
    rw [List.all_eq_true] at h2
    exact ⟨h1.1.1.2, fun x hx => ⟨h2 x hx, h3 x hx⟩, h4⟩

/-- What is asked of the letters that read the strings, at one record. O: the items that are open in
front of the block, as the promise reads them; Op: those that are open behind, as the relation
reads them. -/
structure StringsRide (N : Numbers) (Mg : Meaning P W) (base : Nat) (O : List Item)
    (Op : Item → Prop) : Prop where
  decodes : ∀ a y y', Stays base y y' → Mg.decodes a y → Mg.decodes a y'
  shown : ∀ x y y', Stays base y y' → x ∈ sampledIn N O → Mg.shown x.1 x.2 y → Mg.shown x.1 x.2 y'
  noColl : ∀ a x y y', Stays base y y' → x ∈ sampledIn N O → Mg.noColl x.1 x.2 a y →
    Mg.noColl x.1 x.2 a y'
  items : ∀ a y y' w i, Stays base y y' → Op i → i.holds N Mg a y' w → i.holds N Mg a y w

/-- **At "the record is handed on" LettersRide comes of StringsRide alone.** -/
theorem lettersRide_same {pk : Place} {base : Nat} {f : S → Except String S}
    (hf : ∀ s t, f s = .ok t → t = s) (hk : ps[k]? = some pk)
    (hq : quietRow (rowOf links pk) = true) (ho : (rowOf links pk).outs = [])
    (hm : DoorIdle Mg links pk)
    (H : StringsRide N Mg base ((openSets links ps (start links))[k]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1))) :
    LettersRide N Mg (Yes f) base (FrontAt N Mg links ps k)
      ((openSets links ps (start links))[k + 1]?.getD [])
      ((pubSets Mg.more links ps)[k + 1]?.getD [])
      (openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) (k + 1)) := by
  have eS : sampledIn N ((openSets links ps (start links))[k + 1]?.getD []) =
      sampledIn N ((openSets links ps (start links))[k]?.getD []) := by
    rw [openSets_succ links ps (start links) k pk hk]
    exact sampledIn_step N _ _ hq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p s t y y' e hy h
    obtain rfl := hf s t e
    exact H.decodes _ _ _ hy h
  · intro p s t y e hu hF
    obtain rfl := hf s t e
    exact (front_parts hu hF).1
  · intro p s t y q e hu hF hx
    obtain rfl := hf s t e
    exact pub_of_kept hk ho hm hu hF hx
  · intro p s t y q e hu hF hx
    obtain rfl := hf s t e
    rw [pubSets_succ Mg.more links ps k pk hk] at hx
    exact (front_parts hu hF).2.2 q (mem_pubStep hm hx)
  · intro p s t y x e hu hF hx
    obtain rfl := hf s t e
    rw [eS] at hx
    exact ((front_parts hu hF).2.1 x hx).1
  · intro p s t y y' x e hy hu hF hx
    rw [eS] at hx
    exact H.shown x _ _ hy hx ((front_parts hu hF).2.1 x hx).2.1
  · intro p s t y y' x e hy hu hF hx
    obtain rfl := hf s t e
    rw [eS] at hx
    exact H.noColl _ x _ _ hy hx ((front_parts hu hF).2.1 x hx).2.2
  · intro p s t y y' w i e hy _ _ hop h
    obtain rfl := hf s t e
    exact H.items _ _ _ w i hy hop h

end

#print axioms lettersRide_same

end Johnson.Desc.First.Walk.Tied
