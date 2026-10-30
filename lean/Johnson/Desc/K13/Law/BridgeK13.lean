-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/BridgeK13.lean: THE TIES OF K13's FILES, AS THEY ARE TYPED, SERVE IN THE SECOND
FORM (`TiedAtR`) AT A FILLING FROM WHICH EIGHT NAMES AND ONE CONJUNCT OF "in order" HAVE BEEN
STRUCK. Definitions, and statements with their proofs; free of any kind of sub-protocol. Why. Our
ties spend eight names of the door that only carry a fact on the verifier's state: the proximity
test's four, "K13.weightsOk" and our three; and our conjunct of "in order". These leave the
filling; the facts come from the condition Rch. The bridge (Johnson/Desc/Sound/PlusDoorA.lean)
carries a tie from the wider filling to the narrower. `plus13 D d Mg`: the three struck layers
  laid over Mg again (`fillK12`, Johnson/Desc/K12/Door/FillK12.lean; `fillWeights`,
    Johnson/Desc/First/FillWeights.lean; `fillK13Plus`: ours).
  `cA13`: the class: the eight names. `FactsK13 D d Mg x`: WHAT Rch IS TO GIVE at a state: our
  conjunct of "in order"; the eight tests, each in the text of the layer that laid it; and that
    `pubP` says nothing beside the test at the eight.
  `plus13_hand`, `plus13_io`: outside the class the wider tests are Mg's; the wider "in order" gives
    Mg's.
  `facts13`: `FactsK13` gives the bridge's `FactsAt`, at every border. `tiedAtR_plus13`: **THE
  CALL**: a tie at `plus13 D d Mg` is a tie in the second form at Mg, WHERE the test on the two
    doors accepts at borders k and k + 1, Rch gives `FactsK13`, and Rch is handed on.
What is not claimed. `FactsK13` at any state: one induction a name along the fold is owed, each by
the files that lay the name. Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.PlusDoorA
import Johnson.Desc.K13.Law.FillK13
import Johnson.Desc.K12.Door.FillK12
import Johnson.Desc.First.FillWeights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers More fillWeights weightsItem
  weightsB)
open VerifiableInference.Desc.K12.Door (K12Data fillK12 k12Item atFirstBook atFirstSeats
  atFirstShapes atFirstFits)
open VerifiableInference.Desc.Sound (Frame Piece TiedAt TiedAtR HandsOn widen doorsFitB FactsAt
  tiedAtR_of_classA)

section
variable {Pp W : Type} {nR : ℕ}

/-- **The three struck layers laid over Mg again.** -/
def plus13 (D : DataK13 Pp W nR) (d : K12Data) (Mg : Meaning Pp W) : Meaning Pp W :=
  fillK13Plus D (fillWeights (fillK12 d Mg))

/-- **The class**: the eight names. -/
def cA13 (q : Pub) : Bool := k13PlusItemC q || weightsItem q || k12Item q

/-- **What the condition beside the promise is to give** at a state. -/
structure FactsK13 (D : DataK13 Pp W nR) (d : K12Data) (Mg : Meaning Pp W) (x : Pp × S) :
    Prop where
  order : inOrderK13 D.codes D.shape D.layout x.2 = true
  masks : pileMasksC x.2 = true
  within : pileWithinC x.2 = true
  oneRow : oneRowC x.2 = true
  weights : weightsB x.2 = true
  book : atFirstBook d.ft x.2 = true
  seats : atFirstSeats d.L x.2 = true
  shapes : atFirstShapes d.M x.2 = true
  fits : atFirstFits x.2 = true
  quiet : ∀ q, cA13 q = true → Mg.pubP q x

variable (D : DataK13 Pp W nR) (d : K12Data) (Mg : Meaning Pp W)

/-- Outside the class the wider tests are Mg's. -/
theorem plus13_hand (q : Pub) (h : cA13 q = false) (x : Pp × S) :
    (plus13 D d Mg).pub q x = Mg.pub q x := by
  unfold cA13 at h
  simp only [Bool.or_eq_false_iff] at h
  unfold plus13
  rw [fillK13Plus_else D _ q h.1.1, First.fillWeights_else _ q h.1.2,
    K12.Door.fillK12_else d Mg q h.2]

/-- The wider "in order" gives Mg's. -/
theorem plus13_io (x : Pp × S) (h : (plus13 D d Mg).inOrder x = true) : Mg.inOrder x = true := by
  have h' : (Mg.inOrder x && inOrderK13 D.codes D.shape D.layout x.2) = true := h
  exact (Bool.and_eq_true _ _ ▸ h').1

/-- In the class each test is its layer's, so it accepts where the facts hold. -/
theorem plus13_class (x : Pp × S) (hF : FactsK13 D d Mg x) (q : Pub) (h : cA13 q = true) :
    (plus13 D d Mg).pub q x = true := by
  cases q with
  | more seg name =>
    cases seg with
    | some m => simp [cA13, k13PlusItemC, weightsItem, k12Item] at h
    | none =>
      simp only [cA13, k13PlusItemC, weightsItem, k12Item, Option.isNone_none, Bool.true_and,
        Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (((rfl | rfl) | rfl) | rfl) | (((rfl | rfl) | rfl) | rfl)
      · exact hF.masks
      · exact hF.within
      · exact hF.oneRow
      · exact hF.weights
      · exact hF.book
      · exact hF.seats
      · exact hF.shapes
      · exact hF.fits
  | _ => simp [cA13, k13PlusItemC, weightsItem, k12Item] at h

variable {A Cl : Type} {C : CK} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
  (get : A → Pp × S)

/-- `FactsK13`, asked at a state without a mark alone, gives what the bridge asks, at every
border. -/
theorem facts13 (k : ℕ) (a : A × Fr.E.Str)
    (hF : (get a.1).2.failed = none → FactsK13 D d Mg (get a.1)) :
    FactsAt Mg (plus13 D d Mg).more (plus13 D d Mg).pub (plus13 D d Mg).inOrder cA13 links ps get
      k a := fun hm =>
  ⟨fun h => by
    show (Mg.inOrder (get a.1) && inOrderK13 D.codes D.shape D.layout (get a.1).2) = true
    rw [h, (hF hm).order]
    rfl, fun q _ hc => ⟨plus13_class D d Mg _ (hF hm) q hc, (hF hm).quiet q hc⟩⟩

/-- **THE CALL.** -/
theorem tiedAtR_plus13 (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ) (q : Piece C Fr A Cl W)
    (hD : doorsFitB Mg.more (plus13 D d Mg).more cA13 links ps k = true)
    (hD' : doorsFitB Mg.more (plus13 D d Mg).more cA13 links ps (k + 1) = true)
    (hF : ∀ j a, Rch j a → (get a.1).2.failed = none → FactsK13 D d Mg (get a.1))
    (hs : HandsOn Rch k q)
    (h : TiedAt N (plus13 D d Mg) links ps get k q) : TiedAtR N Mg links ps get Rch k q :=
  tiedAtR_of_classA N Mg (plus13 D d Mg).more (plus13 D d Mg).pub (plus13 D d Mg).inOrder cA13
    links ps get Rch k q (plus13_hand D d Mg) (plus13_io D d Mg) hD hD'
    (fun j a hr => facts13 D d Mg links ps get j a (hF j a hr)) hs h

end

end VerifiableInference.Desc.K13.Law
