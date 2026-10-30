-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HandsMoreAtLater.lean: THE
ROW "E1.more" OF K01_law: THE SIXTH FIELD, "more", OF IM.Hands (Johnson/IMR/HandsDef.lean: what one
sub-protocol owes) AT A LATER SENDING OF KIND K1, WHERE THE FURTHER TESTS E ARE THE TWO TESTS OF THE
TABLE OF JOINTS' PROMISE THAT IM.BK LEAVES OUT (HashBuild.EPub: "in
order", and every public item that is open or tied holds). GENERAL IN THE MEANING Mg: no named item
is spoken of. Definitions, and statements with their proofs.
A FIND, AND ITS CURE. The fields inOrder and pub of FillL (Johnson/Desc/K1/Law/KeepAtLater.lean)
are asked INSIDE THE WHOLE PROMISE (InAt: with the strings y: "decodes",
the OOD samples held, shown, no collision, pubP). IM.Hands.more hands over THE PROMISE's HALF WITH
CODE alone (IM.XK). So at one fixed Mg these binders do not give "more". THE CURE: the half with
code of Mg's promise IS the whole promise of bare Mg: Mg with these five letters set to "true"
(inAt_bare). So an arm that is shown GENERALLY IN Mg from Mg.pub and Mg.inOrder alone (as hPub_of,
PubAtLaterCall.lean, is: it spends hMg : Mg.pub = pubAll D base) is called at bare Mg.
  InB N Mg links ps k x   the promise's half with code in front of sub-protocol k, and no mark.
  bare Mg                 Mg with decodes, held, shown, noColl, pubP set to "true"; pub, inOrder,
                          more and every sentence on a witness as they were.
  inAt_bare               InB at Mg gives InAt at bare Mg, at every y.
  yesOf_of_yes            an accepting step of a seated sub-protocol under B is B's own YesOf.
  more_block              **THE FIELD**, from three arms in InB's form: hOrd ("in order" behind),
                          hRide (an item open on both sides), hNew (an item that comes: RowL's T).
  more_block_bare         the same, the three arms in the top's own form (InAt) AT bare Mg.
What is not claimed. The three arms. That E is the term at which the join is called. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.KeepAtLater
import Johnson.Desc.AtSeats.HandsMore
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Flat OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More)
open VerifiableInference.Desc.K13.Law (openAt)
open HashBuild (EPub epub_parts epub_of)

variable {Pp W : Type}

/-- The promise's half with code in front of sub-protocol k, and no mark. -/
def InB (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (x : Pp × S) : Prop :=
  IM.XK N links ps (EPub x.1 Mg links ps) k x.2 = true ∧ x.2.failed = none

/-- The meaning with the five letters that the promise asks beside its half with code set to
"true". -/
def bare (Mg : Meaning Pp W) : Meaning Pp W :=
  { Mg with
    decodes := fun _ _ => True
    held := fun _ _ _ => true
    shown := fun _ _ _ => True
    noColl := fun _ _ _ _ => True
    pubP := fun _ _ => True }

/-- **The half with code of Mg's promise is the whole promise of bare Mg.** -/
theorem inAt_bare {N : Numbers} {Mg : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ}
    {x : Pp × S} (h : InB N Mg links ps k x) (y : Strs) : InAt N (bare Mg) links ps k x y := by
  obtain ⟨hx, hm⟩ := h
  obtain ⟨a1, a2, a3, a4, a5⟩ := IM.xk_parts hx
  unfold EPub at a5
  rw [Bool.and_eq_true] at a5
  refine ⟨⟨trivial, Or.inr ⟨?_, ?_, fun _ _ => ⟨trivial, trivial⟩, fun _ _ => trivial⟩⟩, hm⟩
  · simp only [Bool.and_eq_true]
    exact ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a5.1⟩, a5.2⟩, a4⟩
  · unfold First.samplesHeld
    exact List.all_eq_true.2 fun _ _ => rfl

/-- An accepting step of a seated sub-protocol under B is B's own yes on rounds that fit. -/
theorem yesOf_of_yes {B : Block S Unit} {c : Block S ProofFile.Cl}
    (hc : c.UnderR (B.retype : Block S ProofFile.Cl)) {ft : ℕ} {s s' : S} (h : IM.Yes ft c s s')
    (z : Pp) : YesOf B (z, s) (z, s') := by
  obtain ⟨rs, cols, n, hst⟩ := h
  obtain ⟨hfit, gs, hd⟩ := step_ok ft _ _ _ rs cols n hst
  rw [hc.1] at hfit
  exact ⟨rfl, rs, gs, hfit, hc.2 _ _ _ _ hd⟩

/-- **THE FIELD "more"**, from three arms in the form of the promise's half with code. -/
theorem more_block (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (z : Pp)
    (ft k : ℕ) (B : Block S Unit) (c : Block S ProofFile.Cl)
    (hc : c.UnderR (B.retype : Block S ProofFile.Cl)) (T : List Pub)
    (hpubs : ∀ q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] ++
        First.pubOfItems (openAt links ps (k + 1)),
      q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) ∨
        q ∈ T)
    (hOrd : ∀ x x', YesOf B x x' → InB N Mg links ps k x → Mg.inOrder x' = true)
    (hRide : ∀ x x' q, YesOf B x x' → InB N Mg links ps k x →
      q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) →
      q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] ++
        First.pubOfItems (openAt links ps (k + 1)) → Mg.pub q x' = true)
    (hNew : ∀ x x' q, YesOf B x x' → InB N Mg links ps k x → q ∈ T → Mg.pub q x' = true) :
    ∀ s s', IM.Yes ft c s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps (EPub z Mg links ps) k s = true → EPub z Mg links ps (k + 1) s' = true := by
  intro s s' hy h0 _ hx
  have hY : YesOf B (z, s) (z, s') := yesOf_of_yes hc hy z
  have hI : InB N Mg links ps k (z, s) := ⟨hx, h0⟩
  have key : ∀ q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] ++
      First.pubOfItems (openAt links ps (k + 1)), Mg.pub q (z, s') = true := by
    intro q hq
    rcases hpubs q hq with hq' | hq'
    · exact hRide _ _ q hY hI hq' hq
    · exact hNew _ _ q hY hI hq'
  exact epub_of (hOrd _ _ hY hI) (fun q hq => key q (List.mem_append_left _ hq))
    fun q hq => key q (List.mem_append_right _ hq)

/-- The same, the three arms in the top's own form, at bare Mg. y₀: any strings. -/
theorem more_block_bare (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place)
    (z : Pp) (ft k : ℕ) (B : Block S Unit) (c : Block S ProofFile.Cl)
    (hc : c.UnderR (B.retype : Block S ProofFile.Cl)) (T : List Pub) (y₀ : Strs)
    (hpubs : ∀ q ∈ (First.pubSets Mg.more links ps)[k + 1]?.getD [] ++
        First.pubOfItems (openAt links ps (k + 1)),
      q ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) ∨
        q ∈ T)
    (hOrder : ∀ x x' y, YesOf B x x' → InAt N (bare Mg) links ps k x y →
      (bare Mg).inOrder x' = true)
    (hPub : ∀ x x' y q, YesOf B x x' → InAt N (bare Mg) links ps k x y →
      q ∈ (First.pubSets (bare Mg).more links ps)[k]?.getD [] ++
        First.pubOfItems (openAt links ps k) →
      q ∈ (First.pubSets (bare Mg).more links ps)[k + 1]?.getD [] ++
        First.pubOfItems (openAt links ps (k + 1)) → (bare Mg).pub q x' = true)
    (hNew : ∀ x x' y q, YesOf B x x' → InAt N (bare Mg) links ps k x y → q ∈ T →
      (bare Mg).pub q x' = true) :
    ∀ s s', IM.Yes ft c s s' → s.failed = none → s'.failed = none →
      IM.XK N links ps (EPub z Mg links ps) k s = true → EPub z Mg links ps (k + 1) s' = true :=
  more_block N Mg links ps z ft k B c hc T hpubs
    (fun x x' hy hI => hOrder x x' y₀ hy (inAt_bare hI y₀))
    (fun x x' q hy hI h1 h2 => hPub x x' y₀ q hy (inAt_bare hI y₀) h1 h2)
    fun x x' q hy hI hq => hNew x x' y₀ q hy (inAt_bare hI y₀) hq

end VerifiableInference.Desc.K1
