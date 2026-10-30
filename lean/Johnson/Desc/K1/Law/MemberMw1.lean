-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/MemberMw1.lean: K01_law: THE MEMBERS AT THE WIDER MEANING AT WHICH k01_fiftyR TAKES k01_fifty: mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) (the composed meaning; plus13's door and public tests; "in order" with groupAllB beside): GENERAL IN
Dm · dk · Mg₀. ALL OVER FOUR THEOREMS (fillsK1_plus13_of, Johnson/Desc/K1/Law/FillsAtPlus13.lean · hrest_plus13, RestAtPlus13.lean · noForms_plus13 · fitsOpen_plus13, DoorAtPlus13.lean), which speak of plus13: mw1 parts from plus13 in ONE conjunct of "in order" alone.
  inAt_down       inside the promise at mw1 ⟹ inside the promise at plus13 (kind-free; at letters)
  fillsK1_mw1     FillsK1's nine equations at mw1, at io0 a := ((mgAll Dm Mg₀).inOrder a && liveB Dm.N Dm.shape a.2)
  hrest_mw1       the top's binder hrest at mw1, under hrest_plus13's own named premises
  boolsK1_mw1     BoolsK1 at mw1: noForms · fitsOpen paid; idx stays a premise
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.K01FiftyR
import Johnson.Desc.K1.Law.RestAtPlus13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13.Law (openAt plus13 cA13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-- **Inside the promise at mw1 ⟹ inside the promise at plus13.** -/
theorem inAt_down {Pp W : Type} {nR : ℕ} (N : Numbers) (D : K13.Law.DataK13 Pp W nR) (dk : K12Data)
    (M9 : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ) (x : Pp × S) (y : Strs)
    {xb : S → Bool}
    (h : InAt N (mw1 N D dk M9 xb) links ps k x y) : InAt N (plus13 D dk M9) links ps k x y := by
  obtain ⟨⟨hd, hr⟩, hm⟩ := h
  refine ⟨⟨hd, ?_⟩, hm⟩
  rcases hr with hx | ⟨h1, h2, h3, h4⟩
  · exact Or.inl hx
  · refine Or.inr ⟨?_, h2, h3, h4⟩
    simp only [Bool.and_eq_true] at h1 ⊢
    obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩, g⟩ := h1
    have e' : ((plus13 D dk M9).inOrder x && liveX N D.shape xb x.2) = true := e
    exact ⟨⟨⟨⟨⟨a, b⟩, c⟩, (Bool.and_eq_true _ _ ▸ e').1⟩, f⟩, g⟩

/-- **Inside the promise at mw1 with a further test ⟹ inside the promise at mw1 without it; and the test holds.** -/
theorem inAt_drop {Pp W : Type} {nR : ℕ} {N : Numbers} {D : K13.Law.DataK13 Pp W nR} {dk : K12Data}
    {M9 : Meaning Pp W} {links : List ModelPart} {ps : List Place} {k : ℕ} {x : Pp × S} {y : Strs}
    {xb : S → Bool} (h : InAt N (mw1 N D dk M9 xb) links ps k x y) :
    InAt N (mw1 N D dk M9) links ps k x y ∧ xb x.2 = true := by
  obtain ⟨⟨hd, hr⟩, hm⟩ := h
  rcases hr with hx | ⟨h1, h2, h3, h4⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, e⟩, f⟩, g⟩ := h1
    have e' : ((plus13 D dk M9).inOrder x && liveX N D.shape xb x.2) = true := e
    rw [Bool.and_eq_true] at e'
    have e2 := e'.2
    unfold liveX at e2
    rw [Bool.and_eq_true] at e2
    refine ⟨⟨⟨hd, Or.inr ⟨?_, h2, h3, h4⟩⟩, hm⟩, e2.2⟩
    simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨a, b⟩, c⟩, ?_⟩, f⟩, g⟩
    show ((plus13 D dk M9).inOrder x && liveX N D.shape (fun _ => true) x.2) = true
    unfold liveX
    rw [e'.1, e2.1]
    rfl

section
variable {Xi Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **FillsK1 at mw1.** -/
theorem fillsK1_mw1 (xb : S → Bool := fun _ => true) :
    FillsK1 Dm.pubD Dm.G Dm.arr Dm.smp Dm.ms Dm.decT Dm.shape Dm.layout
      (fun a => (mgAll Dm Mg₀).inOrder a && liveX Dm.N Dm.shape xb a.2)
      (plus13 (d13 Dm) dk Mg₀).pub XV Dm.sent
      (First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀) (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb) := by
  have h := fillsK1_plus13_of Dm dk Mg₀ _ fun _ => rfl
  exact
    { held := h.held, shown := h.shown, noColl := h.noColl, pin := h.pin, decodes := h.decodes
      pinW := h.pinW
      inOrder := fun a => by
        show ((plus13 (d13 Dm) dk (mgAll Dm Mg₀)).inOrder a && liveX Dm.N Dm.shape xb a.2) = _
        rw [h.inOrder a, Bool.and_right_comm]
      pub := h.pub, pubP := h.pubP }

/-- **hrest at mw1.** -/
theorem hrest_mw1 (Z : ProofFile.Pub) (Bs : ProofFile.PureBase)
    (H : ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ x x' y q,
      YesOf (blkL Z Bs.G₀ l d X arrs) x x' →
      InAt Dm.N (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true) (noL l d) x y →
      q ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      sevenItem q = false → (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀)).pub q x' = true :=
  fun l hl d X arrs hX x x' y q hy hIn hq hq' h7 =>
    H l hl d X arrs hX x x' y q hy (inAt_down _ _ _ _ _ _ _ _ _ hIn) hq hq' h7

/-- **BoolsK1 at mw1.** -/
theorem boolsK1_mw1 (hM : Mg₀.more = {}) (seats : List (ℕ × ℕ)) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (hidx : ∀ l, l < 25 → ∀ d : Bool,
      ∀ u ∈ First.sampledIn Dm.N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
        seats.idxOf u < Dm.N.msgsAt (flatPlacesOf linksFull true)[noL l d]?)
    (xb : S → Bool := fun _ => true) :
    BoolsK1 Dm.N Dm.pubD seats Z G₀ (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀) xb).more (.more none "K12.bookFits") :=
  { idx := hidx, noForms := noForms_plus13 Dm dk Mg₀ hM, fitsOpen := fitsOpen_plus13 Dm dk Mg₀ hM }

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.inAt_down
#print axioms VerifiableInference.Desc.K1.inAt_drop
#print axioms VerifiableInference.Desc.K1.fillsK1_mw1
#print axioms VerifiableInference.Desc.K1.hrest_mw1
#print axioms VerifiableInference.Desc.K1.boolsK1_mw1
