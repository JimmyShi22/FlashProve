-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SpinePlain.lean: THE PLAIN FORM OF THE RULE OF Johnson/Desc/Sound/Spine.lean: the
table's shadow. Definitions, statements written as `def … : Prop`, and their proofs.

Why. A kind's law may be owed without an extractor of its own: "outside the round's lost set a true
statement behind gives a true statement in front, and the promise behind is kept", IF THE WITNESS IS
SUPPLIED ONCE, not kind by kind. The table supplies it once: one witness type for the file, the pins
among the items. Here is the form in which no witness is seen.

What is said. `Piece.Plain`: from every statement with the condition, at the block's errors, the
prover has lost towards: where the block says yes, the statement behind has the condition behind,
and if it is TRUE (a predicate on statements) so is the statement in front. `EachPlain`: every block
of a row, between the predicates at its two places. `shadow R`: "there is a witness".
`PlainOfGoodIn`: a block with `GoodIn` between two relations has the plain law between their
shadows. `SpinePlain`: if every block of a row has its own law and the riding (`EachOwn`), the row
has `EachPlain` at the shadows of "every
open item holds".

Whose the form is. It is the notion that Johnson/Desc/Plain/Leads.lean calls "Keeps" ("the
promise behind, and true behind gives true in front", under one lost set), said of a piece; its own
text was not opened for this file; the names here are others, so that the two can stand in one tree.

`OwnOfGoodIn`: a kind's law between its own conditions and relations gives the block's own law at
the table, under four implications: IT SERVES ONLY A KIND WHOSE CONDITION HOLDS AT MARKED RECORDS
TOO (a marked record is inside every promise of the table). `OwnOfGoodInBut`: THE DOOR FOR EVERY
OTHER KIND: its law is asked at unmarked statements alone; at a marked one the mark stays and what
the row opens holds of nothing. `OwnOfGoodInWide`: THE SAME DOOR, WIDER: the two implications on the
relations are asked only where the proof spends them. `OwnBeside`: a condition that rides may stand
beside the promise. `OwnOfPlain`: THE WAY BACK for a row that lays nothing and whose closed items
read the witness through what its context pins: there a kind may owe the plain law, with the pins
inside both predicates.

Limits. (0) `OwnOfPlain` DOES NOT SERVE A ROW THAT CLOSES AN ITEM WHICH READS A COMPONENT THAT IS
NOT PINNED AT THAT BOUNDARY (the smallness test: its forms read an array that is sent behind its
draw; every part of a later segment's relation): there (cong) fails, and the block's own law says
"for every such witness": more than the plain law, and what soundness needs. At `Agree := fun _ _ =>
True` (pins) is free and (cong) says that the closed items read nothing of the witness. (1) From
`GoodIn` to the plain law it goes always. PLAIN LAWS OF THE KINDS DO NOT JOIN BESIDE A
CARRIED CLAIM ON THE SAME COMPONENT OF THE WITNESS: with W := Bool, "behind: true", "in front: w =
true", and a carried claim "w = false", each block's plain law holds and the joined one fails. So
the joining is done at ONE w (`Piece.Own`), and the shadow is taken last. (2) "TRUE" AT AN EARLY
BOUNDARY MEANS: THE OPEN ITEMS CAN STILL ALL BE MET: the shadow quantifies over the messages of
segments that are not yet sent: these are the prover's to choose.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.Spine

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Reduction Err Shape IOR ExtSpec oneExternalString Doomed)

variable {S Cl W ι : Type} {C : CK} {F : Frame}

/-- **The plain law of a block**: no witness, no extractor. -/
def Piece.Plain (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (T T' : S × F.E.Str → Prop) : Prop :=
  ∀ a, on a → Doomed (uLT C p.ds) p.err fun τ =>
    ∀ b, p.ior.red.out a τ = some b → on' b ∧ (T' b → T a)

/-- Every block of a row has it, between the predicates at its two places. -/
def EachPlain (on : ℕ → S × F.E.Str → Prop) (T : ℕ → S × F.E.Str → Prop) :
    ℕ → List (Piece C F S Cl W) → Prop
  | _, [] => True
  | i, p :: l => p.Plain (on i) (on (i + 1)) (T i) (T (i + 1)) ∧ EachPlain on T (i + 1) l

/-- A relation's shadow: there is a witness. -/
def shadow (R : S × F.E.Str → W → Prop) : S × F.E.Str → Prop := fun a => ∃ w, R a w

/-- A block with `GoodIn` between two relations has the plain law between their shadows. -/
def PlainOfGoodIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop),
    p.GoodIn on on' R R' → p.Plain on on' (shadow R) (shadow R')

/-- The like for a row. -/
def EachPlainOfGoodIn : Prop :=
  ∀ (S Cl W : Type) (C : CK) (F : Frame) (on : ℕ → S × F.E.Str → Prop)
    (R : ℕ → S × F.E.Str → W → Prop) (l : List (Piece C F S Cl W)) (k : ℕ),
    EachGoodIn on R k l → EachPlain on (fun j => shadow (R j)) k l

/-- **The plain form of the rule.** -/
def SpinePlain : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (on : ℕ → S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ℕ → ι → Prop) (O₀ : ι → Prop)
    (l : List (Piece C F S Cl W)) (k : ℕ),
    EachOwn on means In Out O₀ k l →
    EachPlain on (fun j => shadow (relAt means (openAfter In Out O₀ j))) k l

/-- **THE WAY BACK, FOR A ROW WHOSE ITEMS READ THE WITNESS THROUGH WHAT ITS CONTEXT PINS.** A kind
may owe the plain law, WITH THE PINS INSIDE BOTH PREDICATES, and it is lifted to the block's own
law. Ctx: the row's context (it stands in In and in Out). Agree: two witnesses agree on the
components that the context pins. Asked: (pins) inside the condition two witnesses that both meet
the context at one statement agree; (cong) what the row closes says the same of witnesses that
agree; (back) the context rides back past the block at one witness; (id) the block's extractor is
the identity. -/
def OwnOfPlain : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out Ctx : ι → Prop) (Agree : W → W → Prop),
    (∀ i, Ctx i → In i) → (∀ i, Ctx i → Out i) →
    (∀ a w w', on a → (∀ i, Ctx i → means i a w) → (∀ i, Ctx i → means i a w') → Agree w w') →
    (∀ i, In i → ∀ a w w', Agree w w' → means i a w' → means i a w) →
    (∀ a τ b w i, on a → p.ior.red.out a τ = some b → on' b → Ctx i → means i b w →
      means i a w) →
    (∀ a τ w, p.ext a τ w = w) →
    p.Plain on on' (shadow (relAt means In)) (shadow (relAt means Out)) →
    p.Own on on' means In Out

/-- **A KIND's LAW IN ITS OWN WORDS GIVES THE BLOCK's OWN LAW AT THE TABLE.** o, o', R, R': the
kind's own conditions and relations. Asked: the table's promise in front gives the kind's
condition; where the block says yes inside the promise, the kind's condition behind gives the
table's promise behind; what the row opens (with its context) gives the kind's relation behind; the
kind's relation in front gives what the row closes (with its context). -/
def OwnOfGoodIn : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (o o' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop),
    p.GoodIn o o' R R' → (∀ a, on a → o a) →
    (∀ a τ b, on a → p.ior.red.out a τ = some b → o' b → on' b) →
    (∀ b w, relAt means Out b w → R' b w) → (∀ a w, on a → R a w → relAt means In a w) →
    p.Own on on' means In Out

theorem ownOfGoodIn : OwnOfGoodIn := by
  intro S Cl W ι C F p on on' means In Out o o' R R' h ho ho' hR' hR a ha
  refine Doomed.mono _ _ ?_ (h a (ho a ha))
  intro τ hτ b hb
  obtain ⟨hon, hw⟩ := hτ b hb
  exact ⟨ho' a τ b ha hb hon, fun w hO => hR a _ ha (hw w (hR' b w hO))⟩

/-- **The same, where the kind's law speaks of unmarked statements alone.** mk: the statement's
record bears a mark. The table's promise holds at marked records too, a kind's condition need not.
Asked beside: at a marked statement, where the block says yes, the promise behind holds and what the
row opens holds of no witness (the mark stays, and "no mark" stands among what every row opens). -/
def OwnOfGoodInBut : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (mk o o' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop),
    p.GoodIn o o' R R' → (∀ a, on a → ¬ mk a → o a) →
    (∀ a τ b, on a → ¬ mk a → p.ior.red.out a τ = some b → o' b → on' b) →
    (∀ b w, relAt means Out b w → R' b w) →
    (∀ a w, on a → ¬ mk a → R a w → relAt means In a w) →
    (∀ a τ b, on a → mk a → p.ior.red.out a τ = some b → on' b ∧ ∀ w, ¬ relAt means Out b w) →
    p.Own on on' means In Out

theorem ownOfGoodInBut : OwnOfGoodInBut := by
  intro S Cl W ι C F p on on' means In Out mk o o' R R' h ho ho' hR' hR hm a ha
  by_cases hk : mk a
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    exact ⟨(hm a τ b ha hk hb).1, fun w hO => absurd hO ((hm a τ b ha hk hb).2 w)⟩
  · refine Doomed.mono _ _ ?_ (h a (ho a ha hk))
    intro τ hτ b hb
    obtain ⟨hon, hw⟩ := hτ b hb
    exact ⟨ho' a τ b ha hk hb hon, fun w hO => hR a _ ha hk (hw w (hR' b w hO))⟩

/-- **The same door, wider**: the two implications on the relations are asked only WHERE THE PROOF
SPENDS THEM: at an unmarked statement inside the promise, at a yes of the block, with the kind's
condition behind in hand; the second also with what the row opens at (b, w), and at the extractor's
value alone. So a kind whose opened relation holds a public clause on the record behind may take it
from its own condition behind, and need not get it out of the table's items. -/
def OwnOfGoodInWide : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (mk o o' : S × F.E.Str → Prop)
    (R R' : S × F.E.Str → W → Prop),
    p.GoodIn o o' R R' → (∀ a, on a → ¬ mk a → o a) →
    (∀ a τ b, on a → ¬ mk a → p.ior.red.out a τ = some b → o' b → on' b) →
    (∀ a τ b w, on a → ¬ mk a → p.ior.red.out a τ = some b → o' b → relAt means Out b w →
      R' b w) →
    (∀ a τ b w, on a → ¬ mk a → p.ior.red.out a τ = some b → o' b → relAt means Out b w →
      R a (p.ext a τ w) → relAt means In a (p.ext a τ w)) →
    (∀ a τ b, on a → mk a → p.ior.red.out a τ = some b → on' b ∧ ∀ w, ¬ relAt means Out b w) →
    p.Own on on' means In Out

theorem ownOfGoodInWide : OwnOfGoodInWide := by
  intro S Cl W ι C F p on on' means In Out mk o o' R R' h ho ho' hR' hR hm a ha
  by_cases hk : mk a
  · refine Doomed.of_forall _ _ fun τ b hb => ?_
    exact ⟨(hm a τ b ha hk hb).1, fun w hO => absurd hO ((hm a τ b ha hk hb).2 w)⟩
  · refine Doomed.mono _ _ ?_ (h a (ho a ha hk))
    intro τ hτ b hb
    obtain ⟨hon, hw⟩ := hτ b hb
    exact ⟨ho' a τ b ha hk hb hon, fun w hO =>
      hR a τ b w ha hk hb hon hO (hw w (hR' a τ b w ha hk hb hon hO))⟩

/-- **A condition that rides may stand beside the promise** (the table's: "the stored table decodes
with the record", marked or not). -/
def OwnBeside : Prop :=
  ∀ (S Cl W ι : Type) (C : CK) (F : Frame) (p : Piece C F S Cl W) (on on' : S × F.E.Str → Prop)
    (means : ι → S × F.E.Str → W → Prop) (In Out : ι → Prop) (d d' : S × F.E.Str → Prop),
    p.Own on on' means In Out → (∀ a τ b, d a → p.ior.red.out a τ = some b → d' b) →
    p.Own (fun a => d a ∧ on a) (fun b => d' b ∧ on' b) means In Out

theorem ownBeside : OwnBeside := by
  intro S Cl W ι C F p on on' means In Out d d' h hd a ha
  refine Doomed.mono _ _ ?_ (h a ha.2)
  intro τ hτ b hb
  exact ⟨⟨hd a τ b ha.1 hb, (hτ b hb).1⟩, (hτ b hb).2⟩

theorem ownOfPlain : OwnOfPlain := by
  intro S Cl W ι C F p on on' means In Out Ctx Agree hCI hCO hpin hcong hback hid h a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  obtain ⟨hon, himp⟩ := hτ b hb
  refine ⟨hon, fun w hw i hi => ?_⟩
  obtain ⟨w', hw'⟩ := himp ⟨w, hw⟩
  have hc : ∀ j, Ctx j → means j a w := fun j hj => hback a τ b w j ha hb hon hj (hw j (hCO j hj))
  have ag := hpin a w w' ha hc fun j hj => hw' j (hCI j hj)
  rw [hid]
  exact hcong i hi a w w' ag (hw' i hi)

theorem plainOfGoodIn : PlainOfGoodIn := by
  intro S Cl W C F p on on' R R' h a ha
  refine Doomed.mono _ _ ?_ (h a ha)
  intro τ hτ b hb
  obtain ⟨hon, hw⟩ := hτ b hb
  exact ⟨hon, fun ⟨w, hR⟩ => ⟨p.ext a τ w, hw w hR⟩⟩

theorem eachPlainOfGoodIn : EachPlainOfGoodIn := by
  intro S Cl W C F on R l
  induction l with
  | nil => exact fun _ _ => trivial
  | cons p l ih =>
    intro k h
    exact ⟨plainOfGoodIn S Cl W C F p _ _ _ _ h.1, ih (k + 1) h.2⟩

theorem spinePlain : SpinePlain := by
  intro S Cl W ι C F on means In Out O₀ l k h
  exact eachPlainOfGoodIn S Cl W C F on _ l k (spineRule S Cl W ι C F on means In Out O₀ l k h)

/-- THE TWO-LINE MODEL of Limits (1), without any block: plain implications do not join beside a
carried claim on the same component. -/
theorem plain_does_not_join :
    ((∃ _w : Bool, True) → ∃ w : Bool, w = true) ∧
      ¬ ((∃ w : Bool, True ∧ w = false) → ∃ w : Bool, w = true ∧ w = false) := by
  refine ⟨fun _ => ⟨true, rfl⟩, fun h => ?_⟩
  obtain ⟨w, h₁, h₂⟩ := h ⟨false, trivial, rfl⟩
  rw [h₁] at h₂
  cases h₂

end VerifiableInference.Desc.Sound
