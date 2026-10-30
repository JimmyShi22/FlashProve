-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/Sized.lean: over Johnson/Desc/Ok/PlanWritten/Row.lean and SizedLit.lean:
the proof file's sizes and codes, the link's sizes and the six settings of the proof file's three
plans, as the planner makes them, held against written values: the statement with free letters for
the files, the tests with code, a ride with one call of the planner, and plants.

Row or tool. Every declaration here is a tool at the planner. `SizedWritten` is a statement with
free letters for the files: it is proved at no files.

Two instances are derived here, and why. The tests compare records by a decidable equality. Five of
the records' types bear none where they are declared (OnBytes/Params/). For three of them
(`TestSizes`, `LinLines`, `LinSized`) it is derived in OnBytes/Params/Fit/KeySizedParts.lean, which
this file imports for that alone. For the other two (`ProofSized`, `LinkSized`) it is derived here,
by Lean's own handler, field by field: no field is skipped. The two instances reach whoever imports
this file. If the library derives them where the types are declared, these two lines fall.

Definitions, statements and proofs.
  `fProof`, `fLink`, `sixOf`, `fSix`: the three fields as functions of what was made. `kept_fProof`,
    `kept_fLink`, `kept_fSix`: they do not hang on the digest. By definition. `sameSet`,
    `sameSet_eq`: three plans' settings are the same, plan by plan, with code.
  `SizedWritten pol lay KL`: at every digest of 32 bytes all is made, and the three fields are
    `proofSizedFull`, `linkSizedFull`, `sixFull` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean).
    `sizedWritten_one`: the three clauses speak of one m.
  `plantedProofSized`, `plantedLinkSized`, `plantedSix`, `planted_ne`: the written values with one
    number changed: in each the last number of the last field, so that a no shows that the
    comparison runs to the end; each is another value: by evaluations, two of them in Lean's kernel.
  `sizedTests`: twenty-five named tests on what was made: nineteen, a field each; three, a record
    each, whole; three plants. `foretoldSized`: a true first line, twenty-two times true, three
    times false.
  `rideSized note pol lay KL`: for a run: `rideFields` (Johnson/Desc/Ok/PlanWritten/Row.lean) at
    these tests: twenty-six named Bools with one call of the planner. `of_rideSized`: a ride with
    the foretold answers gives `SizedWritten pol lay KL`. It spends the first line and the three
    lines on whole records; beside these the nineteen lines a field and the three plants are
    foretold: they show where a no would lie, and that the evaluator's comparison can say no.

What of OnBytes/Model/ and OnBytes/Tie/ is used: what Johnson/Desc/Ok/PlanWritten/Row.lean names.

Limits. Proved at no files; whether a test here has been run, and what it said, is not told in this
file. A yes is evidence and no proof, and a check of copying against this library's own planner: no
second witness. Not held against any written value here: the key file's sizes; the entry file's
codes; the lines and the setting at the head of `Sized`; the key file's and the entry file's plans'
settings; the planner's seven records with their numbers for the errors; the sendings. The plants
change the written side, one number each. Nothing at a c that has not 32 bytes. Nothing on
soundness.


-/
import Johnson.Desc.Ok.PlanWritten.Row
import Johnson.Desc.Ok.PlanWritten.SizedLit
import OnBytes.Params.Fit.KeySizedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

deriving instance DecidableEq for OnBytes.Params.ProofSized
deriving instance DecidableEq for OnBytes.Params.LinkSized

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open OnBytes.Tie (shortB short_of_test)

/-! ## The fields -/

/-- The proof file's sizes and codes, of what was made. -/
def fProof (m : Made) : OnBytes.Params.ProofSized := m.p.chains.made.sized.proof

/-- The link's sizes, of what was made. -/
def fLink (m : Made) : OnBytes.Params.LinkSized := m.p.chains.made.sized.link

/-- A plan's six settings. -/
def sixOf (P : Fmt.Plan) : SixSet := (P.field, P.salt, P.nonce, P.posB, P.samples, P.saved)

/-- The six settings of the proof file's three plans as read back, of what was made. -/
def fSix (m : Made) : SixSet × SixSet × SixSet :=
  (sixOf m.p.chains.proof.first.given.plan, sixOf m.p.chains.proof.shared.given.plan,
    sixOf m.p.chains.proof.second.given.plan)

/-- It does not hang on the digest. By definition. -/
theorem kept_fProof : Kept fProof := fun _ _ => rfl

/-- It does not hang on the digest. By definition. -/
theorem kept_fLink : Kept fLink := fun _ _ => rfl

/-- They do not hang on the digest. By definition. -/
theorem kept_fSix : Kept fSix := fun _ _ => rfl

/-- **At every digest of 32 bytes all is made, and the three fields are the written values.** -/
def SizedWritten (pol lay KL : ByteArray) : Prop :=
  FieldIs fProof proofSizedFull pol lay KL ∧ FieldIs fLink linkSizedFull pol lay KL ∧
    FieldIs fSix sixFull pol lay KL

/-- The three clauses speak of one m: at every digest of 32 bytes one m is made that has all three
written values. -/
theorem sizedWritten_one {pol lay KL : ByteArray} (h : SizedWritten pol lay KL) (c : ByteArray)
    (hc : c.size = 32) :
    ∃ m, madeOfAt pol lay KL c = .ok m ∧ fProof m = proofSizedFull ∧ fLink m = linkSizedFull ∧
      fSix m = sixFull := by
  obtain ⟨m, hm, e1⟩ := h.1 c hc
  obtain ⟨m2, hm2, e2⟩ := h.2.1 c hc
  obtain ⟨m3, hm3, e3⟩ := h.2.2 c hc
  obtain rfl : m = m2 := Except.ok.inj (hm.symm.trans hm2)
  obtain rfl : m = m3 := Except.ok.inj (hm.symm.trans hm3)
  exact ⟨m, hm, e1, e2, e3⟩

/-- Three plans' settings are the same, plan by plan. With code. -/
def sameSet (x y : SixSet × SixSet × SixSet) : Bool :=
  decide (x.1 = y.1) && decide (x.2.1 = y.2.1) && decide (x.2.2 = y.2.2)

/-- What a yes says. -/
theorem sameSet_eq {x y : SixSet × SixSet × SixSet} (h : sameSet x y = true) : x = y := by
  unfold sameSet at h
  obtain ⟨h12, h3⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h12
  exact Prod.ext (of_decide_eq_true h1) (Prod.ext (of_decide_eq_true h2) (of_decide_eq_true h3))

/-! ## Plants -/

/-- The written value with one batch more. -/
def plantedProofSized : OnBytes.Params.ProofSized :=
  { proofSizedFull with
    batch := { proofSizedFull.batch with batches := proofSizedFull.batch.batches + 1 } }

/-- The written value with one more in the last number of its last field: the last stage's
`rOod`. -/
def plantedLinkSized : OnBytes.Params.LinkSized :=
  { linkSizedFull with
    linked := { linkSizedFull.linked with
      stages := linkSizedFull.linked.stages.dropLast ++
        linkSizedFull.linked.stages.getLast?.toList.map fun s => { s with rOod := s.rOod + 1 } } }

/-- The written settings with one more in the last setting of the last plan. -/
def plantedSix : SixSet × SixSet × SixSet :=
  (sixFull.1, sixFull.2.1,
    (sixFull.2.2.1, sixFull.2.2.2.1, sixFull.2.2.2.2.1, sixFull.2.2.2.2.2.1,
      sixFull.2.2.2.2.2.2.1, sixFull.2.2.2.2.2.2.2 + 1))

/-- Each is another value than the written one. By evaluations, two of them in Lean's kernel. -/
theorem planted_ne :
    plantedProofSized ≠ proofSizedFull ∧ plantedLinkSized ≠ linkSizedFull ∧
      plantedSix ≠ sixFull := by
  refine ⟨by decide +kernel, by decide +kernel, fun e => ?_⟩
  have e1 : sixFull.2.2.2.2.2.2.2 + 1 = sixFull.2.2.2.2.2.2.2 :=
    congrArg (fun x : SixSet × SixSet × SixSet => x.2.2.2.2.2.2.2) e
  exact absurd e1 (by decide)

/-! ## The tests and the ride -/

/-- Twenty-five named tests on what was made: a field each; a record each; three plants. -/
def sizedTests : List (String × (Made → Bool)) :=
  [("to say true: sized.proof.set is the written value",
      fun m => decide ((fProof m).set = proofSizedFull.set)),
    ("to say true: sized.proof.codes is the written value",
      fun m => decide ((fProof m).codes = proofSizedFull.codes)),
    ("to say true: sized.proof.link is the written value",
      fun m => decide ((fProof m).link = proofSizedFull.link)),
    ("to say true: sized.proof.last is the written value",
      fun m => decide ((fProof m).last = proofSizedFull.last)),
    ("to say true: sized.proof.request is the written value",
      fun m => decide ((fProof m).request = proofSizedFull.request)),
    ("to say true: sized.proof.batch.lines is the written value",
      fun m => decide ((fProof m).batch.lines = proofSizedFull.batch.lines)),
    ("to say true: sized.proof.batch.shape is the written value",
      fun m => decide ((fProof m).batch.shape = proofSizedFull.batch.shape)),
    ("to say true: sized.proof.batch.input is the written value",
      fun m => decide ((fProof m).batch.input = proofSizedFull.batch.input)),
    ("to say true: sized.proof.batch.table is the written value",
      fun m => decide ((fProof m).batch.table = proofSizedFull.batch.table)),
    ("to say true: sized.proof.batch.folded is the written value",
      fun m => decide ((fProof m).batch.folded = proofSizedFull.batch.folded)),
    ("to say true: sized.proof.batch.omega is the written value",
      fun m => decide ((fProof m).batch.omega = proofSizedFull.batch.omega)),
    ("to say true: sized.proof.batch.own is the written value",
      fun m => decide ((fProof m).batch.own = proofSizedFull.batch.own)),
    ("to say true: sized.proof.batch.batches is the written value",
      fun m => decide ((fProof m).batch.batches = proofSizedFull.batch.batches)),
    ("to say true: sized.link.shape is the written value",
      fun m => decide ((fLink m).shape = linkSizedFull.shape)),
    ("to say true: sized.link.table is the written value",
      fun m => decide ((fLink m).table = linkSizedFull.table)),
    ("to say true: sized.link.linked is the written value",
      fun m => decide ((fLink m).linked = linkSizedFull.linked)),
    ("to say true: the first plan's six settings are the written ones",
      fun m => decide ((fSix m).1 = sixFull.1)),
    ("to say true: the shared plan's six settings are the written ones",
      fun m => decide ((fSix m).2.1 = sixFull.2.1)),
    ("to say true: the second plan's six settings are the written ones",
      fun m => decide ((fSix m).2.2 = sixFull.2.2)),
    ("to say true: sized.proof, whole, is the written value",
      fun m => decide (fProof m = proofSizedFull)),
    ("to say true: sized.link, whole, is the written value",
      fun m => decide (fLink m = linkSizedFull)),
    ("to say true: the three plans' settings, whole, are the written ones",
      fun m => sameSet (fSix m) sixFull),
    ("a plant, to say false: sized.proof is the written value with one batch more",
      fun m => decide (fProof m = plantedProofSized)),
    ("a plant, to say false: sized.link is the written value with its last number one more",
      fun m => decide (fLink m = plantedLinkSized)),
    ("a plant, to say false: the settings are the written ones with the last one more",
      fun m => sameSet (fSix m) plantedSix)]

/-- What the ride's twenty-six answers are to be. -/
def foretoldSized : List Bool :=
  true :: (List.replicate 22 true ++ [false, false, false])

/-- **For a run**: twenty-six named Bools, with one call of the planner. -/
def rideSized (note : String) (pol lay KL : ByteArray) : List (String × Bool) :=
  rideFields note sizedTests pol lay KL

/-- **A ride with the foretold answers gives the statement.** -/
theorem of_rideSized {note : String} {pol lay KL : ByteArray}
    (h : (rideSized note pol lay KL).map Prod.snd = foretoldSized) :
    SizedWritten pol lay KL := by
  unfold rideSized at h
  obtain ⟨m, hm, hb, ht⟩ := of_rideFields (note := note) (tests := sizedTests) (pol := pol)
    (lay := lay) (KL := KL) (by rw [h]; rfl)
  rw [h] at ht
  have ht : List.replicate 22 true ++ [false, false, false] = sizedTests.map fun t => t.2 m := ht
  have ht : [true, true, true, true, true, true, true, true, true, true, true, true, true, true,
      true, true, true, true, true, true, true, true, false, false, false] =
      sizedTests.map fun t => t.2 m := ht
  unfold sizedTests at ht
  simp only [List.map_cons, List.map_nil] at ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨_, ht⟩ := List.cons.inj ht
  obtain ⟨h1, ht⟩ := List.cons.inj ht
  obtain ⟨h2, ht⟩ := List.cons.inj ht
  obtain ⟨h3, _⟩ := List.cons.inj ht
  have at_ : ∀ {α : Type} (f : Made → α) (w : α), Kept f → f m = w → FieldIs f w pol lay KL :=
    fun f w hk e c hc =>
      ⟨atDigest m c, madeOfAt_at rfl hc (short_of_test hb) hm, (hk m c).trans e⟩
  exact ⟨at_ fProof _ kept_fProof (of_decide_eq_true h1.symm),
    at_ fLink _ kept_fLink (of_decide_eq_true h2.symm),
    at_ fSix _ kept_fSix (sameSet_eq h3.symm)⟩

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.kept_fProof
#print axioms VerifiableInference.PlanWritten.kept_fLink
#print axioms VerifiableInference.PlanWritten.kept_fSix
#print axioms VerifiableInference.PlanWritten.sizedWritten_one
#print axioms VerifiableInference.PlanWritten.sameSet_eq
#print axioms VerifiableInference.PlanWritten.planted_ne
#print axioms VerifiableInference.PlanWritten.of_rideSized
