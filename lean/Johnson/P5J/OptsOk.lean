-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/OptsOk.lean: SEVEN NAMED TESTS ON THE PUBLIC PARAMETERS: WHERE THEY ACCEPT, NO DEFAULT
INSIDE THE TERMS OF THE COMPOSED MEANING's PARAMETERS (`At.𝔇Whole`, LettersAt4.lean) ANSWERS
IN SILENCE. Seven definitions with code; one Lean structure; what each test gives, proved.

Why. Several of these terms read an option and lay a default where it answers nothing (0 · the
empty list · the empty data · all zeros · the identity). At such public parameters the composed
meaning would speak of ANOTHER TERM than is meant, without any statement turning false. In scope of
the goals the scale file and eight numbers of the parameter file are free: a run at one value of
them does not settle the others. So each option is a named test of the head.
  `builtB Zp`      the list of built segments answers at every written segment: shuts `d1At`'s ncl
    (0) · `names3` (the empty list of names) · the arrays' names in `MgData.sent`.
  `tlB Zp`         `Look.tlAt (X Zp) l` answers at every feed-forward segment: shuts `uLAt`'s empty
    data of a closing part.
  `armB Zp`        `(X Zp).A[l / 2]?` answers at every attention segment: shuts `uArm`'s 0.
  `whereB Zp`      `K13.fromOf? Zp` answers and the three rounds of proof of work behind it are
    there: shuts `K13.whereOf`'s four zeros.
  `spotsB Zp lay`  the code switchings' typed table is made (where it is not, the test rejects), and
    `ProofFile.pAtK2? Zp m` answers at every row m of it: shuts `pAtK2`'s numbers that are all 0.
  `wholeB Zp`      `ProofFile.wholeAt Zp` answers: shuts `allAt`'s empty list and `keyAt`'s identity.
  `At.laidB Zp`    (LettersAt2.lean's, by name): the laid data are there.
  `At.OptsOk Zp lay`: all seven accept.
  `OptsOk.builtAt | tlAt | armAt | fromAt | spotsAt | wholeAt`: what six of them give, as sentences.
EVALUATED: each of the seven bodies, as an expression of a file not in this
library, accepted at a stored full-size set's three public files, with
negative tests; there the switchings' rows were asked at m below 40, here at the typed table's own
length. NOT EVALUATED UNDER THESE NAMES. NOT HERE: `free0Of`'s 0 (`FillP1.startB` is its test): no
parameter of the composed meaning reads it. And two more defaults that read a WITNESS, not the
public parameters: `whOf`'s 0 (where `indexOf` answers nothing at the committed table's cells) and
`nuK6`'s two zeros: left to their own files (WhOf.lean, StatedHeadArm.lean).
Limits. Tests and their unfoldings. Nothing on soundness.

-/
import Johnson.P5J.LettersAt4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

/-- The written segments of a sort. -/
def segsOf (k : VerifiableInference.Desc.First.ModelPart) : List ℕ :=
  (List.range links.length).filter fun l => links[l]? == some k

def builtB (Zp : ProofFile.Pub) : Bool :=
  (List.range links.length).all fun l => (Zp.made.p.built.links[l]?).isSome

def tlB (Zp : ProofFile.Pub) : Bool :=
  (segsOf .layers).all fun l => (VerifiableInference.Desc.First.Look.tlAt (X Zp) l).isSome

def armB (Zp : ProofFile.Pub) : Bool :=
  (segsOf .attention).all fun l => ((X Zp).A[l / 2]?).isSome

def whereB (Zp : ProofFile.Pub) : Bool :=
  (VerifiableInference.Desc.K13.fromOf? Zp).isSome &&
    (List.range 3).all fun i => (Zp.plans.1[VerifiableInference.Desc.K13.fromOf Zp + i]?).isSome

def spotsB (Zp : ProofFile.Pub) (lay : ByteArray) : Bool :=
  match (VerifiableInference.Desc.First.K2Caller.tableOf Zp.pol lay Zp.KL).toOption with
  | some t => (List.range t.length).all fun m => (ProofFile.pAtK2? Zp m).isSome
  | none => false

def wholeB (Zp : ProofFile.Pub) : Bool := (ProofFile.wholeAt Zp).isSome

/-- **No default of the parameters' terms answers in silence.** -/
structure OptsOk (Zp : ProofFile.Pub) (lay : ByteArray) : Prop where
  built : builtB Zp = true
  tl : tlB Zp = true
  arm : armB Zp = true
  where' : whereB Zp = true
  spots : spotsB Zp lay = true
  whole : wholeB Zp = true
  laid : laidB Zp = true

theorem all_range {n : ℕ} {p : ℕ → Bool} (h : (List.range n).all p = true) (l : ℕ) (hl : l < n) :
    p l = true :=
  List.all_eq_true.1 h l (List.mem_range.2 hl)

theorem mem_segsOf {k : VerifiableInference.Desc.First.ModelPart} {l : ℕ} (h : links[l]? = some k) :
    l ∈ segsOf k := by
  unfold segsOf
  refine List.mem_filter.2 ⟨List.mem_range.2 ?_, by rw [h]; exact beq_self_eq_true _⟩
  by_contra hn
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at h
  cases h

variable {Zp : ProofFile.Pub} {lay : ByteArray}

theorem OptsOk.builtAt (h : OptsOk Zp lay) (l : ℕ) (hl : l < links.length) :
    (Zp.made.p.built.links[l]?).isSome = true := all_range h.built l hl

theorem OptsOk.tlAt (h : OptsOk Zp lay) (l : ℕ) (hl : links[l]? = some .layers) :
    (VerifiableInference.Desc.First.Look.tlAt (X Zp) l).isSome = true :=
  List.all_eq_true.1 h.tl l (mem_segsOf hl)

theorem OptsOk.armAt (h : OptsOk Zp lay) (l : ℕ) (hl : links[l]? = some .attention) :
    ((X Zp).A[l / 2]?).isSome = true :=
  List.all_eq_true.1 h.arm l (mem_segsOf hl)

theorem OptsOk.fromAt (h : OptsOk Zp lay) :
    (VerifiableInference.Desc.K13.fromOf? Zp).isSome = true :=
  (Bool.and_eq_true _ _ ▸ h.where').1

/-- Wherever the typed row of a code switching answers, so do the place's numbers. -/
theorem OptsOk.spotsAt (h : OptsOk Zp lay) (m : ℕ)
    (hm : (ProofFile.rowAtK2 Zp.pol lay Zp.KL m).isSome = true) : (ProofFile.pAtK2? Zp m).isSome = true := by
  have hs := h.spots
  unfold spotsB at hs
  unfold ProofFile.rowAtK2 at hm
  cases e : (VerifiableInference.Desc.First.K2Caller.tableOf Zp.pol lay Zp.KL).toOption with
  | none => rw [e] at hm; cases hm
  | some t =>
    rw [e] at hs hm
    refine all_range hs m ?_
    by_contra hn
    simp only [Option.bind_some] at hm
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hn)] at hm
    cases hm

theorem OptsOk.wholeAt (h : OptsOk Zp lay) : (ProofFile.wholeAt Zp).isSome = true := h.whole

end P5J.At

#print axioms P5J.At.OptsOk.builtAt
#print axioms P5J.At.OptsOk.tlAt
#print axioms P5J.At.OptsOk.armAt
#print axioms P5J.At.OptsOk.fromAt
#print axioms P5J.At.OptsOk.spotsAt
#print axioms P5J.At.OptsOk.wholeAt
