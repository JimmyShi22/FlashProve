-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Head/HeadLeaves.lean: at the output head's view of a shape (View,
Johnson/Desc/K6/Shape/Seat.lean): where the readers' tests (lettersB) and one test more on the shape
(headCoverTest) accept, every leaf of the head's forms (of a read's entries those below its length
alone) stands to the same leaf with no read (LeafSh.bare, FormsAlike.lean) in the relation
BareOfRowZero: the same slots; no entry on the bare side; every entry in array iU3, row 0, below n.
General in the view, the sizes and n. Nothing is evaluated.

Why. FormsAlike.lean carries a relation from the leaves to the forms; HeadCover.lean uses this one.

  BareOfRowZero iU3 n a a'   the relation. bareOfRowZero_kept: "one behind the other" keeps it.
  placeSh_bareOfRowZero   an entry of a table of reads that is found and long enough stands to
                          noTerm in the relation.
  headCoverTest           the light runs' own test on the shape.
  HeadCoverFacts, headCoverFacts_ofTest   what that test gives.
  **leaves_bareOfRowZero**   leaf by leaf.

Limits. An implication from two tests. hp: the sizes at which the forms run are those at which
readsB reckons "long enough". Nothing says that either test accepts anywhere. What any of this costs
Lean's kernel is not measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Head.FormsAlike
import Johnson.Desc.K6.Shape.Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open VerifiableInference.Desc.First.Shape (AffSh PscSh LedSh HeadHeardSh)
open VerifiableInference.Desc.Kinds.Head.Law (readLenN wideLenN readLen)

local infixl:65 " ⋆ " => AffSh.append

/-- a' has a's slots and no entry; a's entries lie in array iU3, row 0, below n. -/
def BareOfRowZero (iU3 n : Nat) (a a' : AffSh) : Prop :=
  a'.slots = a.slots ∧ a'.ents = [] ∧ ∀ x ∈ a.ents, x.1 = iU3 ∧ x.2.1 = 0 ∧ x.2.2 < n

/-- "One behind the other" keeps the relation. -/
theorem bareOfRowZero_kept (iU3 n : Nat) : KeptByAppending (BareOfRowZero iU3 n) where
  nil := ⟨rfl, rfl, fun x hx => nomatch hx⟩
  app := by
    intro a a' b b' h1 h2
    obtain ⟨s1, e1, r1⟩ := h1
    obtain ⟨s2, e2, r2⟩ := h2
    refine ⟨?_, ?_, fun x hx => ?_⟩
    · show a'.slots ++ b'.slots = a.slots ++ b.slots
      rw [s1, s2]
    · show a'.ents ++ b'.ents = []
      rw [e1, e2]
      rfl
    · have hx' : x ∈ a.ents ++ b.ents := hx
      exact (List.mem_append.1 hx').elim (r1 x) (r2 x)

/-- A form that names no entry stands to itself. -/
theorem bareOfRowZero_self {iU3 n : Nat} {a : AffSh} (h : a.ents = []) : BareOfRowZero iU3 n a a :=
  ⟨rfl, h, fun x hx => by rw [h] at hx; exact nomatch hx⟩

/-- hidSh names no entry. -/
theorem hidSh_namesNoEntry (first n i : Nat) : (hidSh first n i).ents = [] := by
  unfold hidSh
  split <;> rfl

/-- An entry below len of a table of reads that is found, is long enough and ends at or below n, n
at most the number of columns, stands to noTerm in the relation. -/
theorem placeSh_bareOfRowZero {tab : List (String × Nat × Nat)} {iU3 K n : Nat} {name : String}
    {i len : Nat}
    (hK : n ≤ K) (hT : ∀ e ∈ tab, e.2.1 + e.2.2 ≤ n)
    (hf : ((tab.find? fun e => e.1 == name).any fun e => Nat.ble len e.2.2) = true) (hi : i < len) :
    BareOfRowZero iU3 n (placeSh tab iU3 K name i) noTerm := by
  cases hq : tab.find? fun e => e.1 == name with
  | none =>
    rw [hq] at hf
    exact nomatch hf
  | some e =>
    rw [hq] at hf
    have hl : len ≤ e.2.2 := Nat.le_of_ble_eq_true hf
    have hm := hT e (List.mem_of_find?_eq_some hq)
    have hp : e.2.1 + i < K := by omega
    refine ⟨rfl, rfl, fun x hx => ?_⟩
    unfold placeSh at hx
    rw [hq] at hx
    have hx' : x ∈ [(iU3, (e.2.1 + i) / K, (e.2.1 + i) % K)] := hx
    obtain rfl := List.mem_singleton.1 hx'
    refine ⟨rfl, Nat.div_eq_of_lt hp, ?_⟩
    show (e.2.1 + i) % K < n
    rw [Nat.mod_eq_of_lt hp]
    omega

/-- **The light runs' own test, on the shape**: n is at most the reads' array's number of columns;
every table ends at or below n; S2 divides d; JVa ≤ JV; the four forms that the sumchecks leave name
no entry. -/
def headCoverTest (p : Par) (iU3 n : Nat) (v : View) : Bool :=
  letI := p.sizes
  Decidable.decide (n ≤ colsOf v.led iU3) &&
    v.tab.all (fun e => Decidable.decide (e.2.1 + e.2.2 ≤ n)) &&
    Decidable.decide (Norm.d % Norm.S2 = 0) && Decidable.decide (JVa ≤ JV) &&
    [leftSh v.Q, leftSh v.X.tV.p, leftSh v.X.tN.p, leftSh v.X.tH.p].all (·.ents.isEmpty)

/-- S2 divides d, at these sizes. -/
def SizesDivideAt (s : Sizes) : Prop := letI := s; Norm.S2 ∣ Norm.d

/-- JVa ≤ JV, at these sizes: the entry at which the table's keys are cut in two lies within the
padded vocabulary. -/
def KeyLengthsOrderedAt (s : Sizes) : Prop := letI := s; JVa ≤ JV

/-- What headCoverTest says, as facts. -/
structure HeadCoverFacts (p : Par) (iU3 n : Nat) (v : View) : Prop where
  cols : n ≤ colsOf v.led iU3
  tabs : ∀ e ∈ v.tab, e.2.1 + e.2.2 ≤ n
  div : SizesDivideAt p.sizes
  half : KeyLengthsOrderedAt p.sizes
  sq : (leftSh v.Q).ents = []
  pr : (leftSh v.X.tV.p).ents = []
  nm : (leftSh v.X.tN.p).ents = []
  lg : (leftSh v.X.tH.p).ents = []

/-- Where the test accepts, the facts hold. -/
theorem headCoverFacts_ofTest {p : Par} {iU3 n : Nat} {v : View} (h : headCoverTest p iU3 n v =
    true) : HeadCoverFacts p iU3 n v := by
  unfold headCoverTest at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_cons, List.all_nil, Bool.and_true,
    List.all_eq_true, List.isEmpty_iff] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, Nat.dvd_of_mod_eq_zero h3, h4, h5, h6, h7, h8⟩

/-- **Leaf by leaf**: under hp and the two tests, the leaves stand to the bare leaves in the
relation. -/
theorem leaves_bareOfRowZero {p : Par} {h : OnBytes.Model.Head.Shape} {iU3 n : Nat} {v : View}
    (hp : p.sizes = sizesOf h) (hl : lettersB p h iU3 v = true) (hc : headCoverTest p iU3 n v =
        true) :
    @LeavesAlike p.sizes (BareOfRowZero iU3 n) (v.leaves iU3) (v.leaves iU3).bare := by
  have Cv := headCoverFacts_ofTest hc
  unfold lettersB readsB at hl
  simp only [Bool.and_eq_true] at hl
  obtain ⟨-, -, hr⟩ := hl
  rw [hp]
  simp only [readsNeed, List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at hr
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := hr
  letI := sizesOf h
  exact
    { W := fun s => bareOfRowZero_self (hidSh_namesNoEntry _ _ _)
      P := fun s => bareOfRowZero_self (hidSh_namesNoEntry _ _ _)
      sqLeft := bareOfRowZero_self Cv.sq
      sqEnd := fun j => bareOfRowZero_self (by
        show (if j = 0 then slotSh v.X.wpl.sL else if j = 1 then slotSh v.X.wpl.sR else noTerm).ents
            = []
        split
        · rfl
        · split <;> rfl)
      prLeft := bareOfRowZero_self Cv.pr
      prClaimed := bareOfRowZero_self rfl
      prEnd := fun j => bareOfRowZero_self (hidSh_namesNoEntry _ _ _)
      nmLeft := bareOfRowZero_self Cv.nm
      nmClaimed := bareOfRowZero_self rfl
      nmEnd := fun j => bareOfRowZero_self (hidSh_namesNoEntry _ _ _)
      lgLeft := bareOfRowZero_self Cv.lg
      lgClaimed := bareOfRowZero_self rfl
      lgEnd := fun j => bareOfRowZero_self (hidSh_namesNoEntry _ _ _)
      entryN := fun r i hi => by
        cases r
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r1 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r2 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r3 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r4 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r5 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r6 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r7 hi
      wide := fun i hi => placeSh_bareOfRowZero Cv.cols Cv.tabs r8
        (Nat.lt_of_lt_of_le hi (Nat.div_le_div_right (Nat.le_add_right _ _)))
      entryH := fun r i hi => by
        cases r
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r8 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r9 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r10 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r11 hi
        · exact placeSh_bareOfRowZero Cv.cols Cv.tabs r12 hi }

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.BareOfRowZero
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.bareOfRowZero_kept
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.bareOfRowZero_self
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.hidSh_namesNoEntry
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.placeSh_bareOfRowZero
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headCoverTest
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.SizesDivideAt
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.KeyLengthsOrderedAt
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.HeadCoverFacts
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.headCoverFacts_ofTest
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.leaves_bareOfRowZero
