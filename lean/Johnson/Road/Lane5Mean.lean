-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5Mean.lean

The premise of Lane5.lean at the head with the cost ledger, cut by group: one named proposition for
each of the 12 groups of layers, one for each of the 12 attention links, one for the head (25 in
all, each of four clauses: three on the link's own matrices, one seam), gathered in one structure;
and "back": that structure gives that the request is true under its policy.

Why: a theorem on a verifier that takes what is not yet proved as named hypotheses wants the
meaning's half of a proof file's first chain in that form: what each link must deliver, by name, and
one proved step from all of them to the model's statement.

Main definitions and theorems:
* "SeamAt h A k": at every place that segment k may read, link k holds what the owner's link holds
  there: the field "seam" of "Premise" at one k.
* "MeanAt h seg Wz x A k": link k is in order at its own matrices ("LinkOK": its own cells are below
  2^18 in absolute value; every identity of segment k is 0; every key of segment k is an entry of
  its table), and its seam holds. Four clauses a link.
* "MeanG", "MeanA", "MeanH": "MeanAt" at link 2 g, at link 2 g + 1, at link 24, at the family of
  segments with the ledger's head. The three names follow the library's numbering of segments
  (Cm/SegLayout.lean: 2 g is the first segment of group g, all of its four layers but the attention
  weights; 2 g + 1 its attention segment; 24 the head); which segment stands at which number:
  "segPol_ff", "segPol_att", "segPol_head" (Policy/Seg/All.lean).
* "Meaning": the 25, gathered: fields "layers", "attention", "head".
* "meaning_iff_premise": "Meaning" says what "Premise" says, no more and no less.
* "back_of_meaning": at a lawful table and a policy with "Policy.PolCond": r < e and "Meaning" at
  the index's matrix of weights give that the request is true under the policy at that index.
* "meaning_iff": r < e and some matrices with "Meaning" at the index's matrix of weights, if and
  only if the request is true under the policy at that index.
* "meaning_met", "no_meaning": it can be met; it is not true of everything.

Not claimed: all that Lane5.lean and Lane5Ledger.lean do not claim. Above all: that any program,
protocol or accepted proof file shows "MeanG", "MeanA" or "MeanH"; whose matrices "A k" are. These
25 are statements on integer matrices; that a link's claims give them is another's work.

-/
import Johnson.Road.Lane5LedgerGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model

/-! ## 1. The clauses, by link -/

/-- The seam at link k. -/
def SeamAt (h : Cm.Seg.Hd) (A : ℕ → Mx) (k : ℕ) : Prop :=
  ∀ q ∈ Cm.Seg.reads h k, Cm.Seg.at' (A k) q = Cm.Seg.at' (A q.1) q

/-- Link k is in order at its own matrices, and its seam holds. -/
def MeanAt (h : Cm.Seg.Hd) (seg : Segs) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) (k : ℕ) :
    Prop :=
  LinkOK h seg Wz x k (A k) ∧ SeamAt h A k

/-- **Group g of layers**: link 2 g. -/
def MeanG (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) (g : ℕ) : Prop :=
  MeanAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A (2 * g)

/-- **Attention of group g**: link 2 g + 1. -/
def MeanA (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) (g : ℕ) : Prop :=
  MeanAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A (2 * g + 1)

/-- **The head with the cost ledger**: link 24. -/
def MeanH (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) : Prop :=
  MeanAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A 24

/-- **The meaning's half, gathered**: 12 groups of layers, 12 attention links, the head. -/
structure Meaning (s : Cm.Scales) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (A : ℕ → Mx) :
    Prop where
  layers : ∀ g < 12, MeanG s pol Wz x A g
  attention : ∀ g < 12, MeanA s pol Wz x A g
  head : MeanH s pol Wz x A

section Mean
variable {s : Cm.Scales} {pol : AcceptancePolicy} {Wz : Mat} {i : Cm.Idx} {x : Instance ppref} {A : ℕ → Mx}

/-! ## 2. It is the premise -/

/-- Every link below 25 is one of the 25 named. -/
theorem Meaning.at (M : Meaning s pol Wz x A) {k : ℕ} (hk : k < 25) :
    MeanAt Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A k := by
  rcases Nat.even_or_odd' k with ⟨g, rfl | rfl⟩
  · rcases Nat.lt_or_ge g 12 with h | h
    · exact M.layers g h
    · have e : g = 12 := by omega
      subst e
      exact M.head
  · exact M.attention g (by omega)

theorem premise_of_meaning (M : Meaning s pol Wz x A) :
    Premise Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A :=
  ⟨fun _ hk => (M.at hk).1, fun _ hk => (M.at hk).2⟩

theorem meaning_of_premise (P : Premise Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A) :
    Meaning s pol Wz x A :=
  ⟨fun g hg => ⟨P.link (2 * g) (show 2 * g < 25 by omega),
      P.seam (2 * g) (show 2 * g < 25 by omega)⟩,
    fun g hg => ⟨P.link (2 * g + 1) (show 2 * g + 1 < 25 by omega),
      P.seam (2 * g + 1) (show 2 * g + 1 < 25 by omega)⟩,
    ⟨P.link 24 (show 24 < 25 by omega), P.seam 24 (show 24 < 25 by omega)⟩⟩

/-- **The 25 named clauses say what the premise says.** -/
theorem meaning_iff_premise :
    Meaning s pol Wz x A ↔ Premise Cm.Seg.Hd.main (Policy.segPol s pol) Wz x A :=
  ⟨premise_of_meaning, meaning_of_premise⟩

/-! ## 3. Back -/

/-- **Back**: the 25 named clauses give that the request is true under its policy. -/
theorem back_of_meaning (hs : s.Lawful) (hpol : Policy.PolCond pol) (hre : x.r < x.e)
    (M : Meaning s pol i.mat x A) : Policy.IsTrueUnder s pol i x :=
  under_of_premise hs hpol hre (premise_of_meaning M)

/-- **Nothing is lost**: r < e and some matrices with the 25, if and only if the request is true
under its policy. -/
theorem meaning_iff (hs : s.Lawful) (hpol : Policy.PolCond pol) :
    (x.r < x.e ∧ ∃ A, Meaning s pol i.mat x A) ↔ Policy.IsTrueUnder s pol i x := by
  rw [← premiseL_iff hs hpol]
  exact ⟨fun ⟨h, A, M⟩ => ⟨h, A, premise_of_meaning M⟩,
    fun ⟨h, A, P⟩ => ⟨h, A, meaning_of_premise P⟩⟩

end Mean

/-! ## 4. Two guards -/

/-- **The 25 can be met.** -/
theorem meaning_met {s : Cm.Scales} {pol : AcceptancePolicy} (hs : s.Lawful) (hpol : Policy.PolCond pol) :
    ∃ (i : Cm.Idx) (x : Instance ppref) (A : ℕ → Mx),
      x.r = 1023 ∧ x.e = 1024 ∧ Meaning s pol i.mat x A := by
  obtain ⟨i, x, A, h1, h2, P⟩ := premiseL_met hs hpol
  exact ⟨i, x, A, h1, h2, meaning_of_premise P⟩

/-- **The 25 are not true of everything, and the policy is read.** -/
theorem no_meaning {s : Cm.Scales} {pol : AcceptancePolicy} (hs : s.Lawful) (hpol : Policy.PolCond pol)
    (h1 : pol.theta < 256) (h2 : 256 ≤ pol.C) (i : Cm.Idx) (x : Instance ppref)
    (hre : x.r < x.e) (hN : 0 < x.NB) (A : ℕ → Mx) : ¬ Meaning s pol i.mat x A :=
  fun M => no_premiseL hs hpol h1 h2 i x hre hN A (premise_of_meaning M)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.meaning_iff_premise
#print axioms OnBytes.Road.L5.back_of_meaning
#print axioms OnBytes.Road.L5.meaning_iff
#print axioms OnBytes.Road.L5.meaning_met
#print axioms OnBytes.Road.L5.no_meaning
