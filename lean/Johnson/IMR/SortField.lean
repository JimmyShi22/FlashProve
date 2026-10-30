-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/SortField.lean: THE SORT OF THE SEGMENT's OWN PART IN FRONT OF THE
LOOKUP ON THE CALLS: at a segment l < 24 whose written sort is «layers» the verifier's state's own
part is a layers' part (here = .lay b); at one whose written sort is «attention» it is an
attention's (here = .att b). In the form of our theorems for FoldFacts' fields: general in «reached»
and in the reader; it goes in no structure. Used for
the lookups' premise hlay.

WHAT IS SAID.
  sorts_count        a word of the kernel on the written row of sorts IM.linksW: among the segments
                     l < 24 twelve are layers' and twelve attention's: so neither theorem is idle.
  opened_at          THE FIRST HALF OF Johnson/IMR/UnheardAt.lean's unheard_at's OWN PROOF, TYPED
                     AGAIN, so
                     that it HANDS OUT what that theorem hides: the frame's rows fs, the row f at
                     number l and the state m with f.opened m = .ok (the state at border 14 l + 3).
  opened_sort        which sort a row's «opened» lays, by the kind of the link's record: over
                     framesOf_arms (Johnson/Top/H0/Walk/FrameRows.lean).
  writtenSort_at     in scope the written sort at l is that of the built link's kind: over our
                     subs_all (Johnson/IMR/PlacesScope.lean).
  lay_number_at, att_number_at   **the two tops, the border named by its number 14 l + 3.**
  lay_field_at, att_field_at     the same, the border named by its place on the written list: kind
                     K3, piece 2 (Johnson/IMR/UnheardField.lean's calls_number_at).
THE PREMISES IN FRONT, BY NAME: hS · hR · O · hRch («reached» is reached by the wrapped
sub-protocols' steps) · the written sort at l. The fence «no mark» stands among the binders for the
form's sake and IS NOT SPENT. No test on the plan is asked.
What is not claimed. The head's segment. That a state is reached: NO MEMBER. No soundness.

-/
import Johnson.IMR.UnheardField
import Johnson.IMR.PlacesScope
import Johnson.Top.H0.Walk.FrameRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)

/-- Among the segments l < 24 of the written row of sorts twelve are layers' and twelve
attention's. -/
theorem sorts_count :
    ((List.range 24).countP fun l => IM.linksW[l]? == some ModelPart.layers) = 12 ∧
      ((List.range 24).countP fun l => IM.linksW[l]? == some ModelPart.attention) = 12 := by
  decide +kernel

open Johnson.Desc.First.Walk Johnson.Desc.First.Walk.Seat in
/-- Which sort a row's "opened" lays, by the kind of the link's record. -/
theorem opened_sort {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : ℕ} {s t : S}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) (y : f.opened s = .ok t) :
    ∃ X, built[l]? = some X ∧
      (X.kind = 2 ∨ (X.kind = 0 ∧ ∃ b, t.here = .lay b) ∨ (X.kind = 1 ∧ ∃ b, t.here = .att b)) := by
  rcases framesOf_arms h hf with ⟨X, hX, hk, -⟩ | ⟨rfl, X, _, P, hX, hk, -, -, -, ho, -⟩ |
    ⟨-, X, _, P, hX, hk, -, -, -, ho, -⟩ | ⟨-, X, _, P, hX, hk, -, -, -, ho, -⟩
  · exact ⟨X, hX, Or.inl hk⟩
  · rw [ho] at y
    obtain ⟨hB, -, a, -, k'⟩ := Props.openLayZero_iff.1 y
    obtain ⟨b, hb, -⟩ := enterLay_fresh (s := { s with out := a.out }) hB k'
    exact ⟨X, hX, Or.inr (Or.inl ⟨hk, b, hb⟩)⟩
  · rw [ho] at y
    obtain ⟨hB, -, a, -, k'⟩ := Props.openAtt_iff.1 y
    obtain ⟨b, hb, -⟩ := enterAtt_fresh (s := { s with out := a.out }) hB k'
    exact ⟨X, hX, Or.inr (Or.inr ⟨hk, b, hb⟩)⟩
  · rw [ho] at y
    obtain ⟨hB, -, a, -, k'⟩ := Props.openLay_iff.1 y
    obtain ⟨b, hb, -⟩ := enterLay_fresh (s := { s with out := a.out }) hB k'
    exact ⟨X, hX, Or.inr (Or.inl ⟨hk, b, hb⟩)⟩

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- The frame's row at link l < 24 and the state from which its "opened" returns the state at
border 14 l + 3. The first half of unheard_at's own proof, typed again. -/
theorem opened_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ (fs : List Johnson.Desc.First.Walk.Seat.LinkFrame)
        (f : Johnson.Desc.First.Walk.Seat.LinkFrame) (m : S),
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ f.opened m = .ok t₁ := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  by_cases h0 : l = 0
  · subst h0
    obtain ⟨Lk, b, eLk, e0, J⟩ := IM.k1_first_sits hS hR O
    have i0 : c.blocksInOrder[14 * 0 + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [(IM.flatIx_scope hS hR O (by omega : 0 ≤ 24) 0).trans
        (by omega : 14 * 0 + 0 + 2 = 14 * 0 + 2)] at k
    obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
    obtain ⟨fs, fr, m, hfs, hf, -, -, y3, -, -⟩ := J.yes d
    exact ⟨fs, fr, m, hfs, hf, y3⟩
  · obtain ⟨Lk, b, x0, eLk, e0, -, J, -⟩ := IM.k2_link_sits hS hR O l (by omega) h24
    have i0 : c.blocksInOrder[14 * l + 2]? = some b := by
      have k := IM.hear_at_flat eLk e0
      rwa [(IM.flatIx_scope hS hR O (by omega : l ≤ 24) 0).trans
        (by omega : 14 * l + 0 + 2 = 14 * l + 2)] at k
    obtain ⟨rs, gs, d⟩ := fold_next i0 f₀ f₁
    obtain ⟨fs, fr, m, hfs, hf, -, -, y3, -, -⟩ := J.yes d
    exact ⟨fs, fr, m, hfs, hf, y3⟩

/-- In scope the written sort at l is that of the built link's kind. -/
theorem writtenSort_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} {X : Stages.LinkH}
    (hX : Z.p.built.links[l]? = some X) : IM.linksW[l]? = some (ProofFile.subOf X.kind) := by
  rw [← IM.subs_all hS hR O]
  show (Z.p.built.links.toList.map fun X => ProofFile.subOf X.kind)[l]? = _
  rw [List.getElem?_map, Array.getElem?_toList, hX]
  rfl

/-- **At a layers' segment the own part is a layers' part**, the border named by its number. -/
theorem lay_number_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ l a, l < 24 → Rch (14 * l + 3) a → (at_ a).2.failed = none →
      IM.linksW[l]? = some ModelPart.layers → ∃ b, (at_ a).2.here = .lay b := by
  intro l a h24 hr _ hw
  obtain ⟨_, rs, cols, f⟩ := (reach_raw (hRch _ a hr)).fold
  obtain ⟨fs, fr, m, hfs, hf, y3⟩ := opened_at hS hR O h24 f
  obtain ⟨Y, hY, hk⟩ := opened_sort hfs hf y3
  have e := writtenSort_at hS hR O hY
  rw [hw] at e
  rcases hk with hk | ⟨-, hb⟩ | ⟨hk, -⟩
  · rw [hk] at e
    exact absurd e (by decide)
  · exact hb
  · rw [hk] at e
    exact absurd e (by decide)

/-- **At an attention segment the own part is an attention's**, the border named by its number. -/
theorem att_number_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ l a, l < 24 → Rch (14 * l + 3) a → (at_ a).2.failed = none →
      IM.linksW[l]? = some ModelPart.attention → ∃ b, (at_ a).2.here = .att b := by
  intro l a h24 hr _ hw
  obtain ⟨_, rs, cols, f⟩ := (reach_raw (hRch _ a hr)).fold
  obtain ⟨fs, fr, m, hfs, hf, y3⟩ := opened_at hS hR O h24 f
  obtain ⟨Y, hY, hk⟩ := opened_sort hfs hf y3
  have e := writtenSort_at hS hR O hY
  rw [hw] at e
  rcases hk with hk | ⟨hk, -⟩ | ⟨-, hb⟩
  · rw [hk] at e
    exact absurd e (by decide)
  · rw [hk] at e
    exact absurd e (by decide)
  · exact hb

/-- The same, the border named by its place on the written list. -/
theorem lay_field_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p l, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some l →
      p.kind = .K3 → p.piece = 2 → IM.linksW[l]? = some ModelPart.layers →
      ∃ b, (at_ a).2.here = .lay b := by
  intro k a p l hr hu hpl hl hK hc hw
  obtain ⟨h24, rfl⟩ := IM.calls_number_at hpl hK hc hl
  exact lay_number_at hS hR O Rch at_ hRch l a h24 hr hu hw

/-- The same, the border named by its place on the written list. -/
theorem att_field_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {X : Type} (Rch : ℕ → X → Prop)
    (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) k (at_ a)) :
    ∀ k a p l, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some l →
      p.kind = .K3 → p.piece = 2 → IM.linksW[l]? = some ModelPart.attention →
      ∃ b, (at_ a).2.here = .att b := by
  intro k a p l hr hu hpl hl hK hc hw
  obtain ⟨h24, rfl⟩ := IM.calls_number_at hpl hK hc hl
  exact att_number_at hS hR O Rch at_ hRch l a h24 hr hu hw

end Meaning.K2

#print axioms Meaning.K2.sorts_count
#print axioms Meaning.K2.opened_sort
#print axioms Meaning.K2.opened_at
#print axioms Meaning.K2.writtenSort_at
#print axioms Meaning.K2.lay_number_at
#print axioms Meaning.K2.att_number_at
#print axioms Meaning.K2.lay_field_at
#print axioms Meaning.K2.att_field_at
