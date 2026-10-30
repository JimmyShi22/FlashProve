-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3Places.lean: at profile 4 and twelve groups, what `lookAt`
(Johnson/Desc/First/Look/LookAt.lean) and `tlAt` (Johnson/Desc/First/Look/Laid.lean) give at each of
the 25 segments, off the one plan that they read there; and, in that form, the tests "narrowed, it
is the written value" as Bools on the plans. Six definitions with code and ten laws, general in the
public part. No goal is stated.
Why. A closed fact at the full size is a Bool that Lean's kernel evaluates at what the public part's
makers return (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean): at the layers' plans and the
attention's plans, not at a public part.
  `placeD kind i base ns tl behind`: the entry of `lookAt` for the lookup on a segment's digits, by
    itself.
  `lookAt_dig_even`, `lookAt_dig_odd`, `lookAt_dig_head`; `tlAt_even`, `tlAt_odd`, `tlAt_head`:
    segment 2 g reads the layers' plan of group g, segment 2 g + 1 the attention's, segment 24 the
    head's.
  `digOk i ox tl`: a place is there, and its view and the structure's are those of `pFull i` and
    `tFull i` (Johnson/AtFull/ProofRows/K3Full.lean; the views: K3Same.lean). `digOk_gives`: what a
    yes says.
  `digLB G`, `digAB A`, `digHB H lk`: `digOk` at the twelve even segments, the twelve odd ones, the
    head's.
  `readsAB A`: at the twelve attention segments the views of the place of the lookup on the calls
    (`placeA`, AttLaw.lean) and of the structure are those of `cFull i` and `mFull`.
  `at_group`: an `all` over the twelve groups of an `any` at the group's plan, opened.
  **`dig_gives`**, **`reads_gives`**: what a yes of the tests gives at a public part: the premises
    hV of `digEntry_full` and `readsEntry_full` (Johnson/AtFull/ProofRows/K3Rows.lean), to the
    letter.
Limits. NO VALUE IS GIVEN HERE, and no test is shown to say yes. Twelve groups alone. Nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.K3Same
import Johnson.AtFull.Entry.AttLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place lookAt tlAt digitsNext)
open Johnson.AtFull.ProofRows.K3

/-- The place of the lookup on a segment's digits, off what `lookAt` reads there. -/
def placeD (kind : String) (i : Nat) (base : Fork) (ns : Nat) (tl : HTailF2) (behind : Nat) :
    Option Place :=
  (digitsNext ns behind (Forest.elems tl.f9)).map fun nx =>
    { name := s!"LINK {i} ({kind}) digits", link := i, calls := #[tl.z1.call, tl.z2.call],
      pub := tl.f9.pub, lid := tl.lidb, base := base, F := { base.slots ns with next := nx },
      fs := tl.f9, ns := ns, lm := 5 }

variable {X : Verify.Public}

theorem lookAt_dig_even (h4 : X.p4 = true) (hN : X.NGr = 12) {g : Nat} (hg : g < 12) :
    lookAt X (2 * g) true =
      (X.G[g]?).bind fun hp => placeD "layers" (2 * g) hp.Fp.fillL hp.ns hp.tl 0 := by
  have e1 : (2 * g == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : (2 * g % 2 == 0) = true := by
    rw [beq_iff_eq]
    omega
  have e3 : 2 * g / 2 = g := by omega
  unfold lookAt
  simp only [h4, hN, if_true, e1, e2, e3, Bool.false_eq_true, if_false]
  rfl

theorem lookAt_dig_odd (h4 : X.p4 = true) (g : Nat) :
    lookAt X (2 * g + 1) true =
      (X.A[g]?).bind fun a => placeD "attention" (2 * g + 1) a.seam.Fp.fillL a.ns a.seam.tl 0 := by
  have e1 : (2 * g + 1 == 2 * X.NGr) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g + 1) % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e3 : (2 * g + 1) / 2 = g := by omega
  unfold lookAt
  simp only [h4, if_true, e1, e2, e3, Bool.false_eq_true, if_false]
  rfl

theorem lookAt_dig_head (h4 : X.p4 = true) (hN : X.NGr = 12) :
    lookAt X 24 true = placeD "head" 24 (({ trees := X.H.Fp.trees } : Fork).fillL) X.H.ns X.H.tl
      (wsForkSlots X.layers.wsLay.lk) := by
  unfold lookAt
  simp only [h4, hN, if_true]
  rfl

theorem tlAt_even (h4 : X.p4 = true) (hN : X.NGr = 12) {g : Nat} (hg : g < 12) :
    tlAt X (2 * g) = (X.G[g]?).map (·.tl) := by
  have e1 : (2 * g == 2 * 12) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : (2 * g % 2 == 0) = true := by
    rw [beq_iff_eq]
    omega
  have e3 : 2 * g / 2 = g := by omega
  unfold tlAt
  simp only [h4, hN, if_true, e1, e2, e3, Bool.false_eq_true, if_false]

theorem tlAt_odd (h4 : X.p4 = true) (g : Nat) :
    tlAt X (2 * g + 1) = (X.A[g]?).map (·.seam.tl) := by
  have e1 : (2 * g + 1 == 2 * X.NGr) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e2 : ((2 * g + 1) % 2 == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  have e3 : (2 * g + 1) / 2 = g := by omega
  unfold tlAt
  simp only [h4, if_true, e1, e2, e3, Bool.false_eq_true, if_false]

theorem tlAt_head (h4 : X.p4 = true) (hN : X.NGr = 12) : tlAt X 24 = some X.H.tl := by
  unfold tlAt
  simp only [h4, hN, if_true]
  rfl

/-- A place is there, and its view and the structure's are the written ones of segment i. -/
def digOk (i : Nat) (ox : Option Place) (tl : HTailF2) : Bool :=
  ox.any fun x => @decide _ (decP (viewP x) (viewP (pFull i))) &&
    @decide _ (decT (viewT tl) (viewT (tFull i)))

theorem digOk_gives {i : Nat} {ox : Option Place} {tl : HTailF2} (h : digOk i ox tl = true) :
    ∃ x, ox = some x ∧ narrowP x = pFull i ∧ narrowT { tl with f9 := {} } = tFull i := by
  unfold digOk at h
  cases ox with
  | none => cases h
  | some x =>
    simp only [Option.any, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨x, rfl, (narrowP_of_view h.1).trans (narrowP_pFull i),
      (narrowT_of_view h.2).trans (narrowT_tFull i)⟩

/-- The twelve even segments, off the layers' plans. -/
def digLB (G : Array Layer.HPlan2) : Bool :=
  (List.range 12).all fun g => (G[g]?).any fun hp =>
    digOk (2 * g) (placeD "layers" (2 * g) hp.Fp.fillL hp.ns hp.tl 0) hp.tl

/-- The twelve odd segments, off the attention's plans. -/
def digAB (A : Array Attention.Plan) : Bool :=
  (List.range 12).all fun g => (A[g]?).any fun a =>
    digOk (2 * g + 1) (placeD "attention" (2 * g + 1) a.seam.Fp.fillL a.ns a.seam.tl 0) a.seam.tl

/-- The head's segment, off the head's plan and the number lk of the weights' layout. -/
def digHB (H : Head.HPlanH2) (lk : Nat) : Bool :=
  digOk 24 (placeD "head" 24 (({ trees := H.Fp.trees } : Fork).fillL) H.ns H.tl
    (wsForkSlots lk)) H.tl

/-- The twelve attention segments: the lookup on the calls. -/
def readsAB (A : Array Attention.Plan) : Bool :=
  (List.range 12).all fun g => (A[g]?).any fun a =>
    decide (viewC (placeA (2 * g + 1) a) = viewC (cFull (2 * g + 1))) &&
      decide (viewM a.seam.tl = viewM mFull)

/-- An `all` over the twelve groups of an `any` at the group's plan. -/
theorem at_group {α : Type} {A : Array α} {f : Nat → α → Bool}
    (h : ((List.range 12).all fun g => (A[g]?).any (f g)) = true) {g : Nat} (hg : g < 12) :
    ∃ a, A[g]? = some a ∧ f g a = true := by
  have h' := List.all_eq_true.1 h g (List.mem_range.2 hg)
  cases e : A[g]? with
  | none =>
    rw [e] at h'
    cases h'
  | some a =>
    rw [e] at h'
    exact ⟨a, rfl, h'⟩

/-- **What the three tests on the digits give**: the premise hV of `digEntry_full`. -/
theorem dig_gives (h4 : X.p4 = true) (hN : X.NGr = 12) (hL : digLB X.G = true)
    (hA : digAB X.A = true) (hH : digHB X.H X.layers.wsLay.lk = true) :
    ∀ i < 25, ∃ x tl, lookAt X i true = some x ∧ tlAt X i = some tl ∧
      narrowP x = pFull i ∧ narrowT { tl with f9 := {} } = tFull i := by
  intro i hi
  by_cases h24 : i = 24
  · subst h24
    obtain ⟨x, e, a, b⟩ := digOk_gives hH
    exact ⟨x, X.H.tl, (lookAt_dig_head h4 hN).trans e, tlAt_head h4 hN, a, b⟩
  · obtain ⟨g, hg⟩ : ∃ g, i = 2 * g ∨ i = 2 * g + 1 := ⟨i / 2, by omega⟩
    rcases hg with rfl | rfl
    · have hg : g < 12 := by omega
      obtain ⟨hp, e0, ht⟩ := at_group hL hg
      obtain ⟨x, e, a, b⟩ := digOk_gives ht
      refine ⟨x, hp.tl, ?_, ?_, a, b⟩
      · rw [lookAt_dig_even h4 hN hg, e0]
        exact e
      · rw [tlAt_even h4 hN hg, e0]
        rfl
    · have hg : g < 12 := by omega
      obtain ⟨p, e0, ht⟩ := at_group hA hg
      obtain ⟨x, e, a, b⟩ := digOk_gives ht
      refine ⟨x, p.seam.tl, ?_, ?_, a, b⟩
      · rw [lookAt_dig_odd h4, e0]
        exact e
      · rw [tlAt_odd h4, e0]
        rfl

/-- **What the test on attention's lookups on the calls gives**: the premise hV of
`readsEntry_full`. -/
theorem reads_gives (h4 : X.p4 = true) (hA : readsAB X.A = true) :
    ∀ i ∈ attFull, ∃ x tl, lookAt X i false = some x ∧ tlAt X i = some tl ∧
      narrowC x = cFull i ∧ narrowM tl = mFull := by
  intro i hi
  unfold attFull at hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hi
  obtain ⟨a, e0, ht⟩ := at_group hA (List.mem_range.1 hg)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  refine ⟨placeA (2 * g + 1) a, a.seam.tl, ?_, ?_,
    (narrowC_of_view ht.1).trans (narrowC_cFull _), (narrowM_of_view ht.2).trans narrowM_mFull⟩
  · rw [lookAt_odd h4, e0]
    rfl
  · rw [tlAt_odd h4, e0]
    rfl

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.lookAt_dig_even
#print axioms Johnson.AtFull.Entry.lookAt_dig_odd
#print axioms Johnson.AtFull.Entry.lookAt_dig_head
#print axioms Johnson.AtFull.Entry.tlAt_even
#print axioms Johnson.AtFull.Entry.tlAt_odd
#print axioms Johnson.AtFull.Entry.tlAt_head
#print axioms Johnson.AtFull.Entry.digOk_gives
#print axioms Johnson.AtFull.Entry.at_group
#print axioms Johnson.AtFull.Entry.dig_gives
#print axioms Johnson.AtFull.Entry.reads_gives
