-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsAllMg.lean: "EVERY RIDER's SENTENCE READS ONLY WHAT THE TABLE BOOKS", AT A
BORDER OF THE FIRST CHAIN, AT THE COMPOSED MEANING: FROM THE LAWS BY SORT AND ONE CLOSED TEST ON THE
TABLE. Two tests with code, one structure, two theorems.

Why. Every sub-protocol's fifth tie asks `ReadsOkAtQR … k` at its own border k. The laws lie by the
item's sort, some under a fence that speaks of what is open at k. Here they are joined: nobody lists
the riders of a border by hand.

What is said. `readsOkAtQR_of_open`: it is enough to show `ReadsItemQR … k i` of the items that
stand on the table's own list of what is open at k and not on the row's list of what it closes or
reads (by `openIsList` and `openL_iff_openSets`, under the table's three closed tests). `ridersFitB
M links ps k`: A TEST THAT CAN FAIL, on the written lists alone: of every rider at k: a `constr`'s
segment is on the list; where `wo` or `row` rides the index masks' pin is open; a riding `row …
(sample t)` has t < 3; where `pile` or `pileOne` rides the pending rows' law's own border test
accepts; a riding `worth m j r` has 3 < j and m on the list; no `formsT … "weights"` rides; `tie`
and `wrow` do not ride. `SortsPaid 𝔇 Mg links ps get Rch k`: the laws of the seven sorts that are
not paid outright, each under its fence. `readsOkAtQR_of_sorts`: from these two, the
table's three closed tests, k ≤ the list of places' length, and the pins' sorts' laws of
Johnson/Desc/Sound/ReadsAtMg.lean: `ReadsOkAtQR` at k.

Limits. A joining. `SortsPaid` is paid by nobody here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsItems
import Johnson.Desc.Sound.SpineList
import Johnson.Desc.K13.Law.ReadsK13R

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start readsOpen RowClass)
open VerifiableInference.Desc.K13.Law (openAt BorderK13R borderK13RB borderK13R_of)

section
variable {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
  (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)

/-- It is enough at the items on the table's own list of what is open at k. -/
theorem readsOkAtQR_of_open (h1 : readsOpen links ps (start links) = true)
    (h2 : rowsApart links ps = true) (h3 : Item.unmarked ∈ start links) (hk : k ≤ ps.length)
    (h : ∀ i ∈ openAt links ps k, i ∉ insL links ps k →
      ReadsItemQR arr N Mg links ps get Rch k i) :
    ReadsOkAtQR (Fr := Fr) arr N Mg links ps get Rch k :=
  fun i a w w' ha hr hm ho hn hc hw =>
    h i ((openL_iff_openSets links ps (start links) h1 h2 h3 k hk i).1
      ((openIsList Item (insL links ps) (outsL links ps) (start links) k i).1 ho)) hn
      a w w' ha hr hm ho hn hc hw

end

/-- What the laws' fences ask of one rider, given what is open at the border. -/
def riderFitB (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Item → Bool
  | .constr m _ => decide (m < links.length)
  | .wo _ => (openAt links ps k).contains .pinI
  | .row _ (.sample t) => (openAt links ps k).contains .pinI && decide (t < 3)
  | .row _ _ => (openAt links ps k).contains .pinI
  | .pile => borderK13RB M links ps k
  | .pileOne => borderK13RB M links ps k
  | .worth m j _ => decide (3 < j) && decide (m < links.length)
  | .formsT _ _ s => s != "weights"
  | .tie _ => false
  | .wrow => false
  | _ => true

/-- **A test on the written lists**: every rider at k meets its law's fence. -/
def ridersFitB (M : First.More) (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((openAt links ps k).filter fun i => !(insL links ps k).contains i).all
    (riderFitB M links ps k)

section
variable {A Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
  (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)

/-- **The laws of the sorts that are not paid outright, each under its fence.** -/
structure SortsPaid : Prop where
  constr : ∀ m p, m < links.length →
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.constr m p)
  forms : ∀ i, formsSort i = true → (∀ m j, i ≠ .formsT m j "weights") →
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k i
  worth : ∀ m j r, 3 < j → m < links.length →
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.worth m j r)
  carry : ∀ m, ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.carry m)
  wo : Item.pinI ∈ openAt links ps k → ∀ m,
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.wo m)
  row : Item.pinI ∈ openAt links ps k → ∀ m c, Item.row m c ∈ openAt links ps k →
    (∀ t, c = .sample t → t < 3) →
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.row m c)
  pile : BorderK13R (mgAll 𝔇 Mg).more links ps k → ∀ i, i = .pile ∨ i = .pileOne →
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k i

/-- **Every rider at k reads only what the table books.** -/
theorem readsOkAtQR_of_sorts (h1 : readsOpen links ps (start links) = true)
    (h2 : rowsApart links ps = true) (h3 : Item.unmarked ∈ start links) (hk : k ≤ ps.length)
    (hfit : ridersFitB (mgAll 𝔇 Mg).more links ps k = true)
    (S : SortsPaid 𝔇 Mg links ps get Rch k) :
    ReadsOkAtQR (Fr := Fr) 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k := by
  refine readsOkAtQR_of_open _ _ _ _ _ _ _ _ h1 h2 h3 hk fun i hi hn => ?_
  have hf : riderFitB (mgAll 𝔇 Mg).more links ps k i = true :=
    List.all_eq_true.1 hfit i (List.mem_filter.2 ⟨hi, by simpa using hn⟩)
  cases i with
  | constr m p => exact S.constr m p (of_decide_eq_true hf)
  | pin m t => exact readsItem_pins 𝔇 Mg links ps get Rch k _ rfl
  | pinKept m => exact readsItem_pins 𝔇 Mg links ps get Rch k _ rfl
  | tie m => exact absurd hf (by simp [riderFitB])
  | pinI => exact readsItem_pins 𝔇 Mg links ps get Rch k _ rfl
  | pinV => exact readsItem_pins 𝔇 Mg links ps get Rch k _ rfl
  | pinW => exact readsItem_pinW 𝔇 Mg links ps get Rch k
  | forms m j r => exact S.forms _ rfl fun _ _ e => nomatch e
  | formsT m j r =>
    have hne : r ≠ "weights" := by simpa [riderFitB] using hf
    exact S.forms _ rfl fun m' j' e => by
      cases e
      exact hne rfl
  | worth m j r =>
    have hf' : 3 < j ∧ m < links.length := by simpa [riderFitB] using hf
    exact S.worth m j r hf'.1 hf'.2
  | wo m => exact S.wo (by simpa [riderFitB] using hf) m
  | totalB m => exact S.forms _ rfl fun _ _ e => nomatch e
  | total m => exact S.forms _ rfl fun _ _ e => nomatch e
  | row m c =>
    cases c with
    | sample t =>
      have hf' : (openAt links ps k).contains .pinI = true ∧ t < 3 := by
        simpa [riderFitB] using hf
      exact S.row (by simpa using hf'.1) m _ hi fun t' e => by
        cases e
        exact hf'.2
    | carried => exact S.row (by simpa [riderFitB] using hf) m _ hi fun t' e => nomatch e
    | position => exact S.row (by simpa [riderFitB] using hf) m _ hi fun t' e => nomatch e
    | equation => exact S.row (by simpa [riderFitB] using hf) m _ hi fun t' e => nomatch e
  | carry m => exact S.carry m
  | pile => exact S.pile (borderK13R_of hf) _ (Or.inl rfl)
  | pileOne => exact S.pile (borderK13R_of hf) _ (Or.inr rfl)
  | wrow => exact absurd hf (by simp [riderFitB])
  | unmarked => exact readsItem_unmarked 𝔇 Mg links ps get Rch k

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOkAtQR_of_open
#print axioms VerifiableInference.Desc.Sound.readsOkAtQR_of_sorts
