-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsItemWo.lean: A SENTENCE THAT SAYS "THIS ROW HOLDS OF THE WITNESS, AS THE
PENDING ROWS' READER READS IT" READS ONLY WHAT THE TABLE BOOKS FOR THE ITEM wo m. Two theorems.

Why. The item `wo m` rides past many sub-protocols; each one's fifth tie asks `ReadsItemQR` of it
(Johnson/Desc/Sound/ReadsItems.lean). At the composed meaning its sentence reads the witness through
`rwBook` alone, the reader of the pending rows, which finds a mask entry's place through the state's
own book: so the law is not unconditional: it wants the promise and four facts on reached states, as
the pending rows' own law does (Johnson/Desc/K13/Law/ReadsK13R.lean).

What is said. `agree_at_promise`: at a statement inside the promise at a border where the index
masks' pin is open, without a mark, with the four facts, under the two public items' texts (hII,
hIT), the index masks' listed seat (hL) and the list's bound (hbelow): two witnesses that agree on
the cells and on the index masks' message and pad are read alike by `rwBook` at the index masks'
message. `readsItem_wo`: `ReadsItemQR … k (.wo m)`, where the meaning's sentence is "every row that
rowOf gives at the state holds", UNDER THESE SAME PREMISES AND ONE NAMED PREMISE MORE, hOn: every
mask entry that such a row names is of the index masks' message.

Limits. hOn is paid by nobody here. rowOf is a letter: at the composed meaning it is the frame's
reader of a segment's row. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsItems
import Johnson.Desc.K13.Law.ReadsK13R

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers Comp)
open VerifiableInference.Desc.Sound (MsgT Frame onQ meansQ sameQ ReadsItemQR)
open VerifiableInference.Desc.K12.Door (Laid toTree)

section
variable {A Pp Cells Tok : Type} {nR kC : ℕ} {Fr : Frame}

/-- Inside the promise, the pending rows' reader reads two like witnesses alike at the index masks'
message. -/
theorem agree_at_promise (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT))
    (arr : ℕ → ℕ → ℕ) (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape)
    (L : Laid) (hII : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = indexThereC x.2)
    (hL : L.places[N.indexNo]? = some N.index) (hbelow : PlanBelow L N) (links : List ModelPart)
    (ps : List Place) (get : A → Pp × S) (k : ℕ) (hpin : Item.pinI ∈ openAt links ps k)
    (a : A × Fr.E.Str) (ha : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none)
    (hFa : FactsR13 M L (get a.1).2) (w w' : Desc.Wit Cells Tok MsgT) (hc : w.cells = w'.cells)
    (hmsg : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2))
    (hpad : w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2) :
    AgreeAt (get a.1).2.out.indexMasks (rwBook arr mat (get a.1) w)
      (rwBook arr mat (get a.1) w') := by
  obtain ⟨hii, hit, hbk, _⟩ := promise_index N Mg links ps get k hpin a ha hm
  have hI : K1.indexIsB N.indexNo (get a.1).2 = true := by
    rw [← indexIsC_eq, ← hII]
    exact hii
  have hT : K1.indexThereB (get a.1).2 = true := by
    rw [← indexThereC_eq, ← hIT]
    exact hit
  have hbk' := hbk
  unfold First.bookAt at hbk'
  simp only [Bool.and_eq_true, beq_iff_eq] at hbk'
  have hseat : (get a.1).2.book.place[(get a.1).2.out.indexMasks]? = some N.index :=
    eq_of_beq (K1.indexSeat_of_carried ((K12.Coin.seatsPrefix_iff (toTree L) _).1 hFa.seats)
      hbk'.1.2 hT hI hL)
  have hthere : (get a.1).2.out.indexMasks < (get a.1).2.st.oracles.size := by
    have e : ((get a.1).2.st.oracles[(get a.1).2.out.indexMasks]?).isSome = true := hT
    obtain ⟨o, ho⟩ := Option.isSome_iff_exists.1 e
    exact (Array.getElem?_eq_some_iff.1 ho).1
  exact agree_at_index arr mat N M L (get a.1).1 (get a.1).2 hFa.shapes hFa.book hFa.seats hbk'.1.2
    (below_of_plan hbelow (get a.1) ps[k]? hbk hFa.seats) hthere hseat w w' hc hmsg hpad

/-- **The item wo m**, under one named premise on the row. -/
theorem readsItem_wo (N : Numbers) (Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)) (arr : ℕ → ℕ → ℕ)
    (mat : Cells → Fin nR → (Fin kC → Bool) → GE) (M : List OracleShape) (L : Laid)
    (hII : ∀ x, Mg.pub .indexIs x = indexIsC N.indexNo x.2)
    (hIT : ∀ x, Mg.pub .indexThere x = indexThereC x.2)
    (hL : L.places[N.indexNo]? = some N.index) (hbelow : PlanBelow L N) (links : List ModelPart)
    (ps : List Place) (get : A → Pp × S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)
    (hpin : Item.pinI ∈ openAt links ps k) (m : ℕ) (rowOf : S → Option TensorRow)
    (hW : ∀ x y w, Mg.wo m x y w ↔
      ∀ r : TensorRow, rowOf x.2 = some r → Holds Reading.gl (rwBook arr mat x w) r)
    (hFacts : ∀ a, Rch k a → (get a.1).2.failed = none → FactsR13 M L (get a.1).2)
    (hOn : ∀ a r, onQ N Mg links ps get k a → Rch k a → (get a.1).2.failed = none →
      rowOf (get a.1).2 = some r → OnLedger (get a.1).2.out.indexMasks r) :
    ReadsItemQR arr N Mg links ps get Rch k (.wo m) := by
  intro a w w' ha hr hm _ _ hc hw
  have hx : N.index ∈ (Item.wo m).tenants N := by simp [Item.tenants]
  have hmem : ∀ c ∈ [Comp.msg (arr N.index.1 N.index.2), Comp.pad N.index.1 N.index.2],
      c ∈ (Item.wo m).reads arr N links :=
    fun c h => List.mem_append_left _ (List.mem_flatMap.2 ⟨N.index, hx, h⟩)
  have h1 : w.msg (arr N.index.1 N.index.2) = w'.msg (arr N.index.1 N.index.2) :=
    hc (.msg _) (hmem _ (by simp))
  have h2 : w.pad N.index.1 N.index.2 = w'.pad N.index.1 N.index.2 :=
    hc (.pad _ _) (hmem _ (by simp))
  have h3 : w.cells = w'.cells := hc .cells (by simp [Item.reads])
  have hA := agree_at_promise N Mg arr mat M L hII hIT hL hbelow links ps get k hpin a ha hm
    (hFacts a hr hm) w w' h3 h1 h2
  have hw0 : Mg.wo m (get a.1) (Sound.strsOf Fr a.2) w := hw
  show Mg.wo m (get a.1) (Sound.strsOf Fr a.2) w'
  exact (hW _ _ _).2 fun r hrow =>
    (holds_congr Reading.gl (hOn a r ha hr hm hrow) hA).1 ((hW _ _ _).1 hw0 r hrow)

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.agree_at_promise
#print axioms VerifiableInference.Desc.K13.Law.readsItem_wo
