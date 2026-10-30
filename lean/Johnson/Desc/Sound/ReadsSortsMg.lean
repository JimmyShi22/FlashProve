-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsSortsMg.lean: THE LAWS BY SORT, LAID INTO `SortsPaid` AT THE COMPOSED
MEANING. One structure, six theorems.

Why. `readsOkAtQR_of_sorts` (Johnson/Desc/Sound/ReadsAllMg.lean) asks `SortsPaid`: seven sorts'
laws. Five of them lie, general in the composed meaning's parameters: here they are laid in, so that
what is still owed has names: the five congruences of `HidReads`, one on the weights' sentence, one
on the parameter that says `carry`, the law of `worth`, and what the pending rows' reader's laws
ask.

What is said. `BookPrem 𝔇 Mg M L get Rch k`: what the three laws that read through the
state's book ask together: the three public items' texts; the index masks' listed seat; the list's
bound; the four facts and "the statement is tidy" at reached states. `mg_wo`, `mg_row`, `mg_pile`:
the three sorts under it. `mg_forms`: the forms' four sorts, `formsT … "weights"` left out (it never
rides), under one premise on the weights' sentence. `mg_carry`: from a congruence of the parameter
cr1. `sortsPaid_mg`: all seven.

Limits. A joining. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsAllMg
import Johnson.Desc.Sound.ReadsConstr
import Johnson.Desc.Sound.ReadsItemWoMg
import Johnson.Desc.Sound.ReadsItemRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start RowClass)
open VerifiableInference.Desc.K13 (indexIsC indexThereC noneSentC)
open VerifiableInference.Desc.K13.Law (openAt BorderK13R FactsR13 PlanBelow readsItem_wo_mg
  readsItem_row readsOkAtR_k13)
open VerifiableInference.Desc.K12.Door (Laid)

section
variable {A Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (M : List OracleShape) (L : Laid) (links : List ModelPart) (ps : List Place)
  (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)

/-- **What the laws that read through the state's book ask together.** -/
structure BookPrem : Prop where
  indexIs : ∀ x, (mgAll 𝔇 Mg).pub .indexIs x = indexIsC 𝔇.N.indexNo x.2
  indexThere : ∀ x, (mgAll 𝔇 Mg).pub .indexThere x = indexThereC x.2
  noneSent : ∀ x, (mgAll 𝔇 Mg).pub .noneSent x = noneSentC 𝔇.N x.2
  seat : L.places[𝔇.N.indexNo]? = some 𝔇.N.index
  below : PlanBelow L 𝔇.N
  facts : ∀ a, Rch k a → (get a.1).2.failed = none → FactsR13 M L (get a.1).2
  tidy : ∀ a, Rch k a → (get a.1).2.failed = none → Means.tidy4B (get a.1).2.st = true

variable {𝔇 Mg M L links ps get Rch k}

theorem mg_wo (B : BookPrem 𝔇 Mg M L get Rch k) (hpin : Item.pinI ∈ openAt links ps k) (m : ℕ) :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.wo m) :=
  readsItem_wo_mg 𝔇 Mg M L B.indexIs B.indexThere B.seat B.below links ps get Rch k hpin m B.facts

theorem mg_row (B : BookPrem 𝔇 Mg M L get Rch k) (hpin : Item.pinI ∈ openAt links ps k) (m : ℕ)
    (c : RowClass) (hO : Item.row m c ∈ openAt links ps k) (ht : ∀ t, c = .sample t → t < 3) :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.row m c) :=
  readsItem_row 𝔇.N (mgAll 𝔇 Mg) 𝔇.arr M L B.indexIs B.indexThere B.below links ps get Rch k hpin m
    c hO (fun _ _ _ => Iff.rfl) B.facts B.tidy fun t e x hx => by
      have h3 := ht t e
      unfold Numbers.group
      rcases (by omega : t = 0 ∨ t = 1 ∨ t = 2) with rfl | rfl | rfl
      · exact List.mem_append_left _ (List.mem_append_left _ hx)
      · exact List.mem_append_left _ (List.mem_append_right _ hx)
      · exact List.mem_append_right _ hx

theorem mg_pile (B : BookPrem 𝔇 Mg M L get Rch k)
    (hB : BorderK13R (mgAll 𝔇 Mg).more links ps k) (i : Item) (hi : i = .pile ∨ i = .pileOne) :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k i :=
  fun a w w' ha hr hm ho hn hc hw =>
    readsOkAtR_k13 𝔇.N (mgAll 𝔇 Mg) 𝔇.arr 𝔇.mat13 M L links ps get Rch k (fun _ _ _ => Iff.rfl)
      (fun _ _ _ => Iff.rfl) B.indexIs B.indexThere B.noneSent B.seat B.below hB B.facts i hi a w w'
      ha hr hm ho hn hc hw

theorem mg_forms
    (hF : ∀ m j a y w w', (∀ c ∈ (Item.forms m j "weights").reads 𝔇.arr 𝔇.N links, sameQ c w w') →
      𝔇.wt m a y w → 𝔇.wt m a y w')
    (i : Item) (hi : formsSort i = true) (hne : ∀ m j, i ≠ .formsT m j "weights") :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k i := by
  refine readsItem_of_readsAt _ _ _ _ _ _ _ _ _ ?_
  intro a y w w' _ hc hw
  cases i with
  | forms m j r =>
    have hw0 : (∀ p ∈ 𝔇.runs m j r,
        if 𝔇.ah p.1 p.2 = true then
          formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)
        else formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
        (r = "weights" → 𝔇.wt m a y w) := hw
    show (∀ p ∈ 𝔇.runs m j r,
        if 𝔇.ah p.1 p.2 = true then
          formsQA (𝔇.N.sent m) (𝔇.N.group m) (𝔇.Rd m) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w')
        else formsQ (𝔇.Rd m) (𝔇.N.group m) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w')) ∧
        (r = "weights" → 𝔇.wt m a y w')
    refine ⟨fun p hp => ?_, fun e => ?_⟩
    · have h1 := hw0.1 p hp
      by_cases e : 𝔇.ah p.1 p.2 = true
      · rw [if_pos e] at h1 ⊢
        exact formsQA_congr (𝔇.N.sent m) _ (𝔇.Rd m) p.1 p.2 a.2 _ _
          (sameSeats 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N links _ w w' hc) h1
      · rw [if_neg e] at h1 ⊢
        exact formsQ_congr (𝔇.Rd m) _ p.1 p.2 a.2 _ _
          (sameSeats 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N links _ w w' hc) h1
    · subst e
      exact hF m j a y w w' hc (hw0.2 rfl)
  | formsT m j r =>
    have hw0 : (∀ p ∈ 𝔇.runs m j r,
        formsTQ (𝔇.Rd m) 𝔇.St (𝔇.N.sent m 0) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w)) ∧
        (r = "weights" → 𝔇.wt m a y w) := hw
    show (∀ p ∈ 𝔇.runs m j r,
        formsTQ (𝔇.Rd m) 𝔇.St (𝔇.N.sent m 0) p.1 p.2 a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w')) ∧
        (r = "weights" → 𝔇.wt m a y w')
    refine ⟨fun p hp => formsTQ_congr (𝔇.Rd m) 𝔇.St _ p.1 p.2 a.2 _ _
      (sameSeats 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N links _ w w' hc) (hw0.1 p hp), fun e => ?_⟩
    subst e
    exact absurd rfl (hne m j)
  | totalB m =>
    have hw0 : totalBQ (𝔇.after m) (𝔇.N.group m) a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧
        𝔇.rw m a.2 = true := hw
    exact ⟨totalBQ_congr (𝔇.after _) _ a.2 _ _ (sameSeats 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N links _ w w' hc)
      hw0.1, hw0.2⟩
  | total m =>
    have hw0 : totalQ (𝔇.N.group m) a.2 (seatTab 𝔇.cs 𝔇.arr 𝔇.ms w) ∧ 𝔇.rw m a.2 = true := hw
    exact ⟨totalQ_congr _ a.2 _ _ (sameSeats 𝔇.cs 𝔇.arr 𝔇.ms 𝔇.N links _ w w' hc) hw0.1, hw0.2⟩
  | _ => exact nomatch hi

theorem mg_carry
    (hC : ∀ m a y w w', (∀ c ∈ (Item.carry m).reads 𝔇.arr 𝔇.N links, sameQ c w w') →
      𝔇.cr1 m a y w → 𝔇.cr1 m a y w') (m : ℕ) :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.carry m) :=
  fun a w w' _ _ _ _ _ hc hw => hC m (get a.1) (strsOf Fr a.2) w w' hc hw

/-- **All seven.** -/
theorem sortsPaid_mg (R : HidReads 𝔇 links) (B : BookPrem 𝔇 Mg M L get Rch k)
    (hF : ∀ m j a y w w', (∀ c ∈ (Item.forms m j "weights").reads 𝔇.arr 𝔇.N links, sameQ c w w') →
      𝔇.wt m a y w → 𝔇.wt m a y w')
    (hC : ∀ m a y w w', (∀ c ∈ (Item.carry m).reads 𝔇.arr 𝔇.N links, sameQ c w w') →
      𝔇.cr1 m a y w → 𝔇.cr1 m a y w')
    (hW : ∀ m j r, 3 < j → m < links.length →
      ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k (.worth m j r)) :
    SortsPaid 𝔇 Mg links ps get Rch k where
  constr := fun m p hm => readsItem_constr 𝔇 links Mg R ps get Rch k m hm p
  forms := mg_forms hF
  worth := hW
  carry := mg_carry hC
  wo := mg_wo B
  row := mg_row B
  pile := mg_pile B

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.mg_wo
#print axioms VerifiableInference.Desc.Sound.mg_row
#print axioms VerifiableInference.Desc.Sound.mg_pile
#print axioms VerifiableInference.Desc.Sound.mg_forms
#print axioms VerifiableInference.Desc.Sound.mg_carry
#print axioms VerifiableInference.Desc.Sound.sortsPaid_mg
