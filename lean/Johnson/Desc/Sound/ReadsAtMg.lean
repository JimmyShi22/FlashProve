-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsAtMg.lean: AT THE COMPOSED MEANING, AN ITEM's SENTENCE READS NO MORE OF THE
WITNESS THAN THE TABLE BOOKS FOR IT: THE PINS' SORTS. Seven theorems.

Why. The fifth tie of a sub-protocol's law asks that an item which rides past it keeps its sentence
under the extractor. The table gives that from two facts: the extractor lays no component that the
rider reads (`RidersClearQ`), and the rider's sentence reads only the components that `Item.reads`
books (`ReadsOkAtQR`, by `readsOkAtR_of_fit` from `ReadsAt` item by item). `ReadsAt` lies
for the forms' four sorts in `readsAt_forms`, and for the pins' sorts here.

What is said. `msgsOf_congr`: the witness's message at a member is one at two witnesses that agree
on that member's number and seat. `pinAt_congr`, `pinJT_congr`: so is the pin there. `readsAt_pinW`,
`readsAt_pins` (pin m t, pinKept m, pinI, pinV), `readsAt_unmarked`: `ReadsAt` at `mgAll 𝔇 Mg`, at
the table's own `Item.reads 𝔇.arr 𝔇.N links`, under no condition on the statement. `pinsSort`: which
items these are.

Limits. Congruences. Nothing on soundness. The other sorts (wo, pile, pileOne, constr, worth, row,
carry, tie, wrow) are not here.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.ReadsFitLaw
import Johnson.Desc.Sound.EvalKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp)

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat : Fin l.length → ℕ × ℕ) {A Cells Tok : Type}
  (smp : A → (i : Fin l.length) → Option ((sigOf cs l).om i).Smp) (arr : ℕ → ℕ → ℕ)

/-- The witness's message at a member reads that member's number and seat alone. -/
theorem msgsOf_congr (w w' : Wit Cells Tok MsgT) (i : Fin l.length)
    (h1 : w'.msg (arr (seat i).1 (seat i).2) = w.msg (arr (seat i).1 (seat i).2))
    (h2 : w'.pad (seat i).1 (seat i).2 = w.pad (seat i).1 (seat i).2) :
    msgsOf cs l seat arr w' i = msgsOf cs l seat arr w i := by
  funext j
  unfold msgsOf
  cases j with
  | inl q => simp only [tab_congr w w' cs (l.get i).1 _ _ _ h1 h2]
  | inr q => simp only [tab_congr w w' cs (l.get i).1 _ _ _ h1 h2]

/-- So does the pin there. -/
theorem pinAt_congr (w w' : Wit Cells Tok MsgT) (i : Fin l.length) (a : A) (y : Strs)
    (h1 : w'.msg (arr (seat i).1 (seat i).2) = w.msg (arr (seat i).1 (seat i).2))
    (h2 : w'.pad (seat i).1 (seat i).2 = w.pad (seat i).1 (seat i).2)
    (h : PinAt G cs l seat smp arr i a y w) : PinAt G cs l seat smp arr i a y w' := by
  obtain ⟨z, hz, hs, hd⟩ := h
  exact ⟨z, hz, hs, by rw [msgsOf_congr cs l seat arr w w' i h1 h2]; exact hd⟩

end

section
variable {Xi : Type} (G : FileDescription Xi) (cs : OnBytes.Codes) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem)

/-- The pin at a seat reads that seat's message and pad alone. -/
theorem pinJT_congr (j t : ℕ) (a : A) (y : Strs) (w w' : Wit Cells Tok MsgT)
    (h1 : w.msg (arr j t) = w'.msg (arr j t)) (h2 : w.pad j t = w'.pad j t)
    (h : pinJT cs G arr smp ms j t a y w) : pinJT cs G arr smp ms j t a y w' := by
  refine ⟨h.1, fun x hx hs => ?_⟩
  have e : x.1.seat x.2 = (j, t) := hs
  refine pinAt_congr G cs x.1.l x.1.seat (fun z => smp z x.1) arr w w' x.2 a y ?_ ?_ (h.2 x hx hs)
  · rw [e]
    exact h1.symm
  · rw [e]
    exact h2.symm

end

/-- The sorts of this file. -/
def pinsSort : Item → Bool
  | .pin _ _ => true
  | .pinKept _ => true
  | .pinI => true
  | .pinV => true
  | _ => false

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (links : List ModelPart)

/-- What two witnesses that agree on an item's booked components agree on at a tenant's seat. -/
theorem same_at_tenant (i : Item) (w w' : Wit (CellsQ rows cols) Tok MsgT)
    (h : ∀ c ∈ i.reads 𝔇.arr 𝔇.N links, sameQ c w w') (x : ℕ × ℕ) (hx : x ∈ i.tenants 𝔇.N) :
    w.msg (𝔇.arr x.1 x.2) = w'.msg (𝔇.arr x.1 x.2) ∧ w.pad x.1 x.2 = w'.pad x.1 x.2 := by
  have hm : ∀ c ∈ [Comp.msg (𝔇.arr x.1 x.2), Comp.pad x.1 x.2], c ∈ i.reads 𝔇.arr 𝔇.N links :=
    fun c hc => List.mem_append_left _ (List.mem_flatMap.2 ⟨x, hx, hc⟩)
  exact ⟨h (.msg (𝔇.arr x.1 x.2)) (hm _ (by simp)), h (.pad x.1 x.2) (hm _ (by simp))⟩

theorem readsAt_pinW :
    ReadsAt (fun _ _ => True) (fun j => j.reads 𝔇.arr 𝔇.N links) 𝔇.N (mgAll 𝔇 Mg) .pinW := by
  intro a y w w' _ hc hw
  have e : w.cells = w'.cells := hc .cells (by simp [Item.reads, Item.tenants])
  show pinWOf 𝔇.decT a y w'
  have hw' : pinWOf 𝔇.decT a y w := hw
  unfold pinWOf at hw' ⊢
  rw [← e]
  exact hw'

theorem readsAt_pins (i : Item) (hi : pinsSort i = true) :
    ReadsAt (fun _ _ => True) (fun j => j.reads 𝔇.arr 𝔇.N links) 𝔇.N (mgAll 𝔇 Mg) i := by
  intro a y w w' _ hc hw
  have S := same_at_tenant 𝔇 links i w w' hc
  cases i with
  | pin m t =>
    exact fun x hx => pinJT_congr 𝔇.G 𝔇.cs 𝔇.arr 𝔇.smp 𝔇.ms x.1 x.2 a y w w' (S x hx).1 (S x hx).2
      (hw x hx)
  | pinKept m =>
    exact fun x hx => pinJT_congr 𝔇.G 𝔇.cs 𝔇.arr 𝔇.smp 𝔇.ms x.1 x.2 a y w w' (S x hx).1 (S x hx).2
      (hw x hx)
  | pinI =>
    have s := S 𝔇.N.index (by simp [Item.tenants])
    exact pinJT_congr 𝔇.G 𝔇.cs 𝔇.arr 𝔇.smp 𝔇.ms _ _ a y w w' s.1 s.2 hw
  | pinV =>
    have s := S 𝔇.N.w (by simp [Item.tenants])
    exact pinJT_congr 𝔇.G 𝔇.cs 𝔇.arr 𝔇.smp 𝔇.ms _ _ a y w w' s.1 s.2 hw
  | _ => exact nomatch hi

theorem readsAt_unmarked :
    ReadsAt (fun _ _ => True) (fun j => j.reads 𝔇.arr 𝔇.N links) 𝔇.N (mgAll 𝔇 Mg) .unmarked :=
  fun _ _ _ _ _ _ hw => hw

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.pinJT_congr
#print axioms VerifiableInference.Desc.Sound.readsAt_pinW
#print axioms VerifiableInference.Desc.Sound.readsAt_pins
#print axioms VerifiableInference.Desc.Sound.readsAt_unmarked
