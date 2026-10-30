-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/FillsAtPlus13.lean: the nine
equations that K01_law asks of the meaning (`FillsK1`, K1/Law/FillsK1.lean) hold at the wider
meaning `plus13 (d13 Dm) dk (mgAll Dm Mg₀)`: the three struck layers (K13/Law/BridgeK13.lean) laid
again over the composed meaning (Sound/MgAll.lean). General in `Dm` (that file's
structure of all parameters), `dk` and `Mg₀`. Statements with their proofs.
  `pubKeeper_cong`, `pubAll_cong`   `pubAll D base q a` reads `base` at `q` and `a` alone
  `class_unfilled`   at one of the eight names of the class `cA13` no part of `pubAll` answers
  `plus13_own`       at such a name the wider meaning's test does not read what lies beneath
  `pub_plus13`       so the three layers may be laid over `pubAll` or beneath it: the field `pub`
  `fillsK1_plus13_of`, `fillsK1_plus13`   **the nine equations**: at a letter io0 for what "in
                     order" says beside `inOrderK13`, and at `mgAll`'s own term. Seven are `rfl`
The letters: io0 a := Mg₀.inOrder a && (Meaning.backReq (Dm.reqB a.1)).isSome; base := the three
layers' tests over Mg₀'s; MgP := the pending claim's layer over Mg₀ (as `mgAll_pubP` names it).
What is not claimed. Nothing on which public items are open, nor on any sub-protocol. Nothing on
soundness.

-/
import Johnson.Desc.K1.Law.FillsK1
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker Cb Johnson.Pack
open VerifiableInference.Desc.First (S Pub Meaning PubData pubAll pubKeeper keeperItem formsItem
  pubAll_else weightsItem)
open VerifiableInference.Desc.Sound (MsgT MgData CellsQ mgAll d13)
open VerifiableInference.Desc.K13 (k13ItemC k13PlusItemC)
open VerifiableInference.Desc.K13.Law (plus13 cA13 plus13_hand DataK13)
open VerifiableInference.Desc.K12.Door (K12Data k12Item)

/-! ## 1 `pubAll` reads `base` at the item alone -/

section
variable {P : Type}

theorem pubKeeper_cong (nsOf : ℕ → Option ℕ) (f f' : Pub → P × S → Bool) (q : Pub) (a : P × S)
    (h : f q a = f' q a) : pubKeeper nsOf f q a = pubKeeper nsOf f' q a := by
  cases q <;> first | rfl | exact h

theorem pubAll_cong (D : PubData) (base base' : Pub → P × S → Bool) (q : Pub) (a : P × S)
    (h : base q a = base' q a) : pubAll D base q a = pubAll D base' q a := by
  unfold pubAll
  exact First.pubForms_cong D _ _ q a (First.pubK13C_cong D _ _ q a (First.pubK3_cong D _ _ q a
    (First.pubK6K7_cong D _ _ q a (First.pubK4_cong D _ _ q a (First.pubP1_cong D _ _ q a
      (First.pubK5_cong D _ _ q a (First.pubSent_cong D _ _ q a (First.pubSent1_cong D _ _ q a
        (First.pubLeft_cong D _ _ q a (pubKeeper_cong D.nsOf _ _ q a h))))))))))

end

/-! ## 2 The eight names of the class -/

/-- An item of the class is one of eight names that belong to no segment. -/
theorem class_names (q : Pub) (h : cA13 q = true) :
    q = .more none "K13.pileMasks" ∨ q = .more none "K13.pileWithin" ∨
      q = .more none "K13.oneRow" ∨ q = .more none "K13.weightsOk" ∨
      q = .more none "K12.bookInOrder" ∨ q = .more none "K12.seatsCarried" ∨
      q = .more none "K12.msgShapes" ∨ q = .more none "K12.bookFits" := by
  cases q with
  | more seg name =>
    cases seg with
    | some m => simp [cA13, k13PlusItemC, weightsItem, k12Item] at h
    | none =>
      simp only [cA13, k13PlusItemC, weightsItem, k12Item, Option.isNone_none, Bool.true_and,
        Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (((rfl | rfl) | rfl) | rfl) | (((rfl | rfl) | rfl) | rfl)
      · exact .inl rfl
      · exact .inr (.inl rfl)
      · exact .inr (.inr (.inl rfl))
      · exact .inr (.inr (.inr (.inl rfl)))
      · exact .inr (.inr (.inr (.inr (.inl rfl))))
      · exact .inr (.inr (.inr (.inr (.inr (.inl rfl)))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl rfl))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr rfl))))))
  | _ => simp [cA13, k13PlusItemC, weightsItem, k12Item] at h

/-- At an item of the class no part of `pubAll` answers. -/
theorem class_unfilled {P : Type} (D : PubData) (base : Pub → P × S → Bool) (q : Pub)
    (h : cA13 q = true) (a : P × S) : pubAll D base q a = base q a := by
  rcases class_names q h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact pubAll_else D base _ rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl a

/-- At an item of the class the wider meaning's test does not read what lies beneath. -/
theorem plus13_own {Pp W : Type} {nR : ℕ} (D : DataK13 Pp W nR) (dk : K12Data)
    (M M' : Meaning Pp W) (q : Pub) (h : cA13 q = true) (x : Pp × S) :
    (plus13 D dk M).pub q x = (plus13 D dk M').pub q x := by
  rcases class_names q h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-! ## 3 The nine equations -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **The field `pub`**: the three layers over `pubAll` are `pubAll` over the three layers. -/
theorem pub_plus13 : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).pub =
    pubAll Dm.pubD (plus13 (d13 Dm) dk Mg₀).pub := by
  funext q a
  cases hc : cA13 q with
  | true =>
    rw [class_unfilled Dm.pubD _ q hc a]
    exact plus13_own (d13 Dm) dk _ _ q hc a
  | false =>
    rw [plus13_hand (d13 Dm) dk _ q hc a]
    show pubAll Dm.pubD Mg₀.pub q a = _
    exact pubAll_cong Dm.pubD _ _ q a (plus13_hand (d13 Dm) dk Mg₀ q hc a).symm

/-- The nine equations, at a letter `io0` for what "in order" says beside `inOrderK13`: so that a
conjunct more in the composed meaning's "in order" turns the premise `hio` alone. -/
theorem fillsK1_plus13_of (io0 : P × S → Bool) (hio : ∀ a, (mgAll Dm Mg₀).inOrder a = io0 a) :
    FillsK1 Dm.pubD Dm.G Dm.arr Dm.smp Dm.ms Dm.decT Dm.shape Dm.layout io0
      (plus13 (d13 Dm) dk Mg₀).pub X Dm.sent
      (First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀)
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) where
  held := rfl
  shown := rfl
  noColl := rfl
  pin := rfl
  decodes := rfl
  pinW := rfl
  inOrder := fun a => by
    show ((mgAll Dm Mg₀).inOrder a && K13.Law.inOrderK13 Dm.cs Dm.shape Dm.layout a.2) = _
    rw [hio a]
    rfl
  pub := pub_plus13 Dm dk Mg₀
  pubP := rfl

/-- **K1's premises on the meaning hold at the wider meaning over `mgAll`.** -/
theorem fillsK1_plus13 :
    FillsK1 Dm.pubD Dm.G Dm.arr Dm.smp Dm.ms Dm.decT Dm.shape Dm.layout
      (fun a => Mg₀.inOrder a && (_root_.Meaning.backReq (Dm.reqB a.1)).isSome)
      (plus13 (d13 Dm) dk Mg₀).pub X Dm.sent
      (First.FillP1.fillP1 Dm.d1 Dm.rw13 Dm.A1 Dm.cr1 Mg₀)
      (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) :=
  fillsK1_plus13_of Dm dk Mg₀ _ fun _ => rfl

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pubAll_cong
#print axioms VerifiableInference.Desc.K1.class_unfilled
#print axioms VerifiableInference.Desc.K1.plus13_own
#print axioms VerifiableInference.Desc.K1.pub_plus13
#print axioms VerifiableInference.Desc.K1.fillsK1_plus13_of
#print axioms VerifiableInference.Desc.K1.fillsK1_plus13
