-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeAtTable.lean: THE FILLING OF THE LAST CHAIN's BOOK-KEEPING AT THE TABLE's OWN
PROMISE, AND FIVE TRIES. Statements and proofs.

Main names (namespace `VerifiableInference.Desc.Last`).
  `pinO_open_before`, **`onL_next`**: GENERAL IN THE TABLE's LETTERS: the promise `onL`
    (Johnson/Desc/Last/BordersLast.lean) at border k + 1, at the same handed things, shared end AND
    STRINGS, from the promise at k, the book-keeping's yes behind, and "nothing is left" where the
    table asks it.
  `shapeAt_of_fill`, `fill_of_shapeAt`, **`shapeAt_of_onL`**: at PL := `fillAt p R hand ended`:
    inside the table's promise something was handed (`hand x = some f`), the shared chain has ended
    (`ended e = some o`) and `shapeAt` says yes at f and o.
  TRIES. `late_zero`: border 1's test says no to border 0's record. `early_one`: border 0's to
    border 1's. `late_two`: border 3's to border 2's. `no_start`: where the start refuses what was
    handed the test says no at every border and record. `no_pile`: A CLOSED ONE: at an empty pile of
    pending rows it says no, whatever the rest.

Every "there is", walked. f, o (`shapeAt_of_fill`, `shapeAt_of_onL`): tied by `hand x = some f` and
`ended e = some o`: at most one each.
Limits. `onL_next` keeps the strings; behind a piece they do not stay, not even behind one without a
round: the form that the rows can spend is `onL_next_at` (Johnson/Desc/Last/ShapeRows.lean). The
first four tries are conditionals: three of them show that two neighbours' tests cannot both say yes
at one record: while there is no member they may hold for nothing; borders 1 | 2 and 3 | 4 are not
told apart (ShapeAt.lean, limit 3). NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeGives

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.Shared

/-! ## 1 The table's promise, from border to border: general in the table's letters -/

section
variable {S₂ S₃' P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃' P₁) (Oc : P₁ → Strs → Prop)

/-- Omega's pin, open behind a block, was open in front of it. -/
theorem pinO_open_before (k : Nat)
    (h : ((openSetsL lastPlaces startLast)[k + 1]?.getD []).contains .pinO = true) :
    ((openSetsL lastPlaces startLast)[k]?.getD []).contains .pinO = true := by
  have e : openSetsL lastPlaces startLast =
      [[.pinI, .pinV, .ev, .dot, .pinO], [.pinI, .pinV, .pinO, .rows], [.pinI, .pinV, .pinO, .rows],
        [], []] := by decide
  rw [e] at h ⊢
  match k, h with
  | 0, _ => decide
  | 1, _ => decide
  | 2, h => exact absurd h (by decide)
  | 3, h => exact absurd h (by decide)
  | _ + 4, h => exact absurd h (by simp)

/-- **The promise at the next border**, at the same handed things, shared end and strings: from the
promise in front, the book-keeping's yes behind, and "nothing is left" where the table asks it. -/
theorem onL_next {k : Nat} {x : P₁} {e : S₂} {s s' : S₃'} {y : Strs}
    (h : onL N Mg Pm PL Oc k x e s y) (hs : PL.shape (k + 1) x e s' = true)
    (hn : lastPlaces.length ≤ k + 1 → PL.nothingLeft s' = true) :
    onL N Mg Pm PL Oc (k + 1) x e s' y :=
  ⟨h.1, h.2.1, fun hp => h.2.2.1 (pinO_open_before k hp), hs, hn⟩

end

/-! ## 2 At the filling -/

section
variable {S₂ P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂)
  (Oc : P₁ → Strs → Prop) (p : P₁₄) (R : List Fmt.DeclaredRound) (hand : P₁ → Option Handed)
  (ended : S₂ → Option SharedOut)

/-- The filling's yes: something was handed, the shared chain has ended, and `shapeAt` says yes. -/
theorem shapeAt_of_fill {k : Nat} {x : P₁} {e : S₂} {s : S₃}
    (h : (fillAt p R hand ended).shape k x e s = true) :
    ∃ f o, hand x = some f ∧ ended e = some o ∧ shapeAt p R k f o s = true := by
  have h' : (match hand x, ended e with
    | some f, some o => shapeAt p R k f o s
    | _, _ => false) = true := h
  split at h'
  · rename_i f o hf ho
    exact ⟨f, o, hf, ho, h'⟩
  · cases h'

theorem fill_of_shapeAt {k : Nat} {x : P₁} {e : S₂} {s : S₃} {f : Handed} {o : SharedOut}
    (hf : hand x = some f) (ho : ended e = some o) (h : shapeAt p R k f o s = true) :
    (fillAt p R hand ended).shape k x e s = true := by
  show (match hand x, ended e with
    | some f, some o => shapeAt p R k f o s
    | _, _ => false) = true
  rw [hf, ho]
  exact h

/-- **Inside the table's promise at the filling.** -/
theorem shapeAt_of_onL {k : Nat} {x : P₁} {e : S₂} {s : S₃} {y : Strs}
    (h : onL N Mg Pm (fillAt p R hand ended) Oc k x e s y) :
    ∃ f o, hand x = some f ∧ ended e = some o ∧ shapeAt p R k f o s = true :=
  shapeAt_of_fill p R hand ended h.2.2.2.1

end

/-! ## 3 Tries: a border's test fed with a neighbour's record -/

/-- Border 1's test says no to border 0's record. -/
theorem late_zero {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 0 h o s = true) : shapeAt p R 1 h o s = false := by
  cases c : shapeAt p R 1 h o s with
  | false => rfl
  | true =>
    obtain ⟨s₀, B⟩ := behindOk_of_one c
    obtain rfl : s₀ = s := Except.ok.inj (B.start.symm.trans (started_of_shape hs).1)
    obtain ⟨b, y, G, dot, L⟩ := B.laid
    exact absurd L (laid_irrefl _ _ _ _ _ _)

/-- Border 0's test says no to border 1's record. -/
theorem early_one {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 1 h o s = true) : shapeAt p R 0 h o s = false := by
  cases c : shapeAt p R 0 h o s with
  | false => rfl
  | true => rw [late_zero c] at hs; cases hs

/-- Border 3's test says no to border 2's record: no test has begun there. -/
theorem late_two {p : P₁₄} {R : List Fmt.DeclaredRound} {h : Handed} {o : SharedOut} {s : S₃}
    (hs : shapeAt p R 2 h o s = true) : shapeAt p R 3 h o s = false := by
  cases c : shapeAt p R 3 h o s with
  | false => rfl
  | true =>
    obtain ⟨⟨s₀, B⟩, _⟩ := behindOk_of_two hs
    obtain ⟨G, hG, _, hr⟩ := rows_there B
    obtain ⟨s₁, _, _, hc⟩ := shapeAt_inv c
    simp only [clausesAt, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at hc
    have c1 := hc.1
    rw [hG] at c1
    have c2 : G.inRun = true := c1
    rw [hr] at c2
    cases c2

/-- Where the start refuses what was handed, the test says no at every border and record. -/
theorem no_start {p : P₁₄} {R : List Fmt.DeclaredRound} {k : Nat} {h : Handed} {o : SharedOut} {s : S₃}
    {why : String} (hn : start₃E p.codes p.S h.st h.book h.roots h.w h.own h.mask h.pending o =
        .error why) :
    shapeAt p R k h o s = false := by
  unfold shapeAt allClauses
  rw [hn]
  rfl

/-- **A closed try**: at an empty pile of pending rows the test says no: at every border, record,
plan and shared end. -/
theorem no_pile (p : P₁₄) (R : List Fmt.DeclaredRound) (k : Nat) (st : Statement) (bk : TreeBook)
    (roots w own : Nat) (mask : Option Nat) (o : SharedOut) (s : S₃) :
    shapeAt p R k ⟨st, bk, roots, w, own, mask, []⟩ o s = false := by
  cases hc : (!(p.codes.lengthsOk && linOk p.codes p.S)) with
  | true =>
    exact no_start (why := "the shape is not lawful at the codes") (by
      show start₃E p.codes p.S st bk roots w own mask [] o = _
      unfold start₃E
      rw [if_pos hc])
  | false =>
    exact no_start (why := "the first chain's end gives no W, own group and one pending row") (by
      show start₃E p.codes p.S st bk roots w own mask [] o = _
      unfold start₃E
      rw [if_neg (by rw [hc]; exact Bool.false_ne_true)]
      rfl)

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.pinO_open_before
#print axioms VerifiableInference.Desc.Last.onL_next
#print axioms VerifiableInference.Desc.Last.shapeAt_of_fill
#print axioms VerifiableInference.Desc.Last.fill_of_shapeAt
#print axioms VerifiableInference.Desc.Last.shapeAt_of_onL
#print axioms VerifiableInference.Desc.Last.late_zero
#print axioms VerifiableInference.Desc.Last.early_one
#print axioms VerifiableInference.Desc.Last.late_two
#print axioms VerifiableInference.Desc.Last.no_start
#print axioms VerifiableInference.Desc.Last.no_pile
