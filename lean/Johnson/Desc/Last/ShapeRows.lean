-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeRows.lean: THE PROMISE OF THE TABLE OF THE LAST CHAIN's JOINTS, AT THE
FILLING `fillAt`, FROM BORDER TO BORDER BEHIND A PIECE: what rows 0, 1 and 3 owe under the name "the
promise behind follows from the promise in front and the yes". Statements and proofs.

Why. ShapeGives.lean has the steps of the book-keeping at the chain's own record. The table's rows
speak of a piece (Johnson/Desc/Sound/ChainRule.lean) at the wider record (what was handed, the
shared chain's last record, the chain's own) and of the oracles' strings. Here the two are joined.
THE STRINGS DO NOT STAY. Behind a piece the columns of the trees from its base on are what its
stretch has sent: behind a piece without a round: nothing. Below the base, and at the stored table's
cells, they stay (`out_behind`, Johnson/Desc/Sound/SendLaw.lean; `cellStays`, `colStays`,
Johnson/Desc/Sound/StringsStay.lean). So the two parts of the promise that read the strings must
read them below the base.

Main names (namespace `VerifiableInference.Desc.Last`).
  `PromReadsBelow N Pm Oc lo`: A CONDITION ON THE TABLE's LETTERS: Oc, and Omega's "shown, held,
    no collision", go over to strings that agree at the cells and at the trees below lo.
    `onL_next_at`: the promise at the next border at such strings: general in the table's letters.
  `YesAtOwn x b`: A CONDITION ON THE PIECE: where x hands a statement on, what was handed and the
    shared chain's last record ride along, and the chain's block b says yes at the own record in
    front with the own record behind.
  `onQ₃_next`: from border k to k + 1 at the filling, behind a piece. **`rowZero_prom`** (row 0:
    the promise behind K14's second part), **`rowOne_prom`**, `rowOne_same` (`RowOneOwed`'s fields,
    Johnson/Desc/Sound/QuietRows.lean), **`rowThree_owed`** (`RowThreeOwed`): each from `YesAtOwn`
    at the chain's own block and `PromReadsBelow` at the piece's base.

Every "there is", walked. In `YesAtOwn`: rs, gs: the rounds and columns at which the block says yes:
free: the steps hold at all.
Limits. The two conditions are premises: THEY ARE NOT SHOWN of a piece of the description or of a
filling of Oc and Pm. `YesAtOwn` is what a law "the piece's out is its block's yes" and the seat's
text would give: no such law is called here. Row 2's like
(`behind`) is not here: `step_two`'s four debts. NO MEMBER. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.ShapeAtTable
import Johnson.Desc.Sound.QuietRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-! ## 1 The promise at other strings: general in the table's letters -/

section
variable {S₂ S₃' P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃' P₁) (Oc : P₁ → Strs → Prop)

/-- **The promise's two parts that read the strings read them through the stored table and the trees
below lo alone**: a condition on the table's letters Oc and Pm. -/
def PromReadsBelow (lo : Nat) : Prop :=
  ∀ (y y' : Strs), (∀ x, y'.cell x = y.cell x) → (∀ j x, j < lo → y'.col j x = y.col j x) →
    (∀ x : P₁, Oc x y → Oc x y') ∧
      ∀ e : S₂, (PromS.noColl .oOmega).holds N Pm e y → (PromS.noColl .oOmega).holds N Pm e y'

/-- **The promise at the next border, at strings that agree with those in front below lo.** -/
theorem onL_next_at {lo k : Nat} {x : P₁} {e : S₂} {s s' : S₃'} {y y' : Strs}
    (hr : PromReadsBelow N Pm Oc lo) (hc : ∀ i, y'.cell i = y.cell i)
    (hl : ∀ j i, j < lo → y'.col j i = y.col j i) (h : onL N Mg Pm PL Oc k x e s y)
    (hs : PL.shape (k + 1) x e s' = true)
    (hn : lastPlaces.length ≤ k + 1 → PL.nothingLeft s' = true) :
    onL N Mg Pm PL Oc (k + 1) x e s' y' :=
  ⟨(hr y y' hc hl).1 x h.1, h.2.1,
    fun hp => (hr y y' hc hl).2 e (h.2.2.1 (pinO_open_before k hp)), hs, hn⟩

end

/-! ## 2 Rows 1 and 3 at the filling -/

section
variable {P S₁ S₂ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) Wt) (Pm : PromMeaning S₂) (Oc : P × S₁ → Strs → Prop) (p : P₁₄)
  (R : List Fmt.DeclaredRound) (hand : P × S₁ → Option Handed) (ended : S₂ → Option SharedOut)

/-- **The piece's yes is a yes of the chain's block b at the chain's own record, and what was handed
and the shared chain's last record ride along.** -/
def YesAtOwn (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt) (b : Block S₃ Cl) : Prop :=
  ∀ a τ c, x.ior.red.out a τ = some c →
    c.1.1 = a.1.1 ∧ ∃ rs gs, b.decide a.1.2 rs gs = .ok c.1.2

/-- From border k to k + 1 at the filling, behind a piece. -/
theorem onQ₃_next {k : Nat} (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (hr : PromReadsBelow N Pm Oc x.base) (a c : ((P × S₁ × S₂) × S₃) × Fr.E.Str)
    (τ : Iop.Tr (OnBytes.Maker.uLT C x.ds)) (ho : x.ior.red.out a τ = some c) (h1 : c.1.1 = a.1.1)
    (h : onQ₃ N Mg Pm (fillAt p R hand ended) Oc k a)
    (hs : ∀ f o, hand (a.1.1.1, a.1.1.2.1) = some f → ended a.1.1.2.2 = some o →
      shapeAt p R k f o a.1.2 = true → shapeAt p R (k + 1) f o c.1.2 = true)
    (hn : lastPlaces.length ≤ k + 1 → (ChainEnd.untestedL c.1.2.st).all (·.2) = true) :
    onQ₃ N Mg Pm (fillAt p R hand ended) Oc (k + 1) c := by
  obtain ⟨f, o, hf', ho', hk⟩ := shapeAt_of_onL N Mg Pm Oc p R hand ended h
  have e2 : c.2 = behind C Fr x.base x.ds a.2 τ := out_behind x a c τ ho
  show onL N Mg Pm (fillAt p R hand ended) Oc (k + 1) (c.1.1.1, c.1.1.2.1) c.1.1.2.2 c.1.2
    (strsOf Fr c.2)
  rw [h1, e2]
  exact onL_next_at (y := strsOf Fr a.2) (y' := strsOf Fr (behind C Fr x.base x.ds a.2 τ)) N Mg Pm _
    Oc hr (fun i => cellStays C Fr x.base x.ds a.2 τ i)
    (fun j i hj => colStays C Fr x.base x.ds a.2 τ j i hj) h
    (fill_of_shapeAt p R hand ended hf' ho' (hs f o hf' ho' hk)) hn

/-- **ROW 0: the promise behind K14's second part**, at the filling. -/
theorem rowZero_prom (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (hy : YesAtOwn x (batchLinearConstraintsSecondPart p)) (hr : PromReadsBelow N Pm Oc x.base) :
    ∀ a τ c, onQ₃ N Mg Pm (fillAt p R hand ended) Oc 0 a → x.ior.red.out a τ = some c →
      onQ₃ N Mg Pm (fillAt p R hand ended) Oc 1 c := by
  intro a τ c h ho
  obtain ⟨h1, rs, gs, hd⟩ := hy a τ c ho
  exact onQ₃_next N Mg Pm Oc p R hand ended x hr a c τ ho h1 h
    (fun _ _ _ _ hk => step_zero hk rs gs hd) (fun hl => absurd hl (by decide))

/-- **ROW 1's `prom`** (`RowOneOwed`, Johnson/Desc/Sound/QuietRows.lean), at the filling. -/
theorem rowOne_prom (own : Block S₃ Cl) (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (hy : YesAtOwn x (takenSources own)) (hr : PromReadsBelow N Pm Oc x.base) :
    ∀ a τ c, onQ₃ N Mg Pm (fillAt p own.rounds hand ended) Oc 1 a → x.ior.red.out a τ = some c →
      onQ₃ N Mg Pm (fillAt p own.rounds hand ended) Oc 2 c := by
  intro a τ c h ho
  obtain ⟨h1, rs, gs, hd⟩ := hy a τ c ho
  exact onQ₃_next N Mg Pm Oc p own.rounds hand ended x hr a c τ ho h1 h
    (fun _ _ _ _ hk => step_one own hk rs gs hd) (fun hl => absurd hl (by decide))

/-- **ROW 1's `same`.** -/
theorem rowOne_same (own : Block S₃ Cl) (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)
    (hy : YesAtOwn x (takenSources own)) :
    ∀ a τ c, x.ior.red.out a τ = some c → c.1 = a.1 := by
  intro a τ c ho
  obtain ⟨h1, rs, gs, hd⟩ := hy a τ c ho
  exact Prod.ext h1 ((takenSources_exact own a.1.2 rs gs c.1.2).1 hd).1

/-- **ROW 3** (`RowThreeOwed`), at the filling. -/
theorem rowThree_owed (inFront : List (Block S₃ Cl))
    (x : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt) (hy : YesAtOwn x (end₃ inFront))
    (hr : PromReadsBelow N Pm Oc x.base) :
    RowThreeOwed N Mg Pm (fillAt p R hand ended) Oc x := by
  intro a τ c h ho
  obtain ⟨h1, rs, gs, hd⟩ := hy a τ c ho
  exact onQ₃_next N Mg Pm Oc p R hand ended x hr a c τ ho h1 h
    (fun _ _ _ _ hk => (step_three hk inFront rs gs hd).1)
    (fun _ => by
      obtain ⟨e, hf⟩ := end₃_yes inFront a.1.2 c.1.2 rs gs hd
      rw [e]
      exact hf)

end

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.onL_next_at
#print axioms VerifiableInference.Desc.Last.onQ₃_next
#print axioms VerifiableInference.Desc.Last.rowZero_prom
#print axioms VerifiableInference.Desc.Last.rowOne_prom
#print axioms VerifiableInference.Desc.Last.rowOne_same
#print axioms VerifiableInference.Desc.Last.rowThree_owed
