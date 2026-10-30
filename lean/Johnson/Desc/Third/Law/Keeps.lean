-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/Keeps.lean: the last chain's own blocks keep the invariant of
Johnson/Desc/Third/Law/Later.lean. A definition of Prop and theorems.

Main names:
  `Keeps st b`: whatever the block b returns, `Carries (st s) (st s')`.
  `takeOver_inv`, `k14Second_inv`: a yes of the text, taken apart step by step.
  `keeps_k14Second`, `keeps_takenSources`; `takeOver_shape`.

Limits. Nothing on the own proximity test's block, which writes a mark. An invariant, no kind's law
by itself: see Johnson/Desc/Third/Law/Silly.lean [not in this library]. Nothing on soundness or on
hiding.
-/
import Johnson.Desc.Third.Law.Later
import Johnson.Desc.Third.TakenSources

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes OnBytes.Slice
open Desc.Plain (DState)
open VerifiableInference.Desc.Later
open VerifiableInference.Desc.Ground (adoptP elsewhereP joinP addRowP)

namespace VerifiableInference.Desc.Third.Law

/-- **The block drops nothing and writes no mark.** st: the reading of the statement. -/
def Keeps {S Cl : Type} (st : S → Statement) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → Carries (st s) (st s')

/-! ## Reading a course in Except back -/

theorem ok_of_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem some_of_named {α : Type} {n : String} {o : Option α} {x : α} (h : named n o = .ok x) :
    o = some x := by
  cases o with
  | none => cases h
  | some y => exact congrArg some (Except.ok.inj h)

/-! ## K14's second part -/

/-- The taking-over's yes, read back. -/
theorem takeOver_inv (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) :
    ∃ q t y a d₁, o.book.place[o.omega]? = some q ∧ o.book.trees[q.1]? = some t ∧
      o.st.oracles[o.omega]? = some y ∧
      adoptP d #[{ shape := y.shape, leafClass := S.omegaLeafClass }] #[(t.number, t.src)] =
        some a ∧
      a.1[0]? = some r.1 ∧ elsewhereP a.2 r.1 o.st o.omega = some d₁ ∧
      joinP d₁ own r.1 false = some r.2 := by
  unfold takeOver at h
  obtain ⟨q, hq, h⟩ := ok_of_bind h
  obtain ⟨t, ht, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨y, hy, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨mine, hm, h⟩ := ok_of_bind h
  obtain ⟨d₁, h1, h⟩ := ok_of_bind h
  obtain ⟨d₂, h2, h⟩ := ok_of_bind h
  have e : (mine, d₂) = r := Except.ok.inj h
  subst e
  exact ⟨q, t, y, a, d₁, some_of_named hq, some_of_named ht, some_of_named hy, some_of_named ha,
    some_of_named hm, some_of_named h1, some_of_named h2⟩

theorem true_of_need {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- **The taking-over's yes: Omega, in the shared chain's statement, has the plan's shape.** -/
theorem takeOver_shape (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) :
    ∃ y, o.st.oracles[o.omega]? = some y ∧ y.shape = S.omega := by
  unfold takeOver at h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨y, hy, h⟩ := ok_of_bind h
  obtain ⟨_, hs, _⟩ := ok_of_bind h
  exact ⟨y, some_of_named hy, of_decide_eq_true (true_of_need hs)⟩

theorem carries_takeOver (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃)
    (r : Nat × DState Loc₃) (h : takeOver S own o d = .ok r) : Carries d.st r.2.st := by
  obtain ⟨_, _, _, a, d₁, _, _, _, ha, _, h1, h2⟩ := takeOver_inv S own o d r h
  exact ((carries_adoptP _ _ _ _ ha).trans (carries_elsewhereP _ _ _ _ _ h1)).trans
    (carries_joinP _ _ _ _ _ h2)

/-- The block's yes, read back. -/
theorem k14Second_inv {Cl : Type} (p : P₁₄) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s') :
    ∃ x a dot b, s.loc.border = some x ∧ takeOver p.S s.loc.own x.shared (s.withCols []) = .ok a ∧
      linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
        (linLayW a.2.st.codes p.S) = some dot ∧
      addRowP a.2 s.loc.own dot = some b ∧
      s' = { st := b.st, book := b.book, roots := b.roots
             loc := { s.loc with border := none, omega := a.1 } } := by
  simp only [batchLinearConstraintsSecondPart] at h
  obtain ⟨x, hx, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨dot, hd, h⟩ := ok_of_bind h
  obtain ⟨b, hb, h⟩ := ok_of_bind h
  exact ⟨x, a, dot, b, some_of_named hx, ha, some_of_named hd, some_of_named hb,
    (Except.ok.inj h).symm⟩

/-- **K14's second part drops nothing and writes no mark.** -/
theorem keeps_k14Second {Cl : Type} (p : P₁₄) :
    Keeps (fun s : S₃ => s.st) (batchLinearConstraintsSecondPart (Cl := Cl) p) := by
  intro s rs gs s' h
  obtain ⟨x, a, dot, b, _, ha, _, hb, e⟩ := k14Second_inv p s s' rs gs h
  subst e
  exact (carries_takeOver _ _ _ _ _ ha).trans (carries_addRowP _ _ _ _ hb)

/-! ## The two blocks that tie the taken trees' sources -/

theorem takenSources_same {Cl : Type} (own : Block S₃ Cl) (s s' : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (takenSources own).decide s rs gs = .ok s') :
    s' = s := by
  simp only [takenSources, roundlessBlock] at h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  exact (Except.ok.inj h).symm

theorem keeps_takenSources {Cl : Type} (own : Block S₃ Cl) :
    Keeps (fun s : S₃ => s.st) (takenSources own) := by
  intro s rs gs s' h
  rw [takenSources_same own s s' rs gs h]
  exact Carries.refl _

end VerifiableInference.Desc.Third.Law

#print axioms VerifiableInference.Desc.Third.Law.takeOver_shape
#print axioms VerifiableInference.Desc.Third.Law.keeps_k14Second
#print axioms VerifiableInference.Desc.Third.Law.keeps_takenSources
