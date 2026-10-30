-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Prod/FamL.lean: from a judge on prefixes to the library's family of bad sets
(Iop/Rbr.lean: BadFam, BadFam.Clean, BadFam.Within), for every shape. The generic half of what
turns a law of the form "there are bad sets with these bounds; where no bad element was drawn ..."
into round-by-round soundness with an error for each round. No text of a verifier is named.
Definitions, statements and proofs.

X: what a law reads of a round. `Enc X s`: for each round of the shape s, how its message and its
challenge are read as an X. `trL`: a transcript as the list of its rounds' readings. `J pre x`, the
judge: the round read as x, behind the rounds read as pre, has drawn a bad value. `famL J s es
pre`: the family of bad sets: in each round, the challenges c at which J says so of the rounds so
far and this round with c. It is a BadFam: so each set is fixed in front of its challenge by type:
it may read the earlier rounds and this round's message. `famL_clean`: a transcript is clean
exactly if J holds at none of its rounds, each judged behind the rounds in front of it.
`famL_within`: if at round i, for every prefix and message, at most e i challenges are judged bad,
the family is within the errors (errL e). `cnt_mem_le`: where a count of bad elements becomes a
count of challenges: if the challenges are read one-to-one into K, at most S.card of them are read
into S. `doomed_of_judge`: so, by doomed_of_clean: if "lost" holds of every transcript at none of
whose rounds J holds, the empty transcript is Doomed with these errors.

Limits. The prefix goes round by round: a round that draws several elements has the tuple as its
one challenge (the count for such a round: Johnson/Desc/First/Prod/FamTuple.lean). No judge of a
kind is given here. The errors are counts of challenge values for each round, as Doomed's are.
Not claimed: the soundness of any verifier; any probability.

-/
import Iop.Rbr
import Mathlib.Data.Finset.Card
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Prod
open Iop Prob

/-- For each round of the shape: its message and challenge, read as an X. -/
def Enc (X : Type) : Shape → Type
  | [] => Unit
  | r :: s => (r.Msg → r.Chal → X) × Enc X s

/-- A transcript as the list of its rounds' readings. -/
def trL {X : Type} : {s : Shape} → Enc X s → Tr s → List X
  | [], _, _ => []
  | _ :: _, (e, es), (m, c, τ) => e m c :: trL es τ

/-- The family of bad sets of a judge, behind the rounds read as pre. -/
def famL {X : Type} (J : List X → X → Prop) : (s : Shape) → Enc X s → List X → BadFam s
  | [], _, _ => ()
  | _ :: s, (e, es), pre =>
    (fun m => {c | J pre (e m c)}, fun m c => famL J s es (pre ++ [e m c]))

/-- The errors, from a function of the round's number. -/
def errL (e : ℕ → ℕ) : (s : Shape) → ℕ → Err s
  | [], _ => ()
  | _ :: s, i => (e i, errL e s (i + 1))

/-- **Clean: no round is judged bad, each behind the rounds in front of it.** -/
theorem famL_clean {X : Type} (J : List X → X → Prop) :
    ∀ (s : Shape) (es : Enc X s) (pre : List X) (τ : Tr s),
      (famL J s es pre).Clean τ ↔
        ∀ i x, (trL es τ)[i]? = some x → ¬ J (pre ++ (trL es τ).take i) x
  | [], _, _, _ => ⟨fun _ i x h => by
      have h' : ([] : List X)[i]? = some x := h
      simp at h', fun _ => trivial⟩
  | _ :: s, (e, es), pre, (m, c, τ) => by
    have ih := famL_clean J s es (pre ++ [e m c]) τ
    show (¬ J pre (e m c) ∧ (famL J s es (pre ++ [e m c])).Clean τ) ↔
      ∀ i x, (e m c :: trL es τ)[i]? = some x → ¬ J (pre ++ (e m c :: trL es τ).take i) x
    rw [ih]
    constructor
    · rintro ⟨h0, h1⟩ i x hx
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
        subst hx
        simpa using h0
      | succ i =>
        simp only [List.getElem?_cons_succ] at hx
        have := h1 i x hx
        simpa [List.take_succ_cons, List.append_assoc] using this
    · intro h
      refine ⟨by simpa using h 0 (e m c) rfl, fun i x hx => ?_⟩
      have := h (i + 1) x (by simpa using hx)
      simpa [List.take_succ_cons, List.append_assoc] using this

/-- What "at most e i challenges are judged bad at round i" says, round by round. -/
def BoundL {X : Type} (J : List X → X → Prop) (e : ℕ → ℕ) : (s : Shape) → Enc X s → ℕ → Prop
  | [], _, _ => True
  | r :: s, (en, es), i =>
    (∀ (pre : List X) (m : r.Msg), pre.length = i → cnt (fun c : r.Chal => J pre (en m c)) ≤ e i) ∧
      BoundL J e s es (i + 1)

/-- **Within the errors.** -/
theorem famL_within {X : Type} (J : List X → X → Prop) (e : ℕ → ℕ) :
    ∀ (s : Shape) (es : Enc X s) (pre : List X), BoundL J e s es pre.length →
      (famL J s es pre).Within (errL e s pre.length)
  | [], _, _, _ => trivial
  | _ :: s, (en, es), pre, h => by
    refine ⟨fun m => h.1 pre m rfl, fun m c => ?_⟩
    have := famL_within J e s es (pre ++ [en m c]) (by
      rw [List.length_append]
      exact h.2)
    rw [List.length_append] at this
    exact this

/-- **From bad elements of K to bad challenges.** -/
theorem cnt_mem_le {α K : Type} [Finite α] (val : α → K) (hinj : Function.Injective val)
    (S : Finset K) : cnt (fun c : α => val c ∈ S) ≤ S.card := by
  have h : Nat.card {c : α // val c ∈ S} ≤ Nat.card {y : K // y ∈ S} :=
    Nat.card_le_card_of_injective
      (fun x : {c : α // val c ∈ S} => (⟨val x.1, x.2⟩ : {y : K // y ∈ S}))
      (fun a b hab => Subtype.ext (hinj (congrArg (fun y : {y : K // y ∈ S} => y.1) hab)))
  have h2 : Nat.card {y : K // y ∈ S} = S.card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  show Nat.card {c : α // val c ∈ S} ≤ S.card
  rw [← h2]
  exact h

/-- **Round-by-round soundness from a judge**, by the library's doomed_of_clean. -/
theorem doomed_of_judge {X : Type} (J : List X → X → Prop) (e : ℕ → ℕ) (s : Shape) (es : Enc X s)
    (lost : Tr s → Prop) (hb : BoundL J e s es 0)
    (h : ∀ τ, (∀ i x, (trL es τ)[i]? = some x → ¬ J ((trL es τ).take i) x) → lost τ) :
    Doomed s (errL e s 0) lost :=
  doomed_of_clean s (errL e s 0) (famL J s es []) lost (famL_within J e s es [] hb) fun τ hτ =>
    h τ fun i x hx => by
      have := (famL_clean J s es [] τ).1 hτ i x hx
      simpa using this

end VerifiableInference.Desc.First.Prod

#print axioms VerifiableInference.Desc.First.Prod.doomed_of_judge
#print axioms VerifiableInference.Desc.First.Prod.cnt_mem_le
