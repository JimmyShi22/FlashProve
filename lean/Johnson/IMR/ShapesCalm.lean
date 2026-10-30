-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/ShapesCalm.lean (kind-free): FoldFacts' FIELD "K12.msgShapes": WHERE THE DEBT ON
THE BOOK (SendsOn, Johnson/IMR/SendsFold.lean) IS PAID AT THE EMPTY LIST OF SENDINGS, THE DEBT ON
THE SHAPES
(ShapesOn, Johnson/IMR/ShapesFold.lean) IS PAID TOO, if the sub-protocol's accepting decisions let
the
statement grow. Theorems, proved.

Compiled with the whole library.

  places_of_nil   an empty appending leaves the number of the book's places.
  reached_step   at every state that the fold reaches: the statement has as many oracle messages as
    the book has places, and the code table is the first state's: off the debts on the book
    (sends_alongR).
  shapes_of_sends   THE RULE: SendsOn ft codes G [] b; at the states of G: in step, and the code
    table; every accepting decision of b lets the statement grow (Grows, Johnson/Desc/Grows.lean):
    then ShapesOn ft G [] b. So no sub-protocol that sends nothing is walked a second time for the
    shapes.
  shapes_around_sent   for whoever pays a sender's debt: steps that let the statement grow and leave
    the number of its messages, one prover's message (stSent), and such steps again: that message's
    notices' shapes are appended.

OBJECT: SendsOn, ShapesOn. USER: Johnson/IMR/ShapesJoin.lean. LETTERS: all free.

What is not claimed. SendsOn, or "grows", at any sub-protocol. No soundness.
-/
import Johnson.IMR.ShapesFold

set_option autoImplicit false

namespace IM

open OnBytes (Codes OracleNotice TreeBook)
open VerifiableInference.Desc (Block foldBlocks OpenedColumn Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Coin (Appends laidFrom)
open ProofFile (Cl)

/-- An empty appending leaves the number of the book's places. -/
theorem places_of_nil {codes : Codes} {B B' : TreeBook} (h : Appends codes [] B B') :
    B'.place.size = B.place.size := by
  obtain ⟨A, hA, ep, -⟩ := h
  have hA' : (some {} : Option VerifiableInference.Desc.K12.Coin.Laid) = some A := hA
  obtain rfl := Option.some.inj hA'
  have := congrArg List.length ep
  simpa using this

/-- **At every state that the fold reaches**: in step, and the code table is the first state's:
off the debts on the book. -/
theorem reached_step {ft : ℕ} {codes : Codes} {sn : ℕ → List (Array OracleNotice)}
    {bs : List (Block S Cl)} {s₀ : S}
    (h : ∀ j b, bs[j]? = some b → SendsOn ft codes (ReachedAt ft bs s₀ j) (sn j) b)
    (hc : s₀.st.codes = codes) (hi : InStep s₀) {j : ℕ} (hj : j ≤ bs.length) {s : S}
    (hr : ReachedAt ft bs s₀ j s) : InStep s ∧ s.st.codes = codes := by
  obtain ⟨rs, cols, r, hf, rfl⟩ := hr
  obtain ⟨c1, -, i1⟩ := sends_alongR h hc j hj rs cols r hf
  exact ⟨i1 hi, c1⟩

/-- **WHERE THE DEBT ON THE BOOK IS PAID AT THE EMPTY LIST, THE DEBT ON THE SHAPES IS PAID TOO**, if
the sub-protocol's accepting decisions let the statement grow. -/
theorem shapes_of_sends {ft : ℕ} {codes : Codes} {G : S → Prop} {b : Block S Cl}
    (h : SendsOn ft codes G [] b) (hG : ∀ s, G s → InStep s ∧ s.st.codes = codes)
    (hg : ∀ s rs gs s', b.decide s rs gs = .ok s' → Grows s.st s'.st) : ShapesOn ft G [] b := by
  intro s s' rs cols n hs hy
  obtain ⟨i0, c0⟩ := hG s hs
  obtain ⟨-, a1, i1⟩ := h s s' rs cols n hs hy c0
  obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft b s s' rs cols n hy
  have e : s'.st.oracles.size = s.st.oracles.size := by
    have h1 : s'.st.oracles.size = s'.book.place.size := i1 i0
    have h0 : s.st.oracles.size = s.book.place.size := i0
    rw [h1, h0, places_of_nil a1]
  rw [stay_of_grows (hg s _ _ s' hd) e, noticesOf_nil, List.append_nil]

/-! ## For whoever pays a sender's debt -/

/-- **One prover's message, with steps around it that let the statement grow and leave the number of
its oracle messages**: the shapes of that message's notices are appended, and no shape is turned. -/
theorem shapes_around_sent {T T₀ T' : OnBytes.Statement} {sent : Array OracleNotice}
    (g0 : Grows T T₀) (n0 : T₀.oracles.size = T.oracles.size)
    (g1 : Grows (OnBytes.Slice.stSent T₀ sent) T')
    (n1 : T'.oracles.size = (OnBytes.Slice.stSent T₀ sent).oracles.size) :
    shapesOf T' = shapesOf T ++ noticesOf [sent] := by
  rw [stay_of_grows g1 n1, shapes_of_sent, stay_of_grows g0 n0]

end IM

#print axioms IM.shapes_around_sent
#print axioms IM.places_of_nil
#print axioms IM.reached_step
#print axioms IM.shapes_of_sends
