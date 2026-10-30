-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6PubSentences.lean: Law/K6PubMore.lean's sentences_behind WITH ITS PREMISE
ON THE INNERMOST MEANING's PUBLIC SENTENCES ASKED JUST WHERE THE PROOF SPENDS IT; AND THAT PREMISE
AT THE CLOSED MEANING BENEATH (Johnson/Desc/Sound/MgBase.lean: mgBase). Statements and proofs.

Why. sentences_behind asks "hPP : ∀ i x, Mg.pubP i x". At mgBase that is FALSE: there a public
sentence without a test holds just where the one written table gives "no sentence is meant"
(Johnson/Desc/First/AllSaid.lean: saysNone), and is False elsewhere. So a law that asks hPP so
widely is empty at mgBase.

  sentences_open        the same conclusion; hPP at the items that are open behind the sub-protocol
                        at the output head, but for "left" and "leftOn" (which have a sentence of
                        the lookup's, and none in that table).
  pubP_open342_mgBase   that premise holds at mgBase.
  pubP_open342_wide_false   without the two side conditions it is false there ("leftOn 24" is open
                        behind, and that table has no word on it).

WHAT IT IS NOT. sentences_open is an implication, with sentences_behind's other premises as they
were. pubP_open342_mgBase is a closed fact on a table. Nothing on soundness.
LETTERS. No letter stands under "there is" in a conclusion.

-/
import Johnson.Desc.Kinds.Law.K6PubMore
import Johnson.Desc.Sound.MgBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Meaning Pub pubOfItems)
open VerifiableInference.Desc.Sound (Piece Frame MsgT MgData mgAll mgBase onQ pubQ openQ linksFull)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) {Fr : Frame}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- What is open behind, by name. -/
theorem open342_mem (hMore : Mg.more = {}) {i : Pub}
    (hi : i ∈ pubQ (mgAll D Mg).more linksFull (First.flatPlacesOf linksFull true) (341 + 1)) :
    i ∈ [First.Pub.ledger 24, .linkFresh 24, .freeAbove 24,
      .more (some 24) "frame.sentIs", .more (some 24) "ledger.treesAre", .lookOut 24 3,
      .lookIn 24 8, .leftOn 24, .indexIs, .indexThere, .formsInT 24 3 "objects",
      .formsInT 24 4 "own", .formsInT 24 3 "planes", .formsInT 24 4 "join",
      .formsInT 24 4 "weights"] := by
  rw [Sound.mgAll_more_closed D Mg hMore] at hi
  exact open342 ▸ List.mem_append_left _ hi

/-- **EVERY PUBLIC SENTENCE THAT IS OPEN BEHIND THE SUB-PROTOCOL AT THE OUTPUT HEAD HOLDS THERE**:
the innermost meaning's sentences are asked at the open items alone, but for left and leftOn. -/
theorem sentences_open
    {q : Piece (_root_.Run.ckP .two) Fr (P × S) Claim (Wit (Fin rows → Fin cols → GE) Tok MsgT)}
    (H : Seated Wp .two Fr q 24 bef B bS) (hplan : planB Wp = true)
    (hMore : Mg.more = {})
    (hPP : ∀ i ∈ pubQ (mgAll D Mg).more linksFull (First.flatPlacesOf linksFull true) (341 + 1),
      (∀ m, i ≠ .left m) → (∀ m, i ≠ .leftOn m) → ∀ x, Mg.pubP i x)
    (a b : (P × S) × Fr.E.Str) (τ : Iop.Tr (uLT (_root_.Run.ckP .two) q.ds))
    (ha : onQ (Fr := Fr) D.N (mgAll D Mg) linksFull (First.flatPlacesOf linksFull true)
      (fun a => a) 341 a)
    (hm : a.1.2.failed = none) (hb : q.ior.red.out a τ = some b) (hL : K6Left Wp a.1.2) :
    ∀ i ∈ pubQ (mgAll D Mg).more linksFull (First.flatPlacesOf linksFull true) (341 + 1),
      (mgAll D Mg).pubP i b.1 := by
  intro i hi
  have A := Sound.onParts_of_on D.N (mgAll D Mg) linksFull _ (fun a => a) 341 a ha hm
  have hi' := open342_mem D Mg hMore hi
  have other : ∀ j : Pub,
      j ∈ pubQ (mgAll D Mg).more linksFull (First.flatPlacesOf linksFull true) (341 + 1) →
      (∀ m, j ≠ .left m) → (∀ m, j ≠ .leftOn m) → (mgAll D Mg).pubP j b.1 := by
    intro j hj h1 h2
    rw [Sound.mgAll_pubP, First.Look.fill_pubP_other _ _ _ j b.1 h1 h2]
    show if First.FillP1.p1Item j = true then True else Mg.pubP j b.1
    split
    · trivial
    · exact hPP j hj h1 h2 b.1
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inl =>
    have hleft : (mgAll D Mg).pubP (.left 24) a.1 := A.pubP _ (by
      rw [Sound.mgAll_more_closed D Mg hMore]
      decide +kernel)
    rw [Sound.mgAll_pubP] at hleft ⊢
    obtain ⟨p, hp, Lf⟩ : VerifiableInference.OnPublicFiles.k3LeftItemAt Wp 24 a.1.2 := hleft
    obtain ⟨b6, rs, gs, h6, hd⟩ := below_yes_seated H a b τ hb
    exact ⟨p, hp, leftOn_below Wp 24 b6 h6 a.1.2 b.1.2 rs gs hd (k6On_front H hplan a b τ hb hL) p
      Lf⟩
  all_goals exact other _ hi (fun _ => by simp) (fun _ => by simp)

/-- **THE PREMISE HOLDS AT THE CLOSED MEANING BENEATH.** -/
theorem pubP_open342_mgBase :
    ∀ i ∈ pubQ (mgAll D mgBase).more linksFull (First.flatPlacesOf linksFull true) (341 + 1),
      (∀ m, i ≠ .left m) → (∀ m, i ≠ .leftOn m) → ∀ x : P × S,
        (mgBase : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)).pubP i x := by
  intro i hi _ h2 x
  have hi' := open342_mem D mgBase rfl hi
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
  rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl
  case inr.inr.inr.inr.inr.inr.inr.inl => exact absurd rfl (h2 24)
  all_goals
    show (First.saysNone _).isSome = true
    decide

/-- "leftOn 24" is among the items that are open behind. -/
theorem leftOn_open342 : First.Pub.leftOn 24 ∈
    pubQ Sound.mgMore linksFull (First.flatPlacesOf linksFull true) (341 + 1) := by
  decide +kernel

/-- **WITHOUT THE TWO SIDE CONDITIONS THE PREMISE IS FALSE AT THE CLOSED MEANING BENEATH**: at
"leftOn 24" the written table (Johnson/Desc/First/AllSaid.lean) has no word. -/
theorem pubP_open342_wide_false (x : P × S) :
    ¬ ∀ i ∈ pubQ (mgAll D mgBase).more linksFull (First.flatPlacesOf linksFull true) (341 + 1),
      ∀ x : P × S, (mgBase : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)).pubP i x := by
  intro h
  have k := h (.leftOn 24) (by rw [Sound.mgAll_more_base]; exact leftOn_open342) x
  have k' : (First.saysNone (.leftOn 24)).isSome = true := k
  exact absurd k' (by decide)

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubP_open342_wide_false
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.sentences_open
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.pubP_open342_mgBase
