-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LeadsQ.lean: AT THE TABLE OF JOINTS: THE TABLE'S ONE EXTRACTOR, WITH A FRAME FACT
ON THE REPLY AT EVERY BLOCK, PAYS WHAT THE PLAIN FORM'S LIST ASKS (`EachE` with `TokStep`,
Johnson/Desc/Sound/LeadsE.lean). Two definitions and three theorems; no probability in it.

Main names:
  `extQAt_tok`: the token of what the table's extractor gives: at the row that lays it (`laysTok`:
    the block that hears the reply) the token read off the record BEHIND (`tokOf`); at every other
    row the witness's own.
  `RepFact`: **THE FRAME FACT ON THE REPLY, BY SORT OF ROW**: at the row that lays the token: no
    reply is heard in front, and behind the record holds what `tokOf` reads; AT EVERY OTHER ROW THE
    EQUATION: the record's reply is not turned (both ways: "what was heard stays" alone is too
    little). `EachRep`: every block of a row has it, wherever it says
    yes inside its promise.
  `tokStep_of_repFact`: the frame fact gives `TokStep` at the table's extractor. **`eachE_of_extQ`:
    `EachExtQ` (every piece has the table's extractor) and `EachRep` give `EachE`**: so `eachLeadsE`
    feeds the plain form's first chain from `EachGoodIn`, and `steps_token` follows the token.

f: from the witness's type of tokens to the type in which the reply is read: the integer model's
reading of a witness goes through such a map.

Silly members. At rep := "nothing is ever heard" `RepFact` fails at the row that lays the token. At
a list of places without such a row every step keeps the token, and `steps_token`'s premise "a reply
is heard at the end, none at the start" cannot be met.

Limits: `EachRep` IS SHOWN OF NO ROW HERE: it is a fact on each block's own text: for the lookup's
own block at its two seats: Johnson/Desc/First/Look/K3ReplyLeaves.lean; for the block that hears the
reply and for all others: their kinds' files' to show. `EachExtQ` is by the make of the pieces.
Nothing on soundness of its own; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersFill
import Johnson.Desc.Sound.LeadsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers laysSeats laysTok)

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok)
  {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place)
  (get : A → P × First.S) {Tok' : Type} (f : Tok → Tok') (rep : A × Fr.E.Str → Option Tok')

/-- The token of what the table's extractor gives: at the row that lays it, the token read off the
record behind; at every other row the witness's own. -/
theorem extQAt_tok (k : ℕ) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    (extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w).tok =
      match ps[k]? with
      | some p => if laysTok links p then tokOf (get b.1) else w.tok
      | none => w.tok := by
  unfold extQAt
  cases ps[k]? with
  | none => rfl
  | some p =>
    show (extQ cs G arr smp ms decT c₀ tokOf N links p (get a.1) (strsOf Fr a.2)
      (some (get b.1)) w).tok = _
    unfold extQ extAt
    by_cases h : laysTok links p = true
    · simp [h]
    · simp [h]

/-- **THE FRAME FACT ON THE REPLY, BY SORT OF ROW.** rep: the reply that a statement's record holds,
if one was heard. At the row that lays the token: none is heard in front, and behind the record
holds what `tokOf` reads (f: from the witness's type of tokens to the reply's). AT EVERY OTHER ROW:
THE EQUATION: the record's reply is not turned. -/
def RepFact (k : ℕ) (a b : A × Fr.E.Str) : Prop :=
  match ps[k]? with
  | some p =>
    if laysTok links p then rep a = none ∧ rep b = some (f (tokOf (get b.1))) else rep b = rep a
  | none => rep b = rep a

/-- **The frame fact gives what is sure of a step on the reply, at the table's extractor.** -/
theorem tokStep_of_repFact (k : ℕ) (a b : A × Fr.E.Str)
    (h : RepFact tokOf links ps get f rep k a b) :
    TokStep (extQAt cs G arr smp ms decT c₀ tokOf N links ps get) (fun w => f w.tok) rep k a b := by
  unfold RepFact at h
  refine ⟨fun hb w => ?_, fun ha t hb w => ?_, fun t ha => ?_⟩
  · show f (extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w).tok = f w.tok
    rw [extQAt_tok]
    cases hp : ps[k]? with
    | none => rfl
    | some p =>
      rw [hp] at h
      by_cases hl : laysTok links p = true
      · simp only [hl, if_true] at h
        rw [h.2] at hb
        cases hb
      · simp [hl]
  · show f (extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w).tok = t
    rw [extQAt_tok]
    cases hp : ps[k]? with
    | none =>
      rw [hp] at h
      rw [h, ha] at hb
      cases hb
    | some p =>
      rw [hp] at h
      by_cases hl : laysTok links p = true
      · simp only [hl, if_true] at h ⊢
        exact Option.some.inj (h.2.symm.trans hb)
      · simp only [hl, Bool.false_eq_true, if_false] at h
        rw [h, ha] at hb
        cases hb
  · cases hp : ps[k]? with
    | none =>
      rw [hp] at h
      rw [h, ha]
    | some p =>
      rw [hp] at h
      by_cases hl : laysTok links p = true
      · simp only [hl, if_true] at h
        rw [h.1] at ha
        cases ha
      · simp only [hl, Bool.false_eq_true, if_false] at h
        rw [h, ha]

variable {Cl : Type} {C : CK} (on : ℕ → A × Fr.E.Str → Prop)

/-- Every block of a row has the frame fact, wherever it says yes inside its promise. -/
def EachRep : ℕ → List (Piece C Fr A Cl (Wit Cells Tok MsgT)) → Prop
  | _, [] => True
  | k, q :: l =>
    (∀ a τ b, on k a → q.ior.red.out a τ = some b → RepFact tokOf links ps get f rep k a b) ∧
      EachRep (k + 1) l

/-- **AT THE TABLE: every piece has the table's extractor, and every block the frame fact on the
reply: then the row has `EachE`** at the table's extractor and `TokStep`: what `eachLeadsE` and
`steps_token` ask. -/
theorem eachE_of_extQ : ∀ (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ),
    EachExtQ cs G arr smp ms decT c₀ tokOf N links ps get k l →
    EachRep tokOf links ps get f rep on k l →
    EachE on (extQAt cs G arr smp ms decT c₀ tokOf N links ps get)
      (TokStep (extQAt cs G arr smp ms decT c₀ tokOf N links ps get) (fun w => f w.tok) rep) k l
  | [], _, _, _ => trivial
  | _ :: l, k, h, r =>
    ⟨h.1, fun a τ b ha hb =>
      tokStep_of_repFact cs G arr smp ms decT c₀ tokOf N links ps get f rep k a b
        (r.1 a τ b ha hb),
      eachE_of_extQ l (k + 1) h.2 r.2⟩

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extQAt_tok
#print axioms VerifiableInference.Desc.Sound.tokStep_of_repFact
#print axioms VerifiableInference.Desc.Sound.eachE_of_extQ
