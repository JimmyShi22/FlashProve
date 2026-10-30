-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- No soundness is claimed.
/-
Johnson/Flat/Last/RowTwoOwn.lean: THE LAST CHAIN, BLOCK 2 (the proximity test on the request's own group): ITS CLAUSE OF `EachOwn` AT THE TABLE OF THE LAST
CHAIN's JOINTS (Johnson/Desc/Last/BordersLast.lean · Johnson/Desc/Sound/BordersLastQ.lean), FROM THE KIND's LAW IN THE PLAIN FORM AND THREE NAMED
FACTS. A rule: general in the piece and in every letter of the table.

Why. The table's row 2 closes ALL that is open: the rows of the own group and the three pins (W's, the index masks', Omega's). The kind's files state its law
in the plain form: under a promise `onK` the prover has lost towards "where the piece says yes: `QK` of the statement in front". This file says what lies between.
  `openTwo`: what is open at border 2 is just what row 2 closes (by evaluation of the table).
  `frames_rowTwo`: so nothing rides past block 2: `Piece.Frames` holds for nothing.
  `own_rowTwo`: `Piece.Own` at row 2 FROM
    law      the kind's law at this piece: `p.ior.red.Leads onK (fun a _ => QK a) p.err`;
    prom     the table's promise at border 2 gives the law's promise;
    behind   under the table's promise at border 2 the piece's yes gives the table's promise at border 3;
    carry    **THE CARRIAGE**: under the table's promise at border 2, where `QK` holds of the statement in front, the piece's extractor gives, of every
             witness and at every transcript, a witness at which the four items hold.
  `rowTwo`: both, as `EachOwn` asks them at k = 2.
Limits. A JOINING: NOTHING IS PAID: `law` is left to the kind's files, unproved; `carry` holds all of the semantic weight (from "one witness near the group's word at
which every pending row holds" to "the rows hold of the witness's messages, and each member's message is what its word decodes to with its sample") and is
not typed at any filling of the table's letters. Nothing on soundness.
-/
import Johnson.Desc.Sound.BordersLastQProofs
import Johnson.Desc.Plain.Leads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Last
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open _root_.Iop (Doomed)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last

/-- What is open at border 2 is what row 2 closes. -/
theorem openTwo (i : ItemL) : openAfter insQ₃ outsQ₃ (· ∈ startLast) 2 i → insQ₃ 2 i := by
  intro h
  have h' := (openIsList ItemL insL₃ outsL₃ startLast 2 i).1 h
  have e : openL insL₃ outsL₃ startLast 2 = [.pinI, .pinV, .pinO, .rows] := by decide
  rw [e] at h'
  show i ∈ insL₃ 2
  have e' : insL₃ 2 = [.rows, .pinV, .pinI, .pinO] := by decide
  rw [e']
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h' ⊢
  rcases h' with rfl | rfl | rfl | rfl <;> simp

section
variable {P S₁ S₂ S₃ Cl Wt : Type} {C : CK} {Fr : Frame} (N : NumbersS)
  (Mg : MeaningS S₂ (P × S₁) Wt) (ML : MeaningL S₃ Wt) (Pm : PromMeaning S₂)
  (PL : PromMeaningL S₂ S₃ (P × S₁)) (Oc : P × S₁ → Strs → Prop)
  (p : Piece C Fr ((P × S₁ × S₂) × S₃) Cl Wt)

/-- Nothing rides past block 2. -/
theorem frames_rowTwo :
    p.Frames (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML)
      (openAfter insQ₃ outsQ₃ (· ∈ startLast) 2) (insQ₃ 2) :=
  fun _ _ _ _ i _ _ _ ho hn _ => absurd (openTwo i ho) hn

/-- **Row 2's own law, from the kind's law in the plain form and three named facts.** -/
theorem own_rowTwo (onK QK : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop)
    (law : p.ior.red.Leads onK (fun a _ => QK a) p.err)
    (prom : ∀ a, onQ₃ N Mg Pm PL Oc 2 a → onK a)
    (behind : ∀ a τ b, onQ₃ N Mg Pm PL Oc 2 a → p.ior.red.out a τ = some b → onQ₃ N Mg Pm PL Oc 3 b)
    (carry : ∀ a, onQ₃ N Mg Pm PL Oc 2 a → QK a → ∀ τ w i, insQ₃ 2 i →
      meansQ₃ N Mg ML i a (p.ext a τ w)) :
    p.Own (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML) (insQ₃ 2) (outsQ₃ 2) :=
  fun a ha => Doomed.mono _ _
    (fun τ hτ b hb => ⟨behind a τ b ha hb, fun w _ i hi => carry a ha (hτ b hb) τ w i hi⟩)
    (law a (prom a ha))

/-- Both, as `EachOwn` asks them at k = 2. -/
theorem rowTwo (onK QK : ((P × S₁ × S₂) × S₃) × Fr.E.Str → Prop)
    (law : p.ior.red.Leads onK (fun a _ => QK a) p.err)
    (prom : ∀ a, onQ₃ N Mg Pm PL Oc 2 a → onK a)
    (behind : ∀ a τ b, onQ₃ N Mg Pm PL Oc 2 a → p.ior.red.out a τ = some b → onQ₃ N Mg Pm PL Oc 3 b)
    (carry : ∀ a, onQ₃ N Mg Pm PL Oc 2 a → QK a → ∀ τ w i, insQ₃ 2 i →
      meansQ₃ N Mg ML i a (p.ext a τ w)) :
    p.Own (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML) (insQ₃ 2) (outsQ₃ 2) ∧
      p.Frames (onQ₃ N Mg Pm PL Oc 2) (onQ₃ N Mg Pm PL Oc 3) (meansQ₃ N Mg ML)
        (openAfter insQ₃ outsQ₃ (· ∈ startLast) 2) (insQ₃ 2) :=
  ⟨own_rowTwo N Mg ML Pm PL Oc p onK QK law prom behind carry, frames_rowTwo N Mg ML Pm PL Oc p⟩

end

end VerifiableInference.OnPublicFiles.Last

#print axioms VerifiableInference.OnPublicFiles.Last.openTwo
#print axioms VerifiableInference.OnPublicFiles.Last.rowTwo
