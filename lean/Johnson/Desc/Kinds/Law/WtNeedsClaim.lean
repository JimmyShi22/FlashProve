-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/WtNeedsClaim.lean: THE MERGE'S FILES' SENTENCE ON THE CLAIM ON THE WEIGHTS
(Johnson/Top/H0/Fill/FillP1.lean: wtP1) IS FALSE AT EVERY STATE OF THE VERIFIER IN WHICH NO CLAIM ON
THE COMMITTED TABLE IS LAID; AND THE SUB-PROTOCOL AT THE OUTPUT HEAD LAYS NONE.

Why. By the table of joints the item on the run "weights" is open from the border behind that
sub-protocol (piece 4 of the head's segment) to the border in front of the merge (piece 9). The
field claim of the head's own part starts as none (Johnson/Desc/First/State.lean) and, by reading,
is laid by one step alone: the quiet step behind the lookup on the digits, piece 8
(Johnson/Desc/First/Look/K3Whole.lean: quietHead). So a sentence that reads that field cannot be
carried back past piece 8.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  wtP1_needs_claim: wtP1 at a state gives a laid claim there (from wtP1_plain).
  wtP1_false: so where the head's own part holds no claim, wtP1 is false of every witness.
  claim_behind: an accepting step of the piece at the output head leaves that field.
  wtP1_false_behind: SO: no claim in front, wtP1 false behind, of every witness.

Every letter under "there is": wtP1_needs_claim: hd (pinned by the state), claim (by hd).
What it does not say. THAT NO CLAIM IS LAID IN FRONT OF THE SUB-PROTOCOL AT A REACHED STATE: a
premise here (by reading: the field's default, and one setter). Nothing on the pieces 5 to 8.
Nothing on soundness.
-/
import Johnson.Top.H0.Fill.WtPlain
import Johnson.Desc.Sound.K6Tied

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.First.FillP1 (wtP1 wtP1_plain)
open VerifiableInference.Desc.Sound (Piece Frame MsgT)
open Johnson.Desc.First.ForkMerge (HeadMergeP)

/-- **The sentence gives a laid claim.** -/
theorem wtP1_needs_claim {P W : Type} (Pm : HeadMergeP) (ni : ℕ) (cellOf : W → ℕ → ℕ → Cb.Gl.E)
    (maskOf : P × S → W → ℕ → Cb.Gl.E) (a : P × S) (y : Strs) (w : W)
    (h : wtP1 Pm ni cellOf maskOf a y w) :
    ∃ (hd : HeadOwn) (claim : OnBytes.Model.WsClaim), a.2.here = .head hd ∧
      hd.claim = some claim := by
  obtain ⟨_, _, _, _, hd, claim, _, _, e1, e2, _⟩ := wtP1_plain Pm ni cellOf maskOf a y w h
  exact ⟨hd, claim, e1, e2⟩

/-- **Where no claim is laid the sentence is false.** -/
theorem wtP1_false {P W : Type} (Pm : HeadMergeP) (ni : ℕ) (cellOf : W → ℕ → ℕ → Cb.Gl.E)
    (maskOf : P × S → W → ℕ → Cb.Gl.E) (a : P × S) (y : Strs) (w : W) (hd : HeadOwn)
    (e : a.2.here = .head hd) (hn : hd.claim = none) : ¬ wtP1 Pm ni cellOf maskOf a y w := by
  intro h
  obtain ⟨hd', claim, e1, e2⟩ := wtP1_needs_claim Pm ni cellOf maskOf a y w h
  rw [e] at e1
  obtain rfl := First.Here.head.inj e1
  rw [hn] at e2
  cases e2

variable {P Cells Tok : Type} {Wp : OnBytes.Model.Verify.Public} {fld : Fmt.Fld} {Fr : Frame}
  {q : Piece (_root_.Run.ckP fld) Fr (P × S) Claim (Wit Cells Tok MsgT)} {l : ℕ}
  {bef : List (ℕ × ℕ)} {B bS : Block S Claim}

/-- **An accepting step at the output head leaves the field.** -/
theorem claim_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b) :
    ∃ o o' : HeadOwn, a.1.2.here = .head o ∧ b.1.2.here = .head o' ∧ o'.claim = o.claim := by
  obtain ⟨o, F1, X, Q, ho, _, _, e⟩ := k6_behind H a b τ h
  exact ⟨o, { o with F := F1, x := some X, squaresP := some Q }, ho, by rw [e], rfl⟩

/-- **No claim in front: the sentence is false behind, of every witness.** -/
theorem wtP1_false_behind (H : Seated Wp fld Fr q l bef B bS) (a b : (P × S) × Fr.E.Str)
    (τ : Iop.Tr (uLT (_root_.Run.ckP fld) q.ds)) (h : q.ior.red.out a τ = some b)
    (hn : ∀ o, a.1.2.here = .head o → o.claim = none) (Pm : HeadMergeP) (ni : ℕ)
    (cellOf : Wit Cells Tok MsgT → ℕ → ℕ → Cb.Gl.E)
    (maskOf : P × S → Wit Cells Tok MsgT → ℕ → Cb.Gl.E) (y : Strs) (w : Wit Cells Tok MsgT) :
    ¬ wtP1 Pm ni cellOf maskOf b.1 y w := by
  obtain ⟨o, o', e1, e2, e3⟩ := claim_behind H a b τ h
  exact wtP1_false Pm ni cellOf maskOf b.1 y w o' e2 (e3.trans (hn o e1))

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtP1_needs_claim
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtP1_false
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.claim_behind
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.wtP1_false_behind
