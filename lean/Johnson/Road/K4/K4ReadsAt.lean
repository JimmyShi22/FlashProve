-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4ReadsAt.lean: THREE OF THE SEVEN LINES OF THE STRUCTURE K4Reads
(Johnson/Road/K4/K4Reads.lean: what the owners' letters read of the verifier's state, from a state
in a layers' link to the state where the sub-protocol K4 has accepted), EACH AS A THEOREM AT THE
TERM THAT IS MEANT FOR ITS LETTER, general in that term's own letters; AND A FOURTH, req, AT A FORM
OF ITS LETTER, NOT AT A TERM. Statements and proofs.

  **`smp_at`**: the line smp at the named reader of samples, smpNamed cs seats
    (Johnson/Desc/Sound/SmpNamed.lean), at every list of seats: it reads the field st alone
    (smpNamed_same).
  **`stMask_at`**: the line stMask at Stated.of u (Johnson/Desc/Sound/FormsT.lean), at every u: its
    mask row is the data's own: by unfolding.
  **`base_at`**: the line base at the test that always accepts.
  **`req_at`**: the line req wherever the letter's field req reads the public part and the state's
    field req alone.
No new argument.
**Limits.** EACH UNDER AN EQUATION ON THE DATA D ("the letter is that term"): A PREMISE: whoever
composes the meaning pays it. req: THE TERM THAT IS MEANT, hidAtPlan (Johnson/P5J/HidAtPlan.lean:
read, not imported), TAKES ITS FIELD req AS A LETTER OF ITS OWN: so the line falls only where that
letter is of the form asked here: no term is named for it yet. THREE LINES ARE NOT HERE: rw: at the
reader through the state's own book it holds of Rest (rwBook_rest, Johnson/Road/K4/RwBookRest.lean);
the file that states the line itself at the composed meaning's own data,
Johnson/Road/K4/K4ReadsAtMgAll.lean, is not in this library;
decT and head: no term of theirs has passed Lean yet. Nothing on soundness. K04_law, the law of the
sub-protocol K4 itself, IS NOT PROVED.


-/
import Johnson.Road.K4.K4Reads
import Johnson.Desc.Sound.FormsT
import Johnson.Desc.Sound.SmpNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (MsgT GQ Stated smpNamed smpNamed_same)

variable {Xi P Tok : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {D : K4Data Xi P Tok rows cols nR kC X} (Z : P)

/-- **The line smp**, where the letter is the named reader of samples. -/
theorem smp_at {seats : List (ℕ × ℕ)} (hD : D.smp = smpNamed D.cs seats) :
    ∀ s s', LayRest s s' → ∀ sd i, D.smp (Z, s') sd i = D.smp (Z, s) sd i := by
  intro s s' h sd i
  rw [hD]
  exact smpNamed_same D.cs seats (Z, s) (Z, s') h.2.st sd i

/-- **The line stMask**, where the letter is Stated.of u. -/
theorem stMask_at {u : S → Bound GQ → ℕ × String → ℕ → ℕ → GQ} (hD : D.St = Stated.of u) :
    ∀ s s', LayRest s s' → ∀ B j, (D.St.at1 s' B).mask j = (D.St.at1 s B).mask j := by
  intro s s' _ B j
  rw [hD]
  rfl

/-- **The line req**, where the letter's field req reads the public part and the state's field req
alone. -/
theorem req_at {f : P → _ → P5J.TReq} (hD : D.H.req = fun a => f a.1 a.2.req) :
    ∀ s s', LayRest s s' → D.H.req (Z, s) = D.H.req (Z, s') := by
  intro s s' h
  rw [hD]
  show f Z s.req = f Z s'.req
  rw [h.2.req]

/-- **The line base**, where the letter is the test that always accepts. -/
theorem base_at (hD : D.base = fun _ => true) :
    ∀ s s', LayRest s s' → D.base (Z, s) = true → D.base (Z, s') = true := by
  intro s s' _ _
  rw [hD]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.smp_at
#print axioms OnBytes.Road.K4.stMask_at
#print axioms OnBytes.Road.K4.req_at
#print axioms OnBytes.Road.K4.base_at
