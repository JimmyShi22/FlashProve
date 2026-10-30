-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4HeadBlind.lean: THE LINE head OF `K4Reads` (K4Reads.lean: "the output head's part
of the model's relation, said at the verifier's state after K4's sub-protocol accepts, holds at the
state in front") OUT OF ONE EQUATION ON THE DATA's LETTER headPart AND TWO LINES. Why the line is
wanted at K4's places at all: the items constr j p of LATER segments are open across K4's
sub-protocol, the output head's among them. One statement with its proof: rewriting.

  **`head_blind`**: where headPart reads NO STRING, and of the state only the request as the
    relation's reader gives it (H.req) and one token more (tokH): headPart = fun p i a _ w => Hp p i
    (H.req a) (tokH a) w; and these two readers give one value at two states inside the fence: the
    line head.

WHO PAYS. The equation: by its authors' word the term meant for headPart is of that form by its
definition (the token is read at one part alone). H.req: `req_pub` (K4ReadsOf.lean), where it reads
the public part alone. tokH: its filler's.

Limits. Three premises; shown at no filling. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (Frame strsOf MsgT)

variable {Xi P Tok T : Type} {rows cols nR kC : ℕ} {X : Verify.Public}
  {D : K4Data Xi P Tok rows cols nR kC X} (Z : P)

/-- **The line head, where the head's part reads no string, and of the state two readers' values
alone.** -/
theorem head_blind (Fr : Frame) (base : ℕ)
    {Hp : P5J.TPart → IdxM → P5J.TReq → T → Wit (CellsK rows cols) Tok MsgT → Prop}
    {tokH : P × S → T}
    (hD : D.headPart = fun p i a _ w => Hp p i (D.H.req a) (tokH a) w)
    (hreq : ∀ s s', LayRest s s' → D.H.req (Z, s) = D.H.req (Z, s'))
    (htok : ∀ s s', LayRest s s' → tokH (Z, s) = tokH (Z, s')) :
    ∀ s s' (x y : Fr.E.Str), LayRest s s' → SameStr Fr base x y → ∀ p i w,
      D.headPart p i (Z, s') (strsOf Fr y) w → D.headPart p i (Z, s) (strsOf Fr x) w := by
  intro s s' x y h _ p i w hw
  rw [hD] at hw ⊢
  show Hp p i (D.H.req (Z, s)) (tokH (Z, s)) w
  rw [hreq s s' h, htok s s' h]
  exact hw

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.head_blind
