-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TiesAtReq.lean: the letters drop, put and `early` of the sheet
Johnson/Flat/TiesSheet.lean at the requests that the program's reader takes (`Flat.Req`,
Johnson/Flat/LedgerClaim.lean), and `TieGlue` there.

Why. The sheet's letters are plain at all instances of the integer model: put p t is the record with
the reply t. The frame's main road has the instances `Flat.Req`: a subtype: r < e, and the reply is
0 if e is before the window's end. There the record with another reply may be no request: so put
wants a second arm, and "what `early` drops, put back, gives the instance" goes by cases.

Definitions, statements and proofs.
  `dropReq`: a request's reply. `putReq p t`: the request p with the reply t, if that is a request;
    ELSE p ITSELF (the second arm).
  `putReq_glue`: putReq (reqWithoutReply x) (dropReq x) = x. `glueReq`: that is `TieGlue` at the
    frame's configuration of the full size, at every table pp of scales and policy.
  `putReq_val`: the first arm: where e is not before the window's end, or t is 0.
  `putReq_else`: THE SECOND ARM: where e is before the window's end and t is not 0: putReq p t = p.
  `early_putReq`: put turns the reply alone.
  `firstRel_else`: WHAT THE FIRST RELATION OF THE SHEET SAYS AT THE SECOND ARM: at a witness whose
    token is not 0, at a public part whose e is before the window's end, `firstRel` speaks of the
    public part itself, that is of the request with the reply 0.

Limits. The second arm is never reached through `TiesOfFive`: there the witness's token is what
`early` dropped of a request (`TieReads`, `TieFins`), and `putReq_glue` goes by the first arm. But
`TieTells` and `knows` run over ALL witnesses: at the second arm the first relation claims the
request with the reply 0, whatever the witness's token: whoever shows the first chain's clause at
`firstRel` has to meet that too. The reference sizes and the full size's configuration alone: the
small size's requests (`withoutReplySmall`, Johnson/Flat/SmallAtFiles.lean) have no such file yet.
No value of the other letters is laid.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.TiesSheet
import Johnson.Flat.PubReq
import Johnson.Flat.TwoSizesAt
import Johnson.Top.H.TargetAtPolicy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Flat
open Inst.Model OnBytes.Model VerifiableInference.OnPublicFiles.Flat

/-- What `reqWithoutReply` drops: the reply. -/
def dropReq (x : Req) : Fin ppref.V := x.val.y

/-- The request p with the reply t, if that is a request; else p itself. -/
def putReq (p : Req) (t : Fin ppref.V) : Req :=
  if h : WellFormed { p.val with y := t } then ⟨{ p.val with y := t }, h⟩ else p

/-- The first arm. -/
theorem putReq_val (p : Req) (t : Fin ppref.V) (h : p.val.e < ppref.T → t.val = 0) :
    (putReq p t).val = { p.val with y := t } := by
  unfold putReq
  rw [dif_pos (show WellFormed { p.val with y := t } from ⟨p.property.1, h⟩)]

/-- **The second arm.** -/
theorem putReq_else (p : Req) (t : Fin ppref.V) (he : p.val.e < ppref.T) (ht : t.val ≠ 0) :
    putReq p t = p := by
  unfold putReq
  rw [dif_neg (show ¬ WellFormed { p.val with y := t } from fun h => ht (h.2 he))]

/-- **What `reqWithoutReply` drops, put back, gives the request.** -/
theorem putReq_glue (x : Req) : putReq (reqWithoutReply x) (dropReq x) = x :=
  Subtype.ext (putReq_val (reqWithoutReply x) (dropReq x) x.property.2)

/-- put turns the reply alone. -/
theorem early_putReq (p : Req) (t : Fin ppref.V) :
    reqWithoutReply (putReq p t) = reqWithoutReply p := by
  unfold putReq
  split <;> rfl

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ

variable (N : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp))

/-- The frame's configuration of the full size at the requests, at a table of scales and policy. -/
abbrev kcReq : ConfLetters frS.P.T.a :=
  lettersAt (claimsReqAt (frS.toDecR frZ 402653181) N pp) (relationsAndEncodingOfClaims _ E)

/-- `TieGlue` at that configuration. -/
theorem glueReq : TieGlue (kcReq N pp E) reqWithoutReply dropReq putReq := putReq_glue

/-- **What the sheet's first relation says at the second arm.** -/
theorem firstRel_else (DP : WholeD) {W₀ : Type} (tok : W₀ → Fin Inst.Model.ppref.V)
    (cells : W₀ → (kcReq N pp E).conf.Cells) (p : Flat.Req) (rec : (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (w : W₀)
    (he : p.val.e < Inst.Model.ppref.T) (ht : (tok w).val ≠ 0) :
    firstRel (kcReq N pp E) DP putReq tok cells ((p, rec), y) w ↔
      ∀ i, (kcReq N pp E).conf.D y rec = some i → (kcReq N pp E).conf.Rno i p (cells w) := by
  unfold firstRel
  show (∀ i, _ → (kcReq N pp E).conf.Rno i (putReq p (tok w)) (cells w)) ↔ _
  rw [putReq_else p (tok w) he ht]

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.putReq_glue
#print axioms OnBytes.Flat.putReq_else
#print axioms OnBytes.Flat.early_putReq
#print axioms VerifiableInference.OnPublicFiles.glueReq
#print axioms VerifiableInference.OnPublicFiles.firstRel_else
