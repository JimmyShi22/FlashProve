-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/Values.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: K4Opens is a hypothesis, and no statement leads to
it. That it can hold: no example is known. What each of its fields rests on: the head of
Johnson/Road/K4/W/Item.lean. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The hypotheses `K4Worths` and `K4Values` of the member of the layers' own rounds (sub-protocol K4),
and the share of the debt `Exchange` at that member's own item, from one hypothesis: `ItemOpens`
(Johnson/Road/K4/W/Item.lean) at every state behind the member's step and every continuation of the
challenges. WHERE THE NAMES ARE DEFINED. `Exchange`: Johnson/Desc/ProofFile/Honest/Thread/Pays.lean.
`K4Table`, `K4Values`, `ShareAt`: Law/Table.lean. `K4Sits` ("the seat": where the member's step
accepts, the sub-protocol accepts): Law/Sits.lean. `K4Front` (eight clauses on the state in front):
Law/Kept.lean. `K4Worths`: Law/Worth.lean.

  `K4Opens T At b M own rdOf tl p h pc D`   ItemOpens at the table's data, at every such state.
  `worths_of_opens`   K4Opens gives K4Worths.
  `values_of_opens`   with K4Sits and K4Front besides, K4Values.
  `k4_own_share_of_opens`   with K4Table besides, the share at the member's own item.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Worth
import Johnson.Road.K4.W.Item

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4.W (ItemOpens item_worths)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ)
open VerifiableInference.Desc.Plain.K04 (frontRun)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **ALL HYPOTHESES OF THE WORTHS, AT EVERY STATE BEHIND THE MEMBER's STEP**, at every continuation
of the challenges. At says which states in front of the member are meant (Thr T b for `Exchange`,
ThrS T Said b for `ExchangeS`): it is At that has to carry "the witness is valid" and the ties of
the witness's cells to Mm, or the hypothesis is empty. h, pc, D: the plan's shape, its list of calls
and the library's sizes: public, one for all states. This defines a hypothesis; the definition
claims nothing. -/
def K4Opens (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop) (b : Nat)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape)
    (pc : List (List String)) (D : Dim) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    ItemOpens h pc D tl p.P p.g o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))

section
variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat}
  {At : Coins Bk → First.S → Mid W X → Env → Prop} {M : First.S → Bound GQ → Road.Mats GQ}
  {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated} {own : List (Nat × Nat)}
  {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par} {h : Layer.Shape}
  {pc : List (List String)} {D : Dim}

/-- **The worths, from the hypotheses at every state.** CONDITIONAL: on hO. -/
theorem worths_of_opens (hO : K4Opens T At b M own rdOf tl p h pc D) :
    K4Worths T At b M own rdOf tl p :=
  fun blk hblk k s m E ds y cols s' hA hd hS ds' A hseg o fs₁ F₁ ho hf =>
    item_worths (hO blk hblk k s m E ds y cols s' hA hd hS ds' A hseg o fs₁ F₁ ho hf)

/-- **The values.** CONDITIONAL: on the seat, the eight clauses and hO. -/
theorem values_of_opens (hSit : K4Sits T b p) (hF : K4Front T At b M Hh l St own rdOf tl p)
    (hO : K4Opens T At b M own rdOf tl p h pc D) : K4Values T At b M own rdOf tl p :=
  values_of_worths hSit hF (worths_of_opens hO)

/-- **K4's SHARE OF `Exchange` AT ITS OWN ITEM.** CONDITIONAL: on the table's parameters, the seat,
the eight clauses and hO. -/
theorem k4_own_share_of_opens {iOwn iPl iJo : T.ι} {rest : List T.ι}
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) (hSit : K4Sits T b p)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (hO : K4Opens T At b M own rdOf tl p h pc D) :
    ShareAt T At b [iOwn] :=
  k4_own_share_of_worths Tb hSit hF (worths_of_opens hO)

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.worths_of_opens
#print axioms ProofFile.Honest.K4.W.values_of_opens
#print axioms ProofFile.Honest.K4.W.k4_own_share_of_opens
