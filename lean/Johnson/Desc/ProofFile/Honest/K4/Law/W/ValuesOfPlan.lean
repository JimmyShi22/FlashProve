-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ValuesOfPlan.lean: CONDITIONAL.

Not shown here. THAT A FORM IS WORTH 0 ANYWHERE: K4Slots is a hypothesis, and no statement leads to
it. That it can hold: no example is known. What each of its fields rests on: the head of
Johnson/Road/K4/W/Item.lean. Nothing on soundness, on completeness or on any other property.
No property is claimed.

The hypothesis `K4Opens` (Law/W/Values.lean) of the member of the layers' own rounds (sub-protocol
K4) from K4Sits, nine public facts on the plan (`K4Plan`, Johnson/Road/K4/W/GroundOfHear.lean) and
the six fields that speak of a world or of the cells (`ItemSlots`,
Johnson/Road/K4/W/ItemOfKept.lean) at every state behind the member's step; and with it K4Values and
the share of the debt `Exchange` at the member's own item. Where the names are defined: the head of
Law/W/Values.lean.

  `K4Slots T At b M own rdOf tl p h D`   ItemSlots at the table's data, at every such state.
  `opens_of_slots`   K4Sits, K4Plan and K4Slots give K4Opens.
  `values_of_slots`   with K4Front besides, K4Values.
  `k4_own_share_of_slots`   with K4Table besides, the share at the member's own item.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.Values
import Johnson.Road.K4.W.ItemOfKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.K4 (kept_atS)
open OnBytes.Road.K4.W (ItemSlots K4Plan item_of_kept)
open Inst.Model.FFSeg (Dim)
open VerifiableInference.Desc (Link Claim First.S)
open VerifiableInference.Desc.K9 (segAt? LinkHoles)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ)
open VerifiableInference.Desc.Plain.K04 (frontRun)

variable {Bk : ProverCoinCounts} {V W X Pb : Type}

/-- **THE SIX FIELDS THAT SPEAK OF A WORLD OR OF THE CELLS, AT EVERY STATE BEHIND THE MEMBER's
STEP**, at every continuation of the challenges. At says which states in front of the member are
meant (Thr T b for `Exchange`, ThrS T Said b for `ExchangeS`): it is At that has to carry "the
witness is valid" and the ties of the witness's cells to Mm, or the hypothesis is empty. h, pc, D:
the plan's shape, its list of calls and the library's sizes: public, one for all states. This
defines a hypothesis; the definition claims nothing. -/
def K4Slots (T : Thread Bk First.S Claim V W X Pb)
    (At : Coins Bk → First.S → Mid W X → Env → Prop) (b : Nat)
    (M : First.S → Bound GQ → Road.Mats GQ) (own : List (Nat × Nat))
    (rdOf : T.Wt → Nat × Nat → MsgQ) (tl : HTailF2) (p : Par) (h : Layer.Shape) (D : Dim) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', At k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' → ∀ ds' A,
    segAt? s' = some A → ∀ o fs₁ F₁, seatS.own s' = some o →
    frontRun p o (seatS.fork s') = some (fs₁, F₁) →
    ItemSlots h D tl p.P o (seatS.fork s') F₁
      (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (M s' (dataQ own A (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds')))))

section
variable {T : Thread Bk First.S Claim V W X Pb} {b : Nat}
  {At : Coins Bk → First.S → Mid W X → Env → Prop} {M : First.S → Bound GQ → Road.Mats GQ}
  {Hh : LinkHoles} {l : Link First.S Claim} {St : Stated} {own : List (Nat × Nat)}
  {rdOf : T.Wt → Nat × Nat → MsgQ} {tl : HTailF2} {p : Par} {h : Layer.Shape}
  {pc : List (List String)} {D : Dim}

/-- **K4Opens from K4Sits, the plan's public facts and the six fields.** CONDITIONAL. -/
theorem opens_of_slots (hSit : K4Sits T b p) (A : K4Plan h pc p.P p.g tl D)
    (hO : K4Slots T At b M own rdOf tl p h D) : K4Opens T At b M own rdOf tl p h pc D := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf
  obtain ⟨_, hdec⟩ := hSit blk hblk s _ _ s' _ hS.2
  exact item_of_kept (kept_atS hdec) A ho
    (hO blk hblk k s m E ds y cols s' hA hd hS ds' Aq hseg o fs₁ F₁ ho hf)

/-- **The values.** CONDITIONAL: on the seat, the eight clauses, A and hO. -/
theorem values_of_slots (hSit : K4Sits T b p) (hF : K4Front T At b M Hh l St own rdOf tl p)
    (A : K4Plan h pc p.P p.g tl D) (hO : K4Slots T At b M own rdOf tl p h D) :
    K4Values T At b M own rdOf tl p :=
  values_of_opens hSit hF (opens_of_slots hSit A hO)

/-- **K4's SHARE OF `Exchange` AT ITS OWN ITEM.** CONDITIONAL: on the table's parameters, the seat,
the eight clauses, A and hO. -/
theorem k4_own_share_of_slots {iOwn iPl iJo : T.ι} {rest : List T.ι}
    (Tb : K4Table T b iOwn iPl iJo rest Hh l St own rdOf) (hSit : K4Sits T b p)
    (hF : K4Front T At b M Hh l St own rdOf tl p) (A : K4Plan h pc p.P p.g tl D)
    (hO : K4Slots T At b M own rdOf tl p h D) : ShareAt T At b [iOwn] :=
  k4_own_share_of_opens Tb hSit hF (opens_of_slots hSit A hO)

end

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.opens_of_slots
#print axioms ProofFile.Honest.K4.W.values_of_slots
#print axioms ProofFile.Honest.K4.W.k4_own_share_of_slots
