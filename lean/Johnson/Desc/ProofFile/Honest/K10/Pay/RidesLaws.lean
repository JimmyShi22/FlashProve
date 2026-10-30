-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/RidesLaws.lean: what the sentences of four sorts of item say of the verifier's state in front of the closing of a
segment they say of every state that `K10Keeps` (Johnson/Desc/K10/Honest/Keeps.lean) ties to it. At the library's composed
meaning `mgAll` over the head's data with two fields laid (the decoder a constant c; the carried claim a letter carryX),
as the first chain's thread of the honest side has it.

  `keeps_rows`, `keeps_read`   the pending rows on the weights, the book, the code tables and each message's shape are kept
  `keeps_rowAt`      the reader of the pending claim on the weights answers alike, where the index masks' message is a
                    member of no group in front (it reads that message's ledger; a closing shuts its members' ledgers alone)
  `constr_on_k10`    a part of a segment's relation, the digits' part aside
  `pinW_on_k10`      "the weights are what the stored table decodes to"
  `pile_on_k10`      "every pending row on the table of weights holds"
  `wo_on_k10`        "what the own rounds leave for the row on the weights", under `IndexFree` in front
  `indexFree_reached`   under the head, at every border from 3 to 355, at a state that the chain's own blocks reach: the
                    index masks' message is a member of no group

How. The arms are those of the library's `holds_back_light` and `wo_back_k10`
(Johnson/Desc/First/Link/Law/RidersLight.lean), which go from behind to in front over an accepting step; here they go
forward, from `K10Keeps` alone. `constr_on_k10` follows `H2K5.Honest.constr_on_head`
(Johnson/Desc/K5/Honest/Law/RidesAtHead.lean).

Limits. The head is a hypothesis. Nothing shows that a sentence holds at any state. The full size and the older hash alone.
-/
import Johnson.Desc.K10.Honest.KeepsStep
import Johnson.Desc.First.Link.Law.RidersLight
import Johnson.Desc.K5.Honest.Law.RidesAtHead
import Johnson.LPFE1R.K10HeadOpenAt
import Johnson.P5J.K10Two
import Johnson.P1L20R.RoomFold
import Johnson.AtFull.Shape.PlansAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K10
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Strs Wit Chain K9.recOf K9.putRec)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT mgAll mgBase mgAll_pile mgAll_wo mgAll_pinW)
open VerifiableInference.Desc.LinkJoin (IndexFree rowAt_of_ledger rows_putRec tokHOf_of_out)
open VerifiableInference.Desc.K13.Law (RowsTrue rwBook_same)
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.K10.YesFree (K10Keeps keeps_six keeps_st)
open P5J (AtMgA TS)

/-! ## 1 What the four sorts read -/

/-- The pending rows on the weights are kept. -/
theorem keeps_rows {s s' : S} (K : K10Keeps s s') : s'.rows = s.rows := by
  rw [K.1.2]
  exact rows_putRec s _

/-- The book, the code tables and each message's shape are kept. -/
theorem keeps_read {s s' : S} (K : K10Keeps s s') :
    s'.book = s.book ∧ s'.st.codes = s.st.codes ∧
      ∀ o : Nat, (s'.st.oracles[o]?).map (fun a : OnBytes.Oracle => a.shape) =
        (s.st.oracles[o]?).map fun a : OnBytes.Oracle => a.shape :=
  ⟨(keeps_six K).1, (keeps_st K.1.1).1, (keeps_st K.1.1).2.2.1⟩

/-- The reader of the pending claim on the weights answers alike. -/
theorem keeps_rowAt {s s' : S} (K : K10Keeps s s') (hI : IndexFree s) (lay : WsLay) (n : Nat)
    (lin : Params.LinShape) :
    Johnson.Desc.First.Walk.Law.rowAt lay n lin s' =
      Johnson.Desc.First.Walk.Law.rowAt lay n lin s := by
  have ho : s'.out = s.out := (keeps_six K).2.2.2.1
  have hl : Johnson.Desc.First.Walk.Law.leftOf s' = Johnson.Desc.First.Walk.Law.leftOf s := by
    rw [K.1.2]
    exact VerifiableInference.Desc.First.Close.leftOf_putRec s _
  refine rowAt_of_ledger ho hl ?_ lay n lin
  obtain ⟨_, _, G, m, rows, _, _, _, _, _, _, hG, _, _, e⟩ := K.1.1
  have hG' : s.st.groups[(K9.recOf s).frame.group]? = some G := hG
  have est : s'.st = VerifiableInference.Desc.First.Close.spent
      (Slice.begun s.st (K9.recOf s).frame.group G) m := congrArg (·.st) e
  rw [est]
  exact VerifiableInference.Desc.First.Close.behind_ledger _ _ _ _ _
    (hI G (Array.mem_of_getElem? hG'))

/-! ## 2 The four sorts, under the head -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (c : P5J.CellsM OnBytes.Flat.numsFull)
  (carryX : Nat → ProofFile.InstPub × S → Strs → Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT →
    Prop)

/-- **A part of a segment's relation**, the digits' part aside. -/
theorem constr_on_k10 (n : Nat) (p : VerifiableInference.Desc.First.Part) (hp : p ≠ .lookDigits)
    {π : ProofFile.InstPub} {s s' : S} (K : K10Keeps s s') (y y' : Strs)
    (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr n p (π, s) y
      w) :
    (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).constr n p (π, s') y'
      w := by
  have ho : s.out = s'.out := (keeps_six K).2.2.2.1.symm
  have h1 := (H2K5.Door.constrIs_any _ mgBase _ _ _ _ _).1 hm
  refine (H2K5.Door.constrIs_any _ mgBase _ _ _ _ _).2 ?_
  rw [if_neg hp] at h1 ⊢
  refine ⟨h1.1, fun M i hM hH => ?_⟩
  rw [H2K5.Door.bodyAll_blind _ (a := (π, s)) (b := (π, s')) rfl
    (fun p i y y' w => VerifiableInference.Desc.Kinds.Head.Law.Came.headPartK6_blind _ _ _ _ _ _ _
      _ _ _ _ _ p i (π, s) (π, s') y y' w rfl
      (fun _ => tokHOf_of_out (a := (π, s')) (b := (π, s)) ho)) n p i y y' w]
  exact h1.2 M i hM hH

/-- **"The weights are what the stored table decodes to."** -/
theorem pinW_on_k10 {π : ProofFile.InstPub} (s s' : S) (y y' : Strs)
    (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).pinW (π, s) y w) :
    (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).pinW (π, s') y' w := hm

/-- **"Every pending row on the table of weights holds."** -/
theorem pile_on_k10 {π : ProofFile.InstPub} {s s' : S} (K : K10Keeps s s') (y y' : Strs)
    (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).pile (π, s) y w) :
    (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).pile (π, s') y' w := by
  obtain ⟨hb, hc, hsh⟩ := keeps_read K
  have hq : RowsTrue (h.𝔇.rw13 (π, s)) s w := hm
  show RowsTrue (h.𝔇.rw13 (π, s')) s' w
  have e : h.𝔇.rw13 (π, s') w = h.𝔇.rw13 (π, s) w :=
    rwBook_same h.𝔇.arr h.𝔇.mat13 (π, s) (π, s') hb hc hsh w
  intro q hq'
  rw [keeps_rows K] at hq'
  have h1 := hq q hq'
  rw [e]
  exact h1

/-- **"What the own rounds leave for the row on the weights."** -/
theorem wo_on_k10 (m : Nat) {π : ProofFile.InstPub} {s s' : S} (K : K10Keeps s s') (hI : IndexFree s)
    (y y' : Strs) (w : Wit (P5J.CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (hm : (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).wo m (π, s) y w) :
    (mgAll { h.𝔇 with decT := fun _ _ => some c, cr1 := carryX } mgBase).wo m (π, s') y' w := by
  obtain ⟨hb, hc, hsh⟩ := keeps_read K
  rw [mgAll_wo] at hm ⊢
  unfold VerifiableInference.Desc.First.FillP1.woAt at hm ⊢
  intro q hrow
  have e : h.𝔇.rw13 (π, s') w = h.𝔇.rw13 (π, s) w :=
    rwBook_same h.𝔇.arr h.𝔇.mat13 (π, s) (π, s') hb hc hsh w
  have h1 : VerifiableInference.Desc.K13.Law.Holds _ (h.𝔇.rw13 (π, s) w) q := hm q (by
    show Johnson.Desc.First.Walk.Law.rowAt _ _ _ s = some q
    rw [← keeps_rowAt K hI]
    exact hrow)
  rw [← e] at h1
  exact h1

include h in
/-- **At a reached state the index masks' message is a member of no group.** -/
theorem indexFree_reached {b : Nat} (h3 : 3 ≤ b) (h355 : b ≤ 355) {z : ProofFile.InstPub} {s : TS}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) b (z, s)) : IndexFree s := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact P1L20.outOfGroupsB_iff.1 (P1L20.room_out_of_groups h.scope h.reads O
    (Johnson.AtFull.Shape.plans_at h) (P1L20.roomOwes_paid h.scope h.reads O) hr h3 h355)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.keeps_rows
#print axioms ProofFile.Honest.K10.keeps_read
#print axioms ProofFile.Honest.K10.keeps_rowAt
#print axioms ProofFile.Honest.K10.constr_on_k10
#print axioms ProofFile.Honest.K10.pinW_on_k10
#print axioms ProofFile.Honest.K10.pile_on_k10
#print axioms ProofFile.Honest.K10.wo_on_k10
#print axioms ProofFile.Honest.K10.indexFree_reached
