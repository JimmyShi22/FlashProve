-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/JoinClosed.lean: CONDITIONAL: the named premise `JoinOwed` of
the statement on the debts of the member that stands at an attention segment's own rounds
(Johnson/Desc/ProofFile/Honest/K5/Law/Exchange.lean), WITH NO PREMISE ON VALUES FROM THE LOOKUP'S
HONEST SIDE: the lookup's half of the join is drawn from the item on the worth of the keys, which
the member's row asks and which the thread in front therefore holds. One premise still speaks of
what the lookup left: the tie on the key points, the third of `K5Script`. A joining; calls alone.

The road. `join_zero_paid` (Johnson/Desc/ProofFile/Honest/K5/Law/JoinPaid.lean) leaves three
premises on values: the ties' field on the mask row, which stays here in Sc; hD, which `mask_behind`
(Honest/K5/Law/Slots.lean) pays; and `JoinMeets`. `joinMeets_item_at_head`
(Johnson/Desc/K5/Honest/Law/JoinMeetsAtHead.lean) gives the last from the closed filling's item
worth "keys" in front. That item is read off the thread in front as in `planes_at_thr`
(Exchange.lean).

Main names:
  `KeyVecsOwed`     an inner step: a premise's form: along every step of the member at the border,
                    at every continuation: the item's key vectors, which are made of the cells
                    unpacked from the witness's messages, are the library's key vectors on the
                    prover's cells, read
  `joinOwed_closed`   an inner step: `JoinOwed` under `KeyVecsOwed`
  `keyVecsOwed_of_script`   `KeyVecsOwed` from the ties: the tie on the cells, with `kv_of_cells`
                    (Johnson/Desc/K5/Honest/Law/KvOfCells.lean) and `addr_inside_ofPlan`
                    (Johnson/Desc/K5/Honest/Law/AddrIn.lean)
  `joinOwed_script`   **`JoinOwed`**: the statement to take

THE PREMISES OF `joinOwed_script`, ALL: the hypothesis `P5J.AtMgA`; hg, ha: g is one of the twelve
groups and a is its stored plan; Hs (`K5Seated`); hfit, hb: the test `Thread.fits` on the letters;
Sc (`K5Script`: THE THREE TIES, at the sentence's own seats and reading of the witness: THEY ARE NOT
SHOWN); hP: the seat's public data are the plan's shape and own numbers.
Limits. None of these is shown to be met anywhere. `KeyVecsOwed` is a definition: nothing is claimed
of it.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Exchange
import Johnson.Desc.ProofFile.Honest.K5.Law.JoinPaid
import Johnson.Desc.K5.Honest.Law.JoinMeetsAtHead
import Johnson.Desc.K5.Honest.Law.AttAtHead
import Johnson.Desc.K5.Honest.Law.KvOfCells
import Johnson.Desc.K5.Honest.Law.AddrIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att.P (behind behind_inj)
open H2K5.Honest (tOf public_at_head law_at_head joinMeets_item_at_head front_at_head
  stated_at_head)
open ProofFile.Honest.FirstThread (Script WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
    VerifiableInference.Desc.Sound.MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **A premise's form**: along every step of the member at the border from `Thr` in front, at every
continuation ds': at the lookup's place x₁ of the segment: each call's key vector as the item on the
worth of the keys has it (the layout's, on the cells that are unpacked from the witness's messages)
is the library's key vector on the prover's cells, read, at the shape's tables. It is a definition.
Nothing is claimed of it. -/
def KeyVecsOwed (g : Nat) (a : Attention.Plan) (cells : Tr → Cells) (Z5 : Seat5) : Prop :=
  ∀ (blk : Block TS ProofFile.Cl) (k : Coins Bk) (s s' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (E : Env) (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X)
    (cols : List OpenedColumn),
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).bs[borderOf g]? = some blk →
    Thr (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g) k s m E →
    drawsFit blk.rounds ds = true →
    (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).Stepped blk k s m E ds y
      cols s' →
    ∀ ds' x₁, lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ →
      ∀ c : Fin 4, ∀ X < 2 ^ (OnBytes.Road.L5.callsOf a.fs).a c,
        Cb.Fo.forK Cb.Gl.E
          (VerifiableInference.Desc.First.Look.attLay a.S x₁.fs x₁.lm x₁.F.next x₁.ns a.seam.tl) ()
          (Cb.Fo.zext (VerifiableInference.OnPublicFiles.attMu x₁ a.seam.tl h.𝔇.sent h.𝔇.l3.rad
            (H2K5.Door.seatAll h x₁) h.𝔇.arr
            ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).wit k
              m.st.input (m.st.heard ++ (ds ++ ds'))))) c.val X =
          Inst.Model.AttSeg.keyVec (scl := OnBytes.Road.L5.sclOf a.S) (OnBytes.Road.L5.dimOf a.S)
            (OnBytes.Road.L5.tbOf a.S)
            (tOf Reading.gl (inOf Z5.P.S Z5.link (cells m.st.input.trace))) c X

/-- **`JoinOwed` under `KeyVecsOwed`**: no premise on values from the lookup's honest side is left.
Conditional: on hKV (`KeyVecsOwed`: a premise on values, read off the witness's messages), and on
the premises of `joinOwed_script`, which the file's head lists. -/
theorem joinOwed_closed {n : Nat} {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Sc : K5Script (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hP : Z5.P = ⟨a.S, a.own⟩)
    (hKV : KeyVecsOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a cells Z5) :
    JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a := by
  intro blk' k s s' m E ds y cols hmem hT hd hS ds' att hd5 G e es gL kf v hlk hk hj
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hmem)
  obtain ⟨Pl, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att', hd5', G', e', hh, es'⟩ := behind_is _ Hs Dc hd hS
  obtain rfl : att' = att := VerifiableInference.Desc.First.Here.att.inj (e'.symm.trans e)
  obtain ⟨rfl, rfl, _, _⟩ := behind_inj (es'.symm.trans es)
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hfit' := hfit
  unfold Thread.fits at hfit'
  simp only [Bool.and_eq_true] at hfit'
  have hop : Item.worth (2 * g + 1) 2 "keys" ∈
      (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).opened
        (borderOf g) := by
    refine mem_of_fwdFit hfit'.1.1.1.1 hb ?_
    rw [asks_k5 h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h0 := hT.2.2.2.1 (ds ++ ds') _ hop
  obtain ⟨_, _, _, _, _, _, hz⟩ := front_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl
    rfl _ _ (open8_at hg) hr hu hon e
  have hSt := (stated_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) hr hu hon e hd5' G').mask
  refine join_zero_paid Hs Sc hT hd hS.1 e hP (public_at_head h hg ha) (law_at_head h hg ha).1
    (law_at_head h hg ha).2 (mask_behind hS.1 att' G' h.𝔇.St.at1 hSt ds') hz hh hk
    (OnBytes.Road.L5.tbOf a.S) hj fun g0 hg0 => ?_
  obtain ⟨g1, hg1, K3, _⟩ := Sc.keyTie k s m E hT att' e
  obtain rfl : g1 = g0 := Option.some.inj (hg1.symm.trans hg0)
  have R := joinMeets_item_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) (open_k5 hg _ (by simp)) hr hu hon e hh
    ((thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).strs E) h0 hg0 K3
    (hKV blk k s _ m E ds y cols hmem hT hd hS ds' x₁ hx) hlk
  rw [ei, eh, List.append_assoc]
  exact R

/-- **`KeyVecsOwed`, from the ties.** The tie on the cells says that the matrices read off the
witness's data hold the prover's cells at every valid name; the item's key vectors are the library's
key vectors of what these matrices hold (`kv_of_cells`); every valid name lies inside its matrix
(`addr_inside_ofPlan`). Conditional: the hypothesis `P5J.AtMgA`; Hs; Sc; hP. -/
theorem keyVecsOwed_of_script {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (Sc : K5Script (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hP : Z5.P = ⟨a.S, a.own⟩) :
    KeyVecsOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a cells Z5 := by
  intro blk' k s s' m E ds y cols hmem hT hd hS ds' x₁ hx c X _
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hmem)
  obtain ⟨_, Dc⟩ := seated_decides h hg ha Hs.member
  obtain ⟨att, _, _, e, _, _⟩ := behind_is _ Hs Dc hd hS
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨hu, hon⟩ := onAt_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg hT
  have hr := reach_of_thr h hs Q stored ans test carryX item n₁ n₂ valid rides keeps
    (Nat.le_of_lt (List.getElem?_eq_some_iff.1 Hs.member).1) hT
  obtain ⟨blk0, hat⟩ := H2K5.Door.seated_all h hg
  have hA : AddrIn a.S a.seam.tl :=
    H2K5.Honest.addr_inside_ofPlan (H2K5.Door.ofPlan_all h ha) (H2K5.Door.posG_all h hg ha hat)
  cases Z5 with
  | mk link P base keyAt =>
    have hP' : P = ⟨a.S, a.own⟩ := hP
    subst hP'
    exact H2K5.Honest.kv_of_cells h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
      (open8_at hg) hr hu hon e (VerifiableInference.Desc.First.Att.P.segAt_front e) _
      (fun q hq => cells_named Sc hA hT (VerifiableInference.Desc.First.Att.P.segAt_front e)
        (ds ++ ds') q hq) c X

/-- **`JoinOwed`, from the head, the seat, the test on the letters and the ties.** No premise on
values is left beside the ties. Conditional; the premises are listed in the file's head. -/
theorem joinOwed_script {n : Nat} {g : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl}
    (Hs : K5Seated (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 (parAt Zp g a) blk)
    (hfit : (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).fits n = true)
    (hb : borderOf g < n)
    (Sc : K5Script (thrAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) (borderOf g)
      cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms))
    (hP : Z5.P = ⟨a.S, a.own⟩) :
    JoinOwed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps g a :=
  joinOwed_closed h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs hfit hb Sc hP
    (keyVecsOwed_of_script h hs Q stored ans test carryX item n₁ n₂ valid rides keeps hg ha Hs Sc
      hP)

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.joinOwed_closed
#print axioms ProofFile.Honest.K5.keyVecsOwed_of_script
#print axioms ProofFile.Honest.K5.joinOwed_script
