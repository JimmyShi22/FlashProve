-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/JoinT.lean: CONDITIONAL: WITH THE THREAD T A VARIABLE: the
named premise `JoinOwedT` of the statement on the debts of T's member at an attention segment's own
rounds (Johnson/Desc/ProofFile/Honest/K5/Law/DebtsT.lean: "whatever form the lookup's text returns
on the segment's key forms is worth 0 in the item's own world"), from the hypothesis on the public
input, the structure on T's letters, the half's seat, the test on the letters and the ties. A
joining; calls alone.

It is `joinOwed_script` (Johnson/Desc/ProofFile/Honest/K5/Law/JoinClosed.lean) typed anew: where
that proof unfolds the first thread at the library's own letters, this one calls a field of `K5AtT`
(Johnson/Desc/ProofFile/Honest/K5/Law/AtT.lean) or a lemma under it (`reach_T`, `onAt_T`,
`decides_T`, DebtsT.lean). No letter of T is spent that the structure does not hold.

Main name:
  `joinOwedT_script`   **`JoinOwedT h T wt g a`**

THE PREMISES, ALL: h: the hypothesis `P5J.AtMgA`; R (`K5AtT`): nine facts on T's letters at the
member of group g; hg, ha: the group and its plan; Hs (`K5Seated`); hfit, hb: the test `Thread.fits`
on the letters, up to a number beyond the border; Sc (`K5Script`: THE THREE TIES, at the sentence's
own seats and at the sentence's reading of T's witness: THEY ARE NOT SHOWN); hP: the seat's
public data are the plan's shape and own numbers.
Of R are spent: T.bs, T.ft, T.begun (the state in front is reached); T.form, T.formP, T.handed (no
mark, and the table's promise); T.row's asks and T.means at the item worth "keys".
Limits. None of these is shown to be met here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.DebtsT
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
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att.P (behind behind_inj segAt_front)
open H2K5.Honest (public_at_head law_at_head joinMeets_item_at_head front_at_head stated_at_head
  kv_of_cells addr_inside_ofPlan)
open ProofFile.Honest.FirstThread (WtF honest)
open P5J (AtMgA mgAtAll TS CellsM)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : Item → T.ι} {pb : T.P → ProofFile.InstPub} {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (R : K5AtT h T g it pb wt ans test carryX cq)
include R

/-- **`JoinOwedT`, WITH T A VARIABLE**, from the head, the structure on T's letters, the seat, the
test on the letters and the ties. No premise on values is left beside the ties. Conditional; the
premises are listed in the file's head. -/
theorem joinOwedT_script {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) : JoinOwedT h T wt g a := by
  cases Z5 with
  | mk link P base keyAt =>
  have hP' : P = ⟨a.S, a.own⟩ := hP
  subst hP'
  intro blk' k s s' m E ds y cols hmem hT hd hS ds' att hd5 G e es gL kf v hlk hk hj
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hmem)
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  obtain ⟨att', hd5', G', e', hh, es'⟩ := behind_is _ Hs Dc hd hS
  obtain rfl : att' = att := VerifiableInference.Desc.First.Here.att.inj (e'.symm.trans e)
  obtain ⟨rfl, rfl, _, _⟩ := behind_inj (es'.symm.trans es)
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlt : borderOf g < cF.blocksInOrder.length := by
    rw [← R.bs]
    exact (List.getElem?_eq_some_iff.1 Hs.member).1
  have hr := reach_T h R (Nat.le_of_lt hlt) hT
  obtain ⟨⟨l, -, hy⟩, -⟩ := hS.1
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hp0 : pb (T.seat k m s).1 = m.st.input.x.pub := R.handed _ _ _
  have hfit' := hfit
  unfold Thread.fits at hfit'
  simp only [Bool.and_eq_true] at hfit'
  have hq : Item.worth (2 * g + 1) 2 "keys" ∈ asked7 (2 * g + 1) :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have hop : it (Item.worth (2 * g + 1) 2 "keys") ∈ T.opened (borderOf g) :=
    mem_of_fwdFit hfit'.1.1.1.1 hb (by rw [R.asks]; exact List.mem_map.2 ⟨_, hq, rfl⟩)
  have h0 := (R.means _ (Or.inl hq) _ _ _ _).1 (hT.2.2.2.1 (ds ++ ds') _ hop)
  rw [hp0] at h0
  obtain ⟨_, _, _, _, _, _, hz⟩ := front_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl
    rfl _ _ (open8_at hg) hr hu hon e
  have hSt := (stated_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) hr hu hon e hd5' G').mask
  obtain ⟨blk0, hat⟩ := H2K5.Door.seated_all h hg
  have hA : AddrIn a.S a.seam.tl :=
    addr_inside_ofPlan (H2K5.Door.ofPlan_all h ha) (H2K5.Door.posG_all h hg ha hat)
  refine join_zero_paid Hs Sc hT hd hS.1 e rfl (public_at_head h hg ha) (law_at_head h hg ha).1
    (law_at_head h hg ha).2 (mask_behind hS.1 att' G' h.𝔇.St.at1 hSt ds') hz hh hk
    (OnBytes.Road.L5.tbOf a.S) hj fun g0 hg0 => ?_
  obtain ⟨g1, hg1, K3, _⟩ := Sc.keyTie k s m E hT att' e
  obtain rfl : g1 = g0 := Option.some.inj (hg1.symm.trans hg0)
  have J := joinMeets_item_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
    (open8_at hg) (open_k5 hg _ (by simp)) hr hu hon e hh (T.strs E) h0 hg0 K3
    (fun c X _ => kv_of_cells h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _
      (open8_at hg) hr hu hon e (segAt_front e) _
      (fun q hq' => cells_named Sc hA hT (segAt_front e) (ds ++ ds') q hq') c X) hlk
  rw [ei, eh, List.append_assoc]
  exact J

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.joinOwedT_script
