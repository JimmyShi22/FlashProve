-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/SayOwedT.lean: CONDITIONAL, under the library's one head on the
public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), WITH THE `Thread` T A VARIABLE: the named
premise
`SayOwedT` of the statement on the debts of the member that stands at an attention segment's own
rounds (Honest/K5/Law/DebtsT.lean). One statement with its proof: a joining of lemmas.

It is `sayOwed_of` (Honest/K5/Law/SayOwed.lean) with what that proof spends of the first chain's own
`Thread` taken from the structure `K5AtT` (Honest/K5/Law/AtT.lean), by `decides_T`, `onAt_T`,
`reach_T` (Honest/K5/Law/DebtsT.lean) and `atIdn_of_thr` (Honest/K5/Law/IdnAt.lean). All that lies
below, from
`sayAt_member` (Honest/K5/Law/SayMember.lean) down, has T as a variable already.

THE PREMISES THAT ARE LEFT beside the head, the structure and the seat: the three ties between the
witness and the honest side (`K5Script`), WHICH ARE NOT SHOWN; the seat's public data are the
plan's; and `IdnOwed` at T's letter valid, WHICH IS SHOWN OF NO valid.
Main name:
  `sayOwedT_of`

Limits. The head is a hypothesis. At the function OnBytes.secondHashFunction, of which nothing is asked here; at
the library's full size alone. Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.SayOwed
import Johnson.Desc.ProofFile.Honest.K5.Law.DebtsT

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block OpenedColumn Strs Chain)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (seatTab)
open VerifiableInference.Desc.First.Att
open H2K5.Honest (public_at_head front_at_head stated_at_head)
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

/-- **THE NAMED PREMISE `SayOwedT`, WITH THE `Thread` T A VARIABLE** (Honest/K5/Law/DebtsT.lean:
along every step of T's member at the border, at every continuation, what the claims say holds in
the item's own world). CONDITIONAL on: the head h; what is spent of T's letters, as one structure
(R:
`K5AtT`, Honest/K5/Law/AtT.lean); g is below 12, and a is the plan of group g; the half's seat (Hs);
THE THREE TIES BETWEEN THE WITNESS AND THE HONEST SIDE (Sc), at the group's plan and in the letters
in which the item's sentence reads T's witness, WHICH ARE NOT SHOWN; the seat's public data are
the plan's shape and own numbers (hP); AND: WHATEVER INPUT T's LETTER valid ADMITS HAS CELLS THAT
MEET THE LIBRARY's THREE FAMILIES OF IDENTITIES (hV: `IdnOwed`, Honest/K5/Law/IdnAt.lean), WHICH
IS SHOWN OF NO valid. -/
theorem sayOwedT_of (R : K5AtT h T g it pb wt ans test carryX cq) (hg : g < 12)
    {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hV : IdnOwed T.valid cells Z5) : SayOwedT h T wt g a := by
  intro blk' k s s' m E ds y cols hmem hT hd hS ds' att hd5 G gL e hgL es i K hin
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hmem)
  obtain ⟨Pl, Dc⟩ := decides_T h R hg ha Hs.member
  obtain ⟨att', hd5', G', e', hh, es'⟩ := behind_is T Hs Dc hd hS
  obtain rfl : att' = att := by
    rw [e] at e'
    cases e'
    rfl
  obtain ⟨rfl, rfl, -, -⟩ := P.behind_inj (es'.symm.trans es)
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h R hg hT
  have hlen : borderOf g ≤ cF.blocksInOrder.length := by
    have h0 := (List.getElem?_eq_some_iff.1 Hs.member).1
    rw [R.bs] at h0
    exact Nat.le_of_lt h0
  have hr := reach_T h R hlen hT
  obtain ⟨_, _, _, _, _, _, hz⟩ := front_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl
    _ _ (open8_at hg) hr hu hon e
  have St := stated_at_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl _ _ (open8_at hg) hr
    hu hon e hd5' G'
  have hD := mask_behind (s := s) (own := h.𝔇.pubD.N.sent (2 * g + 1) 0)
    (rdOf := fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v)) hS.1 att' G' h.𝔇.St.at1 St.mask ds'
  obtain ⟨MP, MU, M5, MV, M7, M8⟩ := meets_head h hL hg ha hx (honest (mgAtAll h) ans test) rfl rfl
    _ _ (open8_at hg) hr hu hon Hs Sc hT hS.1 e hz hh hP ds' hgL hin
  have hpairs : a.own.pairs ≠ 0 := by
    have h0 := Dc.plan
    unfold P.planOk at h0
    simp only [Bool.and_eq_true, bne_iff_ne] at h0
    have ex : (parAt Zp g a).own = a.own := Hs.own.trans (by rw [hP])
    rw [← ex]
    exact h0.1.2
  exact sayAt_member Hs Sc hT hd hS.1 e hD hz hh hP (public_at_head h hg ha) hpairs
    (atIdn_of_thr T hV hT) hgL hin MP MU M5 MV M7 M8

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sayOwedT_of
