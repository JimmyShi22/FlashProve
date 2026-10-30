-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Idn12/SayOwedT2.lean: CONDITIONAL: the twin of `sayOwedT_of`
(Honest/K5/Law/SayOwedT.lean) WITHOUT THE PREMISE THAT THE INPUT's CELLS MEET THE LIBRARY's THREE
FAMILIES OF IDENTITIES (`IdnOwed`): along every step of the member at an attention segment's own
rounds (kind K5), at every continuation, what the claims say holds in the item's own world
(`SayOwedT`, Honest/K5/Law/DebtsT.lean), WITH THE `Thread` T A VARIABLE.

What stands in that premise's stead. The first two families, and the batch of the third at the
lookup's point, are drawn from three items that the kind's row asks in front (`idn12_T`,
Honest/K5/Law/Idn12/AskedT.lean; `rider_T`, Honest/K5/Law/Idn12/RiderT.lean). They cost: the test
T.fits (what the row asks is open), WHICH THE OLDER LAW DID NOT TAKE, and `HoldsOwed` (at every
valid input the cells that the honest side's letters lay for it hold an index). `K5Script` was
there.

  `sayOwedT_of₂`   CONDITIONAL: **`SayOwedT`**, by `sayAt_member₂`
                   (Honest/K5/Law/Idn12/SayMember2.lean)

Limits. Conditional. `K5Script` is shown by nobody; `HoldsOwed` of no `valid`. The older law stands
beside this one. At the library's full size and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.RiderT
import Johnson.Desc.ProofFile.Honest.K5.Law.Idn12.SayMember2
import Johnson.Desc.ProofFile.Honest.K5.Law.SayOwedT

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
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **THE NAMED PREMISE `SayOwedT`, WITHOUT `IdnOwed`.** T IS A VARIABLE. CONDITIONAL: under the
hypothesis h, `K5AtT`, g below 12 and the group's plan, `K5Seated`, the test T.fits, Sc
(`K5Script`), WHICH IS NOT SHOWN, hP, and hH (`HoldsOwed`), WHICH IS SHOWN OF NO `valid`. -/
theorem sayOwedT_of₂ {n : Nat} (hg : g < 12) {a : Attention.Plan}
    (ha : (P5J.At.X Zp).A[g]? = some a) {cells : Tr → Cells} {Z5 : Seat5}
    {blk : Block TS ProofFile.Cl} (Hs : K5Seated T (borderOf g) cells Z5 (parAt Zp g a) blk)
    (hfit : T.fits n = true) (hb : borderOf g < n)
    (Sc : K5Script T (borderOf g) cells Z5 a blk (h.𝔇.pubD.N.sent (2 * g + 1) 0)
      fun v => seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (wt v))
    (hP : Z5.P = ⟨a.S, a.own⟩) (hH : HoldsOwed T.valid cq) :
    SayOwedT h T wt g a := by
  intro blk' k s s' m E ds y cols hmem hT hd hS ds' att hd5 G gL e hgL es i K hin
  obtain rfl : blk = blk' := Option.some.inj (Hs.member.symm.trans hmem)
  obtain ⟨Pl, Dc⟩ := decides_T h A hg ha Hs.member
  obtain ⟨att', hd5', G', e', hh, es'⟩ := behind_is T Hs Dc hd hS
  obtain rfl : att' = att := by
    rw [e] at e'
    cases e'
    rfl
  obtain ⟨rfl, rfl, -, -⟩ := P.behind_inj (es'.symm.trans es)
  obtain ⟨L, hL⟩ := P5J.At.laid_some Zp h.opts.laid
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨hu, hon⟩ := onAt_T h A hg hT
  have hlen : borderOf g ≤ cF.blocksInOrder.length := by
    have h0 := (List.getElem?_eq_some_iff.1 Hs.member).1
    rw [A.bs] at h0
    exact Nat.le_of_lt h0
  have hr := reach_T h A hlen hT
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
  have I12 := idn12_T h A hg ha Hs hfit hb Sc hP hH hT
  exact sayAt_member₂ Hs Sc hT hd hS.1 e hD hz hh hP (public_at_head h hg ha) hpairs
    ⟨I12.1, I12.2⟩ hgL (rider_T h A hg ha Hs hfit hb Sc hP hT e hgL) hin MP MU M5 MV M7 M8

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.sayOwedT_of₂
