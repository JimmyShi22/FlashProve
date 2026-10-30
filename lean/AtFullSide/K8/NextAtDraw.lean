-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K8/NextAtDraw.lean: the form with the third family at the 25 draws of the smallness test
(the kind K8). The table's step at a draw has no test on values, so the two debts of a member on the
road of the family shapeJ follow from the table's two laws. The kind's own tests on values are not
here: they stand at two later members, 14 l + 9 and 14 l + 10 (347, 348 at the head), in the cells of
the batching and of the step behind it, and they are owed there.

  k8_vals        the table's test on values at a draw says yes of everything
  k8_values, k8_valuesJ   so Values and ValuesJ hold at a draw for nothing, at every thread, Said,
                 family and fall: at a draw the verifier tests no value
  k8_nextJ       the family one member on
  k8_acceptedJ   the member's yes with the family in hand

Limits. Premises: the head; hB, the base of the public part; T.bs = cF.blocksInOrder; hyes, the run on shapes
over the 358 members; at k8_acceptedJ that the honest side fits the member. Nothing here says that the
family holds at any state.
-/
import AtFullSide.K8.KeepsBehind
import Johnson.AtFull.Shape.RuleAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K8.Term
open VerifiableInference.Desc (Chain KindName Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (drawAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest
open Johnson.AtFull.Shape

/-- **At a draw the table has no test on values.** -/
theorem k8_vals (Zp : ProofFile.Pub) (G : ProofFile.Ground) {l : Nat} (hl : l ≤ 24) (s : S) (rs : List Fmt.RoundView)
    (cs : List (List (Nat × List UInt64))) : Tab.vals Zp G (drawAt l) s rs cs = true := by
  have hd : (Tab.draw Zp G l).2 s rs cs = true := by
    unfold Tab.draw
    split <;> rfl
  unfold Tab.vals
  rcases drawAt_cases l with ⟨rfl, e⟩ | ⟨h2, e⟩
  · rw [e, cells_head Zp G 6 (by omega) rfl]
    exact hd
  · rw [e, cells_link Zp G l 5 (by omega) (by omega) rfl]
    exact hd

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}
  {V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **Values at a draw.** True for nothing: at a draw the verifier tests no value. -/
theorem k8_values (T : Thread Bk S ProofFile.Cl V W X Pb)
    (fall : Nat → S → List Fmt.Drawn → Option String) (g : Nat → ShA → Except String ShA)
    {l : Nat} (hl : l ≤ 24) :
    Values T (firstZA g (Tab.vals Zp Bs.G₀)) fall (drawAt l) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => k8_vals Zp Bs.G₀ hl _ _ _

/-- **The same with a family in hand.** -/
theorem k8_valuesJ (T : Thread Bk S ProofFile.Cl V W X Pb) (Said : Nat → Coins Bk → Mid W X → Prop)
    (J : Nat → S → Prop) (fall : Nat → S → List Fmt.Drawn → Option String)
    (g : Nat → ShA → Except String ShA) {l : Nat} (hl : l ≤ 24) :
    ValuesJ T Said J (firstZA g (Tab.vals Zp Bs.G₀)) fall (drawAt l) :=
  valuesJ_of T Said (k8_values T fall g hl)

/-- **The family one member on, at a member of the kind.** -/
theorem k8_nextJ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8) :
    NextJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b := by
  obtain ⟨l, hl, rfl⟩ := k8_number ha hk
  have hb : drawAt l < 358 := by
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨-, e⟩ <;> omega
  exact nextJ_of_shapeV T Said _ hb hyes
    (by rw [hbs]; exact carriesU_of_V (table_all h hB _ hb T.ft).1)
    (k8_valuesJ T Said _ fall _ hl)

/-- **The member's yes with the family in hand, at a member of the kind.** -/
theorem k8_acceptedJ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (T : Thread Bk S ProofFile.Cl V W X Pb) (hbs : T.bs = cF.blocksInOrder)
    (Said : Nat → Coins Bk → Mid W X → Prop)
    (fall : Nat → S → List Fmt.Drawn → Option String) (a₀ : ShA)
    (hyes : (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)).yes a₀ 358 = true)
    {b : Nat} {pl : Place} (ha : P5J.At.ps[b]? = some pl) (hk : pl.kind = KindName.K8)
    (hF : FitsAt T b) :
    AcceptedJ T Said (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀) fall b := by
  obtain ⟨l, hl, rfl⟩ := k8_number ha hk
  have hb : drawAt l < 358 := by
    rcases drawAt_cases l with ⟨-, e⟩ | ⟨-, e⟩ <;> omega
  exact acceptedJ_of_shapeV T Said _ hb hyes
    (by rw [hbs]; exact (table_all h hB _ hb T.ft).2) hF (k8_valuesJ T Said _ fall _ hl)

end

end AtFullSide.K8.Term

#print axioms AtFullSide.K8.Term.k8_vals
#print axioms AtFullSide.K8.Term.k8_values
#print axioms AtFullSide.K8.Term.k8_valuesJ
#print axioms AtFullSide.K8.Term.k8_nextJ
#print axioms AtFullSide.K8.Term.k8_acceptedJ
