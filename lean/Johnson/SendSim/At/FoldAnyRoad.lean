-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FoldAnyRoad.lean: the implication from the general model to fresh at the level of
rows for a spender of a table of any number of rows. Spec.sendFresh and Spec.readUnif imply
Spec.rowsFreshAny. It claims no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; for the instance,
its names and slots, Johnson/SendSim/At/Bridge.lean, "Terms of the instance". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. p is an address that satisfies FoldSpenderAny.
  rowsFreshAny_of_core   Spec.sendFresh and Spec.readUnif imply Spec.rowsFreshAny.
  spentTieAny       If WithinAt holds, the runs that cutAll returns at the spent entry are a
                    function of the instance's coins at the spent names (SpentBack). Pointwise.
  spentUnifAny      If the job fits its place (sendFits) and WithinAt holds, every such function
                    maps uniform values at the spent names to uniform runs.
  spent_inMsg_any   A slot within the sizes (Seat.ok) whose coin p spends is not a tail's slot.
                    Pointwise.
  apart_any         The one spent entry shares no coin's number with another.

Limits.
rowsFreshAny_of_core is an implication only, and this file does not apply it: Spec.rowsFreshAny is
proved in Johnson/SendSim/At/FreshWideProofs.lean.
spentUnifAny concludes an equation between distributions, but only of coins: no message of a sender
is in it. It is a tool for rowsFreshAny_of_core and not a result of its own.
The conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. FoldSpenderAny and Spec.rowsFreshAny are in Johnson/SendSim/At/FoldAny.lean, SpentBack
in Johnson/SendSim/At/CutTie.lean. Johnson/SendSim/At/FreshWideProofs.lean applies
rowsFreshAny_of_core to the theorems sendFresh (Johnson/SendSim/CoreProofs.lean) and readUnif
(Johnson/SendSim/At/ReadUnif.lean), which gives rowsFreshAny. The proofs use fresh_leg
(Johnson/SendSim/At/JoinRows.lean), mendsOffOfAny (Johnson/SendSim/At/FoldAny.lean), back_inj
(Johnson/SendSim/At/SpentUnif.lean), cutAll_onto (Johnson/SendSim/At/Runs.lean) and cutAll_congr,
cutAll_some, ce_names, cf_names (Johnson/SendSim/At/CutProof.lean).
-/
import Johnson.SendSim.At.FoldAny
import Johnson.SendSim.At.SpentUnif
import Johnson.SendSim.At.JoinRows

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (shapeAt)

variable {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}

/-- If FoldSpenderAny holds, a slot within the sizes (hy) whose coin's number is among the spent
numbers is not a tail's slot. -/
theorem spent_inMsg_any (F : FoldSpenderAny P ride Bk ord o p) (k : ℕ) (y : Seat)
    (hy : y.ok P.codes (shapeAt P k) (ride k))
    (hin : inNos (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p)) (y.inE (shapeAt P k))
      (y.no P ride k)) : inMsg y = true := by
  unfold inNos at hin
  obtain ⟨k', R, e, _, hr, hsp, hc, hst, _⟩ := F.one
  cases hE : y.inE (shapeAt P k)
  · rw [hE, hsp] at hin
    simp [fAll, fOf, hc] at hin
  · rw [hE, if_pos rfl, hsp] at hin
    simp only [eAll, List.foldr_cons, List.foldr_nil, Finset.union_empty, eOf, hc, hst,
      Finset.mem_Ico] at hin
    obtain ⟨i, hi⟩ : ∃ i, y.no P ride k = maskStart P ride k' + i :=
      ⟨_, (Nat.add_sub_cancel' hin.1).symm⟩
    have hy' : (Seat.mask i).ok P.codes (shapeAt P k') (ride k') := by
      show i < (stepsOf P.codes (shapeAt P k') (ride k')).mask
      have : i < R.count := by omega
      simpa [stepsOf, hr] using this
    rw [(seat_inj P ride k k' y (.mask i) hy hy' hE (by rw [no_mask]; exact hi)).2]
    rfl

/-- If WithinAt and FoldSpenderAny hold, there is a function back that satisfies SpentBack: for all
coins, the runs that cutAll returns at the spent entry are back applied to the instance's coins at
the spent names. -/
theorem spentTieAny (hW : WithinAt P ride Bk ord o p) (F : FoldSpenderAny P ride Bk ord o p) :
    ∃ back, SpentBack P ride Bk o p back := by
  have hF : Function.FactorsThrough
      (fun c : Cs (dueR P ride) => cutAll c (Bk.spentBy o p))
      (fun c : Cs (dueR P ride) =>
        (sender P ride).cut (spentN P ride Bk o p) (readC P ride c)) := by
    intro c c' e
    have h1 : ∀ n ∈ namesOf P ride (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p)),
        (readC P ride c).1 n = (readC P ride c').1 n := fun n hn => congrFun e ⟨n, hn⟩
    have h2 : ∀ x ∈ tailsOf P ride (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p)),
        (readC P ride c).2 x.1 x.2 = (readC P ride c').2 x.1 x.2 := fun x hx => by
      exfalso
      have hm := spent_inMsg_any F x.1.1 (seatT P x.1 x.2.val).1 (seatT_ok P ride x.1 x.2)
        ((mem_tailsOf _ _ x).1 hx)
      obtain ⟨⟨k, v⟩, q⟩ := x
      rcases v with v | v <;> cases hm
    exact cutAll_congr c c' _ (fun i hi => cf_names _ _ c c' h1 h2 i hi)
      fun i hi => ce_names _ _ c c' h1 h2 i hi
  obtain ⟨back, hb⟩ := (Function.factorsThrough_iff _).1 hF
  refine ⟨fun v => (back v).getD default, fun c => ?_⟩
  obtain ⟨v, hv⟩ := cutAll_some c (Bk.spentBy o p) fun e he => hW e (.inl he)
  have e := congrFun hb c
  simp only [Function.comp] at e
  show cutAll c (Bk.spentBy o p) =
    some ((back ((sender P ride).cut (spentN P ride Bk o p) (readC P ride c))).getD default)
  rw [← e, hv]
  rfl

/-- If FoldSpenderAny holds, no two spent entries share a coin's number: there is one entry. -/
theorem apart_any (F : FoldSpenderAny P ride Bk ord o p) : ApartAll (Bk.spentBy o p) := by
  obtain ⟨_, _, e, _, _, hsp, _⟩ := F.one
  unfold ApartAll
  rw [hsp]
  exact List.pairwise_singleton _ _

open Classical in
/-- If the job fits its place and WithinAt and FoldSpenderAny hold, every function that satisfies
SpentBack maps uniform values at the spent names to uniform runs. An equation between distributions
of coins only: a tool for rowsFreshAny_of_core, not a result of its own. -/
theorem spentUnifAny (hf : sendFits P ride = true) (hW : WithinAt P ride Bk ord o p)
    (F : FoldSpenderAny P ride Bk ord o p)
    (back : (↥(spentN P ride Bk o p) → GF) → CsAll ((Bk.spentBy o p).map Ahead.named))
    (hb : SpentBack P ride Bk o p back) :
    (unif (↥(spentN P ride Bk o p) → GF)).map back =
      unif (CsAll ((Bk.spentBy o p).map Ahead.named)) := by
  refine map_unif_of_bijective ⟨back_inj back hb hf hW, fun v => ?_⟩
  obtain ⟨c, hc⟩ := cutAll_onto (d := dueR P ride) (Bk.spentBy o p) (fun e he => hW e (.inl he))
    (apart_any F) v
  exact ⟨_, Option.some.inj ((hb c).symm.trans hc)⟩

/-- Spec.sendFresh and Spec.readUnif imply Spec.rowsFreshAny. An implication only; the premises are
proved as sendFresh in Johnson/SendSim/CoreProofs.lean and as readUnif in
Johnson/SendSim/At/ReadUnif.lean. -/
theorem rowsFreshAny_of_core (hFr : Spec.sendFresh) (hU : Spec.readUnif) : Spec.rowsFreshAny := by
  intro P first ride data ds asks Bk ord o p hf hs hβ hb hW F
  obtain ⟨bs, hbs⟩ := spentTieAny hW F
  exact fresh_leg hFr hU P first ride data ds asks Bk ord o p hf hs hβ hb
    (mendsOffOfAny P ride ds Bk ord o p hf hβ F) bs hbs (spentUnifAny hf hW F bs hbs)

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.spentTieAny
#print axioms OnBytes.SendSim.At.spentUnifAny
#print axioms OnBytes.SendSim.At.rowsFreshAny_of_core
