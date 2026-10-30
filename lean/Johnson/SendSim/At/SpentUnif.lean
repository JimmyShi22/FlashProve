-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/SpentUnif.lean: under three public premises, every function that connects cutAll
at the entries by which an address spends with the instance's coins (SpentBack) maps uniform values
at the spent names to uniform runs. The proof of Spec.spentUnif.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; sender, readC,
name, number: Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. A statement on distributions of coins alone: no row's message, symbol or
answer of a sender is in it.
  spentUnif           Spec.spentUnif, which is written out, with its three premises and SpentBack,
                      in Johnson/SendSim/At/CutTie.lean.
  back_inj, back_onto   A function with SpentBack is injective, if the job fits its place and
                      WithinAt holds. It is surjective, if WithinAt and MaskSpender or FoldSpender
                      hold.
  apart_spent         Under MaskSpender or FoldSpender, the entries by which p spends share no
                      number, in either field (ApartAll).
  cut_onto            If the job fits its place, every family of values at a set of names in CoinN
                      is the instance's cut of readC c for some coins c of the sender.

Limits. The conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it is proved. A bijection between finite sets maps the uniform distribution to the uniform
distribution (map_unif_of_bijective, Prob/Linear.lean). back is surjective because every family of
runs is cut off some coins, since the entries share no number (cutAll_onto,
Johnson/SendSim/At/Runs.lean); here MaskSpender's field apart is used. back is injective because two
values of the coins with the same cutAll have the same coin at each spent number (cutAll_tells, in
the same file), and the number of a name in spentN is a spent number.

How it fits. rowsFresh (Johnson/SendSim/At/RowsFresh.lean) takes spentUnif as an argument of
rowsFresh_of_core (Johnson/SendSim/At/JoinRows.lean). Johnson/SendSim/At/FoldAnyRoad.lean uses
back_inj, and Johnson/SendSim/At/CoinsFresh.lean uses apart_spent. MaskSpender and FoldSpender are
two of the three cases of SpenderClear (Johnson/SendSim/At/Fresh.lean, "clear").
-/
import Prob.Linear
import Johnson.SendSim.At.Runs

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc Prob
open Johnson.Prover.Send (shapeAt)

variable {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}

/-- Under MaskSpender or FoldSpender at o and p, no two of the entries by which p spends share a
number, in either field. -/
theorem apart_spent (h : MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p) :
    ApartAll (Bk.spentBy o p) := by
  rcases h with M | F
  · refine List.Pairwise.imp_of_mem (fun {e e'} he _ hd => ⟨hd, ?_⟩) M.apart
    have h0 : fOf e = ∅ := Finset.eq_empty_of_forall_notMem fun i hi => by
      have := mem_fAll _ e he i hi
      rw [M.noF] at this
      exact absurd this (Finset.notMem_empty _)
    rw [h0]
    exact Finset.disjoint_empty_left _
  · obtain ⟨_, _, e, _, _, _, hsp, _⟩ := F.one
    unfold ApartAll
    rw [hsp]
    exact List.pairwise_singleton _ _

/-- If the job fits its place (sendFits), every family u of values at a set U of names in CoinN is
the instance's cut at U of readC c, for some coins c of the sender. -/
theorem cut_onto (hf : sendFits P ride = true) (U : Finset (CoinN P ride)) (u : ↥U → GF) :
    ∃ c : Cs (dueR P ride), (sender P ride).cut U (readC P ride c) = u := by
  classical
  obtain ⟨c, hc⟩ := readOnto P ride hf
    ((fun n => if h : n ∈ U then u ⟨n, h⟩ else 0, fun _ _ => 0) : (sender P ride).Coins)
  refine ⟨c, funext fun n => ?_⟩
  show (readC P ride c).1 n.1 = u n
  rw [hc]
  exact dif_pos n.2

variable (back : (↥(spentN P ride Bk o p) → GF) → CsAll ((Bk.spentBy o p).map Ahead.named))
  (hb : SpentBack P ride Bk o p back)

include hb in
/-- If WithinAt holds and MaskSpender or FoldSpender holds at o and p, a function back with
SpentBack is surjective. -/
theorem back_onto (hW : WithinAt P ride Bk ord o p)
    (h : MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p) :
    Function.Surjective back := fun v => by
  obtain ⟨c, hc⟩ := cutAll_onto (d := dueR P ride) (Bk.spentBy o p) (fun e he => hW e (.inl he))
    (apart_spent h) v
  exact ⟨_, Option.some.inj ((hb c).symm.trans hc)⟩

include hb in
/-- If the job fits its place (sendFits) and WithinAt holds, a function back with SpentBack is
injective. -/
theorem back_inj (hf : sendFits P ride = true) (hW : WithinAt P ride Bk ord o p) :
    Function.Injective back := fun u u' e => by
  obtain ⟨c, hc⟩ := cut_onto hf _ u
  obtain ⟨c', hc'⟩ := cut_onto hf _ u'
  have hcut : cutAll c (Bk.spentBy o p) = cutAll c' (Bk.spentBy o p) := by
    rw [hb c, hb c', hc, hc', e]
  obtain ⟨tf, te⟩ := cutAll_tells c c' _ (fun e he => hW e (.inl he)) hcut
  rw [← hc, ← hc']
  funext n
  show coinAt P ride c n.1.1 (seatC P ride n.1) = coinAt P ride c' n.1.1 (seatC P ride n.1)
  have hn := (mem_namesOf _ _ n.1).1 n.2
  unfold inNos at hn
  unfold coinAt
  by_cases hE : (seatC P ride n.1).1.inE (shapeAt P n.1.1) = true
  · rw [if_pos hE] at hn
    rw [if_pos hE, if_pos hE, te _ hn]
  · rw [if_neg hE] at hn
    rw [if_neg hE, if_neg hE, tf _ hn]

open Classical in
/-- Proof of Spec.spentUnif: back is a bijection, by back_inj and back_onto. -/
theorem spentUnif : Spec.spentUnif := by
  intro P ride Bk ord o p hf hW h back hb
  exact map_unif_of_bijective ⟨back_inj back hb hf hW, back_onto back hb hW h⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.spentUnif
