-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/FreshWide.lean: the wider condition at one address (SpenderClearAny), which
allows a table of any number of rows that is sent along; the statements of fresh under it, at the
level of rows and at a Seated side; and the implications between them. It claims no property of the
protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean. Limits of the
folder: Johnson/SendSim/Defs.lean.

What this file has.
  SpenderClearAny     SpenderClear with FoldSpenderAny in the place of FoldSpender: the clause "the
                      table has one row" is dropped, and every other clause stays.
  Spec.rowsFreshWide  Spec.rowsFresh with SpenderClearAny in the place of SpenderClear: its other
                      five premises and its equation are the same.
  Spec.coinsFreshWide Spec.coinsFresh with the same change: an equation on the spent and the known
                      runs only.
  Spec.sendFreshAtPWide   Spec.sendFreshAtP with the same change: the field fresh at one address, at
                      every Seated side.
  rowsFreshWide_of    Proved here, by cases: Spec.rowsFresh and Spec.rowsFreshAny imply
                      Spec.rowsFreshWide.
  sendFreshAtPWide_of_rows   Proved here: Spec.rowsFreshWide and Spec.coinsFreshWide imply
                      Spec.sendFreshAtPWide.
  clearAny_of_clear   Proved here: SpenderClear implies SpenderClearAny.
  foldAnyB_iff, spenderClearAnyB_iff   Proved here: the executable tests foldAnyB and
                      spenderClearAnyB accept exactly if FoldSpenderAny and SpenderClearAny hold.
The three under Spec are statements only; proved under the same names, without "Spec.", in
Johnson/SendSim/At/FreshWideProofs.lean.

Limits. The implications have named propositions as premises, which this file does not prove, so it
proves no equation between distributions by itself. Each statement speaks of one owner and one
spender.

How it fits. SpenderClear and Spec.sendFreshAtP are in Johnson/SendSim/At/Fresh.lean ("clear"),
FoldSpenderAny and Spec.rowsFreshAny in Johnson/SendSim/At/FoldAny.lean, Spec.rowsFresh in
Johnson/SendSim/At/CutTie.lean, Spec.coinsFresh in Johnson/SendSim/At/JoinFresh.lean, the tests in
Johnson/SendSim/At/WideTest.lean. sendFreshAtPWide serves sendFreshAtWide
(Johnson/SendSim/Seat/HandedWideProofs.lean). The condition at all addresses, BookClearAny, is in
Johnson/SendSim/At/BookWide.lean.

Notes: why the wider condition. Spec.rowsFreshAny is only at the level of rows. SpenderClear has the
narrower FoldSpender, so Spec.sendFreshAtP is vacuous at the spender of a table of two rows that is
sent along.
-/
import Johnson.SendSim.At.FoldAny
import Johnson.SendSim.At.JoinFresh
import Johnson.SendSim.At.WideTest

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {S Cl V W X Pb : Type}

/-- The wider condition on the book at an owner o and one address p: p spends nothing of o's coins,
or MaskSpender holds, or FoldSpenderAny holds. It is SpenderClear without the clause "the table has
one row". -/
def SpenderClearAny (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr) : Prop :=
  Bk.spentBy o p = [] ∨ MaskSpender P ride Bk ord o p ∨ FoldSpenderAny P ride Bk ord o p

/-- SpenderClear implies SpenderClearAny. -/
theorem clearAny_of_clear {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts} {ord : List Place}
    {o p : Addr} (h : SpenderClear P ride Bk ord o p) : SpenderClearAny P ride Bk ord o p :=
  h.imp id (Or.imp id foldAny_of_fold)

/-- States Spec.rowsFresh with SpenderClearAny in the place of SpenderClear. If the job fits its
place, the challenge consists of exactly the seeds, no seed's factor is 0, the queried positions are
within the bound, WithinAt holds and p satisfies SpenderClearAny, then over uniform coins the triple
(the runs that p spends, shownR, the known runs) has the same distribution as when the first is
replaced by fresh uniform values, independent of the rest. Statement only; proved as rowsFreshWide
in Johnson/SendSim/At/FreshWideProofs.lean. -/
def Spec.rowsFreshWide : Prop :=
  ∀ (P : K1.Par) (first : Nat) (ride : Nat → Option Ride)
    (data : Nat → Nat → Nat → Option (GF ⊕ GE)) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    sendFits P ride = true → seedsFit P ds = true → (∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) →
    budAt P asks → WithinAt P ride Bk ord o p → SpenderClearAny P ride Bk ord o p →
    (Prob.unif (Cs (dueR P ride))).map (fun c =>
        (cutAll c (Bk.spentBy o p), shownR P first ride data ds asks c,
          cutAll c (Bk.knownBy ord o p))) =
      (Prob.unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride))).map fun a =>
        (some a.1, shownR P first ride data ds asks a.2, cutAll a.2 (Bk.knownBy ord o p))

/-- States Spec.coinsFresh with SpenderClearAny in the place of SpenderClear: if WithinAt and
SpenderClearAny hold at p, the same equation holds for the pair (the runs that p spends, the known
runs). Statement only; proved as coinsFreshWide in Johnson/SendSim/At/FreshWideProofs.lean. -/
def Spec.coinsFreshWide : Prop :=
  ∀ (P : K1.Par) (ride : Nat → Option Ride) (Bk : ProverCoinCounts) (ord : List Place) (o p : Addr),
    WithinAt P ride Bk ord o p → SpenderClearAny P ride Bk ord o p →
    (Prob.unif (Cs (dueR P ride))).map (fun c =>
        (cutAll c (Bk.spentBy o p), cutAll c (Bk.knownBy ord o p))) =
      (Prob.unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs (dueR P ride))).map fun a =>
        (some a.1, cutAll a.2 (Bk.knownBy ord o p))

/-- States that a Seated side has the field fresh of Good at one address p (FreshAtP, with the bound
budAt) if WithinAt and SpenderClearAny hold at p. Statement only; proved as sendFreshAtPWide in
Johnson/SendSim/At/FreshWideProofs.lean. -/
def Spec.sendFreshAtPWide : Prop :=
  ∀ (S Cl V W X Pb : Type) (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (J : SendJob W X) (Bk : ProverCoinCounts)
    (ord : List Place) (p : Addr), Seated σ J →
    WithinAt J.P J.ride Bk ord ⟨σ.block.place, 0⟩ p →
    SpenderClearAny J.P J.ride Bk ord ⟨σ.block.place, 0⟩ p →
    FreshAtP φ σ Bk ord (fun _ _ asks => budAt J.P asks) p

/-- Spec.rowsFresh and Spec.rowsFreshAny imply Spec.rowsFreshWide, by cases on SpenderClearAny. The
premises are proved as rowsFresh in Johnson/SendSim/At/RowsFresh.lean and as rowsFreshAny in
Johnson/SendSim/At/FreshWideProofs.lean. -/
theorem rowsFreshWide_of (H : Spec.rowsFresh) (HA : Spec.rowsFreshAny) : Spec.rowsFreshWide := by
  intro P first ride data ds asks Bk ord o p hf hs hβ hb hW hC
  rcases hC with h0 | hM | hF
  · exact H P first ride data ds asks Bk ord o p hf hs hβ hb hW (Or.inl h0)
  · exact H P first ride data ds asks Bk ord o p hf hs hβ hb hW (Or.inr (Or.inl hM))
  · exact HA P first ride data ds asks Bk ord o p hf hs hβ hb hW hF

/-- Spec.rowsFreshWide and Spec.coinsFreshWide imply Spec.sendFreshAtPWide. Both premises are proved
in Johnson/SendSim/At/FreshWideProofs.lean. -/
theorem sendFreshAtPWide_of_rows (H : Spec.rowsFreshWide) (H0 : Spec.coinsFreshWide) :
    Spec.sendFreshAtPWide := by
  intro S Cl V W X Pb φ σ J Bk ord p h hW hB u hu sp ca m ds asks hd hb _
  rw [members_seated h, List.mem_singleton] at hu
  subst hu
  rw [rounds_fst h] at hd
  have e : ∀ c : Cs (dueR J.P J.ride), σ.shows φ (memberAt σ J) (c, sp, ca) m ds asks =
      if sendFits J.P J.ride then
        some (shownR J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks c)
      else none := fun c => showsAt S Cl V W X Pb φ σ J h m ds asks c hd
  show (Prob.unif (Cs (dueR J.P J.ride))).map (fun c =>
      (cutAll c (Bk.spentBy ⟨σ.block.place, 0⟩ p), σ.shows φ (memberAt σ J) (c, sp, ca) m ds asks,
        cutAll c (Bk.knownBy ord ⟨σ.block.place, 0⟩ p))) =
    (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, 0⟩ p).map Ahead.named) ×
        Cs (dueR J.P J.ride))).map fun a =>
      (some a.1, σ.shows φ (memberAt σ J) (a.2, sp, ca) m ds asks,
        cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, 0⟩ p))
  simp only [e]
  by_cases hf : sendFits J.P J.ride = true
  · simp only [hf, if_true]
    have := congrArg (PMF.map fun t => (t.1, some t.2.1, t.2.2))
      (H J.P J.first J.ride (J.data m.st.input (frontOf m)) ds asks Bk ord ⟨σ.block.place, 0⟩ p hf
        (h.draws ds hd).1 (h.draws ds hd).2 hb hW hB)
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this
  · have hf' : sendFits J.P J.ride = false := by simpa using hf
    simp only [hf', Bool.false_eq_true, if_false]
    have := congrArg (PMF.map fun t => (t.1, (none : Option (List Shown)), t.2))
      (H0 J.P J.ride Bk ord ⟨σ.block.place, 0⟩ p hW hB)
    rw [PMF.map_comp, PMF.map_comp] at this
    exact this

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- foldAnyB accepts exactly if FoldSpenderAny holds. -/
theorem foldAnyB_iff {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} :
    foldAnyB P ride Bk ord o p = true ↔ FoldSpenderAny P ride Bk ord o p := by
  constructor
  · intro h
    simp only [foldAnyB, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, disjoint_of_allE h2⟩
    match hs : Bk.spentBy o p, h1 with
    | [e], h1 =>
      obtain ⟨k, hk, hb⟩ := List.any_eq_true.1 h1
      match hr : ride k, hb with
      | some R, hb =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hb
        refine ⟨k, R, e, List.mem_range.1 hk, hr, rfl, hb.1.1, hb.1.2,
          fun r hr' q hq => not_mem_eAll ?_⟩
        simpa using List.all_eq_true.1 (List.all_eq_true.1 hb.2 r (List.mem_range.2 hr')) q
          (List.mem_range.2 hq)
  · intro h
    obtain ⟨k, R, e, hk, hr, hs, hc, hst, ht⟩ := h.one
    simp only [foldAnyB, Bool.and_eq_true]
    refine ⟨?_, allE_of fun n hn => not_inE (Finset.disjoint_left.1 h.unknown hn)⟩
    rw [hs]
    refine List.any_eq_true.2 ⟨k, List.mem_range.2 hk, ?_⟩
    rw [hr]
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact ⟨⟨hc, hst⟩, List.all_eq_true.2 fun r hr' => List.all_eq_true.2 fun q hq =>
      not_inE (ht r (List.mem_range.1 hr') q (List.mem_range.1 hq))⟩

/-- spenderClearAnyB accepts exactly if SpenderClearAny holds. -/
theorem spenderClearAnyB_iff {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr} :
    spenderClearAnyB P ride Bk ord o p = true ↔ SpenderClearAny P ride Bk ord o p := by
  simp only [spenderClearAnyB, Bool.or_eq_true, List.isEmpty_iff, SpenderClearAny, foldAnyB_iff]
  constructor
  · rintro ((h0 | h1) | h2)
    · exact Or.inl h0
    · exact Or.inr (Or.inl (mask_of_test P ride h1))
    · exact Or.inr (Or.inr h2)
  · rintro (h0 | h1 | h2)
    · exact Or.inl (Or.inl h0)
    · exact Or.inl (Or.inr (test_of_mask P ride h1))
    · exact Or.inr h2

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.rowsFreshWide_of
#print axioms OnBytes.SendSim.At.sendFreshAtPWide_of_rows
#print axioms OnBytes.SendSim.At.spenderClearAnyB_iff
