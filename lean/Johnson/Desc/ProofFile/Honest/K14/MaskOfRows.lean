-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskOfRows.lean: kind K14: AN IMPLICATION: FROM THE SHARED
SENDING's OWNER's SENTENCE AT THE ROWS (Spec.rowsFreshAny, Johnson/SendSim/At/FoldAny.lean: at a
riding table of any number of rows) TO MaskApart (Honest/K14/MaskStated.lean) at this kind's part of
"send o_u". THE PREMISE IS NOT PROVED IN THIS FILE. No property is claimed.

  twoBook         a MADE-UP book of two entries: the first mask's coefficients, spent; o_u's own
                  coins, carried to the same part. It serves the call of the premise and nothing
                  else: no book of a description is meant
  two_spent, two_known   what it hands
  mask_room, two_within, two_fold   the premise's two sentences on the book hold at it
  fresh_at_count  the premise, read at a count that is equal to the shared part's
  maskApart_of_rows   **Spec.rowsFreshAny → MaskApart**

How. The premise is called ONCE, at the data made of the job's vector at the stand in front of the
part, at twoBook. It gives the distribution of three things together: the run that is spent; what
the shared sending's two moves show at these data; o_u's own coins. What this kind's part shows is a
function of the last two: its first round is the shared sending's first (shows_first,
Honest/K14/MaskTie.lean), its second round hangs on o_u's own coins alone (u_answers_below). So the
equation carries over (Prob.map_eq_of_factor). No premise on what was heard is needed.
Limits. Those of MaskApart's docstring. Nothing on a description's book. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.MaskTie
import Johnson.Desc.ProofFile.Honest.K14.MaskStated
import Johnson.SendSim.At.FoldAny
import Johnson.SendSim.At.SeatedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- An instance of the library (Cb.instNonemptyPGD, Cb/Obj/LdObjectReqStd.lean) is offered to every
-- search for Nonempty and sends it after a field that nothing determines; it is struck here.
attribute [-instance] Cb.instNonemptyPGD

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open OnBytes.Slice (GE GF)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.K1 (Ride dueR startR maskStart)
open OnBytes.SendSim.At (Spec.rowsFreshAny FoldSpenderAny WithinAt shownR budAt eAll eOf
  maskTailNo draws_send)

/-- **A made-up book of two entries**: a run of len coins from the number first on, spent; the coins
in front of it, carried to the same part. -/
def twoBook (first len : Nat) : ProverCoinCounts :=
  { first := [], shared := [], second := [], cuts := []
    ahead := [{ name := "the run", owner := ⟨sendPlace 2, 0⟩, start := ⟨0, first⟩
                count := ⟨0, len⟩, spender := ⟨sendPlace 5, 0⟩, once := true },
              { name := "in front", owner := ⟨sendPlace 2, 0⟩, start := ⟨0, 0⟩
                count := ⟨0, first⟩, spender := ⟨sendPlace 5, 0⟩, once := false }] }

/-- What it hands as spent. -/
theorem two_spent (first len : Nat) :
    (twoBook first len).spentBy ⟨sendPlace 2, 0⟩ ⟨sendPlace 5, 0⟩ =
      [{ name := "the run", owner := ⟨sendPlace 2, 0⟩, start := ⟨0, first⟩
         count := ⟨0, len⟩, spender := ⟨sendPlace 5, 0⟩, once := true }] := by
  simp [ProverCoinCounts.spentBy, twoBook]

/-- What it hands beside. -/
theorem two_known (first len : Nat) :
    (twoBook first len).knownBy [] ⟨sendPlace 2, 0⟩ ⟨sendPlace 5, 0⟩ =
      [{ name := "in front", owner := ⟨sendPlace 2, 0⟩, start := ⟨0, 0⟩
         count := ⟨0, first⟩, spender := ⟨sendPlace 5, 0⟩, once := false }] := by
  simp [ProverCoinCounts.knownBy, twoBook]

/-- The premise, read at a count that is equal to the shared part's. -/
theorem fresh_at_count (H : Spec.rowsFreshAny) (P : VerifiableInference.Desc.K1.Par)
    (ride : Nat → Option Ride) (data : Nat → Nat → Nat → Option (GF ⊕ GE))
    (ds : List Fmt.Drawn) (asks : List (List (List Nat))) (Bk : ProverCoinCounts) (ord : List Place)
    (o p : Addr) (h1 : ProofFile.Honest.K1.sendFits P ride = true)
    (h2 : ProofFile.Honest.K1.seedsFit P ds = true)
    (h3 : ∀ s ∈ ProofFile.Honest.K1.seedsAt P ds, OnBytes.Slice.readE s.2 ≠ 0) (h4 : budAt P asks)
    (h5 : WithinAt P ride Bk ord o p) (h6 : FoldSpenderAny P ride Bk ord o p) {d : Due}
    (hd : dueR P ride = d) :
    (Prob.unif (Cs d)).map (fun c =>
        (cutAll c (Bk.spentBy o p), shownR P 0 ride data ds asks (recount hd c),
          cutAll c (Bk.knownBy ord o p))) =
      (Prob.unif (CsAll ((Bk.spentBy o p).map Ahead.named) × Cs d)).map fun a =>
        (some a.1, shownR P 0 ride data ds asks (recount hd a.2),
          cutAll a.2 (Bk.knownBy ord o p)) := by
  subst hd
  exact H P 0 ride data ds asks Bk ord o p h1 h2 h3 h4 h5 h6

section
variable (A : SendPub) (s : OnBytes.Params.IoppStage) (hfit : sendingsFit A.P = true)
  (hm : A.P.S.masksAhead = true) (hs : A.P.S.testU.head? = some s)

include hfit hm hs in
/-- The first mask's coefficients lie within the part's count. -/
theorem mask_room : maskFirstCoin A + (2 * s.k + 1) ≤ (sendingPart (jobU A)).takes.e := by
  have h := room_tie (jobU A) 1 (by rw [u_two A hfit hm]; omega)
  rw [u_sort1 A s hs 0] at h
  have e : dueOf (jobU A).Q.codes (shapeAt (jobU A).Q 1) (.fresh s.k s.h) = 2 * s.k + 1 +
      (shapeAt (jobU A).Q 1).maskRows *
        ((jobU A).Q.codes.mask.getD (shapeAt (jobU A).Q 1).maskCode default).r := rfl
  rw [e] at h
  unfold maskFirstCoin
  omega

include hfit hm hs in
/-- Every entry of the made-up book lies within the shared part's count. -/
theorem two_within :
    WithinAt (jobU A).Q (rideBySort (jobU A)) (twoBook (maskFirstCoin A) (2 * s.k + 1)) []
      ⟨sendPlace 2, 0⟩ ⟨sendPlace 5, 0⟩ := by
  have hr := mask_room A s hfit hm hs
  intro e he
  rw [two_spent, two_known, due_tie (jobU A) (fit_u A hfit)] at *
  simp only [List.mem_singleton] at he
  rcases he with rfl | rfl
  · exact ⟨Nat.zero_le _, hr⟩
  · refine ⟨Nat.zero_le _, ?_⟩
    show 0 + maskFirstCoin A ≤ _
    omega

include hfit hm hs in
/-- The made-up book's spender spends the riding table's coefficients; none of them, and no coin of
a tail of that table, is handed beside. -/
theorem two_fold :
    FoldSpenderAny (jobU A).Q (rideBySort (jobU A)) (twoBook (maskFirstCoin A) (2 * s.k + 1)) []
      ⟨sendPlace 2, 0⟩ ⟨sendPlace 5, 0⟩ := by
  have hJ := fit_u A hfit
  have h2 := u_two A hfit hm
  have hf := msg_fits (jobU A) hJ 1 (by omega)
  rw [u_sort1 A s hs 0] at hf
  simp only [msgShapeFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hf
  obtain ⟨⟨⟨⟨⟨⟨-, ha⟩, hmr⟩, -⟩, -⟩, -⟩, -⟩ := hf
  have hst : maskStart (jobU A).Q (rideBySort (jobU A)) 1 = maskFirstCoin A := by
    rw [maskStart_ride (jobU A).Q (rideBySort (jobU A)) 1 hmr ha,
      start_tie (jobU A) hJ 1 (by omega)]
    rfl
  refine ⟨⟨1, ⟨s.k, s.h⟩, _, by omega, ride_fresh (jobU A) 1 s.k s.h (u_sort1 A s hs 0),
    two_spent _ _, rfl, hst.symm, fun r _ q _ hmem => ?_⟩, ?_⟩
  · rw [two_known] at hmem
    unfold maskTailNo at hmem
    rw [hst] at hmem
    simp only [eAll, eOf, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      Finset.mem_Ico] at hmem
    omega
  · rw [two_spent, two_known]
    refine Finset.disjoint_left.2 fun n h1 h2 => ?_
    simp only [eAll, eOf, List.foldr_cons, List.foldr_nil, Finset.union_empty,
      Finset.mem_Ico] at h1 h2
    omega

end

/-- **Spec.rowsFreshAny → MaskApart.** The premise is not proved here. -/
theorem maskApart_of_rows (H : Spec.rowsFreshAny) : MaskApart := by
  intro S Cl X Pb W₀ Rc Ky A s hfit hm hs wit sim φ σ hrow hr hd u hu sp ca m ds asks hds hb
  rw [members_send σ _ sim hrow, List.mem_singleton] at hu
  subst hu
  have hJ := fit_u A hfit
  have hds' : drawsFit (VerifiableInference.Desc.K1.rounds (jobU A).Q) ds = true := by
    obtain ⟨d₀, d₁, os, h1, h2, -⟩ := hd.rounds
    have e : ((σ.block.rounds.zip σ.block.oracles).take 2).map (·.1) = σ.block.rounds := by
      rw [h1, h2]
      rfl
    rw [← hr, ← e]
    exact hds
  obtain ⟨hseeds, hβ⟩ := draws_send (jobU A).Q hds'
  obtain ⟨x₀, x₁, rfl, -, -⟩ := drawsFit_two
    (d₀ := { entry := VerifiableInference.Desc.K1.seedEntry (jobU A).Q })
    (d₁ := { entry := VerifiableInference.Desc.K1.answerEntry (jobU A).Q }) hds'
  have law := fresh_at_count H (jobU A).Q (rideBySort (jobU A))
    (vecData (jobU A) { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
    (twoBook (maskFirstCoin A) (2 * s.k + 1)) [] ⟨sendPlace 2, 0⟩ ⟨sendPlace 5, 0⟩
    (fits_tie (jobU A) hJ) hseeds hβ hb (two_within A s hfit hm hs) (two_fold A s hfit hm hs)
    (due_tie (jobU A) hJ)
  rw [two_spent, two_known] at law
  have step : (Prob.unif (Cs (sendingPart (jobU A)).takes)).map (fun c =>
        (c.cut ⟨0, maskFirstCoin A⟩ ⟨0, 2 * s.k + 1⟩,
          σ.shows φ (sendingMember σ (jobU A) wit sim) (c, (), ()) m [x₀, x₁] asks,
          c.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩)) =
      (Prob.unif ((Cs ⟨0, 2 * s.k + 1⟩ × Unit) × Cs (sendingPart (jobU A)).takes)).map fun a =>
        (some a.1.1, σ.shows φ (sendingMember σ (jobU A) wit sim) (a.2, (), ()) m [x₀, x₁] asks,
          a.2.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩) := by
    refine Prob.map_eq_of_factor _ _ (fun c a hg => ?_) law
    have g1 := congrArg Prod.fst hg
    have g2 : shownR (jobU A).Q 0 (rideBySort (jobU A))
        (vecData (jobU A) { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
        (recount (due_tie (jobU A) hJ) c) =
      shownR (jobU A).Q 0 (rideBySort (jobU A))
        (vecData (jobU A) { input := wit m.st.input, heard := m.st.heard, own := () }) [x₀, x₁] asks
        (recount (due_tie (jobU A) hJ) a.2) := congrArg (fun y => y.2.1) hg
    have g3 := congrArg (fun y => y.2.2) hg
    simp only [cutAll_single] at g1 g3
    have g1' : (c.cut ⟨0, maskFirstCoin A⟩ ⟨0, 2 * s.k + 1⟩).map (fun x => (x, ())) = some a.1 := g1
    have g3' : (c.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩).map (fun x => (x, ())) =
        (a.2.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩).map fun x => (x, ()) := g3
    have k1 : c.cut ⟨0, maskFirstCoin A⟩ ⟨0, 2 * s.k + 1⟩ = some a.1.1 := by
      cases hc : c.cut ⟨0, maskFirstCoin A⟩ ⟨0, 2 * s.k + 1⟩ with
      | none =>
        rw [hc] at g1'
        cases g1'
      | some x =>
        rw [hc] at g1'
        exact congrArg (fun z => some z.1) (Option.some.inj g1')
    have k3 : c.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩ = a.2.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩ :=
      Option.map_injective (fun x y hxy => congrArg Prod.fst hxy) g3'
    refine Prod.ext k1 (Prod.ext ?_ k3)
    show σ.shows φ (sendingMember σ (jobU A) wit sim) (c, (), ()) m [x₀, x₁] asks =
      σ.shows φ (sendingMember σ (jobU A) wit sim) (a.2, (), ()) m [x₀, x₁] asks
    rw [shows_first (jobU A) hJ wit φ σ sim hd m x₀ x₁ asks c,
      shows_first (jobU A) hJ wit φ σ sim hd m x₀ x₁ asks a.2, g2,
      u_answers_below A s hfit hm hs (wit m.st.input) m.st.heard x₀ c a.2 k3]
  refine step.trans ?_
  have e : (fun a : (Cs ⟨0, 2 * s.k + 1⟩ × Unit) × Cs (sendingPart (jobU A)).takes =>
      (some a.1.1, σ.shows φ (sendingMember σ (jobU A) wit sim) (a.2, (), ()) m [x₀, x₁] asks,
        a.2.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩)) =
      (fun a : Cs ⟨0, 2 * s.k + 1⟩ × Cs (sendingPart (jobU A)).takes =>
        (some a.1, σ.shows φ (sendingMember σ (jobU A) wit sim) (a.2, (), ()) m [x₀, x₁] asks,
          a.2.cut ⟨0, 0⟩ ⟨0, maskFirstCoin A⟩)) ∘
        (Equiv.prodCongr (Equiv.prodPUnit (Cs ⟨0, 2 * s.k + 1⟩))
          (Equiv.refl (Cs (sendingPart (jobU A)).takes))) := rfl
  rw [e]
  exact (PMF.map_comp _ _ _).symm.trans (congrArg (PMF.map _) (Prob.map_unif_equiv _))

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.two_spent
#print axioms ProofFile.Honest.K14.two_known
#print axioms ProofFile.Honest.K14.fresh_at_count
#print axioms ProofFile.Honest.K14.mask_room
#print axioms ProofFile.Honest.K14.two_within
#print axioms ProofFile.Honest.K14.two_fold
#print axioms ProofFile.Honest.K14.maskApart_of_rows
