-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshOwnerLaw.lean: kind K14: THE LAW ON THE COIN THAT "SPLIT"
SPENDS, IN THE FRAME's FORM OF A LAW AT A TEST ON THE BOOK (OwnerLaw, Honest/BookGuard.lean): at the
test spOwnerTest (Honest/K14/FreshOwner.lean), WITH THE GUARD BY NAME IN THE PREMISE.

  cutAll_apart    at a count without a coin of the base field, of low + len coins: two lists of
                  coins with the same cut of the first low coins have the same runs at entries of
                  which no coin lies in the run (low, len). Wider than cutAll_below
                  (Honest/K14/FreshField.lean): an entry of no coin, and an entry that lies wholly
                  beyond the count, are let through. (Kin: cutAll_congr, in the
                  files on the simulator of a sending: the cut reads the coins at the entries'
                  numbers alone: the wider sentence; it does not lie beneath this file)
  fits_gives      what spFits = true gives: oneSpender, the three premises on the shapes, that the
                  owner is the part's address, and withinCount
  sp_owner_law    **THE LAW**: OwnerLaw (spOwnerTest A n) (SpFresh A): NO PREMISE OUTSIDE THE FORM:
                  the three premises on the shapes are read off fits = true
  sp_owner_law'   the same at spOwner A, the value for a list of tests
  ownerLaw_pass, ownerLaw_pass_fits   from a law at a test to a law with another conclusion, where
                  mine, or fits, may be read
  sp_owner_law_any   the law at EVERY mine, all else as in spOwnerTest
  guardClear_of_tests, ok_of_tests   **the two tests of fresh_at_omega give the frame's form**:
                  where oneSpender and knownBelow accept, GuardClear holds at every spender that
                  spends; and, WHERE THE ADDRESS IS THE PART's, THE THREE TESTS ON THE PLAN ACCEPT
                  AND withinCount ACCEPTS TOO, OwnerTest.ok accepts (without these it can reject:
                  said here without a theorem). The converse fails (the like): GuardClear asks less
                  of what is known

WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THIS ENTRY: both proximity tests behind "SPLIT"
are handed o_sp whole; nothing is said here of what they show.

THE PROOF OF THE LAW DOES NOT READ mine, NOR, OF fits, THE ADDRESS AND withinCount: SpFresh is
conditional on the side's row and place; no law here reads withinCount: what that piece buys:
without it a carried entry beyond the part's count makes the whole list of known runs none at all
coins, and the field holds while it says nothing of a known coin (Honest/K14/FreshDefs.lean's
limit). At THE SEATED side at the owner's place the law is called, as sp_owner_law', in rowsServe_of
(Honest/K14/SendingRowsLaw.lean), at the owner's address written out, under hypotheses of its own. A
passage to a law with a conclusion on that side (the form: ownerLaw_pass_fits) needs the owner's
address, and HAS IT FROM fits: the law holds at every mine (sp_owner_law_any), and a mine that is
too wide makes the TEST reject at every other address. Without the address in fits, at the mine that
names every address, a law with that conclusion is FALSE (said here without a theorem).
coin_apart (Honest/K14/FreshShows.lean), which has no book in it, is called as it stands.
What is not claimed. That any book passes the test. All that coin_apart does not claim. Nothing on
what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshOwner
import Johnson.Desc.ProofFile.Honest.K14.FreshOwnerForm
import Johnson.Desc.ProofFile.Honest.K14.FreshField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (FreshMember)
open Prob

/-- **Coins with the same cut of the first low coins have the same runs at entries of which no coin
lies in the run (low, len)**, at a count of low + len coins of the extension field alone. -/
theorem cutAll_apart {d : Due} (hf : d.f = 0) (low len : Nat) (hd : d.e = low + len)
    (c c' : Cs d) (h : c.cut ⟨0, 0⟩ ⟨0, low⟩ = c'.cut ⟨0, 0⟩ ⟨0, low⟩) :
    ∀ es : List Ahead, (∀ k, ¬(inRuns [(low, len)] k ∧ inRuns (coinRunsOf es).e k)) →
      cutAll c es = cutAll c' es
  | [], _ => rfl
  | q :: es, hq => by
    have hc : (⟨0, 0⟩ : Due).f + (⟨0, low⟩ : Due).f ≤ d.f ∧
        (⟨0, 0⟩ : Due).e + (⟨0, low⟩ : Due).e ≤ d.e :=
      ⟨Nat.zero_le _, by show 0 + low ≤ d.e; omega⟩
    have hpt : ∀ i (hi : i < low), c.e ⟨i, by omega⟩ = c'.e ⟨i, by omega⟩ := fun i hi => by
      unfold Cs.cut at h
      rw [dif_pos hc, dif_pos hc] at h
      have h1 := congrFun (congrArg Cs.e (Option.some.inj h)) ⟨i, hi⟩
      have e1 : ∀ hlt : 0 + i < d.e, (⟨0 + i, hlt⟩ : Fin d.e) = ⟨i, by omega⟩ :=
        fun _ => Fin.ext (Nat.zero_add _)
      have h2 : c.e ⟨0 + i, by omega⟩ = c'.e ⟨0 + i, by omega⟩ := h1
      rw [e1] at h2
      exact h2
    have hcut : c.cut q.start q.count = c'.cut q.start q.count := by
      unfold Cs.cut
      by_cases hx : q.start.f + q.count.f ≤ d.f ∧ q.start.e + q.count.e ≤ d.e
      · rw [dif_pos hx, dif_pos hx]
        refine congrArg some (Cs.ext' (fun i => ?_) fun i => ?_)
        · exact absurd i.2 (by have := hx.1; omega)
        · refine hpt _ ?_
          by_contra hge
          refine hq (q.start.e + i.1) ⟨⟨(low, len), List.mem_singleton.2 rfl, ?_, ?_⟩,
            ⟨(q.start.e, q.count.e), List.mem_cons_self, Nat.le_add_right _ _, ?_⟩⟩
          · show low ≤ q.start.e + i.1
            omega
          · show q.start.e + i.1 < low + len
            have h1 := hx.2
            have h2 := i.2
            omega
          · show q.start.e + i.1 < q.start.e + q.count.e
            have h2 := i.2
            omega
      · rw [dif_neg hx, dif_neg hx]
    show ((c.cut q.start q.count).bind fun x => (cutAll c es).map fun y => (x, y)) =
      (c'.cut q.start q.count).bind fun x => (cutAll c' es).map fun y => (x, y)
    rw [hcut, cutAll_apart hf low len hd c c' h es fun k hk =>
      hq k ⟨hk.1, by
        obtain ⟨r, hr, hr'⟩ := hk.2
        exact ⟨r, List.mem_cons_of_mem _ hr, hr'⟩⟩]

/-- What spFits = true gives. -/
theorem fits_gives {A : SendPub} {n : Nat} {B : ProverCoinCounts} {o : Addr} (h : spFits A n B o = true) :
    oneSpender B o (spFirstCoin A) n = true ∧ sendingsFit A.P = true ∧
      A.P.S.sharedSplitNeeded = true ∧ Desc.K14.Honest.SpShape A.P.codes A.P.S n ∧
      o = { place := sendPlace 5, part := 0 } ∧
      withinCount (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) B o =
        true := by
  unfold spFits at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, (Desc.K14.Honest.freshPublic_of h.1.1.2).shape,
    beq_iff_eq.1 h.1.2, h.2⟩

/-- **THE LAW AT THE TEST**, in the frame's form: at every owner that the test names, where fits
accepts and GuardClear holds AT THE GUARD spGuard at every spender that spends. The proof does not
read mine: SpFresh is conditional on the side.
WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THIS ENTRY: both proximity tests behind "SPLIT"
are handed o_sp whole; nothing is said here of what they show. -/
theorem sp_owner_law (A : SendPub) (n : Nat) : OwnerLaw (spOwnerTest A n) (SpFresh A) := by
  intro Bk ord o _ hB hG S Cl X Pb W₀ Rc Ky wit sim φ σ hrow hr hd ho bud hbud u hu p sp ca m ds
    asks hfitD hb _
  subst ho
  obtain ⟨hB', hfit, hs, H, -, -⟩ := fits_gives (A := A) (n := n) hB
  have hca := coin_apart A n hfit hs H wit sim φ σ hrow hr hd u hu
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  have hbud' : spBud A asks := hbud ds asks hb
  have htk := takes_omega A hs H
  have hf : (sendingPart (jobOmega A)).takes.f = 0 := by rw [htk]
  have he : (sendingPart (jobOmega A)).takes.e =
      spFirstCoin A + (n + 1 + (spMaskCode A).r) := by
    rw [htk]
    exact Nat.add_assoc _ _ _
  have hsp := spentBy_filter Bk ⟨σ.block.place, 0⟩ p
  unfold oneSpender at hB'
  match hl : spendersOf Bk ⟨σ.block.place, 0⟩, hB' with
  | [], _ =>
    rw [hl] at hsp
    exact fresh_of_nil _ hsp _ _
  | [e], hB' =>
    rw [hl] at hsp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB'
    obtain ⟨⟨⟨hf0, hlo⟩, hhi⟩, hct⟩ := hB'
    by_cases hp : e.spender = p
    · have hsp' : Bk.spentBy ⟨σ.block.place, 0⟩ p = [e] := by
        rw [hsp]
        simp [hp]
      have hst : e.start = ⟨0, spFirstCoin A + (e.start.e - spFirstCoin A)⟩ := by
        have e1 : e.start = ⟨e.start.f, e.start.e⟩ := rfl
        have e2 : e.start.e = spFirstCoin A + (e.start.e - spFirstCoin A) := by omega
        rw [e1, hf0]
        exact congrArg (Due.mk 0) e2
      have hcl := (hG p (by rw [hsp']; exact List.cons_ne_nil _ _)).2.2
      refine fresh_of_one (d := (sendingPart (jobOmega A)).takes) _ e hsp' _ hst hct
        (by rw [he]; omega) _ _ ?_
      refine map_eq_of_factor _ _ (fun c a hg => ?_)
        (hca (e.start.e - spFirstCoin A) (by omega) sp ca m ds asks hfitD hbud')
      have g1 := congrArg Prod.fst hg
      have g2 := congrArg (fun y => y.2.1) hg
      have g3 := congrArg (fun y => y.2.2) hg
      exact Prod.ext g1 (Prod.ext g2
        (cutAll_apart (d := (sendingPart (jobOmega A)).takes) hf (spFirstCoin A)
          (n + 1 + (spMaskCode A).r) he c a.2 g3 _ hcl))
    · have hsp' : Bk.spentBy ⟨σ.block.place, 0⟩ p = [] := by
        rw [hsp]
        simp [hp]
      exact fresh_of_nil _ hsp' _ _
  | _ :: _ :: _, hB' => cases hB'

/-- The law at the value for a list of tests. -/
theorem sp_owner_law' (A : SendPub) : OwnerLaw (spOwner A) (SpFresh A) :=
  sp_owner_law A (spEntries A)

/-- **From a law at a test to a law with another conclusion**: the passage may read mine. -/
theorem ownerLaw_pass {t : OwnerTest} {F F' : ProverCoinCounts → List Place → Addr → Prop}
    (h : OwnerLaw t F) (hp : ∀ Bk ord o, t.mine o = true → F Bk ord o → F' Bk ord o) :
    OwnerLaw t F' := fun Bk ord o hm hf hg => hp Bk ord o hm (h Bk ord o hm hf hg)

/-- The like, where the passage reads fits. -/
theorem ownerLaw_pass_fits {t : OwnerTest} {F F' : ProverCoinCounts → List Place → Addr → Prop}
    (h : OwnerLaw t F) (hp : ∀ Bk ord o, t.fits Bk ord o = true → F Bk ord o → F' Bk ord o) :
    OwnerLaw t F' := fun Bk ord o hm hf hg => hp Bk ord o hf (h Bk ord o hm hf hg)

/-- **The law at every mine**: its proof reads of the test fits and the guard alone. -/
theorem sp_owner_law_any (A : SendPub) (n : Nat) (m : Addr → Bool) :
    OwnerLaw { spOwnerTest A n with mine := m } (SpFresh A) := by
  intro Bk ord o _ hf hg
  have ho : o = { place := sendPlace 5, part := 0 } :=
    (fits_gives (A := A) (n := n) hf).2.2.2.2.1
  exact sp_owner_law A n Bk ord o (by rw [ho]; exact beq_self_eq_true _) hf hg

/-- **Where the two tests of fresh_at_omega accept, the frame's form holds** at every spender that
spends something of the owner. -/
theorem guardClear_of_tests (A : SendPub) (n : Nat) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr)
    (hB : oneSpender Bk o (spFirstCoin A) n = true)
    (hK : knownBelow Bk ord o (spFirstCoin A) = true) :
    ∀ p, Bk.spentBy o p ≠ [] → GuardClear (spGuard A n) Bk ord o p := by
  intro p hp
  have hsp := spentBy_filter Bk o p
  unfold oneSpender at hB
  unfold knownBelow at hK
  match hl : spendersOf Bk o, hB, hK with
  | [], _, _ =>
    rw [hl] at hsp
    exact absurd hsp hp
  | [e], hB, hK =>
    rw [hl] at hsp
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨-, hlo⟩, -⟩, hct⟩ := hB
    by_cases hpe : e.spender = p
    · have hsp' : Bk.spentBy o p = [e] := by
        rw [hsp]
        simp [hpe]
      have hkn : ∀ q ∈ Bk.knownBy ord o p, q.start.e + q.count.e ≤ spFirstCoin A := fun q hq => by
        simp only [List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true,
          decide_eq_true_eq] at hK
        exact hK q (hpe ▸ hq)
      have hbelow : ∀ k, inRuns (Bk.knownRuns ord o p).e k → k < spFirstCoin A := fun k hk => by
        obtain ⟨r, hr, -, hr2⟩ := hk
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        exact Nat.lt_of_lt_of_le hr2 (hkn q hq)
      refine ⟨⟨fun k hk => ?_, fun k hk => ?_⟩, ⟨fun k hk => ?_, fun k hk => ?_⟩⟩
      · obtain ⟨r, hr, hr1, hr2⟩ := hk.1
        unfold ProverCoinCounts.spentRuns coinRunsOf at hr
        rw [hsp'] at hr
        obtain rfl := List.mem_singleton.1 hr
        have h0 : e.count.f = 0 := by rw [hct]
        have h3 : k < e.start.f + e.count.f := hr2
        have h4 : e.start.f ≤ k := hr1
        omega
      · obtain ⟨r, hr, hr1, -⟩ := hk.1
        unfold ProverCoinCounts.spentRuns coinRunsOf at hr
        rw [hsp'] at hr
        obtain rfl := List.mem_singleton.1 hr
        have h4 : e.start.e ≤ k := hr1
        have h5 := hbelow k hk.2
        omega
      · obtain ⟨r, hr, -⟩ := hk.1
        cases hr
      · obtain ⟨r, hr, hr1, -⟩ := hk.1
        obtain rfl := List.mem_singleton.1 hr
        have h4 : spFirstCoin A ≤ k := hr1
        have h5 := hbelow k hk.2
        omega
    · have hsp' : Bk.spentBy o p = [] := by
        rw [hsp]
        simp [hpe]
      exact absurd hsp' hp
  | _ :: _ :: _, hB, _ => cases hB

/-- So the frame's test at the part's address accepts, where the three tests on the plan and
withinCount accept too. -/
theorem ok_of_tests (A : SendPub) (n : Nat) (Bk : ProverCoinCounts) (ord : List Place) (o : Addr)
    (ho : o = { place := sendPlace 5, part := 0 })
    (hB : oneSpender Bk o (spFirstCoin A) n = true)
    (hK : knownBelow Bk ord o (spFirstCoin A) = true) (hfit : sendingsFit A.P = true)
    (hs : A.P.S.sharedSplitNeeded = true)
    (hP : Desc.K14.Honest.freshPublicB A.P.codes A.P.S n (spMaskCode A).r = true)
    (hW : withinCount (takesOf (jobOmega A).Q.codes (jobOmega A).Q.sent (jobOmega A).sort) Bk o =
      true) :
    (spOwnerTest A n).ok Bk ord o = true := by
  have hF : spFits A n Bk o = true := by
    unfold spFits
    rw [hB, hfit, hs, hP, hW, ho]
    rfl
  unfold OwnerTest.ok
  rw [Bool.and_eq_true]
  refine ⟨hF, List.all_eq_true.2 fun p _ => ?_⟩
  rw [Bool.or_eq_true]
  by_cases hp : Bk.spentBy o p = []
  · exact Or.inl (List.isEmpty_iff.2 hp)
  · exact Or.inr ((guardClearB_iff _ _ _ _ _).2 (guardClear_of_tests A n Bk ord o hB hK p hp))

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.cutAll_apart
#print axioms ProofFile.Honest.K14.fits_gives
#print axioms ProofFile.Honest.K14.sp_owner_law
#print axioms ProofFile.Honest.K14.sp_owner_law'
#print axioms ProofFile.Honest.K14.ownerLaw_pass
#print axioms ProofFile.Honest.K14.ownerLaw_pass_fits
#print axioms ProofFile.Honest.K14.sp_owner_law_any
#print axioms ProofFile.Honest.K14.guardClear_of_tests
#print axioms ProofFile.Honest.K14.ok_of_tests
