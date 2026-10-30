-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskLaw.lean: kind K14: FROM MaskApart TO THE OWNER's LAW IN THE
FRAME's FORM (MaskOwnerLaw), AND THE BRIDGE FROM TWO TESTS ON A BOOK TO THE FRAME's GuardClear
(MaskBridge): the three are stated in Honest/K14/MaskStated.lean. Statements with their proofs. The
first is an implication: its premise is not proved in this file. The second is on lists of numbers
alone. No property is claimed.

  fresh_of_run    from "a run, cut by numbers, is uniform and independent of (what is shown, what is
                  handed beside)" to the two distributions of the field fresh at a book that spends
                  just that run
  mask_count      the part's count: o_u's coins, then the first mask's own stretch
  maskOwnerFits_gives   what the owner's further test gives
  maskOwnerLaw_of_apart   **MaskApart → MaskOwnerLaw**
  maskBridge      **MaskBridge**

How. The book enters on lists alone. Where the book's one spending entry is the run (fits) and no
coin of the first mask's stretch is handed beside (the guard), what is handed beside is cut off
o_u's own coins: a function of MaskApart's third member (cutAll_apart,
Honest/K14/FreshOwnerLaw.lean). Where nothing is spent the two distributions are one (fresh_of_nil,
Honest/Law/ToyLaw.lean). OF fits THIS PROOF READS runIs ALONE; it reads neither mine nor
GuardClear's first clause: the address and the count in fits serve the test's yes, not the law; the
three clauses on the shapes are read in Honest/K14/MaskSend.lean, where the law stands with no
premise outside the frame's form. maskBridge is called in Honest/K14/MaskWhole.lean; its converse
fails (an entry of no coin that starts inside the first mask's coins; a run at or beyond the part's
count).
Limits. Those of the statements' docstrings. That a description's book passes the test is not shown.
-/
import Johnson.Desc.ProofFile.Honest.K14.MaskTie
import Johnson.Desc.ProofFile.Honest.K14.MaskStated
import Johnson.Desc.ProofFile.Honest.K14.FreshOwnerLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- An instance of the library (Cb.instNonemptyPGD, Cb/Obj/LdObjectReqStd.lean) is offered to every
-- search for Nonempty and sends it after a field that nothing determines; it is struck here.
attribute [-instance] Cb.instNonemptyPGD

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open ProofFile.Honest.Small (FreshMember)
open Johnson.Prover.Send (shapeAt)
open OnBytes.SendSim.At (budAt)

/-- **From a run that is cut by numbers to the field's two distributions**, at a list of one entry
that cuts just that run. Sh: what the owner shows. K: what is handed beside. -/
theorem fresh_of_run {γ δ : Type} {d : Due} (es : List Ahead) (e : Ahead) (hes : es = [e])
    (a n : Due) (hst : e.start = a) (hct : e.count = n) (Sh : Cs d → γ) (K : Cs d → δ)
    (h : (Prob.unif (Cs d)).map (fun c => (c.cut a n, Sh c, K c)) =
      (Prob.unif (Cs n × Cs d)).map fun x => (some x.1, Sh x.2, K x.2)) :
    (Prob.unif (Cs d)).map (fun c => (cutAll c es, Sh c, K c)) =
      (Prob.unif (CsAll (es.map Ahead.named) × Cs d)).map fun x => (some x.1, Sh x.2, K x.2) := by
  subst hes hst hct
  have h1 := congrArg (PMF.map fun t : Option (Cs e.count) × γ × δ =>
    (t.1.map fun x => (x, ()), t.2)) h
  rw [PMF.map_comp, PMF.map_comp] at h1
  have e1 : (fun c : Cs d => (cutAll c [e], Sh c, K c)) =
      (fun t : Option (Cs e.count) × γ × δ => (t.1.map fun x => (x, ()), t.2)) ∘
        fun c => (c.cut e.start e.count, Sh c, K c) := funext fun c => by
    rw [cutAll_single]
    rfl
  rw [e1]
  refine h1.trans ?_
  have e2 : ((fun t : Option (Cs e.count) × γ × δ => (t.1.map fun x => (x, ()), t.2)) ∘
        fun x : Cs e.count × Cs d => (some x.1, Sh x.2, K x.2)) =
      (fun x : (Cs e.count × Unit) × Cs d => (some x.1, Sh x.2, K x.2)) ∘
        (Equiv.prodCongr (Equiv.prodPUnit (Cs e.count)).symm (Equiv.refl (Cs d))) := rfl
  rw [e2]
  exact (PMF.map_comp _ _ _).symm.trans (congrArg (PMF.map _) (Prob.map_unif_equiv _))

/-- The part's count: o_u's coins, then the first mask's own stretch; no coin of the base field. -/
theorem mask_count (A : SendPub) (hfit : sendingsFit A.P = true)
    (hm : A.P.S.masksAhead = true) :
    (sendingPart (jobU A)).takes.f = 0 ∧
      (sendingPart (jobU A)).takes.e = (maskRun A).1 + (maskRun A).2 := by
  refine ⟨rfl, ?_⟩
  have h2 := u_two A hfit hm
  show offsetOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort (jobU A).Q.sent.size = _
  rw [h2, offset_succ _ _ _ 1 (by omega)]
  rfl

/-- What the owner's further test gives. -/
theorem maskOwnerFits_gives {A : SendPub} {k : Nat} {B : ProverCoinCounts} {o : Addr}
    (h : maskOwnerFits A k B o = true) :
    runIs B o (maskFirstCoin A) (2 * k + 1) = true ∧ sendingsFit A.P = true ∧
      A.P.S.masksAhead = true ∧ (∃ s, A.P.S.testU.head? = some s ∧ s.k = k) ∧
      o = { place := sendPlace 2, part := 0 } ∧
      withinCount (takesOf (jobU A).Q.codes (jobU A).Q.sent (jobU A).sort) B o = true := by
  unfold maskOwnerFits at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  obtain ⟨s, hs, hk⟩ := Option.map_eq_some_iff.1 h4
  exact ⟨h1, h2, h3, ⟨s, hs, hk⟩, h5, h6⟩

/-- **MaskApart → MaskOwnerLaw.** The premise is not proved here. -/
theorem maskOwnerLaw_of_apart (HA : MaskApart) : MaskOwnerLaw := by
  intro A s hfit hm hs Bk ord o _ hB hG S Cl X Pb W₀ Rc Ky wit sim φ σ hrow hr hd ho bud hbud u hu
    p sp ca m ds asks hfitD hb _
  subst ho
  have hB' := (maskOwnerFits_gives (A := A) (k := s.k) hB).1
  have hca := HA S Cl X Pb W₀ Rc Ky A s hfit hm hs wit sim φ σ hrow hr hd u hu
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  have hbud' : budAt (jobU A).Q asks := hbud ds asks hb
  obtain ⟨hf, he⟩ := mask_count A hfit hm
  have hsp := spentBy_filter Bk ⟨σ.block.place, 0⟩ p
  unfold runIs at hB'
  match hl : spendersOf Bk ⟨σ.block.place, 0⟩, hB' with
  | [], _ =>
    rw [hl] at hsp
    exact fresh_of_nil _ hsp _ _
  | [e], hB' =>
    rw [hl] at hsp
    simp only [Bool.and_eq_true, beq_iff_eq] at hB'
    obtain ⟨hst, hct⟩ := hB'
    by_cases hp : e.spender = p
    · have hsp' : Bk.spentBy ⟨σ.block.place, 0⟩ p = [e] := by
        rw [hsp]
        simp [hp]
      have hcl := (hG p (by rw [hsp']; exact List.cons_ne_nil _ _)).2.2
      refine fresh_of_run (d := (sendingPart (jobU A)).takes) _ e hsp' _ _ hst hct _ _ ?_
      refine Prob.map_eq_of_factor _ _ (fun c a hg => ?_) (hca sp ca m ds asks hfitD hbud')
      have g1 := congrArg Prod.fst hg
      have g2 := congrArg (fun y => y.2.1) hg
      have g3 := congrArg (fun y => y.2.2) hg
      exact Prod.ext g1 (Prod.ext g2
        (cutAll_apart (d := (sendingPart (jobU A)).takes) hf (maskRun A).1 (maskRun A).2 he c a.2
          g3 _ hcl))
    · have hsp' : Bk.spentBy ⟨σ.block.place, 0⟩ p = [] := by
        rw [hsp]
        simp [hp]
      exact fresh_of_nil _ hsp' _ _
  | _ :: _ :: _, hB' => cases hB'

/-- **MaskBridge**: where the book's one spending entry is the run and all that is handed beside
ends below the first mask's first coin, the frame's GuardClear holds at the guard maskGuard. -/
theorem maskBridge : MaskBridge := by
  intro A k Bk ord o hB hK p hp
  have hsp := spentBy_filter Bk o p
  unfold runIs at hB
  unfold knownBelow at hK
  match hl : spendersOf Bk o, hB, hK with
  | [], _, _ =>
    rw [hl] at hsp
    exact absurd hsp hp
  | [e], hB, hK =>
    rw [hl] at hsp
    simp only [Bool.and_eq_true, beq_iff_eq] at hB
    obtain ⟨hst, hct⟩ := hB
    by_cases hpe : e.spender = p
    · have hsp' : Bk.spentBy o p = [e] := by
        rw [hsp]
        simp [hpe]
      have hkn : ∀ q ∈ Bk.knownBy ord o p, q.start.e + q.count.e ≤ maskFirstCoin A :=
        fun q hq => by
          simp only [List.all_cons, List.all_nil, Bool.and_true, List.all_eq_true,
            decide_eq_true_eq] at hK
          exact hK q (hpe ▸ hq)
      have hbelow : ∀ n, inRuns (Bk.knownRuns ord o p).e n → n < maskFirstCoin A := fun n hn => by
        obtain ⟨r, hr, -, hr2⟩ := hn
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hr
        exact Nat.lt_of_lt_of_le hr2 (hkn q hq)
      refine ⟨⟨fun n hn => ?_, fun n hn => ?_⟩, ⟨fun n hn => ?_, fun n hn => ?_⟩⟩
      · obtain ⟨r, hr, hr1, hr2⟩ := hn.1
        unfold ProverCoinCounts.spentRuns coinRunsOf at hr
        rw [hsp'] at hr
        obtain rfl := List.mem_singleton.1 hr
        have h0 : e.count.f = 0 := by rw [hct]
        have h3 : n < e.start.f + e.count.f := hr2
        have h4 : e.start.f ≤ n := hr1
        omega
      · obtain ⟨r, hr, hr1, -⟩ := hn.1
        unfold ProverCoinCounts.spentRuns coinRunsOf at hr
        rw [hsp'] at hr
        obtain rfl := List.mem_singleton.1 hr
        have h0 : e.start.e = maskFirstCoin A := by rw [hst]
        have h4 : e.start.e ≤ n := hr1
        have h5 := hbelow n hn.2
        omega
      · obtain ⟨r, hr, -⟩ := hn.1
        cases hr
      · obtain ⟨r, hr, hr1, -⟩ := hn.1
        obtain rfl := List.mem_singleton.1 hr
        have h4 : maskFirstCoin A ≤ n := hr1
        have h5 := hbelow n hn.2
        omega
    · have hsp' : Bk.spentBy o p = [] := by
        rw [hsp]
        simp [hpe]
      exact absurd hsp' hp
  | _ :: _ :: _, hB, _ => cases hB

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.fresh_of_run
#print axioms ProofFile.Honest.K14.mask_count
#print axioms ProofFile.Honest.K14.maskOwnerFits_gives
#print axioms ProofFile.Honest.K14.maskOwnerLaw_of_apart
#print axioms ProofFile.Honest.K14.maskBridge
