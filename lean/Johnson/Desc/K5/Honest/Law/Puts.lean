-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Puts.lean: CONDITIONAL: what lies in the verifier's ledger behind its
hearing of an attention segment's own rounds (hear, Johnson/Desc/First/Att/K5AttentionKind.lean), part by part
of the row into which the honest side is cut (shapes, Johnson/Desc/K5/Honest/Faces.lean), WITH THE
SLOTS' NUMBERS counted from the first slot that the hearing takes. Definitions of propositions, and
statements with their proofs. No frame of a prover is imported, and no value of the honest side is
spoken of.

  LeadPut m n rs G   the first m items of the first round of rs are scalars, and they lie in G under
                 the slots n, n + 1, .., each with the factor 1
  SumPut k n rs hh G   of a masked sumcheck with the call k whose part's slots begin at n: the
                 scalars in front of it (LeadPut); its first own slot is n + the lead; its first
                 end value's slot stands behind its own slots; under each own slot lies 0 with the
                 factor -1
  PutsAre        that, for the parts of a list in a row
  stages_put     GENERAL in the list of stages, CONDITIONAL: stages that have run (StagesRan,
                 Johnson/Desc/K5/Honest/Law/Calls.lean) from a ledger whose arrays have their
                 length have laid the parts so
  putsAre_sum, putsAre_one   the same by the part's number
  sum_put, one_put   CONDITIONAL: **where the hearing returns**: at part number q, with the slots
                 from F.next + slotsTo x q on (Johnson/Desc/K5/Honest/Law/SlotsTo.lean) and the
                 rounds from firstOf x q on

What is not here: what lies under an end value's slot (the law of the masked sumcheck's honest part
says what lies there); which of the hearing's sumchecks is which part's.

Limits. One direction, from a return. Premise: the ledger's three arrays have their length.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Calls
import Johnson.Desc.K5.Honest.Law.SlotsTo
import Johnson.Desc.First.Att.K5Said
import Johnson.Desc.Part.MaskedSumLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Aff Fork)
open OnBytes.Model.Road (Sized)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Stage St Heard Put Stays Open open_zero take_said
  sum_said close_said batch_said take_spec sum_spec)

/-! ## 1 What lies under a part's slots -/

/-- The first m items of the first round left are scalars, which lie under the slots from n on, each
with the factor 1. -/
def LeadPut (m n : Nat) (rs : List Fmt.RoundView) (G : Fork) : Prop :=
  ∃ pre, Open rs m pre ∧ ∀ i, i < m → Put G (n + i) (pre.getD i zeroE) oneE

/-- **A masked sumcheck's slots.** k: the call; n: the part's first slot; rs: the rounds from the
part's first on; hh: what was heard; G: a ledger behind. It is a definition. -/
structure SumPut (k : Call) (n : Nat) (rs : List Fmt.RoundView) (hh : MaskedSum.Heard) (G : Fork) :
    Prop where
  lead : LeadPut k.lead n rs G
  first : hh.first = n + k.lead
  sEnd : hh.sEnd = n + k.lead + ownSlots k.all
  coefs : ∀ i, i < ownSlots k.all → Put G (hh.first + i) zeroE (subE zeroE oneE)

/-- The parts of a list, in a row. n: the first part's first slot; rs: the rounds from its first on;
ev: for each masked sumcheck among them its start form and what was heard. -/
def PutsAre : List PartShape → Nat → List Fmt.RoundView → List (Aff × MaskedSum.Heard) → Fork → Prop
  | [], _, _, _, _ => True
  | .sum k :: L, n, rs, ev, G => ∃ C hh ev', ev = (C, hh) :: ev' ∧ SumPut k n rs hh G ∧
      PutsAre L (n + (PartShape.sum k).scalars) (rs.drop (k.vs.length + 3)) ev' G
  | .one m :: L, n, rs, ev, G => LeadPut m n rs G ∧ PutsAre L (n + m) (rs.drop 1) ev G

namespace Puts

theorem open_len : ∀ {rs : List Fmt.RoundView} {lead : Nat} {pre : List E}, Open rs lead pre →
    pre.length = lead
  | [], _, _, h => by rw [h.2, h.1]; rfl
  | _ :: _, _, _, h => h.2

/-- The hiding polynomial has as many coefficients as the sumcheck has slots of its own. -/
theorem coefs_len {C : Aff} {vs : List Var} {e : Ends} {F G : Fork} {pre : List E}
    {H : OnBytes.Tie.Pv.Att.PscH} {used : List Fmt.RoundView} {hh : MaskedSum.Heard}
    (S : P.SumSaid C vs e F G pre H used hh) :
    (MaskedSum.hidingAt (hh.vars.zip hh.r)).1.length =
      ownSlots (vs ++ [.point zeroE (e.dY + 1)]) := by
  have hl : H.rs.length = vs.length := by
    have := congrArg List.length S.lens
    rwa [List.length_map, List.length_map] at this
  have hs := S.shape
  unfold MaskedSum.shapeOk at hs
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hs
  rw [MaskedSum.ownSlots_one_add, S.vars, S.r]
  refine MaskedSum.hidingAt_zip_len _ _ (by simp) ?_ ?_
  · rw [List.length_append, List.length_append, List.length_map, hl]
    rfl
  · intro v hv
    rcases List.mem_append.1 hv with h1 | h1
    · exact Nat.le_trans (by omega) (hs.1 v h1).1
    · rw [List.mem_singleton.1 h1]
      exact Nat.succ_le_succ (Nat.zero_le _)

end Puts

open Puts

/-! ## 2 Stages that have run -/

/-- **Stages that have run have laid the parts so.** GENERAL in the stages. pre: the scalars that
wait. CONDITIONAL: the ledger's arrays have their length; the lead scalars that wait are the first
items of the first round left, and lie under the last lead slots taken (lead ≤ F.next), each with
the factor 1. -/
theorem stages_put : ∀ (st : List Stage) (F : Fork) (rs : List Fmt.RoundView) (lead : Nat) (s' : St)
    (ev : List (Aff × MaskedSum.Heard)) (pre : List E), StagesRan st (F, rs, lead) s' ev →
    Sized F → Open rs lead pre → lead ≤ F.next →
    (∀ i, i < lead → Put F (F.next - lead + i) (pre.getD i zeroE) oneE) →
    Sized s'.1 ∧ Stays F s'.1 ∧ PutsAre (shapesOf lead st) (F.next - lead) rs ev s'.1
  | [], F, rs, lead, s', ev, pre, h, hz, _, _, _ => by
    rw [h.1]
    exact ⟨hz, Stays.refl _, trivial⟩
  | .scalars n :: l, F, rs, lead, s', ev, pre, ⟨j, ⟨G, rs', lead'⟩, h1, h2⟩, hz, ho, hle, hp => by
    obtain ⟨v, a1, a2, a3, a4, a5, a6, a7, a8⟩ := take_said h1 hz ho
    obtain ⟨_, _, e3, _⟩ := take_spec h1
    have hpl := open_len ho
    subst e3 a2
    have hn : G.next - (lead + n) = F.next - lead := by omega
    obtain ⟨b1, b2, b3⟩ := stages_put l G rs' (lead + n) s' ev (pre ++ v) h2 a5 a3 (by omega)
      (fun i hi => by
        rw [hn]
        by_cases hc : i < lead
        · rw [List.getD_append _ _ _ _ (by rw [hpl]; exact hc)]
          exact a6 _ _ _ (hp i hc)
        · have h7 := a7 (i - lead) (by omega)
          rw [a4, show F.next + (i - lead) = F.next - lead + i by omega] at h7
          rw [List.getD_append_right _ _ _ _ (by rw [hpl]; omega), hpl]
          exact h7)
    rw [hn] at b3
    exact ⟨b1, a6.trans b2, b3⟩
  | .sum vs e :: l, F, rs, lead, s', _, pre, ⟨C, hh, ev', ⟨G, rs', lead'⟩, rfl, h1, h2⟩, hz, ho,
      hle, hp => by
    obtain ⟨e0, H, used, _, S⟩ := sum_said h1 hz ho
    obtain ⟨e1, _, _⟩ := sum_spec h1
    subst e0 e1
    obtain ⟨b1, b2, b3⟩ := stages_put l G _ 0 s' ev' [] h2 S.sized (open_zero _) (Nat.zero_le _)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
    refine ⟨b1, S.stays.trans b2, C, hh, ev', rfl, ?_, ?_⟩
    · exact
        { lead := ⟨pre, ho, fun i hi => b2 _ _ _ (S.stays _ _ _ (hp i hi))⟩
          first := by
            show hh.first = F.next - lead + lead
            rw [S.first]
            omega
          sEnd := by
            show hh.sEnd = F.next - lead + lead + ownSlots (vs ++ [.point zeroE (e.dY + 1)])
            rw [S.sEnd]
            omega
          coefs := fun i hi => b2 _ _ _ (S.coefs i (by rw [coefs_len S]; exact hi)) }
    · have hn : F.next - lead + (PartShape.sum ⟨lead, vs, some e⟩).scalars = G.next - 0 := by
        show F.next - lead + (lead + ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n) = G.next - 0
        rw [S.next, S.sEnd]
        omega
      rw [hn]
      exact b3
  | .batch rows :: l, F, rs, lead, s', ev, pre, ⟨w, ⟨G, rs', lead'⟩, h1, h2⟩, hz, ho, hle, hp => by
    obtain ⟨e1, e0, r, y, e2, _, _⟩ := batch_said h1 ho
    subst e0 e1 e2
    obtain ⟨b1, b2, b3⟩ := stages_put l G rs' 0 s' ev [] h2 hz (open_zero _) (Nat.zero_le _)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
    refine ⟨b1, b2, ⟨pre, ho, fun i hi => b2 _ _ _ (hp i hi)⟩, ?_⟩
    rw [show G.next - lead + lead = G.next - 0 by omega]
    exact b3
  | .point n :: l, F, rs, lead, s', ev, pre, ⟨d, ⟨G, rs', lead'⟩, h1, h2⟩, hz, ho, hle, hp => by
    obtain ⟨e1, e0, _, r, e2, _⟩ := close_said h1 ho
    subst e0 e1 e2
    obtain ⟨b1, b2, b3⟩ := stages_put l G rs' 0 s' ev [] h2 hz (open_zero _) (Nat.zero_le _)
      (fun i hi => absurd hi (Nat.not_lt_zero i))
    refine ⟨b1, b2, ⟨pre, ho, fun i hi => b2 _ _ _ (hp i hi)⟩, ?_⟩
    rw [show G.next - lead + lead = G.next - 0 by omega]
    exact b3

/-! ## 3 By the part's number -/

/-- The masked sumcheck that is part number q. -/
theorem putsAre_sum : ∀ (L : List PartShape) (n : Nat) (rs : List Fmt.RoundView)
    (ev : List (Aff × MaskedSum.Heard)) (G : Fork), PutsAre L n rs ev G → ∀ (q : Nat) (k : Call),
    L[q]? = some (.sum k) → ∃ C hh, ev[((L.take q).filter isSum).length]? = some (C, hh) ∧
      SumPut k (n + ((L.take q).map (·.scalars)).sum)
        (rs.drop ((L.take q).map (·.rounds)).sum) hh G
  | [], _, _, _, _, _, _, _, h => by cases h
  | .sum k' :: L, n, rs, _, G, ⟨C, hh, ev', rfl, a1, a2⟩, 0, k, h => by
    obtain rfl : k' = k := by
      have := Option.some.inj h
      cases this
      rfl
    exact ⟨C, hh, rfl, a1⟩
  | .sum k' :: L, n, rs, _, G, ⟨C, hh, ev', rfl, a1, a2⟩, q + 1, k, h => by
    obtain ⟨C', hh', b1, b2⟩ := putsAre_sum L _ _ ev' G a2 q k h
    refine ⟨C', hh', b1, ?_⟩
    rw [List.drop_drop, Nat.add_assoc] at b2
    exact b2
  | .one _ :: L, n, rs, ev, G, a, 0, k, h => by cases h
  | .one m :: L, n, rs, ev, G, a, q + 1, k, h => by
    obtain ⟨C', hh', b1, b2⟩ := putsAre_sum L _ _ ev G a.2 q k h
    refine ⟨C', hh', b1, ?_⟩
    rw [List.drop_drop, Nat.add_assoc] at b2
    exact b2

/-- The round by itself that is part number q. -/
theorem putsAre_one : ∀ (L : List PartShape) (n : Nat) (rs : List Fmt.RoundView)
    (ev : List (Aff × MaskedSum.Heard)) (G : Fork), PutsAre L n rs ev G → ∀ (q m : Nat),
    L[q]? = some (.one m) →
      LeadPut m (n + ((L.take q).map (·.scalars)).sum) (rs.drop ((L.take q).map (·.rounds)).sum) G
  | [], _, _, _, _, _, _, _, h => by cases h
  | .one m' :: L, n, rs, ev, G, a, 0, m, h => by
    obtain rfl : m' = m := by
      have := Option.some.inj h
      cases this
      rfl
    exact a.1
  | .one m' :: L, n, rs, ev, G, a, q + 1, m, h => by
    have b2 := putsAre_one L _ _ ev G a.2 q m h
    rw [List.drop_drop, Nat.add_assoc] at b2
    exact b2
  | .sum _ :: L, n, rs, _, G, _, 0, m, h => by cases h
  | .sum k' :: L, n, rs, _, G, ⟨C, hh, ev', rfl, a1, a2⟩, q + 1, m, h => by
    have b2 := putsAre_one L _ _ ev' G a2 q m h
    rw [List.drop_drop, Nat.add_assoc] at b2
    exact b2

/-! ## 4 Where the hearing returns -/

section
variable {x : OnBytes.Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {s' : St} {h : Heard}

/-- Where the hearing returns, the row's parts are laid so. CONDITIONAL: the return; the ledger's
arrays have their length. -/
theorem hear_puts (hh : P.hear x (F, rs, 0) = some (h, s')) (hz : Sized F) :
    Sized s'.1 ∧ Stays F s'.1 ∧ PutsAre (shapes x) F.next rs (startsOf x h) s'.1 :=
  stages_put _ F rs 0 s' _ [] (hear_stages hh) hz (open_zero _) (Nat.zero_le _)
    (fun i hi => absurd hi (Nat.not_lt_zero i))

/-- **The masked sumcheck that is part number q.** CONDITIONAL: as `hear_puts`. -/
theorem sum_put (hh : P.hear x (F, rs, 0) = some (h, s')) (hz : Sized F) (q : Nat) (k : Call)
    (hq : (shapes x)[q]? = some (.sum k)) : ∃ C hd,
      (startsOf x h)[(((shapes x).take q).filter isSum).length]? = some (C, hd) ∧
      SumPut k (F.next + slotsTo x q) (rs.drop (firstOf x q)) hd s'.1 := by
  rw [firstOf_eq]
  exact putsAre_sum _ _ rs _ _ (hear_puts hh hz).2.2 q k hq

/-- **The round by itself that is part number q.** CONDITIONAL: as `hear_puts`. -/
theorem one_put (hh : P.hear x (F, rs, 0) = some (h, s')) (hz : Sized F) (q m : Nat)
    (hq : (shapes x)[q]? = some (.one m)) :
    LeadPut m (F.next + slotsTo x q) (rs.drop (firstOf x q)) s'.1 := by
  rw [firstOf_eq]
  exact putsAre_one _ _ rs _ _ (hear_puts hh hz).2.2 q m hq

end

end H2K5.Honest

#print axioms H2K5.Honest.Puts.open_len
#print axioms H2K5.Honest.Puts.coefs_len
#print axioms H2K5.Honest.stages_put
#print axioms H2K5.Honest.putsAre_sum
#print axioms H2K5.Honest.putsAre_one
#print axioms H2K5.Honest.hear_puts
#print axioms H2K5.Honest.sum_put
#print axioms H2K5.Honest.one_put
