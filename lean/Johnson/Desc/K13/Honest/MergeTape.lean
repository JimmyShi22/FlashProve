-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/MergeTape.lean: THE MERGE OF THE CLAIMS ON THE WEIGHTS, WHERE IT RETURNS, IN
THE FORM THAT THE PILE's FILLER WANTS: what the rounds of its tape sampled, and that what it leaves
of its claims is `mergeRecs` at these (PileDefs.lean of this folder). At both texts of the merge:
the head's (`mergeHear`, Johnson/Desc/First/Fork/MergeKind.lean) and the layers' (`flatForkEnd`,
OnBytes/K/Kc/QuietLink.lean). Two definitions, and statements with their proofs.

NOTHING HERE IS NEW BUT THE FORM. The library has the law: `hear_ended`
(Johnson/Top/H0/MergeLaw/Said.lean): from a return of `mergeHear`: the WHOLE tape, round by round,
with what was sent; wo.rm; wo.recs; and more. `hear_tests` (MergeLaw/Pinned.lean): its first three
tests. `hear_of_flat` (MergeLaw/Flat.lean): a return of `flatForkEnd` is a return of `mergeHear`.
All three are called. Kin: `merge_recAt` (Johnson/Road/K4/MergeRec.lean), `merge_rho`, `crOf`,
`flat_spec` (Road/K4/WoRecs.lean), the steps on a tape in OnBytes/Desc/First/P1/FlTape.lean and
PlainTape.lean.
Main names:
  `tapeSampled t`: for each round of the tape, the elements that it sampled.
  `MergeSampled lk t u sigma rm`: of what the rounds of two tapes sampled: t's sampled sigma; one
    more; rm's lk elements, one each, in their order; one more; none; then what u's sampled. It
    speaks of what was sampled alone: by the type u need not be a tail of t. `MergeSampled.closes`:
    t has lk + 4 rounds more than u.
  `mergeHear_recs`, `flatForkEnd_recs`: **from a return, at any ledger and tape**: `MergeSampled` at
    the tape on which the merge ran and the tape that it leaves, at some sigma and o.rm; and o.recs
    = `mergeRecs` lay cl sigma o.rm.

What is not claimed. One direction: from a return. Which rounds of a proof file a tape's rounds are:
MergeRounds.lean, MergeLayers.lean. What the claims are. Nothing on soundness, completeness or
hiding.

-/
import Johnson.Desc.K13.Honest.PileDefs
import Johnson.Top.H0.MergeLaw.Said
import Johnson.Top.H0.MergeLaw.Flat
import Johnson.Top.H0.MergeLaw.Pinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat hear_tests)
open Johnson.Desc.First.ForkMerge (mergeHear)

/-- For each round of the tape, the elements that it sampled. -/
def tapeSampled (t : Tape) : List (List E) := t.map (·.drawn)

/-- **What a return of the merge says of what the rounds sampled**: t: the tape on which it ran. u:
the tape that it leaves. -/
def MergeSampled (lk : ℕ) (t u : Tape) (sigma : E) (rm : Array E) : Prop :=
  rm.size = lk ∧ ∃ e beta : E,
    tapeSampled t = [sigma] :: [e] :: (rm.toList.map ([·]) ++ [beta] :: [] :: tapeSampled u)

/-- So the tape on which it ran has lk + 4 rounds more than the tape that it leaves. -/
theorem MergeSampled.closes {lk : ℕ} {t u : Tape} {sigma : E} {rm : Array E}
    (h : MergeSampled lk t u sigma rm) : t.length = lk + 4 + u.length := by
  obtain ⟨hs, e, beta, q⟩ := h
  have := congrArg List.length q
  simp only [tapeSampled, List.length_map, List.length_cons, List.length_append,
    Array.length_toList, hs] at this
  omega

/-- **THE HEAD's TEXT OF THE MERGE, FROM A RETURN, at any ledger and tape.** -/
theorem mergeHear_recs {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {o : WsForkOut}
    {F G : Fork} {t u : Tape} (h : mergeHear lay cl sv F t = .ok (o, G, u)) :
    ∃ sigma, MergeSampled lay.lk t u sigma o.rm ∧ o.recs = mergeRecs lay cl sigma o.rm := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, et, _, _, hrm, _, _, _, _, hrecs⟩ :=
    hear_ended h
  have hs : sv.size = cl.size := by
    have h2 := (hear_tests h).1
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    exact h2.2
  refine ⟨x, ⟨?_, o.p.eps, beta, ?_⟩, ?_⟩
  · rw [← Array.length_toList, hrm, List.length_map, hn]
  · rw [et, hrm]
    simp only [tapeSampled, List.map_cons, List.map_append, List.map_map]
    rfl
  · rw [hrecs]
    unfold mergeRecs
    rw [hs]

/-- **THE LAYERS' TEXT, FROM A RETURN.** -/
theorem flatForkEnd_recs {lay : WsLay} {cl : Array WsClaim} {sv : Array ℕ} {o : WsForkOut}
    {F G : Fork} {t u : Tape} (h : flatForkEnd lay cl sv F t = some (o, G, u)) :
    ∃ sigma, MergeSampled lay.lk t u sigma o.rm ∧ o.recs = mergeRecs lay cl sigma o.rm :=
  mergeHear_recs (hear_of_flat h)

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.MergeSampled.closes
#print axioms VerifiableInference.Desc.K13.Honest.mergeHear_recs
#print axioms VerifiableInference.Desc.K13.Honest.flatForkEnd_recs
