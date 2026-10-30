-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FlatMerge.lean: CONDITIONAL.

What is here. THE TWO TEXTS OF THE VERIFIER's MASKED SUMCHECK, TIED AT THE MERGE; AND THE FORM THAT
THE FLAT TEXT's STATE LEAVES THERE IS WORTH 0 ON THE HONEST PART's ROUNDS. Where the library's flat
text of the merge returns (`flatForkEnd`, OnBytes/K/Kc/QuietLink.lean) on a tape, and the part's
text (`hear`, Johnson/Desc/Part/MaskedSum4.lean) returns on rounds that hold what the tape holds
behind its first round, the flat text's state has the letters of what `hear` hands back
(`SameLetters`, Johnson/Desc/Part/MaskedSumFlat.lean), and the value that it shows is the one that
was sent. Statements and proofs.

  `merge_sameLetters`   **the tie**: the letters; the last round holds the value that is shown
  `merge_row_worth`   the state's form is worth what `rowForm` is worth
  `merge_flat_zero`   **the merge**

Limits. The tape's first round is the batching round, which is none of the sumcheck's: `TapeIs`
(FlatCore.lean) is asked of the tape behind it. `hear` is asked from the same ledger, which is
sized, and at the form `wsForkStart` of the flat text's slots and of the powers of the element that
the batching round sampled. The call has no lead, one end value of degree 1 in the further variable,
and plain weights. Every equation between values is between readings, but that of the shown value,
which is on words. For `merge_flat_zero`, at the reading `Reading.gl`, beside these the premises of
`merge_rowForm_sent` (SumEndJobs.lean), and among them: THE START IS A PREMISE, AND IT IS THE JOB's
OWN CONTENT: the claimed form is worth the reading of the cube's total; that form names end values
of the batched sumcheck, on which nothing is shown. THE FLAT FUNCTION LAYS NOTHING UNDER THE
SUMCHECK's OWN SLOTS: the world that is meant, in which these slots hold the part's coins, is that
of a ledger behind the making of the row. THE FLAT FUNCTION IS TYPED AT THE MAKER's LAYOUT: that the
verifier runs it at that layout is not shown. That a verifier's step makes a row of this state on
the shown value, with nothing kept, is by reading. It stands on Johnson/Desc/Part/MaskedSumFlat.lean
and MaskedSumFlatProofs.lean, and on Johnson/Top/H0/MergeLaw/Said.lean and Flat.lean. No property is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FlatCore
import Johnson.Desc.ProofFile.Honest.K4.Law.SumEndJobs
import Johnson.Desc.ProofFile.Honest.K4.Law.SumPoints
import Johnson.Desc.Part.MaskedSumFlatProofs
import Johnson.Top.H0.MergeLaw.Said
import Johnson.Top.H0.MergeLaw.Flat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E mulE addE zeroE oneE)
open OnBytes.Model (Reading World Aff Fork Psc WsLay WsClaim WsForkOut wsForkStart powers)
open OnBytes.Slice (GE)
open OnBytes.K.Kc (Fl Tape flatForkEnd)
open OnBytes.Desc.First.P1 (tapeEps shown_some)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum
open VerifiableInference.Desc.First.MergeLaw (hear_ended hear_of_flat)
open ProofFile.Honest.SumLaw

variable {V : Type}

/-! ## 1 The tie at the merge -/

/-- **Where both texts return on the same rounds.** -/
theorem merge_sameLetters {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G G' : Fork}
    {t u : Tape} {wo : WsForkOut} (hF : flatForkEnd lay cl sv F t = some (wo, G, u))
    (hS : OnBytes.PscRun.Sized F) (vs : List Var)
    (hk : vs.map Var.weight = List.replicate lay.lk (OnBytes.Psc.Weight.plain 3))
    {rounds : List Fmt.RoundView} {h : Heard}
    (hh : hear (wsForkStart sv (powers (tapeEps t) sv.size)) ⟨0, vs, some ⟨1, 1⟩⟩ F rounds =
      some (h, G'))
    (hT : TapeIs (t.drop 1) rounds) :
    SameLetters wo.p h ∧ ∃ rv, rounds.getLast? = some rv ∧ scalars rv.vals = some [wo.fvp] := by
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, hn, _, et, hTp, hE, _, _, _, hhide, hsh, _⟩ :=
    hear_ended (hear_of_flat hF)
  have ex : tapeEps t = x := by
    rw [et]
    rfl
  rw [ex] at hh
  have d1 : t.drop 1 =
      ⟨some OnBytes.Model.RoundName.pscEpsilon.name, 0, r1, [] ++ [mu], [wo.p.eps]⟩ ::
        (qs.map (VerifiableInference.Desc.First.MergeLaw.rd
            OnBytes.Model.RoundName.pscRound.name 0) ++
          ⟨some OnBytes.Model.RoundName.pscY.name, 1, rY, [c], [beta]⟩ ::
          ⟨some OnBytes.Model.RoundName.pscValues.name, 0, rV, [v], []⟩ :: u) := by
    rw [et]
    rfl
  have hvl : vs.length = (qs.map (VerifiableInference.Desc.First.MergeLaw.rd
      OnBytes.Model.RoundName.pscRound.name 0)).length := by
    have e := congrArg List.length hk
    rw [List.length_map, List.length_replicate] at e
    rw [e, List.length_map, hn]
  obtain ⟨eh, hL, rv, b1, b2⟩ := heard_of_tape (front := []) d1 hTp vs hvl hh hT
  have hp : (qs.map (VerifiableInference.Desc.First.MergeLaw.rd
      OnBytes.Model.RoundName.pscRound.name 0)).map pairOf = qs.map fun q => (q.2.1, q.2.2) := by
    rw [List.map_map]
    rfl
  rw [hp] at eh hL
  rw [← hk] at hE
  have hF' : OnBytes.PscRun.Sized ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork) := hS
  obtain ⟨_, _, hin, _⟩ := OnBytes.PscRun.hideRun_ok _ G wo.sFv #[v] beta hF' hhide
  have ev : wo.fvp = v := by
    rw [(shown_some hsh).2.2]
    exact (hin 0 (by simp)).2.2.2.1
  refine ⟨?_, rv, b1, by rw [ev]; exact b2⟩
  rw [eh]
  exact flatEnded _ _ _ _ _ _ _ _ _ _ _ hE hL

/-- **The state's form is worth what the part's `rowForm` is worth**, at every summand S0 and kept
form, at every reading and in every world. -/
theorem merge_row_worth {K : Type} [CommRing K] (ρ : Reading K) (W : World K) {lay : WsLay}
    {cl : Array WsClaim} {sv : Array Nat} {F G G' : Fork} {t u : Tape} {wo : WsForkOut}
    (hF : flatForkEnd lay cl sv F t = some (wo, G, u)) (hS : OnBytes.PscRun.Sized F)
    (vs : List Var) (hk : vs.map Var.weight = List.replicate lay.lk (OnBytes.Psc.Weight.plain 3))
    {rounds : List Fmt.RoundView} {h : Heard}
    (hh : hear (wsForkStart sv (powers (tapeEps t) sv.size)) ⟨0, vs, some ⟨1, 1⟩⟩ F rounds =
      some (h, G'))
    (hT : TapeIs (t.drop 1) rounds) (S0 : E) (kept : Aff) :
    (wo.p.rowForm S0 kept).value ρ W = (rowForm h S0 kept).value ρ W :=
  flatRowTie K ρ W wo.p h S0 kept (merge_sameLetters hF hS vs hk hh hT).1

/-! ## 2 The merge's own row -/

/-- **At the merge the form that the flat text's state leaves, made on the value that it shows and
with nothing kept, is worth 0.** tp: the tape, the batching round first. -/
theorem merge_flat_zero (name endName : String) (Q : K4Pub)
    (c : SumCoins name endName (mergeSum Q)) (st : State K4In Unit) (seen : Seen)
    (ds : List Fmt.Drawn) (rounds : List Fmt.RoundView) (F G : Fork) (h : Heard) (Wd : World GE)
    {cl : Array WsClaim} {sv : Array Nat} {tp u : Tape} {G2 : Fork} {wo : WsForkOut}
    (hd : drawsOk ((mergeSum Q).callAt st.input (frontOf st seen)) ds = true)
    (ha : alone (sumPart (V := V) name endName (mergeSum Q)) c st seen ds = some rounds)
    (hh : hear (wsForkStart sv (powers (tapeEps tp) sv.size))
      ((mergeSum Q).callAt st.input (frontOf st seen)) F rounds = some (h, G))
    (hs : ∀ i, i < ownSlots ((mergeSum Q).callAt st.input (frontOf st seen)).all →
      Wd.slot (h.first + i) = hidingCoin c i)
    (cls : List WsClaim) (hc : mergeClaimsAt Q st.input (ptsOf Q st.input st.heard) = some cls)
    (hσ : (wsForkStart sv (powers (tapeEps tp) sv.size)).value Reading.gl Wd = Reading.gl.val
      (mergeJobOf Q.P.wsLay st.input.w cls (ptsOf Q st.input st.heard).rhoW).cube.total)
    (hF : flatForkEnd Q.P.wsLay cl sv F tp = some (wo, G2, u)) (hS : OnBytes.PscRun.Sized F)
    (hT : TapeIs (tp.drop 1) rounds) :
    (wo.p.rowForm wo.fvp {}).value Reading.gl Wd = 0 := by
  have hk := merge_weights Q st.input (frontOf st seen)
  obtain ⟨_, rv, a1, a2⟩ := merge_sameLetters hF hS _ hk hh hT
  obtain ⟨r', s', b1, b2, _, b4⟩ := merge_rowForm_sent (V := V) name endName Q c st seen ds rounds
    _ F G h {} Wd hd ha hh hs cls hc hσ
  have e1 : rv = r' := Option.some.inj (a1.symm.trans b1)
  rw [e1] at a2
  have e2 : [wo.fvp] = s' := Option.some.inj (a2.symm.trans b2)
  rw [← e2] at b4
  rw [merge_row_worth Reading.gl Wd hF hS _ hk hh hT]
  have b5 : (rowForm h wo.fvp {}).value Reading.gl Wd =
      Reading.gl.val h.eps * (({} : Aff).value Reading.gl Wd) := b4
  rw [b5, Aff.value_empty, mul_zero]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.merge_sameLetters
#print axioms ProofFile.Honest.K4.merge_row_worth
#print axioms ProofFile.Honest.K4.merge_flat_zero
