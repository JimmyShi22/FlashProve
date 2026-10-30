-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/FromStep.lean: kind K13, the members' batching: WHAT THE MEMBER's
OWN ACCEPTED STEP SAYS OF THE STATE IN FRONT OF IT AND OF THE STATE BEHIND IT. Statements with their
proofs, general in the thread.

Why. Three of the sentences that a chain's thread asks at a member (`Behind`, `Exchange`,
`MadeNext`, Honest/Thread/Pays.lean) have the member's accepted step in hand (`Thread.Stepped`).
From that step alone, where the member returns only where the kind's own sub-protocol `atM3` does,
the nine guards on the state in front follow, and so does the form of the state behind. So none of
these sentences needs "the thread in front gives the guards" as a premise.

The road. The step's return holds the return of the member's decision (`K1.step_ok`,
Johnson/Desc/K1/Law/AtRecord.lean); that is a return of `atM3 P` (the premise); where `atM3 P`
returns, the guards held in front (`guards_of_return`, GuardsShape.lean of this folder) and the
state behind is `withClaim` (`atM3_return_row`, Johnson/Desc/K13/Honest/ShapeSim.lean); `play`
leaves the prover's input (`play_mid`, Honest/Law/Along.lean).
Main names:
  `k13_from_yes_row`: **the statement, with the row of the claim by name**, from the one premise
    "the member returns only where `atM3 P` does, with the same state".
  `k13_from_yes`: the same with "there is a row" in the stead of the row's name.
  `k13_from_step`: **the same from `MemberIs`** (ShapeAtM3.lean of this folder), of which it spends
    the field `back` alone.

What is not claimed. That a member's step accepts anywhere. That the premise holds of a member: at
the IOP as written in Lean, `memberIs_open` (ShapeAtM3.lean). Which challenge and which heard rounds
the sumcheck's run is at: that these are the step's own is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K13.ShapeAtM3
import Johnson.Desc.ProofFile.Honest.K13.GuardsShape
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.K13.Honest.ShapeSim
import Johnson.Desc.K1.Law.AtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (takeMasksP)
open VerifiableInference.Desc.K13 (Where atM3 St)
open VerifiableInference.Desc.K13.Law (dOf)
open VerifiableInference.Desc.K13.Honest (withClaim atM3_return_row)

variable {Bk : ProverCoinCounts} {Cl Cl' V W X Pb : Type} {T : Thread Bk S Cl V W X Pb} {P : Where}

/-- **From the member's accepted step, with the row by name**: the nine guards held of the state in
front; the state behind is `withClaim`, at what the verifier's taking returns, at W's announcement,
and at THE ROW THAT THE BATCHING HANDS ON (`Batt.rowOf`) at what the sumcheck's run returns on the
slots taken, at some challenge x and some heard rounds; the prover's input is as it was. hback: the
member returns only where the kind's own sub-protocol does, with the same state. -/
theorem k13_from_yes_row {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hback : ∀ rs gs t', blk.decide s rs gs = .ok t' →
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t')
    (hS : T.Stepped blk k s m En ds y cols s') :
    K13Guards P s ∧ ∃ (t : List Nat × St) (msg : Array OracleNotice) (x : E) (hd : Psc.Heard)
        (o : Psc.Out),
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧
      Psc.run (Batt.claimOf s.out.pending x) (Batt.summandOf s.out.pending x)
        (t.1.map fun i => ⟨s.out.indexMasks, i⟩) hd = some o ∧
      s' = withClaim s t.2.st msg (Batt.rowOf s.out.pending o) ∧ y.2.st.input = m.st.input := by
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, hst⟩ := hS
  obtain ⟨-, gs, hd⟩ := VerifiableInference.Desc.K1.step_ok T.ft blk s s' _ cols _ hst
  have ha := hback _ gs s' hd
  obtain ⟨t, msg, x, hh, o, ht, hm, -, hr, e⟩ := atM3_return_row ha
  exact ⟨guards_of_return ha, t, msg, x, hh, o, ht, hm, hr, e, (play_mid l ds [] m y hy).1⟩

/-- **From the member's accepted step**: the nine guards held of the state in front; the state
behind is `withClaim`, at what the verifier's taking returns and at W's announcement; the prover's
input is as it was. hback: the member returns only where the kind's own sub-protocol does, with the
same state. -/
theorem k13_from_yes {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hback : ∀ rs gs t', blk.decide s rs gs = .ok t' →
      (atM3 (Cl := Cl') P).decide s rs gs = .ok t')
    (hS : T.Stepped blk k s m En ds y cols s') :
    K13Guards P s ∧ ∃ t msg row,
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧ s' = withClaim s t.2.st msg row ∧
      y.2.st.input = m.st.input := by
  obtain ⟨hG, t, msg, -, -, o, ht, hm, -, e, ei⟩ := k13_from_yes_row (Cl' := Cl') hback hS
  exact ⟨hG, t, msg, _, ht, hm, e, ei⟩

/-- **The same from `MemberIs`.** -/
theorem k13_from_step {b : Nat} (hM : MemberIs T.bs b P Cl') {blk : Block S Cl}
    (hb : T.bs[b]? = some blk) {k : Coins Bk} {s s' : S} {m : Mid W X} {En : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hS : T.Stepped blk k s m En ds y cols s') :
    K13Guards P s ∧ ∃ t msg row,
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧ s' = withClaim s t.2.st msg row ∧
      y.2.st.input = m.st.input :=
  k13_from_yes (Cl' := Cl') (fun rs gs t' h => hM.back blk hb s rs gs t' h) hS

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.k13_from_yes_row
#print axioms ProofFile.Honest.K13.k13_from_yes
#print axioms ProofFile.Honest.K13.k13_from_step
