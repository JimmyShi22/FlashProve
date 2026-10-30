-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/OutMore.lean: THE ROUNDS OF THE MASKED SUMCHECK's PART WITHOUT
THE SEALED DIGEST, and two small tools on the call's variables. A sub-protocol's decision is shown
its rounds without the sealed digest (`noDigest`, Johnson/Desc/Block.lean); the part reads a
challenge's elements alone: so the part's rounds without that digest are its rounds at the
challenges without it (`bare`, Honest/Law/Play.lean). Statements with their proofs.
Main names:
  `varOut_none`: at no variable there is no round.
  `noDigest_rvSaid`, `elemOf_bare`, `drawnE_bare`: one round; a challenge's element.
  `noDigest_varOut`: the variables' rounds. `noDigest_sumOut`: **the part's rounds, whole.**
  `withPoints_plain`: at plain variables there is no point to lay in.

Limits. Neither the state in front of the part nor what is shown in front of it is changed: what was
heard and shown there keeps its digests. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Out
import Johnson.Desc.ProofFile.Honest.Law.Play

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Part.MaskedSum

variable {W X : Type}

/-- At no variable there is no round. -/
theorem varOut_none (eps : E) (poly : List E → List E) (a : E) (past : List E)
    (ds : List Fmt.Drawn) : varOut eps poly [] a past ds = [] := by
  rw [varOut.eq_def]

/-- A round in which scalars are said, without the sealed digest. -/
theorem noDigest_rvSaid (l : List E) (d : Fmt.Drawn) :
    noDigest (rvSaid l d) = rvSaid l (bare d) := rfl

/-- The element that a challenge holds does not hang on its digest. -/
theorem elemOf_bare (d : Fmt.Drawn) : elemOf (bare d) = elemOf d := rfl

/-- The challenges' elements are those of the challenges without the digest. -/
theorem drawnE_bare (ds : List Fmt.Drawn) : drawnE (ds.map bare) = drawnE ds := by
  rw [drawnE_eq, drawnE_eq, List.map_map]
  rfl

/-- The variables' rounds without the sealed digest are the rounds at the challenges without it. -/
theorem noDigest_varOut (eps : E) (poly : List E → List E) : ∀ (L : List (Var × List E)) (a : E)
    (past : List E) (ds : List Fmt.Drawn),
    (varOut eps poly L a past ds).map noDigest = varOut eps poly L a past (ds.map bare)
  | [], a, past, ds => by rw [varOut_none, varOut_none]; rfl
  | _ :: _, a, past, [] => by rw [List.map_nil, varOut_nil]; rfl
  | (v, w) :: rest, a, past, d :: ds => by
    rw [List.map_cons, varOut_cons, varOut_cons, List.map_cons, noDigest_varOut eps poly rest,
      elemOf_bare]
    rfl

/-- **The part's rounds without the sealed digest are its rounds at the challenges without it.** -/
theorem noDigest_sumOut {name endName : String} (J : SumJob W X) (c : SumCoins name endName J)
    (t : State W X) (seen : Seen) : ∀ ds : List Fmt.Drawn,
    (sumOut J c t seen ds).map noDigest = sumOut J c t seen (ds.map bare)
  | [] => rfl
  | d0 :: ds => by
    have e1 : (ds.map bare).take (J.callAt t.input (frontOf t seen)).all.length =
        (ds.take (J.callAt t.input (frontOf t seen)).all.length).map bare := by rw [List.map_take]
    have e2 : (ds.map bare).drop (J.callAt t.input (frontOf t seen)).all.length =
        (ds.drop (J.callAt t.input (frontOf t seen)).all.length).map bare := by rw [List.map_drop]
    have e : drawnE (bare d0 :: (ds.take (J.callAt t.input (frontOf t seen)).all.length).map bare) =
        drawnE (d0 :: ds.take (J.callAt t.input (frontOf t seen)).all.length) :=
      drawnE_bare (d0 :: ds.take (J.callAt t.input (frontOf t seen)).all.length)
    simp only [sumOut, List.map_cons, List.map_append, noDigest_varOut, noDigest_rvSaid,
      elemOf_bare]
    rw [e1, e2, e]
    cases J.shape.ends with
    | none => rfl
    | some e' =>
      cases ds.drop (J.callAt t.input (frontOf t seen)).all.length with
      | nil => rfl
      | cons dl _ => rfl

/-- At plain variables there is no point to lay in. -/
theorem withPoints_plain (d : Nat) : ∀ k : Nat,
    withPoints (List.replicate k (.plain d)) [] = List.replicate k (.plain d)
  | 0 => rfl
  | k + 1 => congrArg (Var.plain d :: ·) (withPoints_plain d k)

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.varOut_none
#print axioms ProofFile.Honest.SumLaw.noDigest_rvSaid
#print axioms ProofFile.Honest.SumLaw.elemOf_bare
#print axioms ProofFile.Honest.SumLaw.drawnE_bare
#print axioms ProofFile.Honest.SumLaw.noDigest_varOut
#print axioms ProofFile.Honest.SumLaw.noDigest_sumOut
#print axioms ProofFile.Honest.SumLaw.withPoints_plain
