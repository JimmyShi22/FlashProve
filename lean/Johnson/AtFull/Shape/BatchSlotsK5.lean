-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/BatchSlotsK5.lean: THE SLOTS OF K5's FOUR RUNS OF CLAIMS ("first", "keys",
"join", "second") AT THE TWELVE ATTENTION LINKS OF THE PROOF FILE's OWN FIRST CHAIN (Slot,
Johnson/Desc/First/Batch/Shape/BatchBuild.lean), under the head at which the library's laws on that
chain speak (P5J.AtMgA, Johnson/P5J/MgAtAll.lean). A joining of laws; nothing is evaluated.

  `claims_at`: the lot's sub-protocol states the kind's four runs, typed at claims.
  `same_refl`: a state has its own reply (the library's IM.sameReply_self, to the letter:
    Johnson/IMR/FrontSeat.lean). `look_join`: the run that the kind's list states under "join".
  **`k5_slots`** (g < 12): Bs by baseOf's value · Lk by cF.links[2 g + 1]? · A by Bs.G₀.W.A[g]?:
    there are slots for the pairs (2, "first"), (2, "keys"), (2, "join"), (2, "second") of Lk.hear
    whose laws' runG ARE k5FirstG A, k5KeysG A, k5JoinG A, k5SecondG A, and whose pre IS, at all
    four, preK5 A (another house's Johnson/Desc/K5/Honest/Law/RunsLaw.lean and RunsJoin.lean). Each
    slot's bare run is named too.

Limits. FOUR OF THE FIFTEEN RUNS BY KIND AND NAME (48 of the 215 runs). A slot pays nothing of its
law's pre. UNDER THE HEAD: that it has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the earlier hash. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.SeatsNamed
import Johnson.Desc.First.Batch.Shape.BatchBuild
import Johnson.Desc.K5.Honest.Law.RunsLaw
import Johnson.Desc.K5.Honest.Law.RunsJoin
import Johnson.Desc.First.Att.K05JoinRunN
import Johnson.IMR.K5Seat
import Johnson.Desc.First.Shape.ChainF

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att (P.k5AtN P.runsN P.parCOf P.keysOfO)
open H2K5.Honest (firstLaw keysLaw secondLaw joinLaw k5FirstG k5KeysG k5SecondG k5JoinG preK5
  first_ok_is keys_ok_is second_ok_is join_ok_is joinRunA)
open VerifiableInference.Desc.K9.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

theorem claims_at {W : Verify.Public} {l g : Nat} {before : List (Nat × Nat)} {b : Block S Claim}
    {A : Attention.Plan} (h : P.k5AtN W l g before = some b) (hA : W.A[g]? = some A) :
    b.claims = P.runsN A := by
  unfold VerifiableInference.Desc.First.Att.P.k5AtN at h
  rw [hA] at h
  obtain rfl := Option.some.inj h
  rfl

theorem same_refl (s : S) : ProofFile.sameReply s s = true := by
  unfold ProofFile.sameReply
  exact beq_self_eq_true _

theorem look_join (A : Attention.Plan) : (P.runsN A).lookup "join" = some (joinRunA A) := by
  have e : (P.runsN A).lookup "join" = some (VerifiableInference.Desc.First.Att.P.runN
    (VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls (Cl := Aff) id)
      (P.keysOfO A))) := rfl
  rw [e, VerifiableInference.Desc.First.Att.P.join_runN_eq]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem k5_slots (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (Lk : Link S ProofFile.Cl) (A : Attention.Plan),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      cF.links[2 * g + 1]? = some Lk ∧ Bs.G₀.W.A[g]? = some A ∧
      (∃ T : Slot ProofFile.sameReply Lk.hear (2, "first"), T.bare = K5Law.runFirst (P.parCOf A) ∧
        T.law.runG = k5FirstG A ∧ T.law.pre = preK5 A) ∧
      (∃ T : Slot ProofFile.sameReply Lk.hear (2, "keys"), T.bare = K5Law.runKeys (P.parCOf A) ∧
        T.law.runG = k5KeysG A ∧ T.law.pre = preK5 A) ∧
      (∃ T : Slot ProofFile.sameReply Lk.hear (2, "join"), T.bare = joinRunA A ∧
        T.law.runG = k5JoinG A ∧ T.law.pre = preK5 A) ∧
      ∃ T : Slot ProofFile.sameReply Lk.hear (2, "second"), T.bare = K5Law.runSecond (P.parCOf A) ∧
        T.law.runG = k5SecondG A ∧ T.law.pre = preK5 A := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', A, e1, e2, hat, hla, hA, -, -, -⟩ := IM.k5_of h.scope h.reads O g hg
  have hs : Lk.hear[2]? = some (IM.seatedAs ProofFile.sameReply
      (IM.k5Dress Zp ("A" ++ toString g) b') b.name (IM.k5Place g)) :=
    e2.trans (congrArg some hla)
  have hc : (IM.k5Dress Zp ("A" ++ toString g) b').claims = P.runsN A :=
    (show (IM.k5Dress Zp ("A" ++ toString g) b').claims = b'.claims from rfl).trans
      (claims_at hat hA)
  refine ⟨Bs, Lk, A, O.made, e1, hA, ⟨
    { lot := _, name := _, place := _, seated := hs, bare := K5Law.runFirst (P.parCOf A)
      states := by rw [hc]; rfl
      law := firstLaw A
      keeps := fun n s s' cs hr => by rw [(first_ok_is A hr).1]; exact same_refl s
      still := fun n s s' cs hr => by rw [(first_ok_is A hr).1] }, rfl, rfl, rfl⟩, ⟨
    { lot := _, name := _, place := _, seated := hs, bare := K5Law.runKeys (P.parCOf A)
      states := by rw [hc]; rfl
      law := keysLaw A
      keeps := fun n s s' cs hr => by rw [(keys_ok_is A hr).1]; exact same_refl s
      still := fun n s s' cs hr => by rw [(keys_ok_is A hr).1] }, rfl, rfl, rfl⟩, ⟨
    { lot := _, name := _, place := _, seated := hs, bare := joinRunA A
      states := by rw [hc]; exact look_join A
      law := joinLaw A
      keeps := fun n s s' cs hr => by
        obtain ⟨F, gq, KF, y, -, -, -, -, -, -, rfl⟩ := join_ok_is A hr
        unfold ProofFile.sameReply
        rw [VerifiableInference.Desc.First.TailClaims.Law.Tests.out_putFork]
        exact beq_self_eq_true _
      still := fun n s s' cs hr => by
        obtain ⟨F, gq, KF, y, -, -, -, -, -, -, rfl⟩ := join_ok_is A hr
        exact VerifiableInference.Desc.First.Shape.putFork_st s _ }, rfl, rfl, rfl⟩,
    { lot := _, name := _, place := _, seated := hs, bare := K5Law.runSecond (P.parCOf A)
      states := by rw [hc]; rfl
      law := secondLaw A
      keeps := fun n s s' cs hr => by rw [(second_ok_is A hr).1]; exact same_refl s
      still := fun n s s' cs hr => by rw [(second_ok_is A hr).1] }, rfl, rfl, rfl⟩

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.claims_at
#print axioms Johnson.AtFull.Shape.look_join
#print axioms Johnson.AtFull.Shape.k5_slots
#print axioms Johnson.AtFull.Shape.same_refl
