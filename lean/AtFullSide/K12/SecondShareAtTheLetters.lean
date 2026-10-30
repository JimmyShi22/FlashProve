-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the kind's share at the last chain, at the letters' names.
/-
AtFullSide/K12/SecondShareAtTheLetters.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

Can the hypotheses be met together at a real run? NOT KNOWN. P : `OpenLast` h O IS ITSELF A PREMISE:
it holds a proposition on the tables' depths at all coins, and no value of it is laid in this file
or beneath it; nor is one of K : `OpenG`. hsays is `rowsSay_at_the_letters`
(AtFullSide/K12/RowsSayAtTheLetters.lean), from h, the maker's return and P.
eI: that the value T's third family is
the named thread's is a premise here, not laid (said to hold by rfl at the value made of the named
threads). Nothing shows that ready or runC returns or that a part of the test is called.

What is here. AtFullSide/K12/SecondShareK12.lean's ends AT THE NAMES OF
AtFullSide/Honest/TheLetters.lean (another house's files of definitions): the base maker's return, G
:= `theG` h P K, the last chain's thread `thread₃` h P R, its companion `said₃` h P R, which holds
the tie to the two earlier chains' ends, and the filling's job P.ownMany. No definition; three
statements.

  `ownTestDebts_at_the_letters`   the three debts from the third alone.
  `k12_on₃_at_the_letters`   `OnAtRunAt₃` at ThrS (`thread₃` h P R) (`said₃` h P R), at every list
      of the kind K12 of `theG`'s last chain: the third conjunct of the socket `threads_of_named`
      (Johnson/T3/ThreadsAtRing.lean), cut to the kind.
  `k12_bud₃_at_the_letters`   the kind's share of bud₃ there.

WHAT THE NAMES PAY: the ring (`theGAtBase_prover`) · the head (`HeadAtReturn`.head) · hI₃ (by rfl,
once the family is the named one) · hM (`OpenLast`.ownIsTheFilling) · the debts thread (by the
texts: `lastThread`, `lastParts`, `lastLettersOf`) and said (`said₃`'s first half). WHAT IS LEFT: eI
· hsays · hrows, with the rule's own hR, T, hρ, hrun. hrows hangs on the hole `OpenG`.rows: that the
rows laid there for the last chain at the kind K12 are `lotW`'s.

Limits. All limits of AtFullSide/K12/SecondShareK12.lean's head, and of the letters' files' own
heads: a value there may turn at a named minute, and then this file turns with it. At `theG`, which
stands at the head's description, not at the return's. The letters A and B of G's lists are read by
nothing here: the family is T's. The two instances on `P5J.TS` and `Desc.K14.St` are binders:
`thread₃` reads a default through them. Nothing on completeness, soundness or hiding.
No property is claimed.
-/
import AtFullSide.K12.SecondShareK12
import AtFullSide.Honest.TheLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open VerifiableInference.Desc (KindName)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest ProofFile.Honest.FirstThread ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.Sim2
open ProofFile.Honest.Term (matrixInput baseMaker theGAtBase_prover)
open AtFullSide.Honest.TheLetters

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-- CONDITIONAL: on hsays. **`OwnTestDebts` at the letters' names, from its third field alone**: the
thread `thread₃` is the library's last thread at the written list of the trees taken over, by the
texts; the companion `said₃` gives the field's letter by its first half. -/
theorem ownTestDebts_at_the_letters {O : OpenShared A} (P : OpenLast h O)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit) (k : Coins A.B)
    (hsays : ∀ (st : h.description.S₃) (m₀ : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
      (c : RowCoins [(firstPart P.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
          (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart P.ownMany.toRun.toTest]),
      ThrS (thread₃ h P R) (said₃ h P R) 2 k st m₀ E₀ →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) placeW
        [(firstPart P.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins
                              ProofFile.Inst Cells) Unit),
          restPart P.ownMany.toRun.toTest] 0 = .ok c →
      SaysAt P.ownMany m₀.st.input (frontOf m₀) (restCoins P.ownMany.toRun.toTest c.2.1)) :
    OwnTestDebts h.description A.Z h.places h.firstChain A.H k P.ownMany (thread₃ h P R)
      (said₃ h P R) :=
  ⟨⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, HEq.rfl⟩, fun _ _ hs => hs.1, hsays⟩

/-- CONDITIONAL: see the head. **K12's SHARE OF on₃ AT THE LETTERS' NAMES**: `k12_on₃_at_named` at
the base maker's return, at G := `theG`, at the last chain's thread `thread₃`, its companion `said₃`
and the filling's job `OpenLast`.ownMany. The ring, the job's equation and two of the three debts
are no premises. -/
theorem k12_on₃_at_the_letters (made : baseMaker Z = .ok A) {O : OpenShared A} (P : OpenLast h O)
    (K : OpenG A Z) {w₀ : FullSizeMatrix} {rc : IndexCommitterCoins} {x : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst OnBytes.TableKey Cells Unit Unit}
    (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (T : ThreadsP h.description A.B A.H w₀ rc x k R)
    (eI : T.I₃ = ThrS (thread₃ h P R) (said₃ h P R))
    (hsays : ∀ (st : h.description.S₃) (m₀ : Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit) (E₀ : Env)
      (c : RowCoins [(firstPart P.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
          (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit),
        restPart P.ownMany.toRun.toTest]),
      ThrS (thread₃ h P R) (said₃ h P R) 2 k st m₀ E₀ →
      lendRow A.B (A.B.rowsOf 2) (k.look 2) placeW
        [(firstPart P.ownMany.toRun.toTest : Part (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins
                              ProofFile.Inst Cells) Unit),
          restPart P.ownMany.toRun.toTest] 0 = .ok c →
      SaysAt P.ownMany m₀.st.input (frontOf m₀) (restCoins P.ownMany.toRun.toTest c.2.1))
    (hrows : ∀ L ∈ (theG h P K).second, L.place.kind = KindName.K12 →
      K12RowAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G L)
    (ρ : Draws) (r : RunC h.description) (hρ : ρ.due h.description = true)
    (hrun : runC h.description A.B A.H w₀ rc x k ρ = .ok r) :
    ∀ L ∈ (theG h P K).second, L.place.kind = KindName.K12 →
      OnAtRunAt₃ (theG h P K) A.H w₀ rc x k (ThrS (thread₃ h P R) (said₃ h P R)) ρ r L :=
  k12_on₃_at_named h.head matrixInput OnBytes.HonestTrace.Sz.ref openHonest made h.description rfl
    (theGAtBase_prover made h (parts h P) K.rows) hR T _ eI P.ownMany P.ownIsTheFilling _ _ rfl
    (ownTestDebts_at_the_letters h P R k hsays) hrows ρ r hρ hrun

/-- CONDITIONAL: on the head at the return and hrows. **K12's SHARE OF bud₃ AT THE LETTERS' G.** -/
theorem k12_bud₃_at_the_letters {O : OpenShared A} (P : OpenLast h O) (K : OpenG A Z)
    (hrows : ∀ L ∈ (theG h P K).second, L.place.kind = KindName.K12 →
      K12RowAtW matrixInput OnBytes.HonestTrace.Sz.ref openHonest A.Z A.G L) :
    ∀ L ∈ (theG h P K).second, L.place.kind = KindName.K12 →
      Johnson.M1.BudOwed₃ h.description L :=
  k12_bud₃_at_base h.head.toAtMg matrixInput OnBytes.HonestTrace.Sz.ref openHonest h.description
    rfl A.G hrows

end AtFullSide.K12

#print axioms AtFullSide.K12.ownTestDebts_at_the_letters
#print axioms AtFullSide.K12.k12_on₃_at_the_letters
#print axioms AtFullSide.K12.k12_bud₃_at_the_letters
