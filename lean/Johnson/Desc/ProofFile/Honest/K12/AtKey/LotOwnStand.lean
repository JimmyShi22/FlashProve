-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnStand.lean: THE SENTENCE ON VALUES `SaysAt`
(K12/AsksWhole.lean) AT A STAND OF THE KEY FILE's OWN TEST, at every thread at whose stands
`StandFactsAtOwnTest` holds, at the job at a prover's parts: from what is left on the parts, on the
rounds in front, and the two debts on values AT THE TERM `wordsAtKeyOwnTest`.

  `RoundsInFrontOfOwnTest`   public: the thread plays chain 2; the rounds in front of the test are the first chain's,
                             then a round that draws the point, then others
  `StandFactsAtOwnTest`      two facts at a stand, as a premise's form: at a stand the way
                             in returns the job's state on entry, and the state has the closed shape
  `says_clause_at_stand`     the clause

What is paid on the way. The tidy mark: `own_closed`, `tidy_of_line` (OwnKernel.lean).
`StatementAtOwnTest`: `statement_at_shape`. `BookAtOwnTest`, `SharedPlanAtOwnTest`: `book_at_own_test`, `plan_at_own_test`.
`HeardAtOwnTest`: `heard_at_own_test`, off `Thr`'s clause `Fit`. `WordsTied`: `wordsTied_at_key_own_test`.

What stays a premise. `OwnSenders` and `SendersReadInFront` on the parts; `RoundsInFrontOfOwnTest`; `StandFactsAtOwnTest`;
that the place is the written one; openRows: every row of the own group says of the term; sampleRows: the members' sample rows say of the term.

Can it be empty. It speaks at stands: at a thread without a stand at number 2 it is idle. openRows and sampleRows are
asked at every stand, of a term that names the run's coins k, the input and the challenges heard: whether a thread's
invariant gives them hangs on the thread's witness being that term on the members' tables (`items_at_term`). `Thr`'s clause on
how the state was made lets the rounds seen be any that the verifier's fold takes: so at `Said` := anything weaker than
«the senders' answers are those seen», and a witness that is tied to nothing, the two premises are unmeetable.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: it stands behind `ThrS` and `lendRow`'s return.
- In scope, at the full size, at `keyBook`.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnSays
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnStatement
import Johnson.Desc.ProofFile.Honest.K12.AtKey.LotOwnHeard
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Group)
open OnBytes.Means (AllSay sampleItem)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Ground.Sh (stTidyB)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim descriptionFromSource)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyLay (pWK)
open AtPublicFiles.AtFiles (Sh₃ sh₃ SF ZW)
open AtPublicFiles.AtFiles.Full (X0)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyFile (KeyParts)
open ProofFile.Honest.K12.Light (SaysAt)

variable {V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub} {Xs : Source} {Nr : H2U.PlaceNums}
  {Pl : LaterPlaces}

/-- **What the tie asks of the rounds in front of the test**: public. -/
structure RoundsInFrontOfOwnTest (T : Thread (keyBook K₀) S₃ Claim V (Local W₀ Rc Xi Unit) X Pb)
    (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (pointLength : ℕ) : Prop where
  chain : T.chain = 2
  point : ∃ d rest, T.ahead ++ declsTo T.bs 2 =
    (descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds) ++ d :: rest ∧ d.entry.drawE = pointLength

/-- **Two facts at a stand**, as a premise's form. -/
def StandFactsAtOwnTest (T : Thread (keyBook K₀) S₃ Claim V (Local W₀ Rc Xi Unit) X Pb)
    (Said : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (A : ProofFile.Honest.K12.Light.ManyJob (Local W₀ Rc Xi Unit) X) : Prop :=
  ∀ k st m E, ThrS T Said 2 k st m E → ∀ A₀ A₂ : Sh₃, X0 = some A₀ → ZW.run 2 A₀ = .ok A₂ →
    enterOwn st = .ok (A.rec₀ m.st.input (frontOf m)) ∧ sh₃ SF st = A₂

/-- **`SaysAt` AT A STAND OF THE KEY FILE's OWN TEST.** NOT IN FRONT OF A LAW OVER COINS: this
file's head. -/
theorem says_clause_at_stand (hK₀ : fullPub = some K₀) (K : KeyParts W₀ Rc X₀ X Wk)
    {T : Thread (keyBook K₀) S₃ Claim V (Local W₀ Rc Xi Unit) X Pb}
    {Said : ℕ → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop}
    (stand : StandFactsAtOwnTest T Said (jobAtKeyOwnTest K Xs Nr Pl))
    (written : pWK Pl = piKWFull) (senders : OwnSenders K)
    (challengesBeforeVectorW challengesOfFirstChain : ℕ)
    (hfirst : challengesOfFirstChain = ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length)
    (reads : SendersReadInFront K
      (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain))
    (rounds : RoundsInFrontOfOwnTest T Xs Nr Pl K.send.P.par.S.kCol)
    (openRows : ∀ k st m E, ThrS T Said 2 k st m E → ∀ G : Group,
      st.st.groups[st.loc.own]? = some G → AllSay rdE st.st G.rows.toList
        (wordsAtKeyOwnTest K (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) k
          m.st.input m.st.heard))
    (sampleRows : ∀ k st m E, ThrS T Said 2 k st m E → ∀ G : Group,
      st.st.groups[st.loc.own]? = some G → sampleItem rdE st.st G.members.toList
        (wordsAtKeyOwnTest K (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) k
          m.st.input m.st.heard)) :
    ∀ k st m E (c : RowCoins [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest :
        Part V (Local W₀ Rc Xi Unit) X), restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest]),
      ThrS T Said 2 k st m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf T.chain) (k.look T.chain)
        (jobAtKeyOwnTest K Xs Nr Pl).p.place
        [(firstPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest :
          Part V (Local W₀ Rc Xi Unit) X), restPart (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest] 0 =
          .ok c →
      SaysAt (jobAtKeyOwnTest K Xs Nr Pl) m.st.input (frontOf m)
        (restCoins (jobAtKeyOwnTest K Xs Nr Pl).toRun.toTest c.2.1) := by
  intro k st m E c u hc
  obtain ⟨A₀, A₂, h₀, h₂, hL, -, -⟩ := own_closed
  obtain ⟨hen, hsh⟩ := stand k st m E u A₀ A₂ h₀ h₂
  have htidy : stTidyB st.st = true := by
    rw [← (show (sh₃ SF st).2.tidy = stTidyB st.st from rfl), hsh]
    exact tidy_of_line hL
  have hS := statement_at_shape senders h₀ h₂ hsh challengesBeforeVectorW challengesOfFirstChain
  obtain ⟨d, rest, hr, hd⟩ := rounds.point
  have hfit : drawsFit ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds) ++ d :: rest) m.st.heard =
      true := by
    rw [← hr]
    exact u.1.2.1
  have hear := heard_at_own_test K
    (numbersAtFullSize challengesBeforeVectorW challengesOfFirstChain) _ d rest m.st.heard hfit
    hfirst.symm hd
  rw [rounds.chain] at hc
  exact says_at_stand _ _ _ _ hen htidy _ (openSays_of_group _ _ _ (openRows k st m E u))
    (sampleRows k st m E u)
    (wordsTied_at_key_own_test K Xs Nr Pl _ reads (book_at_own_test hK₀ senders written)
      (plan_at_own_test senders) hfirst k m.st.input (frontOf m) m.st.heard hear c hc st.st
      st.loc.own hS)

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.RoundsInFrontOfOwnTest
#print axioms ProofFile.Honest.K12.AtKey.StandFactsAtOwnTest
#print axioms ProofFile.Honest.K12.AtKey.says_clause_at_stand
