-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsShows.lean: ShowsU and ShowsO
(Honest/K14/Exchange2.lean): what the two sendings' parts show in their second rounds is what the
honest tables' out-of-domain (OOD) answers are, at what an honest prover holds as
Honest/K14/Holds2.lean lays it (holds2), under Plan2, HalfIn and SendShapes.

  SendShapes      three public facts on the shapes of the two sendings' messages
  HalfIn          the first half at the sending's place among the halves O.hs has one part, the
                  sending's lifted part
  sp_noMain       o_sp has no main row: from Plan2
  jobU_par        K1's parameters of the job at "send o_u" are the chain's own
  coins_msg       a message's coins off the part's own coins are the run's coins as holds2 names
                  them, at the chain number 1
  showsU_of       **ShowsU**, under the four premises below
  showsO_of       **ShowsO**, under the same four
  exchange2_of, exchange5_of   so Exchange at the two sendings, with no premise on what is shown,
                  under the same four and one more: no two messages have one tenant (hN)

What is assumed. The plan's public facts (Plan2). HalfIn: among O.hs the half at the sending's place
is the lifted part, at the job whose point is the chain's round number 0. What the prover holds is
holds2. SendShapes: o_u and o_omega have no mask row, a main row, entries of the extension field and
no more OOD answers than their code's message length; the first mask has no main row (its shape is
read with a default: where "send o_u" has no second message the field speaks of the default shape).
For the two Exchange statements alone, one premise more: hN: the letter O.N.tenant is injective, so
no two messages have one tenant. (That the two members declare K1's rounds and stand at the
sendings' places follows from Plan2, at every O.)
For the first mask, "what the prover holds" is DEFINED in holds2 as the coded table, read: at that
message these statements unfold a definition.
What is not claimed. That these premises hold at the shared chain's thread of the IOP as written in
Lean. (Files above this one have SendShapes at the two typed shapes,
Honest/K14/SendingsShowsAt.lean, and HalfIn at one laid term of the open letters, where the shape
splits, Honest/K14/Thread2Full.lean: halfIn_full.) Nothing on the tables beneath the roots: the
sentences are on the second rounds' items alone. Nothing on a verifier's decision, on soundness or
on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.Holds2
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.K14.SendingsAnswers
import Johnson.Desc.ProofFile.Honest.K14.SendingsCoins
import Johnson.Desc.ProofFile.Honest.K14.SendingsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open Desc.K14 (P14 first)
open Desc.K14.Honest
open Desc.K14.Law (parU parO)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice} {layO : TreeLay}

/-- **Three public facts on the shapes of the two sendings' messages.** The field mask reads the
shape of "send o_u"'s message number 1 with getD: where the job has no second message it speaks of
the default shape. -/
structure SendShapes (Q : P14) : Prop where
  u : VecShape Q.codes Q.par.S.fold.u
  omega : VecShape Q.codes Q.par.S.omega
  mask : ((jobU ⟨Q, 0⟩).Q.sent.getD 1 default).shape.mainRows = 0

/-- The first half at the place pl among the halves O.hs (find? sees no later one) has one part, the
sending's lifted part. -/
def HalfIn (O : Others Bk W₀ Rc X₀ P₁ Wt) (pl : VerifiableInference.Desc.Place) (J : SendJob)
    (wit : Common W₀ Rc TableKey → Ask) : Prop :=
  (O.hs.find? fun g => g.place == pl) =
    some { place := pl, parts := [liftSend wit (sendingPart J)] }

/-- o_sp has no main row: the plan's own test on the linear part's shape has it. -/
theorem sp_noMain (hQ : Plan2 Q sentU layO) : Q.par.S.sharedSplit.mainRows = 0 := by
  have hsh := (VerifiableInference.Desc.Own.linFits_iff Q.codes Q.par.S).1 hQ.facts.lin
  rcases hsh.1.2.2.2.2.2.2.2.2.2.2.2.2.2.1 with e | e
  · rw [hQ.facts.two] at e
    cases e
  · exact e.1

/-- A message's coins off the part's own coins are the run's coins as holds2 names them. Stated at
the chain number 1 (Bk.rowsOf 1, k.look 1), where the row is lent its coins (h). -/
theorem coins_msg (k : Coins Bk) (J : SendJob) (pl : VerifiableInference.Desc.Place)
    {W X : Type} {p : Part Empty W X} {c : RowCoins [p]}
    (h : lendRow Bk (Bk.rowsOf 1) (k.look 1) pl [p] 0 = .ok c) (n : Nat) :
    coinsOfMsg k J pl n = msgCoins J (coinsE c.1.1).toArray n :=
  funext fun _ => (lent_shared k h _).symm

/-- K1's parameters of the job at "send o_u" are the chain's own, where withU returns the notices
sentU (hU). -/
theorem jobU_par (hU : Desc.K14.withU Q.S = some sentU) (n : Nat) :
    (jobU ⟨Q, n⟩).Q = parU Q sentU := by
  show Desc.K14.parK1 Q 2 "o_u and the first mask" ((Desc.K14.withU Q.S).getD #[]) = _
  rw [hU]
  rfl

/-- **ShowsU**, under Plan2, HalfIn at "send o_u"'s place, O.holds = holds2 and SendShapes. -/
theorem showsU_of (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (hh : HalfIn O (sendPlace 2) (jobU ⟨Q, 0⟩) (witOf Q weights rand))
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) : ShowsU Q sentU O Cl := by
  obtain ⟨B⟩ := hQ.eight
  intro blk k s m E ds y cols Ra Rb hblk hd hA hMv hrs
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  have L := F.at2 hblk
  obtain ⟨dU, pU, dO, pO⟩ := send_declares Q 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  have hpl : blk.place = sendPlace 2 := L.place.trans pU
  have hhalf : ((letters2 Q sentU O Cl).thread.hs.find? fun g => g.place == blk.place) =
      some { place := blk.place
             parts := [liftSend (witOf Q weights rand) (sendingPart (jobU ⟨Q, 0⟩))] } := by
    rw [hpl]
    exact hh
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, ho₀, hs₀, ho₁, hs₁⟩ :=
    (sendDeclared_like L.rounds L.oracles dU).rounds
  obtain ⟨x₀, x₁, c, -, hc, hp, -⟩ := send_moved (jobU ⟨Q, 0⟩) (witOf Q weights rand) blk d₀ d₁
    os hr ho hf₀ hf₁ ho₀ hs₀ ho₁ hs₁ hhalf hl m ds hd
  obtain rfl := Except.ok.inj (hy.symm.trans hp)
  obtain ⟨rfl, rfl⟩ : (⟨[], x₀⟩ : Fmt.RoundView) = Ra ∧
      (⟨sendShownAt (jobU ⟨Q, 0⟩) c.1.1 (witOf Q weights rand m.st.input) (m.st.heard ++ [x₀]),
        x₁⟩ : Fmt.RoundView) = Rb := by
    simpa [roundsOf, playedBy] using hrs
  obtain ⟨W, D, hseen, -, hd1, u⟩ := FlatAt.stepTo1 (B := B) F hQ.facts.goes 0 _ s _ [] c₀ [] hfold
  have S := hQ.pub m.st.input.key
  have t := S.to1 u
  have hT : s.st.codes = Q.codes := by
    rw [← hd1]
    exact (S.at1 t).carried.codes
  have hseen' : m.seen = [W.R1] := hseen
  have hh : m.st.heard = [W.R1].map (·.drawn) := by rw [← hsm, hseen']
  have e1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [hh]; rfl
  have eQ := jobU_par (Q := Q) hQ.facts.goes 0
  rw [hpl] at hc
  have hs0 : ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.fold.u := by
    rw [eQ]
    exact (shapeAt_of_get (parU Q sentU) 0 ⟨Q.par.S.fold.u, Q.par.S.fold.leafClass⟩
      (by rw [Desc.K14.Law.parK1_sent]; exact withU_zero hQ.facts.goes)).1
  have hsz : (jobU ⟨Q, 0⟩).Q.sent.size ≤ 2 := by
    rw [eQ, Desc.K14.Law.parK1_sent, hQ.facts.goesTwo]
  show sendShownAt (jobU ⟨Q, 0⟩) c.1.1 (witOf Q weights rand m.st.input) (m.st.heard ++ [x₀]) = _
  rw [e1, hO, shown_read (jobU ⟨Q, 0⟩) c.1.1 (witOf Q weights rand m.st.input) m.st.heard x₀ []
    s.st (by rw [hT, eQ]; rfl)
    (rowsU Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn) (holds2 Q weights rand k m.st.input))
    (holds2 Q weights rand k m.st.input).w₀ fun kk hkk part j _ =>
      rowsU_read Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
        (holds2 Q weights rand k m.st.input) (witOf Q weights rand m.st.input)
        (m.st.heard ++ [x₀]) (coinsE c.1.1).toArray hsz hs0 hSh.u hSh.mask
        (by
          rw [← elems_one]
          show elems (((m.st.heard ++ [x₀]).drop 0).take 1) = _
          rw [hh]
          rfl)
        t.point (fun _ _ => rfl)
        (by
          show readCoins Q.codes ((jobU ⟨Q, 0⟩).Q.sent.getD 0 default).shape _ = _
          rw [hs0, coins_msg k (jobU ⟨Q, 0⟩) (sendPlace 2) hc 0])
        (by
          rw [← coins_msg k (jobU ⟨Q, 0⟩) (sendPlace 2) hc 1]
          show (holds2 Q weights rand k m.st.input).cMask = _
          unfold holds2
          cases Q.S.testU.head? <;> rfl)
        kk hkk part j, eQ]

/-- **ShowsO**, under Plan2, HalfIn at "send o_omega"'s place, O.holds = holds2 and SendShapes. -/
theorem showsO_of (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (hh : HalfIn O (sendPlace 5) (jobOmega ⟨Q, 0⟩) (witOf Q weights rand))
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) : ShowsO Q sentU O Cl := by
  obtain ⟨B⟩ := hQ.eight
  intro blk k s m E ds y cols Ra Rb hblk hd hA hMv hrs
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  have L := F.at5 hblk
  obtain ⟨dU, pU, dO, pO⟩ := send_declares Q 0 B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made
  have hpl : blk.place = sendPlace 5 := L.place.trans pO
  have hhalf : ((letters2 Q sentU O Cl).thread.hs.find? fun g => g.place == blk.place) =
      some { place := blk.place
             parts := [liftSend (witOf Q weights rand) (sendingPart (jobOmega ⟨Q, 0⟩))] } := by
    rw [hpl]
    exact hh
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨hsm, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  obtain rfl : s₀ = first Q.codes m.st.input.key := hbeg
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, ho₀, hs₀, ho₁, hs₁⟩ :=
    (sendDeclared_like L.rounds L.oracles dO).rounds
  obtain ⟨x₀, x₁, c, -, hc, hp, -⟩ := send_moved (jobOmega ⟨Q, 0⟩) (witOf Q weights rand) blk d₀
    d₁ os hr ho hf₀ hf₁ ho₀ hs₀ ho₁ hs₁ hhalf hl m ds hd
  obtain rfl := Except.ok.inj (hy.symm.trans hp)
  obtain ⟨rfl, rfl⟩ : (⟨[], x₀⟩ : Fmt.RoundView) = Ra ∧
      (⟨sendShownAt (jobOmega ⟨Q, 0⟩) c.1.1 (witOf Q weights rand m.st.input)
        (m.st.heard ++ [x₀]), x₁⟩ : Fmt.RoundView) = Rb := by
    simpa [roundsOf, playedBy] using hrs
  obtain ⟨W, D, hseen, -, hd4, u⟩ := FlatAt.stepTo4 (B := B) F hQ.facts.goes 0 _ s _ [] c₀ [] hfold
  have S := hQ.pub m.st.input.key
  obtain ⟨x2, ids2, t⟩ := S.to4 u
  have hT : s.st.codes = Q.codes := by
    rw [← hd4]
    exact (S.at4 t).carried.codes
  have hseen' : m.seen = [W.R1, W.R2a, W.R2b, W.R4] := hseen
  have hh : m.st.heard = [W.R1, W.R2a, W.R2b, W.R4].map (·.drawn) := by rw [← hsm, hseen']
  have e1 : firstRv m.st.heard = rvOf W.R1.drawn := by rw [hh]; rfl
  rw [hpl] at hc
  obtain ⟨w2, w0, w1⟩ := withOmega_two hQ.facts.two
  have sO : (jobOmega ⟨Q, 0⟩).Q.sent = Desc.K14.withOmega Q.S := Desc.K14.Law.parK1_sent Q 5 _ _
  have hs0 : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 0 default).shape = Q.par.S.omega :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 0 ⟨Q.par.S.omega, Q.par.S.omegaLeafClass⟩
      (by rw [sO]; exact w0)).1
  have hs1 : ((jobOmega ⟨Q, 0⟩).Q.sent.getD 1 default).shape = Q.par.S.sharedSplit :=
    (shapeAt_of_get (jobOmega ⟨Q, 0⟩).Q 1 ⟨Q.par.S.sharedSplit, Q.par.S.sharedSplitLeafClass⟩
      (by rw [sO]; exact w1)).1
  have hsz : (jobOmega ⟨Q, 0⟩).Q.sent.size ≤ 2 := by
    rw [sO]
    exact Nat.le_of_eq w2
  show sendShownAt (jobOmega ⟨Q, 0⟩) c.1.1 (witOf Q weights rand m.st.input)
    (m.st.heard ++ [x₀]) = _
  rw [e1, hO, shown_read (jobOmega ⟨Q, 0⟩) c.1.1 (witOf Q weights rand m.st.input) m.st.heard x₀
    [] s.st hT
    (rowsO Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn) (holds2 Q weights rand k m.st.input))
    (words1 Q sentU (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
      (holds2 Q weights rand k m.st.input)) fun kk hkk part j _ =>
      rowsO_read Q (first Q.codes m.st.input.key) (rvOf W.R1.drawn)
        (holds2 Q weights rand k m.st.input) (witOf Q weights rand m.st.input)
        (m.st.heard ++ [x₀]) (coinsE c.1.1).toArray hsz hs0 hs1 hSh.omega (sp_noMain hQ)
        (by
          rw [← elems_one]
          show elems (((m.st.heard ++ [x₀]).drop 0).take 1) = _
          rw [hh]
          rfl)
        t.front.front.front.point (fun _ _ => rfl)
        (by
          show readCoins Q.codes Q.S.omega _ = _
          rw [coins_msg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) hc 0]
          rfl)
        (by
          show readCoins Q.codes Q.S.sharedSplit _ = _
          rw [coins_msg k (jobOmega ⟨Q, 0⟩) (sendPlace 5) hc 1]
          rfl)
        kk hkk part j]
  rfl

/-- **«Exchange» at "send o_u", with no premise on what is shown**: under showsU_of's four premises
and hN: no two messages have one tenant. -/
theorem exchange2_of (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (hh : HalfIn O (sendPlace 2) (jobU ⟨Q, 0⟩) (witOf Q weights rand))
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) :
    Exchange (letters2 Q sentU O Cl).thread 2 :=
  exchange2 hQ O Cl hN (showsU_of hQ O Cl weights rand hh hO hSh)

/-- **«Exchange» at "send o_omega", with no premise on what is shown**: under showsO_of's four
premises and hN: no two messages have one tenant. -/
theorem exchange5_of (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt) (Cl : Type)
    (hN : Function.Injective O.N.tenant) (weights : W₀ → Weights) (rand : Rc → TableRand)
    (hh : HalfIn O (sendPlace 5) (jobOmega ⟨Q, 0⟩) (witOf Q weights rand))
    (hO : O.holds = holds2 Q weights rand) (hSh : SendShapes Q) :
    Exchange (letters2 Q sentU O Cl).thread 5 :=
  exchange5 hQ O Cl hN (showsO_of hQ O Cl weights rand hh hO hSh)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sp_noMain
#print axioms ProofFile.Honest.K14.coins_msg
#print axioms ProofFile.Honest.K14.jobU_par
#print axioms ProofFile.Honest.K14.showsU_of
#print axioms ProofFile.Honest.K14.showsO_of
#print axioms ProofFile.Honest.K14.exchange2_of
#print axioms ProofFile.Honest.K14.exchange5_of
