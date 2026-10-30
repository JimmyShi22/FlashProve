-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshShows.lean: kind K14: THE SENTENCE WITH CONTENT ON THE COIN
THAT "SPLIT" SPENDS, AT THE PART THAT OWNS IT: the one part of the row at "send o_omega"
(Honest/K14/Sendings.lean). No book occurs here.

  omega_noMask    what is read here of the test on the two sendings' shapes
  members_send    a row of one part has one member, number 0
  shows_send      what a sending's part shows (Side.shows, Honest/Side.lean), written out: the
                  columns of its tables at the asked positions; its out-of-domain (OOD) answers
  shows_congr     what the part at "send o_omega" shows is the same at two lists of its coins with
                  the same o_omega's coins, the same symbols of o_sp's row at the asked residues and
                  the same left side of o_sp's sample row
  apart_of_congr  the law for ANY function of the coins that is the same at such two lists
  fit_send        challenges that fit the member's rounds are two, and the first fits "SEND seed"
  coin_apart      **over the part's own coins, sampled uniformly, all else fixed: THE ENTRY NUMBER
                  kappa OF o_sp, kappa < n · WHAT THE PART SHOWS · ALL OF o_omega's COINS have the
                  distribution in which the first is sampled afresh, uniformly, apart from the
                  part's coins.** So the entry is uniform, and independent of the two others
                  together

WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THIS ENTRY: both proximity tests behind "SPLIT"
are handed o_sp whole; nothing is said here of what they show.

What is assumed, all on public data. hfit: the one test on the two sendings' shapes (sendingsFit),
taken whole, as Honest/K14/Sendings.lean asks of every law on a coin of these parts: what is read of
it is that o_omega has no mask row. hs: the shape splits. H: SpShape
(Johnson/Desc/K14/Honest/FreshAtChain.lean). hrow: the side's row is the part, beside any simulator.
hr: its sub-protocol declares the two rounds of the shared sending at the job's own parameters. hd:
SendDeclared (Honest/K14/SendingsPlay.lean): under it the part shows both rounds at all coins;
without it the sentences are not known to fail. Of the challenges: that they fit the declared rounds
(drawsFit); of the positions: spBud (Honest/K14/FreshDefs.lean).
How. The coins are cut in four: o_sp's tail, pad and entries; o_omega's coins (coinsFour). What is
shown is the same at two lists of coins with the same o_omega's coins, the same symbols of o_sp's
row at the asked residues and the same answer of o_sp (column_congr, sent_shown_congr,
answers_congr). The library's fresh_words makes (symbols, answer, entries) a uniform triple
(sp_law); its two premises on the seed follow from drawsFit, WITH hr AND hd (fit_send,
firstSeed_of_fit, omega_seeds): without hr the first declared round need not be "SEND seed". Then
apart_of_law and the library's map_eq_of_factor (Prob/LawKit.lean).
For a caller. IN A FILE THAT IMPORTS Honest/K14/Thread2Full.lean (so also under
Honest/K14/SendingsShapesLaw.lean) Lean's search for an instance of Nonempty at Cb.Gl.E, at Cs d and
at their products ran out of its limit (synthInstance.maxHeartbeats, 20000) in a test, so a
statement with Prob.unif of these types did not elaborate there. In a second test the same searches
went through there behind "attribute [-instance] Cb.instNonemptyPGD": an instance of the library
(Cb/Obj/LdObjectReqStd.lean) that is offered to every search for Nonempty. The compiled theorems can
be imported beside that file. Hence this file imports Honest/K14/SendingsShapes.lean alone and reads
what it needs off the test in place (omega_noMask); no instance is struck here.
What is not claimed. The challenges and the positions are fixed outside the distribution. Nothing on
the field exact, on a simulator, on roots, salts or paths. That an honest prover's program samples
these coins uniformly. That a run's positions meet the bound. Nothing on what is or is not hidden;
no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshLawKit
import Johnson.Desc.ProofFile.Honest.K14.FreshSeed
import Johnson.Desc.ProofFile.Honest.K14.FreshColumns
import Johnson.Desc.ProofFile.Honest.K14.FreshAnswers
import Johnson.Desc.ProofFile.Honest.K14.SendingsPlay
import Johnson.Desc.ProofFile.Honest.K14.SendingsShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E zeroE)
open VerifiableInference.Desc (Place K1.cutSeeds)

variable {S Cl X Pb W : Type}

/-- The test on the two sendings' shapes gives that o_omega has no mask row. -/
theorem omega_noMask (Q : Desc.K14.P14) (h : sendingsFit Q = true) : Q.S.omega.maskRows = 0 := by
  unfold sendingsFit carriersFit vecShapeFits at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact h.1.2.1.1.2.1.1.1.1

/-- A row of one part has one member, number 0. -/
theorem members_send (σ : Side S Cl Empty W X Pb) (p : Part Empty W X) (sim : Sim Pb)
    (hrow : σ.row = [(p, sim)]) :
    σ.members = [{ number := 0
                   rounds := (σ.block.rounds.zip σ.block.oracles).take p.moves.length
                   part := p, sim := sim }] := by
  unfold Side.members
  rw [hrow]
  rfl

/-- **What a sending's part shows**, written out. h: what the part is handed of coins; of it the
part's own coins alone are read. -/
theorem shows_send (J : SendJob) (wit : W → Ask) (σ : Side S Cl Empty W X Pb) (sim : Sim Pb)
    (hd : SendDeclared σ.block J) (φ : Face Empty W Pb)
    (h : (liftSend wit (sendingPart J) : Part Empty W X).Coins) (m : Mid W X) (x₀ x₁ : Fmt.Drawn)
    (asks : List (List (List Nat))) :
    σ.shows φ { number := 0
                rounds := (σ.block.rounds.zip σ.block.oracles).take
                  (liftSend wit (sendingPart J) : Part Empty W X).moves.length
                part := liftSend wit (sendingPart J), sim := sim } h m [x₀, x₁] asks =
      some [{ vals := []
              cols := ((sendTablesAt J h.1 (wit m.st.input) m.st.heard).map some).zipIdx.map
                fun y =>
                  match y.1 with
                  | some t => ((((asks[0]?).getD [])[y.2]?).getD []).map fun p => (p, t.col p)
                  | none => [] },
            { vals := sendShownAt J h.1 (wit m.st.input) (m.st.heard ++ [x₀]), cols := [] }] := by
  obtain ⟨d₀, d₁, os, hr, ho, hf₀, hf₁, -⟩ := hd.rounds
  have hb : σ.block.rounds.zip σ.block.oracles = [(d₀, os), (d₁, [])] := by
    rw [hr, ho]
    rfl
  have hp := send_plays (X := X) J wit σ.block d₀ d₁ os hb hf₀ hf₁ (φ.sees m.st.input) (h, ()) m
    x₀ x₁
  have e : ({ place := σ.block.place, parts := [liftSend wit (sendingPart J)] } :
      Placed Empty W X).steps σ.block (φ.sees m.st.input) (h, ()) =
      (liftSend wit (sendingPart J) : Part Empty W X).steps σ.block.name ⟨σ.block.place, 0⟩
        ((σ.block.rounds.zip σ.block.oracles).take
          (liftSend wit (sendingPart J) : Part Empty W X).moves.length)
        (φ.sees m.st.input) h := List.append_nil _
  rw [e] at hp
  unfold Side.shows
  show (play _ [x₀, x₁] [] m).toOption.map _ = _
  rw [hp]
  rfl

/-- **What the part at "send o_omega" shows is the same at two lists of its coins** with the same
o_omega's coins, the same symbols of o_sp's row at the asked residues, and the same left side of
o_sp's sample row at the first seed that is cut off the first challenge. -/
theorem shows_congr (A : SendPub) (n : Nat) (hs : A.P.S.sharedSplitNeeded = true)
    (hz0 : A.P.S.omega.maskRows = 0) (H : Desc.K14.Honest.SpShape A.P.codes A.P.S n)
    (wit : W → Ask) (sim : Sim Pb) (φ : Face Empty W Pb) (σ : Side S Cl Empty W X Pb)
    (hd : SendDeclared σ.block (jobOmega A)) (hf : (sendingPart (jobOmega A)).takes.f = 0)
    (he : (sendingPart (jobOmega A)).takes.e = spFirstCoin A + (n + 1) + (spMaskCode A).r)
    (sp : CsAll (liftSend wit (sendingPart (jobOmega A)) : Part Empty W X).spends)
    (ca : CsAll (liftSend wit (sendingPart (jobOmega A)) : Part Empty W X).carries) (m : Mid W X)
    (x₀ x₁ : Fmt.Drawn) (asks : List (List (List Nat)))
    (c c' : Cs (sendingPart (jobOmega A)).takes)
    (g4 : (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).2 =
      (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').2)
    (g2 : ∀ p ∈ spAsked A asks,
      Johnson.Prover.Link.symG (Desc.K14.Honest.spSymCode A.P.codes A.P.S)
          (p % 2 ^ (spMaskCode A).logN)
          (Desc.K14.Honest.maskRowOf n (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.2)
          (Desc.K14.Honest.maskTailOf (Desc.K14.Honest.spSymCode A.P.codes A.P.S).r
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.1) =
        Johnson.Prover.Link.symG (Desc.K14.Honest.spSymCode A.P.codes A.P.S)
          (p % 2 ^ (spMaskCode A).logN)
          (Desc.K14.Honest.maskRowOf n
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.2)
          (Desc.K14.Honest.maskTailOf (Desc.K14.Honest.spSymCode A.P.codes A.P.S).r
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.1))
    (g3 : OnBytes.Means.value OnBytes.Slice.rdE
          (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
          (VerifiableInference.Desc.K1.sampleRow
            (VerifiableInference.Desc.K1.Msg.of (jobOmega A).Q.codes A.P.S.sharedSplit) 1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).2 0 zeroE)
          (fun _ _ j => Desc.K14.Honest.maskRowOf n
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.2 j) =
        OnBytes.Means.value OnBytes.Slice.rdE
          (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
          (VerifiableInference.Desc.K1.sampleRow
            (VerifiableInference.Desc.K1.Msg.of (jobOmega A).Q.codes A.P.S.sharedSplit) 1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).2 0 zeroE)
          fun _ _ j => Desc.K14.Honest.maskRowOf n
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.2 j) :
    σ.shows φ { number := 0
                rounds := (σ.block.rounds.zip σ.block.oracles).take
                  (liftSend wit (sendingPart (jobOmega A)) : Part Empty W X).moves.length
                part := liftSend wit (sendingPart (jobOmega A)), sim := sim }
        (c, sp, ca) m [x₀, x₁] asks =
      σ.shows φ { number := 0
                  rounds := (σ.block.rounds.zip σ.block.oracles).take
                    (liftSend wit (sendingPart (jobOmega A)) : Part Empty W X).moves.length
                  part := liftSend wit (sendingPart (jobOmega A)), sim := sim }
        (c', sp, ca) m [x₀, x₁] asks := by
  have hw := words_four (spFirstCoin A) n (spMaskCode A).r hf he c c' g4
  have hcols := sent_shown_congr (jobOmega A).Q.codes (jobOmega A).Q.sent
    ((jobOmega A).rows { input := wit m.st.input, heard := m.st.heard, own := () }
      (coinsE c).toArray)
    ((jobOmega A).rows { input := wit m.st.input, heard := m.st.heard, own := () }
      (coinsE c').toArray)
    (fun t => (((asks[0]?).getD [])[t]?).getD []) fun tree p hp => by
      obtain ⟨hm, ht⟩ := omega_rows_congr A hs hz0
        { input := wit m.st.input, heard := m.st.heard, own := () } _ _ hw
      refine column_congr A hs hz0 H _ _ tree p hm ht fun htree => ?_
      have hp' : p ∈ spAsked A asks := by
        unfold spAsked
        rw [htree]
        exact hp
      rw [sp_sym_read A hs H _ hf he c, sp_sym_read A hs H _ hf he c']
      exact g2 p hp'
  have hans : sendShownAt (jobOmega A) c (wit m.st.input) (m.st.heard ++ [x₀]) =
      sendShownAt (jobOmega A) c' (wit m.st.input) (m.st.heard ++ [x₀]) := by
    unfold sendShownAt
    rw [elems_lately]
    refine congrArg (List.map Said.got) (answers_congr A hs hz0 H _ _ _
      (omega_rows_congr A hs hz0
        { input := wit m.st.input, heard := m.st.heard ++ [x₀], own := () } _ _ hw).1 ?_)
    rw [sp_answer_read A hs H _ _ _ _ _ fun j hj => sp_row_read A hs H _ hf he c j hj,
      sp_answer_read A hs H _ _ _ _ _ fun j hj => sp_row_read A hs H _ hf he c' j hj]
    exact g3
  rw [shows_send (jobOmega A) wit σ sim hd φ (c, sp, ca) m x₀ x₁ asks,
    shows_send (jobOmega A) wit σ sim hd φ (c', sp, ca) m x₀ x₁ asks]
  show some [({ vals := [], cols := _ } : Shown),
      { vals := sendShownAt (jobOmega A) c _ _, cols := [] }] =
    some [({ vals := [], cols := _ } : Shown),
      { vals := sendShownAt (jobOmega A) c' _ _, cols := [] }]
  rw [hans]
  exact congrArg (fun y => some [({ vals := [], cols := y } : Shown), _]) hcols

/-- **The law, for ANY function Sh of the coins that is the same at two lists of coins** with the
same first coins, the same symbols of o_sp's row at the asked residues, and the same left side of
o_sp's sample row. d: any count of spFirstCoin A + (n + 1) + r coins of the extension field. -/
theorem apart_of_congr (A : SendPub) (n : Nat) (hs : A.P.S.sharedSplitNeeded = true)
    (H : Desc.K14.Honest.SpShape A.P.codes A.P.S n) {d : Due} (hf : d.f = 0)
    (he : d.e = spFirstCoin A + (n + 1) + (spMaskCode A).r) {γ : Type} (Sh : Cs d → γ)
    (kappa : Nat) (hk : kappa < n) (x₀ : Fmt.Drawn) (asks : List (List (List Nat)))
    (hx₀ : drawFit { entry := VerifiableInference.Desc.K1.seedEntry (jobOmega A).Q } x₀ = true)
    (hbud : spBud A asks)
    (hSh : ∀ c c' : Cs d, (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).2 =
        (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').2 →
      (∀ p ∈ spAsked A asks,
        Johnson.Prover.Link.symG (Desc.K14.Honest.spSymCode A.P.codes A.P.S)
          (p % 2 ^ (spMaskCode A).logN)
          (Desc.K14.Honest.maskRowOf n (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.2)
          (Desc.K14.Honest.maskTailOf (Desc.K14.Honest.spSymCode A.P.codes A.P.S).r
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.1) =
        Johnson.Prover.Link.symG (Desc.K14.Honest.spSymCode A.P.codes A.P.S)
          (p % 2 ^ (spMaskCode A).logN)
          (Desc.K14.Honest.maskRowOf n (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.2)
          (Desc.K14.Honest.maskTailOf (Desc.K14.Honest.spSymCode A.P.codes A.P.S).r
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.1)) →
      OnBytes.Means.value OnBytes.Slice.rdE
          (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
          (VerifiableInference.Desc.K1.sampleRow
            (VerifiableInference.Desc.K1.Msg.of (jobOmega A).Q.codes A.P.S.sharedSplit) 1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).2 0 zeroE)
          (fun _ _ j => Desc.K14.Honest.maskRowOf n
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c).1.2.2 j) =
        OnBytes.Means.value OnBytes.Slice.rdE
          (localOf (jobOmega A).Q.codes (jobOmega A).Q.sent)
          (VerifiableInference.Desc.K1.sampleRow
            (VerifiableInference.Desc.K1.Msg.of (jobOmega A).Q.codes A.P.S.sharedSplit) 1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).1
            ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
              (x₀.elems.map E.ofTriple)).getD 0 default).2 0 zeroE)
          (fun _ _ j => Desc.K14.Honest.maskRowOf n
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.1
            (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he c').1.2.2 j) →
      Sh c = Sh c') :
    (Prob.unif (Cs d)).map (fun c =>
        (c.eAt (spFirstCoin A + kappa), Sh c, c.cut ⟨0, 0⟩ ⟨0, spFirstCoin A⟩)) =
      (Prob.unif (Cb.Gl.E × Cs d)).map fun a =>
        ((Except.ok a.1 : Except String Cb.Gl.E), Sh a.2,
          a.2.cut ⟨0, 0⟩ ⟨0, spFirstCoin A⟩) := by
  obtain ⟨hseed0, hcoord⟩ := omega_seeds A hs H
  obtain ⟨hβ, hzl⟩ := firstSeed_of_fit (jobOmega A).Q x₀ hseed0 hx₀
  obtain ⟨T, hT, hmem⟩ :=
    residues_set (spMaskCode A).logN (spMaskCode A).r (spAsked A asks) hbud
  have hlaw := sp_law A hs H T hT
    ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
      (x₀.elems.map E.ofTriple)).getD 0 default).1
    ((K1.cutSeeds (jobOmega A).Q.coordinates (jobOmega A).Q.seeds
      (x₀.elems.map E.ofTriple)).getD 0 default).2 (by rw [hzl]; exact hcoord) hβ
  have hap := apart_of_law ⟨kappa, hk⟩
    (coinsFour (spFirstCoin A) n (spMaskCode A).r hf he) _ hlaw
  refine Prob.map_eq_of_factor _ _ (fun c a hg => ?_) hap
  have g1 := congrArg Prod.fst hg
  have g2 := congrArg (fun y => y.2.1) hg
  have g3 := congrArg (fun y => y.2.2.1) hg
  have g4 := congrArg (fun y => y.2.2.2) hg
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show c.eAt (spFirstCoin A + kappa) = .ok a.1
    rw [eAt_four (spFirstCoin A) n (spMaskCode A).r hf he c ⟨kappa, hk⟩]
    exact congrArg Except.ok g1
  · exact hSh c a.2 g4 (fun p hp => congrFun g2 ⟨⟨p % 2 ^ (spMaskCode A).logN,
      Nat.mod_lt _ (Nat.two_pow_pos _)⟩, hmem p hp _⟩) g3
  · exact cut_four (spFirstCoin A) n (spMaskCode A).r hf he c a.2 g4

/-- Challenges that fit the rounds of a sending's one member are two, and the first fits "SEND
seed". -/
theorem fit_send (J : SendJob) (wit : W → Ask) (σ : Side S Cl Empty W X Pb)
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds J.Q) (hd : SendDeclared σ.block J)
    (ds : List Fmt.Drawn)
    (h : drawsFit (((σ.block.rounds.zip σ.block.oracles).take
      (liftSend wit (sendingPart J) : Part Empty W X).moves.length).map (·.1)) ds = true) :
    ∃ x₀ x₁, ds = [x₀, x₁] ∧
      drawFit { entry := VerifiableInference.Desc.K1.seedEntry J.Q } x₀ = true := by
  obtain ⟨d₀, d₁, os, hr', ho', -⟩ := hd.rounds
  have hb : σ.block.rounds.zip σ.block.oracles = [(d₀, os), (d₁, [])] := by
    rw [hr', ho']
    rfl
  have e01 : [d₀, d₁] = [{ entry := VerifiableInference.Desc.K1.seedEntry J.Q },
      { entry := VerifiableInference.Desc.K1.answerEntry J.Q }] := hr'.symm.trans hr
  have hd0 : d₀ = { entry := VerifiableInference.Desc.K1.seedEntry J.Q } := (List.cons.inj e01).1
  rw [hb] at h
  have h' : drawsFit [d₀, d₁] ds = true := h
  obtain ⟨x₀, x₁, e, hx₀, -⟩ := drawsFit_two h'
  exact ⟨x₀, x₁, e, hd0 ▸ hx₀⟩

variable {W₀ Rc Ky : Type}

/-- **The entry number kappa of o_sp is uniform, and independent of what the part shows together
with all of o_omega's coins.**
WHAT THE PART SHOWS IS NOT ALL THAT A RUN SHOWS OF THIS ENTRY: both proximity tests behind "SPLIT"
are handed o_sp whole; nothing is said here of what they show. -/
theorem coin_apart (A : SendPub) (n : Nat) (hfit : sendingsFit A.P = true)
    (hs : A.P.S.sharedSplitNeeded = true) (H : Desc.K14.Honest.SpShape A.P.codes A.P.S n)
    (wit : Common W₀ Rc Ky → Ask) (sim : Sim Pb) (φ : Face Empty (Common W₀ Rc Ky) Pb)
    (σ : Side S Cl Empty (Common W₀ Rc Ky) X Pb)
    (hrow : σ.row = [(liftSend wit (sendingPart (jobOmega A)), sim)])
    (hr : σ.block.rounds = VerifiableInference.Desc.K1.rounds (jobOmega A).Q)
    (hd : SendDeclared σ.block (jobOmega A)) :
    ∀ u ∈ σ.members, ∀ kappa, kappa < n → ∀ sp ca m ds asks,
      drawsFit (u.rounds.map (·.1)) ds = true → spBud A asks →
      (Prob.unif (Cs u.part.takes)).map (fun c =>
          (c.eAt (spFirstCoin A + kappa), σ.shows φ u (c, sp, ca) m ds asks,
            c.cut ⟨0, 0⟩ ⟨0, spFirstCoin A⟩)) =
        (Prob.unif (Cb.Gl.E × Cs u.part.takes)).map fun a =>
          (.ok a.1, σ.shows φ u (a.2, sp, ca) m ds asks, a.2.cut ⟨0, 0⟩ ⟨0, spFirstCoin A⟩) := by
  intro u hu kappa hk sp ca m ds asks hfitD hbud
  rw [members_send σ _ sim hrow] at hu
  obtain rfl := List.mem_singleton.1 hu
  obtain ⟨x₀, x₁, rfl, hx₀⟩ := fit_send (jobOmega A) wit σ hr hd ds hfitD
  have htk := takes_omega A hs H
  have hf : (sendingPart (jobOmega A)).takes.f = 0 := by rw [htk]
  have he : (sendingPart (jobOmega A)).takes.e =
      spFirstCoin A + (n + 1) + (spMaskCode A).r := by rw [htk]
  exact apart_of_congr A n hs H (d := (sendingPart (jobOmega A)).takes) hf he _ kappa hk x₀ asks hx₀
    hbud fun c c' g4 g2 g3 =>
      shows_congr A n hs (omega_noMask A.P hfit) H wit sim φ σ hd hf he sp ca m x₀ x₁ asks c c' g4
        g2 g3

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.omega_noMask
#print axioms ProofFile.Honest.K14.members_send
#print axioms ProofFile.Honest.K14.shows_send
#print axioms ProofFile.Honest.K14.shows_congr
#print axioms ProofFile.Honest.K14.apart_of_congr
#print axioms ProofFile.Honest.K14.fit_send
#print axioms ProofFile.Honest.K14.coin_apart
