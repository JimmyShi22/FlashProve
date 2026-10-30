-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsPlay.lean: the rows of the two sendings of the batch's
shared rounds play: at a sub-protocol that declares two rounds which the part's messages fit (the
first with oracle messages, the second with none), the frame's function play returns over both, at
every coin, input and challenge; and where neither round opens a tree or reads a committed table, no
column is read. What is sent and where the run stands behind are named as terms.

  liftSend, sendHalves_eq   the lift by which proverSidesOfSharedSendings (Honest/K14/Sendings.lean) lays the two
                  parts
  sendTablesAt    the tables that a sending's part sends: of its own coins, the input as the part is
                  handed it, and the challenges heard
  sendShownAt     the items in the clear of its second round, the out-of-domain (OOD) answers: of
                  the same, the challenges heard now with the round's own seeds as the last
  send_plays      **a sending's row plays**: the first round shows no item and the tables of
                  sendTablesAt, the second the items of sendShownAt and no table
  send_moved      the prover's side of the member's step, at the frame's own functions: wherever
                  chainSteps returns at the member, under the premises listed below, play returns,
                  and the columns are laid: none, since neither round opens a tree or reads a
                  committed table. c: the coins that the book lends the row
  SendDeclared    what send_moved asks of a sub-protocol and a job, as one proposition
  send_declares   where the library's blocks P returns eight sub-protocols (hb), the second and the
                  fifth of them, the two sendings that the library makes at the parameters P,
                  declare such rounds, at their places, and the two parts' messages fit them, at
                  the jobs over P and ANY number at': by two_sendings
                  (Johnson/Desc/K14/Law/LedgerSeedRounds.lean) and Honest/K14/SendingsFit.lean

What is assumed in send_plays and send_moved. The sub-protocol declares two rounds, the first with
the oracle messages os, the second with none; every message of the part's first move fits the first,
every message of its second move the second. In send_moved besides: neither round opens a tree or
reads a committed table (ho₀, hs₀, ho₁, hs₁); the first half that is found at the member's place
holds the lifted part and no other (hf); chainSteps returns at the member (hl); the challenges fit
the two rounds (hfit).
What is not claimed. That chainSteps returns. That blocks P returns eight, or that the shared
chain's list holds these eight. Nothing on a verifier's decision, on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsFit
import Johnson.Desc.ProofFile.Honest.K14.KitTwo
import Johnson.Desc.ProofFile.Honest.K13.DebtsKit
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.K14.Law.LedgerSeedRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E)
open OnBytes.Slice (toE)
open VerifiableInference.Desc (Block Place OpenedColumn K1.cutSeeds)
open ProofFile.Honest.K13 (chainSteps_one)

variable {S Cl W X W₀ Rc Ky : Type}

/-- The lift by which a sending's part is laid in a wider input and state. wit: what the part is
handed of the input. Kin: liftK14 A weights (Honest/K14/PartsPlay.lean) has the same body, at
wit := fun c => ⟨entriesOf A.S (weights c.w₀)⟩. -/
def liftSend (wit : W → Ask) (p : Part Empty Ask Unit) : Part Empty W X :=
  p.lift (fun v => v) wit (fun _ => ()) fun x _ => x

/-- The two halves of proverSidesOfSharedSendings, with the lift by its name. -/
theorem sendHalves_eq (A : SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    (proverSidesOfSharedSendings A weights rand : List (Placed Empty (Common W₀ Rc Ky) X)) =
      [{ place := sendPlace 2
         parts := [liftSend (fun c => ⟨rowsOf A.P.S (weights c.w₀) (rand c.rc)⟩)
           (sendingPart (jobU A))] },
       { place := sendPlace 5
         parts := [liftSend (fun c => ⟨rowsOf A.P.S (weights c.w₀) (rand c.rc)⟩)
           (sendingPart (jobOmega A))] }] := rfl

/-- **The tables that a sending's part sends.** own: the part's own coins; a: the input as the part
is handed it; h: the challenges heard. -/
def sendTablesAt (J : SendJob) (own : Cs (sendingPart J).takes) (a : Ask) (h : List Fmt.Drawn) :
    List Table :=
  sentTables J.Q.codes J.Q.sent
    (J.rows { input := a, heard := h, own := () } (coinsE own).toArray)

/-- **The items in the clear of a sending's second round.** h: the challenges heard, the round's own
seeds the last. The term is total: it cuts the seeds off the last challenge of h (lately 1),
whatever that holds, and at an empty h off nothing, without a word. -/
def sendShownAt (J : SendJob) (own : Cs (sendingPart J).takes) (a : Ask) (h : List Fmt.Drawn) :
    List Fmt.ItemValue :=
  ((answersOf J.Q (J.rows { input := a, heard := h, own := () } (coinsE own).toArray)
    (K1.cutSeeds J.Q.coordinates J.Q.seeds
      (elems (({ input := a, heard := h, own := () } : State Ask Unit).lately 1)))).map
        fun y => Said.answer (toE y.triple)).map Said.got

/-- **A sending's row plays**, where the sub-protocol's rounds and oracle messages are the two pairs
(d₀, os) and (d₁, []) (hb), every message of the part's first move fits d₀ with os (hf₀) and every
message of its second move fits d₁ (hf₁): at all coins c, every stand m and both challenges. -/
theorem send_plays (J : SendJob) (wit : W → Ask) (b : Block S Cl) (d₀ d₁ : Fmt.DeclaredRound)
    (os : List VerifiableInference.Desc.Oracle)
    (hb : b.rounds.zip b.oracles = [(d₀, os), (d₁, [])])
    (hf₀ : ∀ L,
      ({ vals := [], tables := sentTables J.Q.codes J.Q.sent L } : Sending).fits d₀ os = true)
    (hf₁ : ∀ L seeds,
      ({ vals := (answersOf J.Q L seeds).map fun y => .answer (toE y.triple), tables := [] } :
        Sending).fits d₁ [] = true)
    (v : Option Empty) (c : RowCoins [(liftSend wit (sendingPart J) : Part Empty W X)])
    (m : Mid W X) (x₀ x₁ : Fmt.Drawn) :
    play (({ place := b.place, parts := [liftSend wit (sendingPart J)] } :
        Placed Empty W X).steps b v c) [x₀, x₁] [] m =
      .ok ([playedBy b [] ((sendTablesAt J c.1.1 (wit m.st.input) m.st.heard).map some) x₀,
          playedBy b (sendShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])) [] x₁],
        pastOf (pastOf m [] x₀) (sendShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])) x₁) :=
  two_plays b d₀ d₁ os [] hb (liftSend wit (sendingPart J)) _ _ rfl (fun _ _ => rfl)
    (fun w => nomatch w) v c m x₀ x₁ ⟨[], sendTablesAt J c.1.1 (wit m.st.input) m.st.heard⟩
    ⟨(answersOf J.Q (J.rows ⟨wit m.st.input, m.st.heard ++ [x₀], ()⟩ (coinsE c.1.1).toArray)
      (K1.cutSeeds J.Q.coordinates J.Q.seeds
        (elems ((⟨wit m.st.input, m.st.heard ++ [x₀], ()⟩ : State Ask Unit).lately 1)))).map
          fun y : E => Said.answer (toE y.triple), []⟩ rfl (hf₀ _) rfl (hf₁ _ _)

/-- **A sending: played**, under send_plays' premises and: neither round opens a tree or reads a
committed table (ho₀, hs₀, ho₁, hs₁); the first half found at the member's place holds the lifted
part alone (hf); chainSteps returns at the member (hl); the challenges fit the rounds (hfit). Then
lendRow and play return, and fillCols returns no column. c: the coins that the book lends the
row. -/
theorem send_moved (J : SendJob) (wit : W → Ask) (b : Block S Cl) (d₀ d₁ : Fmt.DeclaredRound)
    (os : List VerifiableInference.Desc.Oracle) (hr : b.rounds = [d₀, d₁])
    (ho : b.oracles = [os, []])
    (hf₀ : ∀ L,
      ({ vals := [], tables := sentTables J.Q.codes J.Q.sent L } : Sending).fits d₀ os = true)
    (hf₁ : ∀ L seeds,
      ({ vals := (answersOf J.Q L seeds).map fun y => .answer (toE y.triple), tables := [] } :
        Sending).fits d₁ [] = true)
    (ho₀ : d₀.opens = []) (hs₀ : d₀.stored = []) (ho₁ : d₁.opens = []) (hs₁ : d₁.stored = [])
    {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d} {v : Option Empty}
    {hs : List (Placed Empty W X)}
    (hf : (hs.find? fun h => h.place == b.place) =
      some { place := b.place, parts := [liftSend wit (sendingPart J)] })
    {l : List (Step W X)} (hl : chainSteps B rows look v [b] hs = .ok l) (m : Mid W X)
    (ds : List Fmt.Drawn) (hfit : drawsFit b.rounds ds = true) :
    ∃ (x₀ x₁ : Fmt.Drawn) (c : RowCoins [(liftSend wit (sendingPart J) : Part Empty W X)]),
      ds = [x₀, x₁] ∧
      lendRow B rows look b.place [(liftSend wit (sendingPart J) : Part Empty W X)] 0 = .ok c ∧
      play l ds [] m =
        .ok ([playedBy b [] ((sendTablesAt J c.1.1 (wit m.st.input) m.st.heard).map some) x₀,
          playedBy b (sendShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])) [] x₁],
        pastOf (pastOf m [] x₀) (sendShownAt J c.1.1 (wit m.st.input) (m.st.heard ++ [x₀])) x₁) ∧
      ∀ (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
        (tree : Fmt.TreeSource → Option (Place × Table)),
        fillCols (readsOf chain ft stored tree b.rounds ds) [] = .ok [] := by
  obtain ⟨c, hc, rfl⟩ := chainSteps_one hf hl
  obtain ⟨x₀, x₁, rfl, -, -⟩ := drawsFit_two (d₀ := d₀) (d₁ := d₁) (ds := ds)
    (by rw [← hr]; exact hfit)
  refine ⟨x₀, x₁, c, rfl, hc,
    send_plays J wit b d₀ d₁ os (by rw [hr, ho]; rfl) hf₀ hf₁ v c m x₀ x₁,
    fun chain ft stored tree => ?_⟩
  rw [hr, reads_none_two chain ft stored tree d₀ d₁ x₀ x₁ ho₀ hs₀ ho₁ hs₁]
  rfl

/-- What send_moved asks of a sub-protocol b and a job J. -/
structure SendDeclared (b : Block S Cl) (J : SendJob) : Prop where
  rounds : ∃ d₀ d₁ os, b.rounds = [d₀, d₁] ∧ b.oracles = [os, []] ∧
    (∀ L, ({ vals := [], tables := sentTables J.Q.codes J.Q.sent L } : Sending).fits d₀ os = true) ∧
    (∀ L seeds,
      ({ vals := (answersOf J.Q L seeds).map fun y => .answer (toE y.triple), tables := [] } :
        Sending).fits d₁ [] = true) ∧
    d₀.opens = [] ∧ d₀.stored = [] ∧ d₁.opens = [] ∧ d₁.stored = []

/-- **The two sendings that the library makes at the parameters P declare such rounds**, at their
places, and the two parts' messages fit them: b2 and b5 are the second and the fifth of the eight
sub-protocols that blocks P returns, where it returns eight (hb). at' is any number. That the shared
chain's list holds these eight is not shown here. -/
theorem send_declares (P : Desc.K14.P14) (at' : Nat)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hb : Desc.K14.blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    SendDeclared b2 (jobU ⟨P, at'⟩) ∧ b2.place = sendPlace 2 ∧
      SendDeclared b5 (jobOmega ⟨P, at'⟩) ∧ b5.place = sendPlace 5 := by
  obtain ⟨sentU, hU, rfl, rfl⟩ := Desc.K14.Law.two_sendings P b1 b2 b3 b4 b5 b6 b7 b8 hb
  have eU : (jobU ⟨P, at'⟩).Q = Desc.K14.parK1 P 2 "o_u and the first mask" sentU := by
    show Desc.K14.parK1 P 2 "o_u and the first mask" ((Desc.K14.withU P.S).getD #[]) = _
    rw [hU]
    rfl
  refine ⟨⟨_, _, _, rfl, rfl, fun L => ?_, fun L seeds => ?_, rfl, rfl, rfl, rfl⟩, rfl,
    ⟨_, _, _, rfl, rfl, fun L => ?_, fun L seeds => ?_, rfl, rfl, rfl, rfl⟩, rfl⟩
  · rw [eU]
    exact seed_fits P _ _ rfl L
  · rw [eU]
    exact answer_fits _ L seeds
  · exact seed_fits P _ _ rfl L
  · exact answer_fits _ L seeds

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.sendHalves_eq
#print axioms ProofFile.Honest.K14.send_plays
#print axioms ProofFile.Honest.K14.send_moved
#print axioms ProofFile.Honest.K14.send_declares
