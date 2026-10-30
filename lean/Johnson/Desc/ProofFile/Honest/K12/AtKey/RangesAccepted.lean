-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesAccepted.lean: the key file's test on the ranges, the
first chain's member 15 at the place ⟨1, none, 5, .K12⟩, is accepted at the first chain's thread
(laid₁, E2E/KeyRest.lean), from the thread's pair, with the truth of the open rows as one named
premise on the state on entry.

  RowsTrue       the rows that the test takes in, at the state on entry that the verifier holds at
                 the border 15, are true of the member's words: the words that the job's sending
                 lays, at the coins that the book lends the test
  acceptedS_rng  the half is laid · the thread's table behind tree 1 is the sending's (TbIsSent,
                 E2E/KeyRangesWholeS.lean) · RowsTrue, at every stand of the pair ⟹ AcceptedS at
                 member 15, at every fall
  rowsTrue_of_wit   where the thread stands at 15 and the letter L's witness reads as the job's
                 words (WitIsJob, E2E/KeyRangesGrows.lean), RowsTrue holds

By what. acceptedS_ranges (E2E/KeyRangesSeatedS.lean), which stands on accepts_every_list through
k12Front_ranges (E2E/KeyRangesSeated.lean), and enters_of_thr (E2E/KeyRangesJob.lean); old_of_tb
(E2E/KeyRangesWholeS.lean).

What RowsTrue asks. RowsTrue is the one place where what a prover holds enters this test. G is the
ranges' group at the state s; its open rows are those that the lookups left, with the sample rows
of its one member, message 1 of the sending of the multiplicities. The words are read off
plainOne (sentRanges …): the multiplicities that the letter entry names, through msgData, and the
masks that the stretch C.mem 0 carries. So where the sender in the prover's parts lays other data
than sentRanges at that entry, the words here are not the words that were sent. That the two
agree, and what is left then, is in RangesAtProver.lean. Where the letter L's witness reads as
these words, RowsTrue follows from the thread's own open sentence: allSay_of_thr
(E2E/KeyRangesGrows.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: RowsTrue and TbIsSent are asked from the pair ThrS, and the end
  AcceptedS has that pair as a premise.
- RowsTrue is asked at every stand of the pair and given at none. It is no tautology: it ties the
  rows, which speak of what the lookups sent, to the words that entry lays, and nothing here says
  that the two agree. At a Said or a thread that holds nowhere the theorem is idle: that the pair
  holds at any run is not said here.
- In scope; at the written sizes.
- AcceptedS is one debt of member 15 in the frame. It says that the member's step accepts where the
  pair stands and the play returns; neither is shown here. That the play returns:
  RangesPlays.lean, under its premises.
- Nothing on completeness, soundness or hiding.
-/
import E2E.KeyRangesWholeS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Key (Xi FirstState)
open OnBytes.Means (AllSay layoutOf)
open OnBytes.Slice (GF rdE begun runRows)
open AtPublicFiles.AtFiles (KeySourced rangesState)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyThread (KeyFill laid₁ rangesTestJob sentRanges TbIsSent WitIsJob acceptedS_ranges old_of_tb
  allSay_of_thr)
open VerifierAndGoals (InScope)

variable {W₀ Rc Cells M Smp Rec X' : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The rows that the test takes in are true of the member's words.** s: the verifier's state at
the border 15. m: where the prover's run stands. C: the coins that the test's second part reads. -/
def RowsTrue (s : FirstState) (m : Mid (Local W₀ Rc Xi Unit) X') (C : TestCoins) : Prop :=
  ∀ G, (rangesState s).st.groups[(rangesState s).g]? = some G →
    AllSay rdE (begun (rangesState s).st (rangesState s).g G)
      (runRows (rangesState s).st G).toList
      (wordsAt (begun (rangesState s).st (rangesState s).g G) (layoutOf (rangesState s).st G)
        (plainOne (sentRanges Xs entry groups first) m.st.input (C.mem 0)
          ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m) C)))

variable (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **The rows are true where L's witness reads as the job's words**, off the thread's own open
sentence. NOT IN FRONT OF A LAW OVER COINS. -/
theorem rowsTrue_of_wit (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {k : Coins (keyBook K₀)} {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E) (C : TestCoins)
    (hW : WitIsJob (X' := X') Xs N Pl entry groups first L k s m C) :
    RowsTrue (X' := X') Xs N Pl entry groups first s m C :=
  fun G hG => allSay_of_thr Xs N Pl entry groups first L w₀ rc x hs tb hsrc scope hT C hW G hG

/-- **Member 15 is accepted, from the pair, at every letter for a fall.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem acceptedS_rng (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x hs tb k m)
    (hRows : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
          restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c →
      RowsTrue (X' := X') Xs N Pl entry groups first s m
        (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x hs tb) Said fall 15 :=
  acceptedS_ranges Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope Said hhalf
    (fun k s m E c hT hc =>
      ⟨old_of_tb Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc scope c hT.1 hc
        (hTb k s m E hT), hRows k s m E c hT hc⟩) fall

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.acceptedS_rng
