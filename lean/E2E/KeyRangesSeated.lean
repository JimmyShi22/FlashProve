-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesSeated.lean: THE KEY FILE's TEST ON THE RANGES, SEATED IN THE FIRST CHAIN's THREAD, IS
ACCEPTED AT EVERY LETTER FOR A FALL, FROM A SHORT NAMED LIST OF WHAT IS STILL OWED. An assembly: the
premises of `accepted_every` (Johnson/Desc/ProofFile/Honest/K12/EveryAt.lean) at `laid₁`
(E2E/KeyRest.lean), the border 15 and the job `rangesTestJob` (E2E/KeyRangesJob.lean), in scope, at the key
file's book at the written sizes. What reads the plan, the book or the SHAPE of the verifier's state
is paid here by calls, and so are the three marks on the open rows (E2E/KeyMarksThr.lean,
E2E/KeyShapeValues15.lean); what is left is gathered in one structure. Statements and proofs.

  `RangesOwes`    WHAT IS STILL OWED WHERE THE THREAD STANDS AT THE BORDER 15: the tree at hand in
                 front holds the job's tree's columns (`OldAt`) · the group's open rows say true
                 things of the member's words
  `sent_codes`, `sent_msgs`    in scope the sending's codes and messages are the written ones
  **`k12Front_ranges`**    the thread at 15 · the row of the two parts is lent its coins ·
                 `RangesOwes` ⟹ `K12Front`
  **`accepted_ranges`**    the half is laid · `RangesOwes` at every stand, at the coins that the
                 book lends the two parts there ⟹ `Accepted (laid₁ …) fall 15` at every letter fall

Limits.
- `RangesOwes` IS ASKED AT EVERY STAND OF THE THREAD, at the coins that the book lends there; NO
  MEMBER OF IT IS GIVEN. Its two clauses read values, which hang on the input, the coins and the
  challenges in front.
- THAT THE BOOK LENDS THIS JOB's TWO PARTS THEIR COINS AT ALL is not shown in this file: the frame's
  lending refuses a part that is typed at another count than the book's entry has; were the counts
  to part, the premise and the end would both be empty. It is shown, at all coins, in
  E2E/KeyRangesLends.lean.
- THE FIRST CLAUSE BINDS THE LETTER tb: the thread's own clause on the trees at hand ties the table
  behind the chain's own tree number 1 to tb. Where tb is simply defined as the job's own table the
  clause holds and says nothing of a run; it has content where tb is the table that the frame's play
  sends: E2E/KeyRangesWholeS.lean pays it from a tie on tb's own value. It asks the columns below
  2 ^ 22: it can be met only where tb's table behind that tree has a log-length of 22 or more. Its
  part "the tree is among those sent in front" is asked though this file could pay it.
- THE SECOND CLAUSE IS THE CONTENT, AND IT BINDS THE LETTER L: it speaks of the multiplicities that
  the letter entry names and of the coins that the book carries; the thread's own sentences that are
  open at the border 15 speak of L's witness, among them "every open row of the group holds at the
  witness". Nothing here ties the two: for an L whose witness's message is not these words the
  clause is false wherever the thread stands. The law from that sentence to this clause, under a
  named tie on L: E2E/KeyRangesGrows.lean.
- "The half is laid" is asked. In scope alone; at the written sizes. The written place and shape
  were typed off prints; in scope they are held against the description's own numbers
  (`place_sourced`) and against the run of its guards on shapes (`core15`).
- `Accepted` is a premise's form of the frame's: it says that the member's step accepts where the
  thread stands and the frame's play returns; that the thread stands there, and that the play
  returns, is not shown here.
- Another road ends at the same number: E2E/KeyShapeFirstAccepted.lean's `accepted_first15`, from
  `FitsAt` and one premise on `valsK12`; no statement ties the two; this file spends of the shape's
  road the term T15, `Enters` and the three marks alone.
- IT RESTS ON FILES THAT NO READER HAS SEEN, among them EveryAt, RunOfThr (this library's K12
  folder), E2E/KeyRangesReturns, KeyRangesSeat, KeyMarksThr, and four files of
  Johnson/Desc/K12/Honest/Shape/.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRangesJob
import E2E.KeyRangesShape15
import E2E.KeyRangesTrees
import E2E.KeyRangesReturns
import E2E.KeyShapeValues15
import Johnson.Desc.ProofFile.Honest.K12.EveryAt
import Johnson.Desc.ProofFile.Honest.K12.FrontAtKey
import Johnson.Desc.ProofFile.Honest.K12.TiesAtKey
import Johnson.Desc.ProofFile.Honest.K12.AtKeyRanges
import Johnson.Desc.ProofFile.Honest.K12.FormPubAt
import Johnson.Desc.ProofFile.Honest.K12.TermLen
import Johnson.Desc.ProofFile.Honest.K12.RunOfThr
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.K12.Honest.Shape.TestSeatAsksRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 P12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (Xi FirstState Claim enterRanges leaveRanges enterAndAsk
  rangesParams pieces)
open VerifiableInference.Desc.Ground.Sh (stTidyB stPlainB)
open OnBytes.Means (AllSay layoutOf)
open OnBytes.Slice (GF rdE begun runRows)
open AtPublicFiles.AtFiles (KeyNamed KeySourced keyFileDescription Enters rangesState)
open AtPublicFiles.AtFiles.Full (shape15_of_thr thinSh_15 testSh_15 leaves_15 six_sourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook rideMsg sendingPar_sent)
open AtPublicFiles.KeyTest (sMsg)
open H2K.Member (piKRFull codesKeyFull piKRFull_planOk)
open H2K.Pub (sgOf)
open Lk6.AtPlan (keyFull)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.Sh (claimsB asks_record_KR runRows_plain)
open ProofFile.Honest.K12

section
variable {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles} {K : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **What is still owed where the thread stands at the border 15.** s: the verifier's state. m:
where the prover's run stands. E: the tables at hand. C: the coins that the term reads. -/
structure RangesOwes (s : FirstState) (m : Mid (Local W₀ Rc Xi Unit) X') (E : Env)
    (C : TestCoins) : Prop where
  old : OldAt E ((rangesTestJob (X' := X') Xs N Pl entry groups first).trees₀ m.st.input (frontOf m) C.mem
    ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m) C))
    (fun k => [Fmt.TreeSource.own 1].getD k (.own 0))
  allSay : ∀ G, (rangesState s).st.groups[(rangesState s).g]? = some G →
    AllSay rdE (begun (rangesState s).st (rangesState s).g G)
      (runRows (rangesState s).st G).toList
      (wordsAt (begun (rangesState s).st (rangesState s).g G) (layoutOf (rangesState s).st G)
        (plainOne (sentRanges Xs entry groups first) m.st.input (C.mem 0)
          ((rangesTestJob (X' := X') Xs N Pl entry groups first).first m.st.input (frontOf m) C)))

/-- In scope the sending's codes are the written ones. -/
theorem sent_codes (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (sentRanges Xs entry groups first).P.codes = keyFull.codes :=
  (six_sourced hsrc scope).codes

/-- In scope its messages are the written ones. -/
theorem sent_msgs (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (sentRanges Xs entry groups first).P.sent = OnBytes.Wf.messageOf keyFull.ranges.x := by
  show (VerifiableInference.Desc.Key.sendingPar Xs.Y.k.oneTime pieces.msg _
    (OnBytes.Wf.messageOf Xs.Y.k.oneTime.ranges) groups).sent = _
  rw [sendingPar_sent, (six_sourced hsrc scope).ranges]
  rfl

variable (L : KeyFill (keyBook K) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins (keyBook K) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **`K12Front` at the thread, from what is still owed.** -/
theorem k12Front_ranges (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) {k : Coins (keyBook K)}
    {s : FirstState} {m : Mid (Local W₀ Rc Xi Unit) X'} {E : Env}
    (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
      Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
      restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)])
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E)
    (hc : lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
      [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c)
    (O : RangesOwes (X' := X') Xs N Pl entry groups first s m E
      (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1)) :
    K12Front (rangesTestJob (X' := X') Xs N Pl entry groups first)
      (enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams N)) leaveRanges s m E c := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  have hJ : (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).p = piKRFull := rfl
  have hrec : (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).rec₀ m.st.input
      (frontOf m) = rangesState s :=
    rec_of_thr Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb scope hsrc.named hT
  have hrec0 : recRanges (X' := X') Xs H2K.Member.nKRFull Pl m.st.input (frontOf m) =
      rangesState s := hrec
  have hsh := shape15_of_thr hsrc scope (laid₁ Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb) rfl
    (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT
  have hsent : E.sent = 2 := by
    obtain ⟨-, -, -, -, ⟨-, -, e, -⟩, -, -⟩ := hT
    rw [e, trees15_laid Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb hsrc scope]
  have hEnt : Enters Xs.Y.k.oneTime s :=
    AtPublicFiles.AtFiles.enters_of_B (AtPublicFiles.AtFiles.pubOf Xs) keyFull.codes
      (by rw [hsh]; exact AtPublicFiles.AtFiles.Full.enters15 (six_sourced hsrc scope))
  have hTidy : stTidyB s.d.st = true :=
    (congrArg (·.2.tidy) hsh).trans AtPublicFiles.AtFiles.Full.loc15.2.2
  have hM := AtPublicFiles.AtFiles.marks_of_thr (AtPublicFiles.AtFiles.Full.pre_len hsrc scope)
    (laid₁ Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb) rfl (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT
  have hCl : claimsB (rangesState s) = true :=
    AtPublicFiles.AtFiles.claims_of_gRng (AtPublicFiles.AtFiles.pubOf Xs) keyFull.codes H2K.Member.nKRFull
      (by rw [hsh]; exact AtPublicFiles.AtFiles.Full.gRng_six (six_sourced hsrc scope)) hM
  have hcd := sent_codes Xs H2K.Member.nKRFull Pl entry groups first hsrc scope
  have hms := sent_msgs Xs H2K.Member.nKRFull Pl entry groups first hsrc scope
  obtain ⟨Dp, h1, F, a1, a2, a3⟩ := front_data_KR (X := X') (sentRanges Xs entry groups first)
    (recRanges Xs H2K.Member.nKRFull Pl) m.st.input (frontOf m)
    (restCoins (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first) c.2.1) hcd hms
    (by rw [hrec0]; exact thinSh_15 s hsh) (by rw [hrec0]; exact hTidy)
    (by rw [hrec0]; exact hM.1) (by rw [hrec0]; exact hCl)
  obtain ⟨s₁, t₁, rest₁', hst, hk⟩ :=
    stages_KRJ (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first) hJ
  have hk' : (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).s₀.k =
      (sgOf (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).s₀).h +
        (sgOf (rangesTestJob (X' := X') Xs H2K.Member.nKRFull Pl entry groups first).s₀).g := by
    unfold TestJob.s₀
    rw [hst]
    exact hk
  refine ⟨?_, ⟨[22], fun k => [Fmt.TreeSource.own 1].getD k (.own 0), ?_, ?_, O.old⟩, ?_,
    piKRFull_planOk, formPubB_KR, termLen_KR,
    ⟨codesKeyFull, Dp, _, _, by rw [h1]; exact planB_KR, F, a1, a2, a3, ?_⟩, ?_⟩
  · exact agree_of_ties' _ (sMsg, 1) rfl (keyBook K) _ _ c hc _ _ (ties_ranges K hK) hk'
      fun mem mem' h => congrArg _ (jobRng_rows Xs H2K.Member.nKRFull Pl entry groups first _ _ mem
        mem' h)
  · show [((sentRanges Xs entry groups first).P.trees.getD 0 {}).logN] = [22]
    rw [depth_KR _ hcd hms]
  · rw [hsent]
    exact opensFit_KR _ hJ rfl
  · exact enters_of_thr Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb scope hsrc.named hT hEnt
      (asks_record_KR (rangesState s) (testSh_15 s hsh) hTidy
        (fun G hG => runRows_plain hM.1 hG) hCl)
  · intro G hG
    rw [hrec] at hG ⊢
    exact O.allSay G hG
  · intro t' rs gs ha
    rw [hrec] at ha
    exact leaves_15 s hsh t' rs gs ha s

/-- **The member is accepted, at every letter for a fall.** -/
theorem accepted_ranges (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (O : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)]),
      Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E →
      lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
          restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c →
      RangesOwes (X' := X') Xs N Pl entry groups first s m E
        (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    Accepted (laid₁ Xs N Pl L w₀ rc x hs tb) fall 15 :=
  accepted_every (laid₁ Xs N Pl L w₀ rc x hs tb) 15
    (rangesTestJob (X' := X') Xs N Pl entry groups first)
    (enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams N)) leaveRanges
    ⟨member_laid Xs N Pl L w₀ rc x hs tb scope hsrc.named _ rfl, hhalf,
      stages_KRJ _ (place_sourced hsrc scope),
      fun k s m E c hT hc => k12Front_ranges Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc
        scope c hT hc (O k s m E c hT hc)⟩ fall

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.sent_codes
#print axioms AtPublicFiles.KeyThread.sent_msgs
#print axioms AtPublicFiles.KeyThread.k12Front_ranges
#print axioms AtPublicFiles.KeyThread.accepted_ranges
