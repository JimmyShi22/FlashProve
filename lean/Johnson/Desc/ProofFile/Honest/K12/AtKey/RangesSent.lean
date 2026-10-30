-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesSent.lean: the truth of the rows that the key file's
test on the ranges takes in, said of what the sender sends: of the rows that the sending of the
multiplicities makes at its own purse, with no coin of the test's in it.

  plainOf        one message's rows as plain rows, at every member's number
  wordsAt_plain  the words of the job's plain rows are those of the member's rows: the words read
                 the member's main and mask rows alone
  RowsTrueOf     the rows that the test takes in, at the verifier's state, are true of the words of
                 a message's rows
  rowsTrue_of_sent   at the coins that the book lends the test and the purse that it lends the
                 sender, RowsTrueOf at the sender's rows gives RowsTrue
  acceptedS_at_sent   AcceptedS at member 15 at the key file's prover, from RowsTrueOf at the
                 sender's rows

By what. coinsTie_KR (K12/BookTiesAtKey.lean): the test's stretch and the sender's purse hold the
same coins; mem_is_sent (K12/RowsCongr.lean): so the member's rows are the sender's.

What is left of the rows' truth. The premise of acceptedS_at_sent reads the parts through the job's
sending alone; under MsgIsJob (RangesAtProver.lean) that sending is the parts' msg. It says: where
the pair stands at the border 15, each open row of the ranges' group, and each sample row of its one
member, holds of the rows that the sender made at the input and its purse. The open rows are those
that the two lookups' sides left: they read what these sides sent. So the premise binds the parts'
msg to their look0 and look1: the multiplicities that msg lays have to be those that the lookups'
claims speak of. It reads no coin of the test's.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: the premise is asked from the pair ThrS.
- The premise is given at no value. It is no tautology: nothing here says that the words that
  entry lays agree with what the lookups' sides sent.
- In scope; at the written sizes.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesTable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open OnBytes (Statement GroupLayout)
open OnBytes.Means (AllSay layoutOf)
open OnBytes.Slice (GF rdE begun runRows)
open Johnson.Prover.Send (shapeAt)
open H2K.Member (nKRFull)
open AtPublicFiles.AtFiles (KeySourced rangesState)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeyTest (sMsg)
open AtPublicFiles.KeyThread (KeyFill laid₁ recRanges rangesTestJob sentRanges purse_cut sent_codes sent_msgs
  ride_same)
open AtFullSide.K12 (withTests)
open VerifierAndGoals (InScope)

/-- One message's rows as plain rows, at every member's number. d: the rows are of degree 3. -/
def plainOf (V : Johnson.Prover.Send.Rows) (d : Bool) : PlainRows where
  M := fun _ => V.main d
  T := fun _ => V.mainTl d
  Z := fun _ => V.mask
  ZT := fun _ => V.maskTl
  F := fun _ _ => 0
  FT := fun _ _ => 0

/-- **The words of the job's plain rows are those of the member's rows.** -/
theorem wordsAt_plain {W : Type} (S : Statement) (Ly : GroupLayout) (Q : OneSent W) (w : W)
    (Sx : Stretch) (Pst : Johnson.Prover.Link.PS) (V : Johnson.Prover.Send.Rows) (hV : V = Q.mem w Sx) :
    wordsAt S Ly (plainOne Q w Sx Pst) =
      wordsAt S Ly (plainOf V ((shapeAt Q.P 0).mainDeg == 3)) := by
  subst hV
  funext o part idx
  unfold wordsAt
  rfl

/-- **The rows that the test takes in are true of the words of a message's rows.** -/
def RowsTrueOf (s : FirstState) (V : Johnson.Prover.Send.Rows) (d : Bool) : Prop :=
  ∀ G, (rangesState s).st.groups[(rangesState s).g]? = some G →
    AllSay rdE (begun (rangesState s).st (rangesState s).g G)
      (runRows (rangesState s).st G).toList
      (wordsAt (begun (rangesState s).st (rangesState s).g G) (layoutOf (rangesState s).st G)
        (plainOf V d))

section
variable {W₀ Rc Cells M Smp Rec X₀ X Wk : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **RowsTrue from the sender's rows.** k: a run's coins. c: what the book lends the test. c₁: what
it lends the sender. -/
theorem rowsTrue_of_sent (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (k : Coins (keyBook K₀))
    (c : RowCoins [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
      Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
      restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)])
    (hc : lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place
      [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)] 0 = .ok c)
    (c₁ : Cs (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride))
    (hown : ((k.look 0) sMsg).2.cut ⟨0, 0⟩
      (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) =
        some c₁)
    (s : FirstState) (m : Mid (Local W₀ Rc Xi Unit) X)
    (h : RowsTrueOf s (K1.rowsR (sentRanges Xs entry groups first).P
        (sentRanges Xs entry groups first).ride
        ((sentRanges Xs entry groups first).data m.st.input) c₁ 0)
      ((shapeAt (sentRanges Xs entry groups first).P 0).mainDeg == 3)) :
    RowsTrue (X' := X) Xs N Pl entry groups first s m
      (restCoins (rangesTestJob (X' := X) Xs N Pl entry groups first) c.2.1) := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  have T := coinsTie_KR K₀ hK (sentRanges Xs entry groups first)
    (sent_codes Xs nKRFull Pl entry groups first hsrc scope)
    (sent_msgs Xs nKRFull Pl entry groups first hsrc scope) ride_same rfl
    (recRanges Xs nKRFull Pl) m.st.input ((keyBook K₀).rowsOf 0) (k.look 0) c hc c₁ hown
  have e : K1.rowsR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride
      ((sentRanges Xs entry groups first).data m.st.input) c₁ 0 =
      (sentRanges Xs entry groups first).mem m.st.input
        ((restCoins (rangesTestJob (X' := X) Xs nKRFull Pl entry groups first) c.2.1).mem 0) :=
    mem_is_sent (sentRanges Xs entry groups first) m.st.input _ c₁ T.memF T.memE
  intro G hG
  rw [wordsAt_plain _ _ (sentRanges Xs entry groups first) m.st.input _ _ _ e]
  exact h G hG

variable (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (own₀ : X)
  (rest : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)
  (Kp : KeyParts W₀ Rc X₀ X Wk) (pU pO : P12)

/-- **Member 15 is accepted at the key file's prover, from what the sender sends.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem acceptedS_at_sent (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hRows : ∀ k s m E (c₁ : Cs (K1.dueR (sentRanges Xs entry groups first).P
        (sentRanges Xs entry groups first).ride)),
      ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
        (tbRng Xs N Pl entry groups first own₀ rest)) Said 15 k s m E →
      ((k.look 0) sMsg).2.cut ⟨0, 0⟩
        (K1.dueR (sentRanges Xs entry groups first).P (sentRanges Xs entry groups first).ride) =
          some c₁ →
      RowsTrueOf s (K1.rowsR (sentRanges Xs entry groups first).P
          (sentRanges Xs entry groups first).ride
          ((sentRanges Xs entry groups first).data m.st.input) c₁ 0)
        ((shapeAt (sentRanges Xs entry groups first).P 0).mainDeg == 3))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first
      (tbRng Xs N Pl entry groups first own₀ rest)) Said fall 15 :=
  acceptedS_at_table Xs N Pl entry groups first own₀ rest L w₀ rc x Kp pU pO hK hsrc scope hP Said
    (fun k s m E c hT hc => by
      obtain ⟨c₁, hown⟩ := purse_cut Xs N Pl entry groups first hK hsrc scope k
      exact rowsTrue_of_sent Xs N Pl entry groups first hK hsrc scope k c hc c₁ hown s m
        (hRows k s m E c₁ hT hown))
    fall

end

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.plainOf
#print axioms ProofFile.Honest.K12.AtKey.wordsAt_plain
#print axioms ProofFile.Honest.K12.AtKey.rowsTrue_of_sent
#print axioms ProofFile.Honest.K12.AtKey.acceptedS_at_sent
