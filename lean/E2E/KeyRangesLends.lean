-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesLends.lean: THE KEY FILE's BOOK LENDS THE TWO PARTS OF THE TEST ON THE RANGES THEIR
COINS, AT EVERY FAMILY OF A RUN's COINS, FOR THE JOB `rangesTestJob` (E2E/KeyRangesJob.lean), in scope. The
laws of E2E/KeyRangesSeated.lean take "the row of the two parts is lent its coins c" as a premise;
the frame's lending refuses a part that is typed at another count than the book's entry has. Here
that premise is shown to be met at all coins: so these laws are not empty on that account. By
`lends_KR` (Johnson/Desc/ProofFile/Honest/K12/MembersAtKey.lean), which holds the job's count
against the book's by the kernel's own evaluation. Statements and proofs.

  `ride_same`    the riding table of the sending of the multiplicities, in two files' texts, is one
  **`members_ranges`**   in scope the job's list of members is the skeleton's (`jobRanges`,
                 E2E/KeyTestSizes.lean)
  **`lends_ranges`**   in scope, at the key file's book at the written sizes, wherever the half is
                 laid, AT ALL COINS: the row is lent its coins, and the laying of the member's steps
                 returns

Limits. In scope; at the written sizes. It says that the lending returns; nothing on what the coins
are. Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyRangesSeated
import Johnson.Desc.ProofFile.Honest.K12.MembersAtKey

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi FirstState Claim enterRanges leaveRanges enterAndAsk
  rangesParams)
open OnBytes.Slice (GF)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook rideMsg)
open AtPublicFiles.KeyTest (sMsg jobRanges)
open H2K.JointK (rngEntry)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12

theorem ride_same : rideMsg = rideKR := rfl

section
variable {W₀ Rc X' : Type} {Z : PublicFiles} {K : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **In scope the job's list of members is the skeleton's.** -/
theorem members_ranges (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    (rangesTestJob (X' := X') Xs N Pl entry groups first).members = jobRanges.members := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  exact members_KR (sentRanges Xs entry groups first)
    (sent_codes Xs H2K.Member.nKRFull Pl entry groups first hsrc scope)
    (sent_msgs Xs H2K.Member.nKRFull Pl entry groups first hsrc scope) ride_same rfl _

/-- **The book lends the row its coins, at all coins.** -/
theorem lends_ranges (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (k : Coins (keyBook K)) (v : Option (Local W₀ Rc Xi Unit)) :
    ∃ c, lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
          restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c ∧
      chainSteps (keyBook K) ((keyBook K).rowsOf 0) (k.look 0) v [rngEntry Xs.Y.k.oneTime N] hs =
        .ok ((proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)).steps
          (rngEntry Xs.Y.k.oneTime N) v c) := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  exact lends_KR K hK (sentRanges Xs entry groups first)
    (sent_codes Xs H2K.Member.nKRFull Pl entry groups first hsrc scope)
    (sent_msgs Xs H2K.Member.nKRFull Pl entry groups first hsrc scope) ride_same rfl
    (recRanges Xs H2K.Member.nKRFull Pl) (rngEntry Xs.Y.k.oneTime H2K.Member.nKRFull)
    (enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams H2K.Member.nKRFull)) leaveRanges
    (seatOf_rngEntry Xs.Y.k.oneTime H2K.Member.nKRFull _ rfl) hs hhalf k v

end

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.ride_same
#print axioms AtPublicFiles.KeyThread.members_ranges
#print axioms AtPublicFiles.KeyThread.lends_ranges
