-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyRangesSeatedS.lean: THE LAW OF E2E/KeyRangesSeated.lean FROM THE PAIR: the key file's test on
the ranges, seated in the first chain's thread `laid₁`, is accepted in the form that the key file's
law on acceptance takes at a row (`AcceptedS`, Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean;
`YesS` in E2E/DebtsOfPairs.lean): from the thread TOGETHER WITH A LETTER ON WHERE THE PROVER's RUN
STANDS. What is still owed (`RangesOwes`) is asked at the stands of the pair alone: fewer than the
thread's. A statement and its proof, by calls.

  **`acceptedS_ranges`**   the half is laid · `RangesOwes` at every stand of the pair, at the coins
                 that the book lends the two parts there ⟹ `AcceptedS (laid₁ …) Said fall 15`, at
                 every letter Said and every letter fall

Limits. Those of E2E/KeyRangesSeated.lean. `RangesOwes` is met at no value. Nothing on completeness,
on soundness or on what is hidden.


-/
import E2E.KeyRangesSeated
import Johnson.Desc.ProofFile.Honest.K12.EveryAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyThread
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi FirstState Claim enterRanges leaveRanges enterAndAsk
  rangesParams)
open OnBytes.Slice (GF)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open VerifierAndGoals (PublicFiles InScope)
open ProofFile.Honest
open ProofFile.Honest.K12

variable {W₀ Rc Cells M Smp Rec X' : Type} {Z : PublicFiles} {K : KeyPub}
  (Xs : VerifiableInference.Desc.Key.Source) (N : H2U.PlaceNums)
  (Pl : VerifiableInference.Desc.Key.LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
  (L : KeyFill (keyBook K) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'))
  (tb : Fmt.TreeSource → Coins (keyBook K) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **The member is accepted, from the pair, at every letter for a fall.** -/
theorem acceptedS_ranges (hK : fullPub = some K) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true)
    (Said : Nat → Coins (keyBook K) → Mid (Local W₀ Rc Xi Unit) X' → Prop)
    (hhalf : (hs.find? fun g => g.place == (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := X') Xs N Pl entry groups first)))
    (O : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
        restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15 k s m E →
      lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X') Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X') Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X'),
          restPart (rangesTestJob (X' := X') Xs N Pl entry groups first)] 0 = .ok c →
      RangesOwes (X' := X') Xs N Pl entry groups first s m E
        (restCoins (rangesTestJob (X' := X') Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x hs tb) Said fall 15 :=
  acceptedS_every (laid₁ Xs N Pl L w₀ rc x hs tb) Said 15
    (rangesTestJob (X' := X') Xs N Pl entry groups first)
    (enterAndAsk (enterRanges Xs.Y.k.oneTime) (rangesParams N)) leaveRanges
    ⟨member_laid Xs N Pl L w₀ rc x hs tb scope hsrc.named _ rfl, hhalf,
      stages_KRJ _ (place_sourced hsrc scope),
      fun k s m E c hT hc => k12Front_ranges Xs N Pl entry groups first L w₀ rc x hs tb hK hsrc
        scope c hT.1 hc (O k s m E c hT hc)⟩ fall

end AtPublicFiles.KeyThread

#print axioms AtPublicFiles.KeyThread.acceptedS_ranges
