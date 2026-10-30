-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/RangesAtProver.lean: the key file's test on the ranges at
the key file's prover: PlaysS and AcceptedS at member 15 of the first chain's thread whose halves
are those of keyProver (E2E/KeyProver.lean), at parts whose letter rng is the test's half; and so at
the parts with the four tests laid (withTests, AtFullSide/K12/KeyFourTests.lean).

  find_of_nodup     in a list whose places are apart, a search by a member's place finds it
  find_rng          keyProver's first chain finds the test's half at the test's place
  atPlaces_withTests   the parts with the four tests stand at the first chain's places, where the
                    parts did, in scope
  MsgIsJob          THE PREMISE ON THE PARTS: what their sending of the multiplicities lays is what
                    the test's job reads: P, ride, data
  playsS_at_prover, acceptedS_at_prover   PlaysS and AcceptedS at keyProver
  playsS_at_tests, acceptedS_at_tests   the same at withTests

What is asked of the parts. AtPlaces: the six other halves of the first chain bear their places, so
that a search by the test's place finds the test. MsgIsJob, for RowsTrue to speak of what was sent:
K.msg lays what sentRanges lays at the letters entry, groups, first that the test is laid at. So
entry is K.msg's own: the matrix that the sender reads. No theorem
here needs MsgIsJob: PlaysS reads no row, and AcceptedS reads the rows through RowsTrue alone,
which speaks of the job's words. It is what makes these words the sent ones: without it RowsTrue
can hold of words that no sender sent.

Limits.
- NOT IN FRONT OF A LAW OVER COINS: as RangesPlays.lean and RangesAccepted.lean.
- The parts' other fields, and the letters L and tb of the thread, stay letters.
- That ready returns at these halves, that the thread holds at a run, and that the lookups' sides
  send what makes RowsTrue hold are not said here.
- In scope; at the written sizes.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.KeyFourTests
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesAccepted
import Johnson.Desc.ProofFile.Honest.K12.AtKey.RangesPlays

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Key (Xi FirstState Source LaterPlaces)
open OnBytes.Slice (GF)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.KeyBook (KeyPub fullPub keyBook)
open AtPublicFiles.KeyFile (KeyParts keyProver first_places)
open AtPublicFiles.KeyThread (KeyFill laid₁ D rangesTestJob sentRanges TbIsSent place_sourced)
open AtFullSide.K12 (withTests)
open VerifierAndGoals (InScope)

/-- **In a list whose images are apart, a search by a member's image finds it.** -/
theorem find_of_nodup {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) {g : α} :
    ∀ (l : List α), g ∈ l → (l.map f).Nodup → l.find? (fun h => f h == f g) = some g
  | [], hm, _ => by cases hm
  | a :: t, hm, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases e : f a = f g
    · have hag : a = g := by
        rcases List.mem_cons.1 hm with rfl | h
        · rfl
        · exact absurd (e ▸ List.mem_map_of_mem h) hn.1
      rw [List.find?_cons, beq_iff_eq.2 e]
      rw [hag]
    · have hg : g ∈ t := by
        rcases List.mem_cons.1 hm with rfl | h
        · exact absurd rfl e
        · exact h
      rw [List.find?_cons, show (f a == f g) = false from beq_false_of_ne e]
      exact find_of_nodup f t hg hn.2

section
variable {W₀ Rc X₀ X Wk Cells M Smp Rec : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Kp : KeyParts W₀ Rc X₀ X Wk)
  (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- **The first chain finds the test's half at the test's place.** -/
theorem find_rng (hP : Kp.AtPlaces) (hr : Kp.rng = proverSideOfProximityTest (rangesTestJob Xs N Pl entry groups first)) :
    ((keyProver Kp).first.find? fun g =>
      g.place == (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place) =
      some (proverSideOfProximityTest (rangesTestJob Xs N Pl entry groups first)) := by
  have hmem : Kp.rng ∈ (keyProver Kp).first := by
    show Kp.rng ∈ [_, _, _, _, Kp.rng, _, _]
    simp
  have hnd : ((keyProver Kp).first.map (·.place)).Nodup := by
    rw [first_places Kp hP]
    decide
  have hf := find_of_nodup (fun g : Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X =>
    g.place) (keyProver Kp).first hmem hnd
  rw [hr] at hf
  exact hf

/-- The parts with the four tests stand at the first chain's places, where the parts did. -/
theorem atPlaces_withTests (h : Kp.AtPlaces) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (pU pO : P12) :
    (withTests Kp Xs N Pl pU pO entry groups first).AtPlaces := by
  refine ⟨h.idx, h.msg, h.look0, h.look1, ?_, h.batt, h.w⟩
  show (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place = _
  rw [AtPublicFiles.KeyThread.jobRng_p, place_sourced hsrc scope]
  decide +kernel

/-- **The premise on the parts**: what their sending of the multiplicities lays is what the test's
job reads: its public data, what rides, and its data at every input and front. The number of its
first message is not read by the job. -/
structure MsgIsJob : Prop where
  par : Kp.msg.P = (sentRanges Xs entry groups first).P
  ride : Kp.msg.ride = (sentRanges Xs entry groups first).ride
  data : ∀ (w : Local W₀ Rc Xi Unit) (fr : Front X),
    Kp.msg.data w fr = (sentRanges Xs entry groups first).data w

variable (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (tb : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **Member 15 plays at the key file's prover.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem playsS_at_prover (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (hr : Kp.rng = proverSideOfProximityTest (rangesTestJob Xs N Pl entry groups first))
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x (keyProver Kp).first tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x (keyProver Kp).first tb k m)
    (own₀ : X)
    (htb : ∀ τ, τ < 3 → tb (.own (2 + τ)) =
      testTbl 0 (rangesTestJob (X' := X) Xs N Pl entry groups first) own₀
        (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ) :
    PlaysS (laid₁ Xs N Pl L w₀ rc x (keyProver Kp).first tb) Said 15 :=
  playsS_rng Xs N Pl entry groups first L w₀ rc x _ tb hK hsrc scope Said
    (find_rng Kp Xs N Pl entry groups first hP hr) hTb own₀ htb

/-- **Member 15 is accepted at the key file's prover.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem acceptedS_at_prover (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (hr : Kp.rng = proverSideOfProximityTest (rangesTestJob Xs N Pl entry groups first))
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x (keyProver Kp).first tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x (keyProver Kp).first tb k m)
    (hRows : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x (keyProver Kp).first tb) Said 15 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)] 0 = .ok c →
      RowsTrue (X' := X) Xs N Pl entry groups first s m
        (restCoins (rangesTestJob (X' := X) Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x (keyProver Kp).first tb) Said fall 15 :=
  acceptedS_rng Xs N Pl entry groups first L w₀ rc x _ tb hK hsrc scope Said
    (find_rng Kp Xs N Pl entry groups first hP hr) hTb hRows fall

end

section
variable {W₀ Rc X₀ X Wk Cells M Smp Rec : Type} {Z : VerifierAndGoals.PublicFiles} {K₀ : KeyPub}
  (Kp : KeyParts W₀ Rc X₀ X Wk)
  (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (pU pO : P12)
  (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)
  (L : KeyFill (keyBook K₀) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (tb : Fmt.TreeSource → Coins (keyBook K₀) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- **Member 15 plays at the prover with the four tests laid.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem playsS_at_tests (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb k m)
    (own₀ : X)
    (htb : ∀ τ, τ < 3 → tb (.own (2 + τ)) =
      testTbl 0 (rangesTestJob (X' := X) Xs N Pl entry groups first) own₀
        (roundsTo (D Xs N Pl).first.blocksInOrder 15) (fun _ _ _ => true) τ) :
    PlaysS (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb) Said 15 :=
  playsS_at_prover _ Xs N Pl entry groups first L w₀ rc x tb hK hsrc scope
    (atPlaces_withTests Kp Xs N Pl entry groups first hP hsrc scope pU pO) rfl Said hTb own₀ htb

/-- **Member 15 is accepted at the prover with the four tests laid.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem acceptedS_at_tests (hK : fullPub = some K₀) (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) (hP : Kp.AtPlaces)
    (Said : Nat → Coins (keyBook K₀) → Mid (Local W₀ Rc Xi Unit) X → Prop)
    (hTb : ∀ k s m E, ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb) Said 15 k s m E →
      TbIsSent Xs N Pl entry groups first L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb k m)
    (hRows : ∀ k s m E (c : RowCoins [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
        restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)]),
      ThrS (laid₁ Xs N Pl L w₀ rc x
        (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb) Said 15 k s m E →
      lendRow (keyBook K₀) ((keyBook K₀).rowsOf 0) (k.look 0)
        (rangesTestJob (X' := X) Xs N Pl entry groups first).p.place
        [(firstPart (rangesTestJob (X' := X) Xs N Pl entry groups first) :
          Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) X),
          restPart (rangesTestJob (X' := X) Xs N Pl entry groups first)] 0 = .ok c →
      RowsTrue (X' := X) Xs N Pl entry groups first s m
        (restCoins (rangesTestJob (X' := X) Xs N Pl entry groups first) c.2.1))
    (fall : Nat → FirstState → List Fmt.Drawn → Option String) :
    AcceptedS (laid₁ Xs N Pl L w₀ rc x
      (keyProver (withTests Kp Xs N Pl pU pO entry groups first)).first tb) Said fall 15 :=
  acceptedS_at_prover _ Xs N Pl entry groups first L w₀ rc x tb hK hsrc scope
    (atPlaces_withTests Kp Xs N Pl entry groups first hP hsrc scope pU pO) rfl Said hTb hRows fall

end

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.find_of_nodup
#print axioms ProofFile.Honest.K12.AtKey.find_rng
#print axioms ProofFile.Honest.K12.AtKey.atPlaces_withTests
#print axioms ProofFile.Honest.K12.AtKey.playsS_at_prover
#print axioms ProofFile.Honest.K12.AtKey.acceptedS_at_prover
#print axioms ProofFile.Honest.K12.AtKey.playsS_at_tests
#print axioms ProofFile.Honest.K12.AtKey.acceptedS_at_tests
