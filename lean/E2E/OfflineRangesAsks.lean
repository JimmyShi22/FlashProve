-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- No sorry.
/-
E2E/OfflineRangesAsks.lean: THE BRIDGE OF E2E/OfflineTestAsks.lean AT THE KEY FILE's PROXIMITY TEST ON THE RANGES (the first
chain's place ⟨1,–,5⟩): from where the first chain's thread stands at the border 15 to the two clauses on the
asks that are left of the condition at the test's second part (`LeftAtRanges`,
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowRangesAtRun.lean), at the state behind the first part's rounds and at
the blocks that the second part is handed as carried.

  `ranges_first_public`   the job's public part, in scope
  `ranges_asks_in_front`  the thread at 15 · the row of the two parts is lent · `RangesOwes`
                        (E2E/KeyRangesSeated.lean) ⟹ `AsksInFront` at the written codes and one tree
  `InRanges`              THE NAMED PREMISE: "the first chain's thread stands at the border 15 in front of this
                        state": the frame's own `InsideOf` (Honest/Law/Inside.lean) at the thread's sentence at
                        15 and the first part's number of rounds
  `OwesAtRanges`          THE OTHER: `RangesOwes` at every stand of the thread at 15, at the coins that the book
                        lends the two parts there: the premise of `accepted_ranges`, at one value of the coins
  `LeftOfInside`, `ranges_left_of_inside`   **THE BRIDGE**, its statement and its proof: the two ⟹ `LeftAtRanges`

Limits. Both premises are asked; no member of either is given here. `OwesAtRanges` holds the one sentence on
values: the group's open rows say true things of the member's words. Of `RangesOwes` the clause `allSay` alone
is spent. It is stated at a state on entry that is the job's own letter; under `InRanges` that state is the
structure that the test's seat makes of the verifier's state (`rec_of_thr`, E2E/KeyRangesJob.lean). Nothing on
any property.
-/
import E2E.OfflineTestAsks
import E2E.OfflineRangesFive
import E2E.KeyRangesSeated
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowRangesPub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Sim2 (LeftAtRanges simRanges)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces FirstState)
open OnBytes.Slice (GF)
open H2K.Member (piKRFull codesKeyFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub rngPlace)
open AtPublicFiles.KeyThread (rangesTestJob RangesOwes laid₁ KeyFill)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open VerifierAndGoals (PublicFiles InScope)

section Key
variable {W₀ Rc Cells M Smp Rec : Type} {Z : PublicFiles} {K : KeyPub} (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (entry : Local W₀ Rc Xi Unit → Nat → Nat → GF) (groups : List (List Nat))
  (first : Nat) (L : KeyFill (keyBook K) W₀ Rc Cells M Smp Rec) (w₀ : W₀) (rc : Rc) (x : Xi)
  (hs : List (Placed (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit))
  (tb : Fmt.TreeSource → Coins (keyBook K) → Local W₀ Rc Xi Unit → List Fmt.Drawn → Place × Table)

/-- The job's public part, in scope. -/
theorem ranges_first_public (hsrc : KeySourced Z Xs N Pl) (scope : InScope Z = true) :
    ∃ s next rest,
      FirstPartPublic (rangesTestJob (X' := Unit) Xs N Pl entry groups first) s next rest := by
  obtain ⟨s, next, rest, P, -⟩ := ranges_public entry groups first hsrc scope
  exact ⟨s, next, rest, P.stages, P.split, P.enough, P.sorts, P.tables⟩

/-- **The sentence in front of the test, where the thread stands at the border 15.** -/
theorem ranges_asks_in_front (hsrc : KeySourced Z Xs N Pl)
    (scope : InScope Z = true) {k : Coins (keyBook K)} {s : FirstState}
    {m : Mid (Local W₀ Rc Xi Unit) Unit} {E : Env} (C : TestCoins)
    (hT : Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E)
    (O : RangesOwes (X' := Unit) Xs N Pl entry groups first s m E C) :
    AsksInFront (rangesTestJob (X' := Unit) Xs N Pl entry groups first) codesKeyFull 1 m.st.input
      (frontOf m) C := by
  obtain rfl := AtPublicFiles.AtFiles.Full.nums_sourced hsrc scope
  have hrec0 : AtPublicFiles.KeyThread.recRanges (X' := Unit) Xs H2K.Member.nKRFull Pl m.st.input (frontOf m) =
      AtPublicFiles.AtFiles.rangesState s :=
    AtPublicFiles.KeyThread.rec_of_thr Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb scope hsrc.named hT
  have hsh := AtPublicFiles.AtFiles.Full.shape15_of_thr hsrc scope
    (laid₁ Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb) rfl (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT
  have hTidy : VerifiableInference.Desc.Ground.Sh.stTidyB s.d.st = true :=
    (congrArg (·.2.tidy) hsh).trans AtPublicFiles.AtFiles.Full.loc15.2.2
  have hM := AtPublicFiles.AtFiles.marks_of_thr (AtPublicFiles.AtFiles.Full.pre_len hsrc scope)
    (laid₁ Xs H2K.Member.nKRFull Pl L w₀ rc x hs tb) rfl (fun _ _ _ _ _ hb => ⟨_, hb⟩) hT
  have hCl : ProofFile.Honest.Sh.claimsB (AtPublicFiles.AtFiles.rangesState s) = true :=
    AtPublicFiles.AtFiles.claims_of_gRng (AtPublicFiles.AtFiles.pubOf Xs) Lk6.AtPlan.keyFull.codes H2K.Member.nKRFull
      (by rw [hsh]; exact AtPublicFiles.AtFiles.Full.gRng_six (AtPublicFiles.AtFiles.Full.six_sourced hsrc scope)) hM
  have hcd := AtPublicFiles.KeyThread.sent_codes Xs H2K.Member.nKRFull Pl entry groups first hsrc scope
  have hms := AtPublicFiles.KeyThread.sent_msgs Xs H2K.Member.nKRFull Pl entry groups first hsrc scope
  obtain ⟨Dp, h1, F, a1, a2, a3⟩ := front_data_KR (X := Unit)
    (AtPublicFiles.KeyThread.sentRanges Xs entry groups first)
    (AtPublicFiles.KeyThread.recRanges Xs H2K.Member.nKRFull Pl) m.st.input (frontOf m) C hcd hms
    (by rw [hrec0]; exact AtPublicFiles.AtFiles.Full.thinSh_15 s hsh) (by rw [hrec0]; exact hTidy)
    (by rw [hrec0]; exact hM.1) (by rw [hrec0]; exact hCl)
  refine ⟨Dp, _, _, h1, planB_KR, frontAsksD_of _ _ _ F, a1, a2, a3, fun G hG => ?_⟩
  have hrec : (rangesTestJob (X' := Unit) Xs H2K.Member.nKRFull Pl entry groups first).rec₀ m.st.input
      (frontOf m) = AtPublicFiles.AtFiles.rangesState s := hrec0
  rw [hrec] at hG ⊢
  exact O.allSay G hG

/-- **THE NAMED PREMISE: the first chain's thread stands at the border 15 in front of this state.** b: the
sub-protocol of the test. m: the state behind the first part's rounds. E: the tables at hand there. -/
def InRanges (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl) (k : Coins (keyBook K))
    (m : Mid (Local W₀ Rc Xi Unit) Unit) (E : Env) : Prop :=
  InsideOf Face.own (keyBook K) 0 hs b (Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15)
    (firstLen piKRFull.nums.stages) k m E

/-- **What is still owed wherever the thread stands at the border 15**, at the coins that the book lends
the test's two parts there, at one value of the run's coins. -/
def OwesAtRanges (k : Coins (keyBook K)) : Prop :=
  ∀ s m E (c : RowCoins [(firstPart (rangesTestJob (X' := Unit) Xs N Pl entry groups first) :
      Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit),
      restPart (rangesTestJob (X' := Unit) Xs N Pl entry groups first)]),
    Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15 k s m E →
    lendRow (keyBook K) ((keyBook K).rowsOf 0) (k.look 0)
      (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p.place
      [(firstPart (rangesTestJob (X' := Unit) Xs N Pl entry groups first) :
        Part (Local W₀ Rc Xi Unit) (Local W₀ Rc Xi Unit) Unit),
        restPart (rangesTestJob (X' := Unit) Xs N Pl entry groups first)] 0 = .ok c →
    RangesOwes (X' := Unit) Xs N Pl entry groups first s m E
      (restCoins (rangesTestJob (X' := Unit) Xs N Pl entry groups first) c.2.1)

/-- **THE BRIDGE: its statement.** -/
def LeftOfInside : Prop :=
  fullPub = some K → KeySourced Z Xs N Pl → InScope Z = true →
  ∀ (b : Block (keyFileDescription Xs N Pl).S₁ (keyFileDescription Xs N Pl).Cl), b ∈ (keyFileDescription Xs N Pl).first.blocksInOrder →
    b.place = rngPlace →
    (hs.find? fun g => g.place == b.place) =
      some (proverSideOfProximityTest (rangesTestJob (X' := Unit) Xs N Pl entry groups first)) →
    ∀ (k : Coins (keyBook K)) (m : Mid (Local W₀ Rc Xi Unit) Unit) (E : Env),
      InRanges Xs N Pl L w₀ rc x hs tb b k m E →
      OwesAtRanges Xs N Pl entry groups first L w₀ rc x hs tb k →
      ∀ ca : CsAll (restMember (V := Local W₀ Rc Xi Unit)
          (rangesTestJob (X' := Unit) Xs N Pl entry groups first) (simRanges Xs N Pl)).part.carries,
        carriedAt (keyBook K) k 0 ⟨rngPlace, 1⟩ (restMember (V := Local W₀ Rc Xi Unit)
          (rangesTestJob (X' := Unit) Xs N Pl entry groups first) (simRanges Xs N Pl)).part = .ok ca →
        LeftAtRanges (rangesTestJob (X' := Unit) Xs N Pl entry groups first) codesKeyFull
          piKRFull.nums.first (stretches _ ca) m

/-- **THE BRIDGE: its proof.** -/
theorem ranges_left_of_inside :
    LeftOfInside (Z := Z) Xs N Pl entry groups first L w₀ rc x hs tb := by
  intro hK hsrc scope b hb hbp hhalf k m E hin O ca hca
  obtain ⟨a, next, rest, P⟩ := ranges_first_public Xs N Pl entry groups first hsrc scope
  have hlaid := ranges_laid entry groups first hsrc scope hb hbp
  have hor : b.oracles.length = b.rounds.length := by
    have h := ((planOk_all hsrc.named.plan).1 b hb).2
    unfold Block.shaped at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1
  have hJ : (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p = piKRFull :=
    AtPublicFiles.KeyThread.place_sourced hsrc scope
  have hpl : b.place = (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p.place := by
    rw [hbp, hJ]
    exact ProofFile.Honest.K12.Sim2.place_KR.symm
  have hin' : InsideOf Face.own (keyBook K) 0 hs b (Thr (laid₁ Xs N Pl L w₀ rc x hs tb) 15)
      (firstLen (rangesTestJob (X' := Unit) Xs N Pl entry groups first).p.nums.stages) k m E := by
    rw [hJ]
    exact hin
  have h := left_of_inside (rangesTestJob (X' := Unit) Xs N Pl entry groups first) codesKeyFull 1 a next rest
    P (by rw [hJ]; exact formPubB_KR) hlaid hor hhalf hin'
    (fun st m₀ E₀ c hT hc => ranges_asks_in_front Xs N Pl entry groups first L w₀ rc x hs tb hsrc
      scope _ hT (O st m₀ E₀ c hT (by rw [← hpl]; exact hc))) ca (by rw [hbp]; exact hca)
  obtain ⟨Dp, cc, R, h1, h2, h3⟩ := h
  exact ⟨Dp, cc, R, h1.trans ProofFile.Honest.K12.Sim2.first_KR_length.symm, h2, h3⟩

end Key

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.ranges_first_public
#print axioms AtPublicFiles.OfflineRows.ranges_asks_in_front
#print axioms AtPublicFiles.OfflineRows.InRanges
#print axioms AtPublicFiles.OfflineRows.OwesAtRanges
#print axioms AtPublicFiles.OfflineRows.LeftOfInside
#print axioms AtPublicFiles.OfflineRows.ranges_left_of_inside
