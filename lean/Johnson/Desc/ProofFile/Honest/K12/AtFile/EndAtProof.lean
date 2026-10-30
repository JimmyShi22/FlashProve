-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/EndAtProof.lean: the end of a shared chain laid as the proof
file's: a thread whose list is nine members, the test on G_u, the test on G_omega and the end: the
verifier's state at border 11 has the shape that the guards' run gives, so the end says yes. Nothing
of what the two tests leave is read but its shape.

  gKP, ZP              the guards on the shape at any plan of K14's eight and any two tests
  tidy_kept_at, carries_at   (B1) at every member
  accepted_at_end      the end is accepted at every stand at 11

By what. accepted_sealed, shape_at, run_front, carries2, carries_withMark, test₂_carries,
end₂_carries, end₂_returns: the twin at the proof file of accepted_eleven (E2E/KeyAcceptEleven.lean).

Limits.
  * hyes, that the guards' run returns, is a premise here: a closed test answers it.
  * Nothing on completeness, soundness or hiding.
-/
import E2E.KeyShapeSharedTies
import E2E.KeyThreads
import Johnson.Desc.K12.Law.SitsChains

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open OnBytes (TableKey OracleNotice)
open OnBytes.Params
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat
open _root_.Desc.K14 (P14 St blocksOr)
open _root_.Desc.K14.Honest (Eight FlatAt)
open _root_.Desc.K14.Shape (Sh2 sh2 factsB updS)
open ProofFile.Honest.K14 (Plan2 ChainAt carries2)
open H2K.JointK (guEntry omegaEntry pGu pGomega)
open AtPublicFiles.AtFiles (Sh₂ sh₂ gTest₂ gEnd₂ withMark test₂_carries end₂_carries end₂_returns
  carries_withMark eight_tidy)

/-- The guard of the sub-protocol number b, b below 9. -/
def gKP (Q : P14) (sentU : Array OracleNotice) (b : Nat) : Sh₂ → Except String Sh₂ :=
  withMark fun a =>
    if factsB Q b a then .ok (updS Q sentU b a) else .error "a guard on the shape"

/-- **The guards on the shape along the twelve members.** -/
def ZP (Q : P14) (sentU : Array OracleNotice) (pU pO : P12)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) : Shape St where
  Sh := Sh₂
  sh := sh₂
  g := fun b =>
    if b < 9 then gKP Q sentU b
    else if b = 9 then gTest₂ pU (·.gU) (·.firstMask)
    else if b = 10 then gTest₂ pO (·.gOmega) (fun _ => none)
    else gEnd₂
  vals := v

section
variable {Cl V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk St Cl V W X Pb} {Q : P14}
  {sentU : Array OracleNotice} {layO : OnBytes.TreeLay} {c : OnBytes.Model.Verify.Chains}
  {key : W → TableKey} {N : H2U.Places4} {nO : H2U.PlaceNums}

/-- Each of the nine keeps the mark on the statement. -/
theorem tidy_kept_at {bs : List (Block St Cl)} {B : Eight Q} (F : FlatAt bs c B) (ft : Nat)
    (hplan : ∀ b ∈ blocksOr Q, b.planOk = true) {b : Nat} (h8 : b ≤ 8) (blk : Block St Cl)
    (hblk : bs[b]? = some blk) (s : St) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : St) (n : Nat)
    (h : blk.step ft s rs cols = .ok (s', n)) (hT : stTidyB s.st = true) :
    stTidyB s'.st = true := by
  by_cases h0 : b = 0
  · subst h0
    have hl := F.at0 hblk
    rw [hl.step] at h
    have hd := ((VerifiableInference.Desc.step_iff ft (_root_.Desc.K14.frontBlock c) s s' rs cols n).1 h).2.1
    have e : s = s' := Except.ok.inj hd
    rw [← e]
    exact hT
  · obtain ⟨x, hx, hl⟩ := AtPublicFiles.AtFiles.Full.like_at F (by omega) h8 hblk
    rw [hl.step] at h
    exact eight_tidy (ft := ft) Q x hx (hplan x hx) s s' rs cols n h hT

/-- **(B1) at every member.** -/
theorem carries_at (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hplan : ∀ b ∈ blocksOr Q, b.planOk = true)
    (h9 : T.bs[9]? = some (guEntry Cl N)) (h10 : T.bs[10]? = some (omegaEntry Cl nO))
    (h11 : T.bs[11]? = some (H2K.JointK.sharedEnd Cl Q N)) (hlen : T.bs.length = 12)
    (he : (pGu N).early = true) (ha : (pGu N).answers = 1)
    (he' : (pGomega nO).early = true) (ha' : (pGomega nO).answers = 1)
    (v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool) (j : Nat) :
    Carries T.bs T.ft (ZP Q sentU (pGu N) (pGomega nO) v) j := by
  obtain ⟨B⟩ := hQ.eight
  have F := hT.bs B
  by_cases hj : j < 9
  · intro blk hblk s rs cols s' n t hstep hg
    have hg' : gKP Q sentU j (sh₂ s) = .ok t := by
      have q : (ZP Q sentU (pGu N) (pGomega nO) v).g j = gKP Q sentU j := by
        show (if j < 9 then gKP Q sentU j else _) = _
        rw [if_pos hj]
      rw [q] at hg
      exact hg
    exact carries_withMark (ft := T.ft) (bs := T.bs) (b := j) _
      (carries2 (guard := factsB Q) (upd := updS Q sentU) (vals := v) B F hQ.facts.goes
        hQ.facts.two T.ft j (by omega) fun _ => rfl)
      (fun blk hblk s rs cols s' n h hT =>
        tidy_kept_at F T.ft hplan (by omega) blk hblk s rs cols s' n h hT)
      blk hblk s rs cols s' n t hstep hg'
  by_cases h9' : j = 9
  · subst h9'
    refine carries_seat h9 fun _ _ _ => ?_
    exact test₂_carries (·.gU) (·.firstMask) (·.gU) (·.firstMask) (fun _ => rfl) (fun _ => rfl) _
      he ha _ _
  by_cases h10' : j = 10
  · subst h10'
    refine carries_seat h10 fun _ _ _ => ?_
    exact test₂_carries (·.gOmega) (fun _ => none) (·.gOmega) (fun _ => none) (fun _ => rfl)
      (fun _ => rfl) _ he' ha' _ _
  by_cases h11' : j = 11
  · subst h11'
    refine carries_seat h11 fun _ _ _ => ?_
    exact end₂_carries (blocksOr Q ++ tests N) [] []
  · intro blk hb
    have hl := (List.getElem?_eq_some_iff.1 hb).1
    omega

/-- **The end is accepted at every stand at 11.** -/
theorem accepted_at_end {a₀ : Sh₂} (hQ : Plan2 Q sentU layO) (hT : ChainAt T Q c key)
    (hplan : ∀ b ∈ blocksOr Q, b.planOk = true)
    (h9 : T.bs[9]? = some (guEntry Cl N)) (h10 : T.bs[10]? = some (omegaEntry Cl nO))
    (h11 : T.bs[11]? = some (H2K.JointK.sharedEnd Cl Q N)) (hlen : T.bs.length = 12)
    (he : (pGu N).early = true) (ha : (pGu N).answers = 1)
    (he' : (pGomega nO).early = true) (ha' : (pGomega nO).answers = 1)
    (hyes : (ZP Q sentU (pGu N) (pGomega nO) (fun _ _ _ _ => true)).yes a₀ 12 = true)
    (hfirst : ∀ k w h s₀, T.valid w → T.begun k w h s₀ → sh₂ s₀ = a₀)
    (hn : (T.hs.find? fun g => g.place == (H2K.JointK.sharedEnd Cl Q N).place) = none)
    (fall : Nat → St → List Fmt.Drawn → Option String) : Accepted T fall 11 := by
  refine AtPublicFiles.AtFiles.accepted_sealed T h11 rfl rfl hn fun k s m E rs gs hA => ?_
  have hC := carries_at hQ hT hplan h9 h10 h11 hlen he ha he' ha' (fun _ _ _ _ => true)
  have shp := shape_at T (ZP Q sentU (pGu N) (pGomega nO) (fun _ _ _ _ => true)) (n := 12)
    (by rw [hlen]) (by omega) hyes hfirst hC hA
  obtain ⟨t, ht⟩ := run_front (ZP Q sentU (pGu N) (pGomega nO) (fun _ _ _ _ => true)) a₀ 12 12
    (by omega) hyes
  have hg : gEnd₂ (sh₂ s) = .ok t := by
    have ht' : ((ZP Q sentU (pGu N) (pGomega nO) (fun _ _ _ _ => true)).run 11 a₀).bind
        ((ZP Q sentU (pGu N) (pGomega nO) (fun _ _ _ _ => true)).g 11) = .ok t := ht
    rw [shp] at ht'
    exact ht'
  exact end₂_returns (blocksOr Q ++ tests N) rs gs s t hg rfl

end

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.gKP
#print axioms ProofFile.Honest.K12.AtFile.ZP
#print axioms ProofFile.Honest.K12.AtFile.tidy_kept_at
#print axioms ProofFile.Honest.K12.AtFile.carries_at
#print axioms ProofFile.Honest.K12.AtFile.accepted_at_end
