-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedStandTwelve.lean: NOT IN FRONT OF A LAW OVER COINS. The
proof file's shared thread at the base prover, walked to its end: from the start that ready gives,
through all twelve members, at the letter that keeps the field.

  keepsEq              the letter of what a member outside K14's and the tests keeps: the state
  five_at_end          FiveAtBorder at 11 at the term
  stand_twelve_at_base from a stand at 0 and each member's rounds
  stand_twelve_at_ready the statement, from what ready returns

Premises left of stand_twelve_at_ready, each named. H18: the five at K14's eight. F: WalkFacts at the
term. P₀: member 0. hn: no half
at the end's place. hk: the input's key has sizes that fit. hds: the lists fit.

By what. stand_eleven_at_base (SharedStandAtBase.lean), five_eleven (MemberEnd.lean), end_at_head
(EndAtHead.lean), enters_sharedParts (Honest/Thread/TheLaterThreads.lean), runs_of_ready
(MemberRunsAt.lean), start_at_letter (SharedStand.lean).

Limits. A walk of the thread's steps, not a run of the frame. At the base return alone. Nothing on
completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.SharedStandAtBase
import Johnson.Desc.ProofFile.Honest.K12.AtFile.MemberEnd
import Johnson.Desc.ProofFile.Honest.K12.AtFile.EndAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtFile.MemberRunsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (sharedPlaces)
open Desc.K14 (St blocks blocksOr)
open ProofFile.Honest.K14 (form2 kp2)
open ProofFile.Honest.K12.AtFile (end_member end_at_head ended_of_last five_eleven runs_of_ready)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.FirstThread

/-- What a member outside K14's and the tests keeps: the state. -/
def keepsEq : Place → St → St → Prop := fun _ s s' => s' = s

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn files A)
  {b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit} {nO : H2U.PlaceNums} (w : Common FullSizeMatrix IndexCommitterCoins TableKey)
  (pO : P12) (rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared)

local notation "𝐓" =>
  sharedThread h (readsBase h)
    (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest [] keepsEq)) w

/-- At member 11 the thread keeps the state. -/
theorem keeps_end (s s' : St) : (𝐓).keeps 11 s s' ↔ s' = s := by
  have e11 : (sharedPlaces true)[11]? = some ⟨2, none, 11, .frame⟩ := rfl
  have hk : ∀ s s', kp2 (K1.qAt A.Z h.places) (sentFirstOf A.Z h.places)
      (keepsAtBase h.places keepsEq) ⟨2, none, 11, .frame⟩ s s' ↔ s' = s := by
    intro s s'
    unfold kp2
    rw [if_neg (by decide)]
    unfold keepsAtBase
    rw [if_neg (by decide), if_neg (by decide)]
    exact Iff.rfl
  constructor
  · intro k
    exact (hk s s').1 (k _ e11)
  · intro e p hp
    obtain rfl := Option.some.inj (e11.symm.trans hp)
    exact (hk s s').2 e

/-- **The five at the chain's end, at the term.** -/
theorem five_at_end (hO : h.places.O = some nO)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hk : ∀ v, (𝐓).valid v → keyFits v.key (K1.qAt A.Z h.places).par.S.fold.index = true)
    (hn : ((𝐓).hs.find? fun g => g.place ==
      (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt A.Z h.places) h.places).place) = none)
    (Said : ℕ → Coins A.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fall : ℕ → St → List Fmt.Drawn → Option String) : FiveAtBorder (𝐓) Said fall 11 := by
  refine five_eleven (lettersBase h
      (sharedParts h (laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest [] keepsEq)) (readsBase h)
      w) Said fall rfl
    (end_member h.head hO _ hb) rfl rfl hn ?_ (end_at_head h.head hO _ hb hk hn fall) ?_
    (fun _ _ _ _ _ _ hc => absurd hc List.not_mem_nil)
    (fun _ s _ _ _ => (keeps_end h w pO rest s s).2 rfl)
    (fun _ s _ _ s' _ k => (keeps_end h w pO rest s s').1 k)
    (fun _ i h1 h2 s y y' v hu => AtPublicFiles.KeySharedQuiet.holds_free _ _ _ _ i h1 h2 s y y' v hu)
  · intro d rs gs d' hd
    have hd' : (VerifiableInference.Desc.K12.Seat.last (blocksOr (K1.qAt A.Z h.places) ++
        VerifiableInference.Desc.K12.Seat.tests h.places)).decide d rs gs = .ok d' := hd
    exact ended_of_last _ hd'
  · intro s
    show form2 (K1.qAt A.Z h.places) (fun _ _ => true) 12 s = true
    unfold form2
    rw [if_neg (by decide)]

/-- **The walk to the chain's end.** -/
theorem stand_twelve_at_base
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hk : ∀ v, (𝐓).valid v → keyFits v.key (K1.qAt A.Z h.places).par.S.fold.index = true)
    (hn : ((𝐓).hs.find? fun g => g.place ==
      (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt A.Z h.places) h.places).place) = none)
    (H18 : ∀ b, 1 ≤ b → b ≤ 8 → FiveAtBorder (𝐓) (SaidField (𝐓) BaseNil) (fun _ _ _ => none) b)
    (F : WalkFacts (𝐓) 12) (P₀ : MemberPaid (𝐓) (SaidField (𝐓) BaseNil) 0)
    {k : Coins A.B} {s₀ : St} {m₀ : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit} {E₀ : Env}
    (start : ThrS (𝐓) (SaidField (𝐓) BaseNil) 0 k s₀ m₀ E₀)
    (ds : ℕ → List Fmt.Drawn) (R : ∀ j, j < 12 → MemberRuns (𝐓) k j (ds j)) :
    ∃ (s : St) (m : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit) (E : Env),
      ThrS (𝐓) (SaidField (𝐓) BaseNil) 12 k s m E ∧
      m.st.heard =
        m₀.st.heard ++ ((List.range 9).flatMap fun j => ds (0 + j)) ++ ds 9 ++ ds 10 ++ ds 11 := by
  obtain ⟨_, _, s, _, _, m, _, _, E, _, _, u, _, _, hh⟩ := stand_eleven_at_base h w base hb
    hO pO hO' rest keepsEq H18 F P₀ start ds fun j hj => R j (by omega)
  obtain ⟨s', m', E', u', h', -⟩ := step_of_paid (𝐓) (SaidField (𝐓) BaseNil) (n := 12) F.fits
    (by omega) (paid_of_border F (by omega)
      (five_at_end h w pO rest hO hb hk hn _ _)) (R 11 (by omega)) u
  exact ⟨s', m', E', u', by rw [h', hh]⟩

/-- **The walk to the chain's end, from what ready returns.** -/
theorem stand_twelve_at_ready
    (base : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL matrixFilling = .ok A)
    (hb : blocks (K1.qAt A.Z h.places) = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hO : h.places.O = some nO) (hO' : (fourOf h.places).O = some pO)
    (hk : ∀ v, (𝐓).valid v → keyFits v.key (K1.qAt A.Z h.places).par.S.fold.index = true)
    (hn : ((𝐓).hs.find? fun g => g.place ==
      (H2K.JointK.sharedEnd ProofFile.Cl (K1.qAt A.Z h.places) h.places).place) = none)
    (H18 : ∀ b, 1 ≤ b → b ≤ 8 → FiveAtBorder (𝐓) (SaidField (𝐓) BaseNil) (fun _ _ _ => none) b)
    (F : WalkFacts (𝐓) 12) (P₀ : MemberPaid (𝐓) (SaidField (𝐓) BaseNil) 0)
    {k : Coins A.B} {R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} {x : ProofFile.Inst}
    (hR : ready h.description A.B A.H w.w₀ w.rc x k = .ok R) (hw : R.common = w)
    (ds : ℕ → List Fmt.Drawn)
    (hds : ∀ j, j < 12 → ∃ blk, (𝐓).bs[j]? = some blk ∧ drawsFit blk.rounds (ds j) = true) :
    ∃ (s : St) (m : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit) (E : Env),
      ThrS (𝐓) (SaidField (𝐓) BaseNil) 12 k s m E ∧
      m.st.heard = ((List.range 9).flatMap fun j => ds (0 + j)) ++ ds 9 ++ ds 10 ++ ds 11 := by
  have E₂ := enters_sharedParts (reads := readsBase h)
    (L := laterBase h [b1, b2, b3, b4, b5, b6, b7, b8] pO rest [] keepsEq) hR
    (fun _ hc => absurd hc List.not_mem_nil)
  rw [hw] at E₂
  have st := start_at_letter E₂ rfl
  obtain ⟨s, m, E, u, hh⟩ := stand_twelve_at_base h w pO rest base hb hO hO' hk hn H18 F P₀
    st ds fun j hj => by
      obtain ⟨blk, e, hd⟩ := hds j hj
      exact runs_of_ready hR _ rfl rfl rfl rfl F.stops e hd
  refine ⟨s, m, E, u, ?_⟩
  rw [hh]
  rfl

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.stand_twelve_at_ready
#print axioms ProofFile.Honest.Term.keepsEq
#print axioms ProofFile.Honest.Term.keeps_end
#print axioms ProofFile.Honest.Term.five_at_end
#print axioms ProofFile.Honest.Term.stand_twelve_at_base
