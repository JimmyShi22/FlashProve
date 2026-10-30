-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnSamplesAt.lean: at a stand in front of the key file's own test the sample
rows of the own group's members have no written-out factor, from the two earlier chains' folds and the chain's
start. Steps of the verifier's: nothing is shown of any prover.

  `stay_at`       a sampled message of the start stands at the stand with the same sample rows
  `omega_at`      the copy of Omega: number = the start's count of messages
  `public_samples`   the public facts on the two sendings, in scope
  `samples_at`    the clause

By what. `sample_idx`, `sample_w` (OwnSamples.lean), `sample_omega`, `copy_plain` (OwnOmega.lean), `own_closed`
(OwnKernel.lean), `first_end_shape`, `shared_end_shape`, `start_shape`, `stand_shape` (OwnShape.lean).

Limits.
- FORM ALONE: nothing on what a row holds of.
- hfit: the key fits: a premise.
- NOT IN FRONT OF A LAW OVER COINS: `samples_at` stands behind `Thread.Made`.
- At the full size. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnOmega
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnKernel
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnSeat
import E2E.KeyLastThread

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace ProofFile.Honest.K12.AtKey
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.Ground (By)
open VerifiableInference.Desc.Ground.Sh (stSh grpSh grp_get)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi Claim FirstState descriptionFromSource thirdPar sendW pieces)
open VerifiableInference.Desc.Third (S₃)
open VerifiableInference.Desc.Third.Law (laid_k14Second takenSources_same)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.K1 (SmpStay shapesOf)
open Johnson.RunOne.KeyKeeps (st₁ st₃)
open Johnson.RunOne.KeySmp (start₃_same)
open Johnson.RunOne.KeyWalk (flat_smp₃)
open Johnson.RunOne.KeySendGood (parW gW)
open ProofFile.Honest.K12.AtFile (EndsAre)
open _root_.Desc.K14 (St)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription sh₃ Sh₃ SF ZW)
open AtPublicFiles.AtFiles.Full (QK X0 V12)

variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {Nr : H2U.PlaceNums} {Pl : LaterPlaces}

/-- A sampled message of the start stands at the stand with the same sample rows. -/
theorem stay_at {ft : ℕ} {s₀ st : S₃} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hf : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], [])) :
    SmpStay s₀.st st.st :=
  VerifiableInference.Desc.Keeps.foldBlocks_keeps (By SmpStay st₃) (fun _ => SmpStay.refl _)
    (fun _ _ _ p q => p.trans q) ft _
    (fun b hb => Johnson.RunOne.KeyWalk.flat_smp₃ b (List.mem_of_mem_take hb)) s₀ rs cols _ hf

/-- **The copy of Omega.** om: Omega's number at the shared chain's end. hy: Omega's rows there are plain. -/
theorem omega_at {ft : ℕ} {s₀ st : S₃} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    (hf : foldBlocks ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ rs cols = .ok (st, [], []))
    (hy : ∀ b : VerifiableInference.Desc.Third.Border, s₀.loc.border = some b →
      ∀ y, b.shared.st.oracles[b.shared.omega]? = some y → ∀ r ∈ y.sampleRows.toList, PlainRow r)
    {x : OnBytes.Oracle} (hx : st.st.oracles[s₀.st.oracles.size]? = some x) :
    ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  obtain ⟨a, b, c, d, hflat, ha, hb⟩ : ∃ a b c d : Block S₃ Claim,
      (descriptionFromSource Xs Nr Pl).second.blocksInOrder = [a, b, c, d] ∧
      (∀ s rs gs, a.decide s rs gs =
        (VerifiableInference.Desc.Third.batchLinearConstraintsSecondPart (Cl := Claim) (thirdPar Xs.chains)).decide s rs gs) ∧
      (∀ s rs gs, b.decide s rs gs = (VerifiableInference.Desc.Third.takenSources
        (VerifiableInference.Desc.Key.ownTest Pl)).decide s rs gs) :=
    ⟨_, _, _, _, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  rw [hflat] at hf
  have hf' : foldBlocks ft [a, b] s₀ rs cols = .ok (st, [], []) := hf
  obtain ⟨s₁, n₁, -, h₁, hrest⟩ := VerifiableInference.Desc.Sound.foldBlocks_cons_ok ft a [b] s₀ _ _ _ hf'
  obtain ⟨s₂, n₂, -, h₂, hend⟩ := VerifiableInference.Desc.Sound.foldBlocks_cons_ok ft b [] s₁ _ _ _ hrest
  have e₂ : s₂ = st := by
    unfold foldBlocks at hend
    exact congrArg Prod.fst (Except.ok.inj hend)
  obtain ⟨g₁, d₁⟩ := _root_.Desc.K14.Law.step_decides ft a s₀ s₁ _ _ n₁ h₁
  obtain ⟨g₂, d₂⟩ := _root_.Desc.K14.Law.step_decides ft b s₁ s₂ _ _ n₂ h₂
  rw [ha] at d₁
  rw [hb] at d₂
  have e₁ : s₂ = s₁ := takenSources_same _ s₁ s₂ _ g₂ d₂
  obtain ⟨bd, y, G, dot, L⟩ := laid_k14Second _ s₀ s₁ _ g₁ d₁
  have hx' : s₁.st.oracles[s₀.st.oracles.size]? = some x := by
    rw [← e₁, e₂]
    exact hx
  exact copy_plain L (hy bd L.border y L.there) hx'

/-- **The public facts on the two sendings**, in scope. -/
theorem public_samples (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true) :
    ∃ (bw : Block FirstState Claim) (msg : Array OracleNotice),
      sendW Xs.Y.k.oneTime pieces
        (VerifiableInference.Desc.Key.rootsBefore Xs.Y.D.1
          (VerifiableInference.Desc.Key.batchRound Xs.Y.D.1)) (gW Xs) = some bw ∧
      OnBytes.linMessageW Xs.Y.k.oneTime.lin = some msg ∧ (parW Xs msg).sent.size = 2 ∧
      (∃ hk₀ : 0 < (shapesOf (parW Xs msg)).length, (shapesOf (parW Xs msg))[0].answers ≠ 0) ∧
      Xs.Y.k.oneTime.indexMasks.shape.answers ≠ 0 := by
  obtain ⟨bw, hw, -, -, -⟩ := AtPublicFiles.AtFiles.Full.public_first_sourced hs scope
  have h6 := AtPublicFiles.AtFiles.Full.six_sourced hs scope
  have hc := msg_own
  unfold msgB at hc
  cases hmsg : OnBytes.linMessageW SF with
  | none =>
    rw [hmsg] at hc
    cases hc
  | some msg =>
    rw [hmsg] at hc
    have hc' : (msg.size == 2 && (msg.toList.head?.any fun n => n.shape.answers != 0)) = true := hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc'
    obtain ⟨h2, hh⟩ := hc'
    have hsh : shapesOf (parW Xs msg) = msg.toList.map (·.shape) := by
      unfold parW
      rw [Johnson.RunOne.KeyMsg.shapes_of]
    have hsz : (parW Xs msg).sent.size = 2 := by
      have e : (parW Xs msg).sent.toList = msg.toList := by
        simp [parW, VerifiableInference.Desc.K1.Par.sent, VerifiableInference.Desc.Key.sendingPar]
      have e' := congrArg List.length e
      simpa [h2] using e'
    refine ⟨bw, msg, hw, ?_, hsz, ?_, ?_⟩
    · have e : Xs.Y.k.oneTime.lin = SF := h6.lin
      rw [e]
      exact hmsg
    · cases hl : msg.toList with
      | nil =>
        rw [hl] at hh
        cases hh
      | cons n t =>
        rw [hl] at hh
        have hn : n.shape.answers ≠ 0 := by simpa using hh
        have hs' : shapesOf (parW Xs msg) = n.shape :: t.map (·.shape) := by
          rw [hsh, hl]
          rfl
        exact ⟨by rw [hs']; exact Nat.succ_pos _, by simpa [hs'] using hn⟩
    · have e : Xs.Y.k.oneTime.indexMasks = Lk6.AtPlan.keyFull.once.input := h6.indexMasks
      rw [e]
      exact idx_own

/-- **The clause `samples`.** -/
theorem samples_at (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    {V Pb W₀ Rc Tr X : Type} {Bk : ProverCoinCounts}
    (T : Thread Bk S₃ Claim V (Local W₀ Rc Xi Tr) X Pb)
    (hbs : T.bs = (descriptionFromSource Xs Nr Pl).second.blocksInOrder) {k : Coins Bk} {st : S₃}
    {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hM : T.Made 2 k st m E) {base : List OpenedColumn}
    {e₁ : FirstState} {e₂ : St} (hE : EndsAre (descriptionFromSource Xs Nr Pl) m base e₁ e₂)
    (hb : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ →
      (descriptionFromSource Xs Nr Pl).start₃ ((descriptionFromSource Xs Nr Pl).pub m.st.input.x) e₁ e₂ = .ok s₀)
    (hfit : keyFits ((descriptionFromSource Xs Nr Pl).pub m.st.input.x).key QK.par.S.fold.index = true)
    (G : Group) (hG : st.st.groups[st.loc.own]? = some G) :
    ∀ o ∈ G.members.toList, ∀ x : OnBytes.Oracle, st.st.oracles[o]? = some x →
      ∀ r ∈ x.sampleRows.toList, PlainRow r := by
  obtain ⟨A₀, A₂, h₀, h₂, -, hmem, hom⟩ := own_closed
  obtain ⟨bw, msg, hb₀, hm, hsz, ⟨hk₀, ha₀⟩, hidx⟩ := public_samples hs scope
  obtain ⟨-, -, -, -, s₀, cols, hbeg, -, hfold⟩ := hM
  obtain ⟨r₁, r₂, rest, c₁, c₂, -, -, -, -, -, -, f₁, f₂⟩ := hE
  have hst := hb s₀ hbeg
  have g₁ := first_end_shape hs scope _ f₁
  have g₂ := shared_end_shape hs scope _ hfit f₂
  have g₀ := start_shape hs scope _ g₁ g₂ hst h₀
  have hf : foldBlocks T.ft ((descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2) s₀ (m.seen.drop T.front) cols =
      .ok (st, [], []) := by
    rw [← hbs]
    exact hfold
  have gs := stand_shape hs scope hf g₀ h₂
  have hstay := stay_at hf
  have hsame : s₀.st = st₁ (show FirstState from e₁) := start₃_same hst
  -- the three numbers
  have hL : A₀.1.st.oracles.length = s₀.st.oracles.size := by
    rw [← g₀]
    show (s₀.st.oracles.toList.map _).length = _
    simp
  have hmems : G.members.toList = [0, s₀.st.oracles.size - 2, s₀.st.oracles.size] := by
    have e : (toTest A₂).core.st.groups[(toTest A₂).g]? = some (grpSh G) := by
      rw [← gs]
      show (stSh st.st).groups[st.loc.own]? = _
      rw [grp_get, hG]
      rfl
    unfold membersB at hmem
    rw [e] at hmem
    have h' : ((grpSh G).members == [0, A₀.1.st.oracles.length - 2, A₀.1.st.oracles.length]) = true :=
      hmem
    have h'' := beq_iff_eq.1 h'
    rw [hL] at h''
    exact h''
  intro o ho x hx
  rw [hmems] at ho
  rcases List.mem_cons.1 ho with rfl | ho
  · obtain ⟨y, hy, hys, hyp⟩ := sample_idx f₁ hidx
    rw [← hsame] at hy
    obtain ⟨z, hz, -, -, hzr⟩ := hstay.2 _ y hy hys
    obtain rfl := Option.some.inj (hx.symm.trans hz)
    rw [hzr]
    exact hyp
  rcases List.mem_cons.1 ho with rfl | ho
  · obtain ⟨y, hy, hys, hyp⟩ := sample_w hb₀ hm hsz hk₀ ha₀ f₁
    rw [← hsame] at hy
    obtain ⟨z, hz, -, -, hzr⟩ := hstay.2 _ y hy hys
    obtain rfl := Option.some.inj (hx.symm.trans hz)
    rw [hzr]
    exact hyp
  rcases List.mem_cons.1 ho with rfl | ho
  · refine omega_at hf ?_ hx
    intro bd hbd y hy
    obtain ⟨h, o, hh, hoe, hE₃⟩ := (AtPublicFiles.KeyLastThread.start_key Xs Nr Pl _ _ _ _).1 hst
    obtain ⟨f, -, hs₃⟩ := VerifiableInference.Desc.Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ hE₃
    obtain ⟨-, -, e₀⟩ := VerifiableInference.Desc.Third.Law.start₃_inv _ _ _ _ hs₃
    have hbd' : bd = { g := f.g, shared := o } := by
      rw [e₀] at hbd
      exact (Option.some.inj hbd).symm
    have ho' : (_root_.Desc.K14.ended e₂).map VerifiableInference.Desc.Third.sharedOfEnd = some o := hoe
    obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 ho'
    have hom₂ : e₂.loc.oOmega = (AtPublicFiles.AtFiles.sharedOf V12).omega := by
      rw [← g₂, AtPublicFiles.AtFiles.sharedOf_eq]
      rfl
    unfold _root_.Desc.K14.ended at hE'
    split at hE'
    · obtain rfl := Option.some.inj hE'
      rw [hbd'] at hy
      have hy' : e₂.st.oracles[e₂.loc.oOmega]? = some y := hy
      rw [hom₂] at hy'
      obtain ⟨y', h1, -, h3⟩ := sample_omega hs scope _ hfit f₂ (AtPublicFiles.AtFiles.sharedOf V12).omega hom
      obtain rfl := Option.some.inj (hy'.symm.trans h1)
      exact h3
    · cases hE'
  · cases ho

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.stay_at
#print axioms ProofFile.Honest.K12.AtKey.omega_at
#print axioms ProofFile.Honest.K12.AtKey.public_samples
#print axioms ProofFile.Honest.K12.AtKey.samples_at
