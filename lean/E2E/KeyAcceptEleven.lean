-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyAcceptEleven.lean: the shared chain's end, member 11, is accepted at the key's thread,
WHEREVER THE THREAD STANDS AT BORDER 11: `Accepted` is a sentence from `Thr` at 11, and no thread is shown
to stand there.

Why. The end reads the statement's shape alone (`end₂_law`). The shape at a border of the thread is what the
guards' run returns there (`shape₂_of_thr`), and the run returns to its last term at the written values
(`run₂_sourced`). So nothing of what the two tests leave is read but its shape.

Main names.
  `accepted_eleven`: THE CALL, general in the thread's table, `Kp` and `Vd`.

What stays open. The premises: the instance's key fits the index; no half at the end's place. That `Thr` at 11
stands, which hangs on members 9 and 10. Nothing here says that a test accepts.

NOT IN FRONT OF A LAW OVER COINS: `accepted_eleven` bears this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. Its ground: it is a sentence at every run's coins, and the
thread's clauses at `k` inside it are of the first kind. `x` is a letter here, with `hk` its one premise.
None: the bar is flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeySharedQuiet
import E2E.KeyShapeThirdStart
import E2E.KeyThreads
import E2E.KeyStandOne

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace AtPublicFiles.KeyAcceptEleven
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Own (keyFits)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St first)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription flat_last Sh₂ sh₂ gEnd₂ end₂_returns Z₂ Z₂At accepted_sealed)
open AtPublicFiles.AtFiles.Full (QK PF gK₂ V0 V12 run₂_sourced shape₂_of_thr pre_len₂ omega_full later_sourced
  len₂_sourced)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (threadKey)
open AtPublicFiles.KeyStandOne (inK)

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **The shared chain's end is accepted**, from `Thr` at 11.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem accepted_eleven {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hk : keyFits x.key QK.par.S.fold.index = true)
    (hn : ((keyProver K).shared.find? fun g => g.place == (keyFileDescription Xs Nr Pl).shared.last.place) = none)
    (fall : Nat → St → List Fmt.Drawn → Option String) :
    Accepted (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)) fall 11 := by
  have hbs : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).bs = (keyFileDescription Xs Nr Pl).shared.blocksInOrder :=
    (AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).bs
  have hlen : (keyFileDescription Xs Nr Pl).shared.blocksInOrder.length = 12 := len₂_sourced hs scope
  obtain ⟨blk, e, hr, ho, hp, hd⟩ := flat_last (keyFileDescription Xs Nr Pl).shared
  have h11 : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).bs[11]? = some blk := by
    rw [hbs]
    rw [hlen] at e
    exact e
  let v : Nat → St → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool := fun _ _ _ _ => true
  have hbeg : ∀ k w h s₀, (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).valid w → (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd (inK w₀ rc x)).begun k w h s₀ →
      ∃ y, s₀ = (keyFileDescription Xs Nr Pl).start₂ y ∧ keyFits y.key QK.par.S.fold.index = true := by
    intro k w h s₀ hv hb
    obtain ⟨rfl, -⟩ := hv
    exact ⟨x, hb, hk⟩
  refine accepted_sealed _ h11 (hr.trans rfl) (ho.trans rfl) (by rw [hp]; exact hn)
    fun k s m E rs gs hT => ?_
  have shp := shape₂_of_thr hs scope v _ hbs hbeg (b := 11) (by omega) hT
  have r12 := run₂_sourced hs scope v
  have e12 : (Z₂At Xs.chains Pl gK₂ v).run 12 V0 =
      ((Z₂At Xs.chains Pl gK₂ v).run 11 V0).bind ((Z₂At Xs.chains Pl gK₂ v).g 11) := rfl
  rw [e12, shp] at r12
  have hP : Pl = PF := later_sourced hs scope
  subst hP
  have g11 : (Z₂At Xs.chains PF gK₂ v).g 11 = gEnd₂ := by
    obtain ⟨layO, hQ⟩ := AtPublicFiles.AtFiles.Full.plan2_full
    obtain ⟨B⟩ := hQ.eight
    have h9 := pre_len₂ Xs.chains PF (AtPublicFiles.AtFiles.Full.par_sourced hs scope) B
    show (if 11 < (H2K.JointK.keySharedPre Xs.chains PF).length then gK₂ 11
      else if 11 = (H2K.JointK.keySharedPre Xs.chains PF).length then _ else _) = _
    rw [h9, if_neg (by omega), if_neg (by omega)]
    cases PF.O with
    | none => rfl
    | some nO =>
      show (if 11 = 9 + 1 then _ else gEnd₂) = _
      rw [if_neg (by omega)]
  have hg : gEnd₂ (sh₂ s) = .ok V12 := by
    rw [g11] at r12
    exact r12
  rw [hd]
  exact end₂_returns (_root_.Desc.K14.blocksOr (VerifiableInference.Desc.Key.sharedPar Xs.chains
    (VerifiableInference.Desc.Key.beforeSharedPoint PF)) ++ VerifiableInference.Desc.Key.sharedTests PF)
    rs gs s V12 hg rfl

end

end AtPublicFiles.KeyAcceptEleven

#print axioms AtPublicFiles.KeyAcceptEleven.accepted_eleven
