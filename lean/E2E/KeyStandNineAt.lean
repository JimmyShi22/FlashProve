-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyStandNineAt.lean: the key's shared thread at border 9, at terms, as `stand_three`
(E2E/KeyStandMember.lean) has it at border 3.

Main names.
  `SaysNine`: what the open items say at border 9: the sample constraints of o_u, o_omega, o_sp, and the
    rows recG, loc, foldU, foldOmega, hold of the witness's words.
  `items_at_nine`: they hold wherever the thread stands at border 9.
  `lists_fit6`, `lists_nine`: some lists of challenges fit.
  `stand_nine`: at every letter `Said`, field `o` of the start, `tt`, `Kp`: where `Said` holds at the start and
    `SaidNext` at the first nine members: at every run's coins, index, committer's coins, seed and every list of challenges that
    fits at the six members with rounds: the thread stands at border 9, and they hold.

What stays open. As at `stand_three`: `hKp`, `hE`, `hV`, `hS`, `hSN` on the letters; no run of the frame; the
words are the honest words; the tie of tables to words is at `pair_three` alone, of «send o_u»; a row's summands are not shown to lie within the
statement's tables; `hPin`. By our reading of the forward rows, the seven are all that is open at 9, `row (sample m)` being one
sentence with `pin m`; no test in this file says so. A constraint list that
is empty makes an item say nothing: `HasRow`, the rows' lengths and the two ranges' sizes stand in
the end for that. `lengthsOk` is not stated; no job of the test on G_u is written.

NOT IN FRONT OF A LAW OVER COINS: `items_at_nine` and `stand_nine` bear this label; the rule is at its home,
the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: as at `stand_three`. None: the bar is
flat.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyStandNine
import E2E.KeyStandMember

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.KeyStandNineAt
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (Place OpenedColumn)
open VerifiableInference.Desc.Shared (NumbersS MeaningS Msg2 ItemS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource)
open _root_.Desc.K14 (St blocks blocksOr)
open _root_.Desc.K14.Honest (SmpOwn)
open _root_.Desc.K14.Law (RowsU RowsO)
open AtPublicFiles.AtFiles (KeySourced)
open AtPublicFiles.AtFiles.Full (QK)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace frontPlace)
open AtPublicFiles.KeyFile (KeyParts keyProver keyProver_shared)
open Bind.ForProver (shapeOf shapeOfIndex linOf rowsFit encW oodSh Seed)
open AtPublicFiles.KeyFiveFields (pubKey)
open AtPublicFiles.KeySharedThread (parKey randKey threadKey)
open AtPublicFiles.KeyFile (keyProver)
open AtPublicFiles.KeyAsksKey (tableKey)
open AtPublicFiles.KeyStandOne (startAt inK envK)
open AtPublicFiles.KeyStandMember (keyOf front_apart)


/-- **Some lists fit at the six members with rounds**, at any list over the eight. -/
theorem lists_fit6 {Cl : Type} {T : List (VerifiableInference.Desc.Block St Cl)} {Q : _root_.Desc.K14.P14}
    (e : Q = QK)
    (hm : ∃ b1 b2 b3 b4 b5 b6 b7 b8 : VerifiableInference.Desc.Block St Unit,
      blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
      ∀ i (c : VerifiableInference.Desc.Block St Unit), [b1, b2, b3, b4, b5, b6, b7, b8][i]? = some c →
        ∀ blk, T[1 + i]? = some blk → blk.rounds = c.rounds ∧ blk.oracles = c.oracles ∧
          blk.place = c.place) :
    ∃ ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn,
      (∀ blk, T[1]? = some blk → drawsFit blk.rounds ds₁ = true) ∧
      (∀ blk, T[2]? = some blk → drawsFit blk.rounds ds₂ = true) ∧
      (∀ blk, T[4]? = some blk → drawsFit blk.rounds ds₄ = true) ∧
      (∀ blk, T[5]? = some blk → drawsFit blk.rounds ds₅ = true) ∧
      (∀ blk, T[7]? = some blk → drawsFit blk.rounds ds₇ = true) ∧
      (∀ blk, T[8]? = some blk → drawsFit blk.rounds ds₈ = true) := by
  subst e
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb, hm⟩ := hm
  have dc := AtPublicFiles.KeyStandMember.draws_closed
  have eb : blocksOr QK = [b1, b2, b3, b4, b5, b6, b7, b8] := by
    unfold blocksOr
    rw [hb]
    rfl
  rw [eb] at dc
  refine ⟨b1.rounds.map AtPublicFiles.KeyStandMember.fitOf, b2.rounds.map AtPublicFiles.KeyStandMember.fitOf,
    b4.rounds.map AtPublicFiles.KeyStandMember.fitOf, b5.rounds.map AtPublicFiles.KeyStandMember.fitOf,
    b7.rounds.map AtPublicFiles.KeyStandMember.fitOf, b8.rounds.map AtPublicFiles.KeyStandMember.fitOf,
    fun blk hblk => ?_, fun blk hblk => ?_, fun blk hblk => ?_, fun blk hblk => ?_,
    fun blk hblk => ?_, fun blk hblk => ?_⟩
  · rw [(hm 0 b1 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b1 (by simp)
  · rw [(hm 1 b2 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b2 (by simp)
  · rw [(hm 3 b4 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b4 (by simp)
  · rw [(hm 4 b5 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b5 (by simp)
  · rw [(hm 6 b7 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b7 (by simp)
  · rw [(hm 7 b8 rfl blk hblk).1]
    exact List.all_eq_true.1 dc b8 (by simp)

/-- What the thread's open items say at border 9, of a state and a witness's words. -/
def SaysNine {Wt : Type} (Xs : Source) (Pl : LaterPlaces) (ℓ : WitLens Wt) (s : St) (w : Wt) : Prop :=
  SmpOwn (num .oU) s (ℓ.get w) ∧ SmpOwn (num .oOmega) s (ℓ.get w) ∧ SmpOwn (num .oSp) s (ℓ.get w) ∧
    RowsU rdE 0 (parKey Xs Pl).par.S.fold.index.answers s (ℓ.get w) ∧
    RowsU rdE (parKey Xs Pl).par.S.fold.index.answers (parKey Xs Pl).par.S.fold.columns s (ℓ.get w) ∧
    RowsU rdE ((parKey Xs Pl).par.S.fold.index.answers + (parKey Xs Pl).par.S.fold.columns) 1 s
      (ℓ.get w) ∧
    RowsO rdE 0 1 s (ℓ.get w)

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- **The items at border 9.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem items_at_nine {k : Coins (keyBook K₀)} {s : St} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env}
    (u : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 9 k s m E) (ds : List Fmt.Drawn) :
    SaysNine Xs Pl ℓ s ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).wit k m.st.input
      (m.st.heard ++ ds)) := by
  have hI := u.2.2.2.1 ds
  refine ⟨hI (ItemS.pin .oU) ?_ .oU rfl, hI (ItemS.pin .oOmega) ?_ .oOmega rfl,
    hI (ItemS.pin .oSp) ?_ .oSp rfl, hI (ItemS.row .recG) ?_, hI (ItemS.row .loc) ?_,
    hI (ItemS.row .foldU) ?_, hI (ItemS.row .foldOmega) ?_⟩
  all_goals
    show _ ∈ fwdOpen SharedRows.start (SharedRows.rows true) 9
    decide

end

section
variable {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K₀ : KeyPub) (K' : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tk : Nat → Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (tt : Nat → Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins (keyBook K₀) → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop)
  (Said : Nat → Coins (keyBook K₀) → Mid (Common W₀ Rc TableKey) X₀ → Prop)
  (o : Option (List OpenedColumn))
  (f : W₀ → Weights) (g : Rc → ℕ → TableRand) (Z₀ : ProofFile.Pub)
  (w₀ : W₀) (rc : Rc) (x : Xi)

/-- **Some lists fit at this thread.** -/
theorem lists_nine {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace) :
    ∃ ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn,
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true) ∧
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true) ∧
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[4]? = some blk → drawsFit blk.rounds ds₄ = true) ∧
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[5]? = some blk → drawsFit blk.rounds ds₅ = true) ∧
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[7]? = some blk → drawsFit blk.rounds ds₇ = true) ∧
      (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[8]? = some blk → drawsFit blk.rounds ds₈ = true) := by
  subst hx
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  have hsp₀ : (planData (parKey Xs Pl)).S.sharedSplitNeeded = true := hQ.facts.two
  have hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place, (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place].Nodup := by
    show [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K'.onU.place, K'.onOmega.place].Nodup
    rw [pU, pO]
    decide
  obtain ⟨B⟩ := hQ.eight
  have H := AtPublicFiles.KeyStandThree.halves_key Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀ tk tt rest
    Kp Vd rfl hsp₀ hap
    (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
  have E8 : AtEight (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
      (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
      (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)) 1 (parKey Xs Pl) (planData (parKey Xs Pl)) (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).weights :=
    atEight2 B (AtPublicFiles.KeySharedThread.sentKey Xs Pl) VerifiableInference.Desc.Key.Claim H
  exact lists_fit6 (AtPublicFiles.AtFiles.Full.par_sourced hs scope) E8.eight

/-- **The thread at border 9, at terms.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem stand_nine {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (hK₀ : fullPub = some K₀) (sd : Seed (shapeOf (pubKey Z₀ Xs.chains)) × ℕ)
    (hx : x = ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
    (hN : Function.Injective Nm.tenant) (hPin : ∀ v s y u, (Mg₀ v).pinT s y u)
    (hKp : ∀ b ∈ [0, 11], ∀ s, Kp b s s) (hE : ∀ s s', Kp 0 s s' → s' = s)
    (hV : Vd (inK w₀ rc x))
    (qr : AtPublicFiles.Stops.QuietHalf K'.rng) (qU : AtPublicFiles.Stops.QuietHalf K'.onU)
    (qO : AtPublicFiles.Stops.QuietHalf K'.onOmega) (qw : AtPublicFiles.Stops.QuietHalf K'.own)
    (pU : K'.onU.place = foldedTestPlace) (pO : K'.onOmega.place = omegaTestPlace)
    (k : Coins (keyBook K₀)) (ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ : List Fmt.Drawn)
    (hd₁ : (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[1]? = some blk → drawsFit blk.rounds ds₁ = true))
    (hd₂ : (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[2]? = some blk → drawsFit blk.rounds ds₂ = true))
    (hd₄ : (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[4]? = some blk → drawsFit blk.rounds ds₄ = true))
    (hd₅ : (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[5]? = some blk → drawsFit blk.rounds ds₅ = true))
    (hd₇ : (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[7]? = some blk → drawsFit blk.rounds ds₇ = true))
    (hd₈ : (∀ blk, (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).bs[8]? = some blk → drawsFit blk.rounds ds₈ = true))
    (hS : Said 0 k (startAt (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) o (inK w₀ rc x)))
    (hSN : ∀ b, b < 9 → SaidNext (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)) Said b) :
    ∃ (s : St) (m : Mid (Common W₀ Rc TableKey) X₀) (E : Env),
      ThrS (threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)) Said 9 k s m E ∧
      m.st.heard = ds₁ ++ ds₂ ++ ds₄ ++ ds₅ ++ ds₇ ++ ds₈ ∧
      SaysNine Xs Pl ℓ s ((threadKey Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
        (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
        (inK w₀ rc x)).wit k m.st.input m.st.heard) ∧
      AtPublicFiles.KeyStandNine.HasRow (num .oU) s ∧ AtPublicFiles.KeyStandNine.HasRow (num .oOmega) s ∧
      AtPublicFiles.KeyStandNine.HasRow (num .oSp) s ∧
      (_root_.Desc.K14.Law.rowsOn s s.loc.gU).length = (parKey Xs Pl).par.S.fold.index.answers +
        (parKey Xs Pl).par.S.fold.columns + 1 ∧
      (_root_.Desc.K14.Law.rowsOn s s.loc.gOmega).length = 1 ∧
      0 < (parKey Xs Pl).par.S.fold.index.answers ∧ 0 < (parKey Xs Pl).par.S.fold.columns := by
  subst hx
  have es := AtPublicFiles.AtFiles.sized_sourced hs scope
  have hfit : rowsFit (shapeOf (pubKey Z₀ Xs.chains)) (linOf (pubKey Z₀ Xs.chains)).kLo
      (linOf (pubKey Z₀ Xs.chains)).matrixRows = true := by
    show rowsFit (shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index)
      Xs.chains.made.sized.key.once.shape.kLo Xs.chains.made.sized.key.once.shape.matrixRows = true
    rw [es]
    exact AtPublicFiles.KeyFiveFields.rows_full
  have ha : (shapeOf (pubKey Z₀ Xs.chains)).a ≤ 32 := by
    show (shapeOfIndex Xs.chains.made.sized.key.once.shape.fold.index).a ≤ 32
    rw [es]
    exact AtPublicFiles.KeyFiveFields.a_full
  have F := AtPublicFiles.KeyFiveFields.five_made Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd f g Z₀ hfit ha rfl rfl
    (fun _ _ _ => rfl) w₀ rc sd
  obtain ⟨layO, hQ⟩ := AtPublicFiles.KeySharedThread.plan_key hs scope
  have hsp₀ : (planData (parKey Xs Pl)).S.sharedSplitNeeded = true := hQ.facts.two
  have hap : [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place, (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place].Nodup := by
    show [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7, K14.place 8,
      K'.onU.place, K'.onOmega.place].Nodup
    rw [pU, pO]
    decide
  have hO' := AtPublicFiles.KeySharedQuiet.over_key Xs Nr Pl (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀
    (tableKey Xs Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) tk tt) rest Kp Vd
    (inK w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩)
  obtain ⟨s, m, E, u, h, r₀, r₂, r₃, c₁, c₂, c₃, c₄⟩ := AtPublicFiles.KeyStandNine.pair_nine Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀ tk tt rest Kp Vd Said o w₀ rc ⟨oodSh (shapeOf (pubKey Z₀ Xs.chains)) (pubKey Z₀ Xs.chains) ⟨f w₀, g rc, sd⟩⟩ hs scope hK₀ F rfl rfl hap hN qr qU qO qw k hV
    (by
      intro ds i hi
      have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 0 := hi
      rw [AtPublicFiles.KeySharedQuiet.open_front] at hi'
      obtain rfl := List.mem_singleton.1 hi'
      exact hPin _ _ _ _)
    hKp hE (fun v s y _ u _ _ => hPin v s _ u)
    (by
      intro blk hblk
      rw [hO'.bs] at hblk
      have hb₀ : ∃ b₀, (descriptionFromSource Xs Nr Pl).shared.blocksInOrder[0]? = some b₀ ∧ b₀.place = frontPlace :=
        ⟨_, rfl, rfl⟩
      obtain ⟨b₀, e₀, hp⟩ := hb₀
      obtain rfl : b₀ = blk := Option.some.inj (e₀.symm.trans hblk)
      rw [List.find?_eq_none]
      intro g' hg
      have hmem : g'.place ∈ (keyProver (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g)).shared.map (·.place) := List.mem_map.2 ⟨g', hg, rfl⟩
      rw [keyProver_shared _ hsp₀] at hmem
      have hmem' : g'.place ∈ [K14.place 1, K14.sendPlace 2, K14.place 4, K14.sendPlace 5, K14.place 7,
          K14.place 8, foldedTestPlace, omegaTestPlace] := by
        have e1 : (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onU.place = foldedTestPlace := pU
        have e2 : (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g).onOmega.place = omegaTestPlace := pO
        rw [e1, e2] at hmem
        exact hmem
      rw [hp, front_apart _ hmem']
      exact Bool.false_ne_true)
    pU pO ds₁ ds₂ ds₄ ds₅ ds₇ ds₈ hd₁ hd₂ hd₄ hd₅ hd₇ hd₈ hS hSN
  refine ⟨s, m, E, u, h, ?_, r₀, r₂, r₃, c₁, c₂, c₃, c₄⟩
  have it := items_at_nine Xs Nr Pl K₀ (keyOf (pubKey Z₀ Xs.chains) Xs Pl K' f g) ℓ Nm Mg₀ _ rest _ _ _ u.1 []
  rw [List.append_nil] at it
  exact it

end

end AtPublicFiles.KeyStandNineAt

#print axioms AtPublicFiles.KeyStandNineAt.lists_fit6
#print axioms AtPublicFiles.KeyStandNineAt.lists_nine
#print axioms AtPublicFiles.KeyStandNineAt.items_at_nine
#print axioms AtPublicFiles.KeyStandNineAt.stand_nine
