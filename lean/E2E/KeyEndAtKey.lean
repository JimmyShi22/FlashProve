-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeyEndAtKey.lean: at the key file's shared thread, what its last state notes: the point, Omega's
number and the codes, in scope, wherever the thread stands at its last border.

Why. `dot_item` (E2E/KeyDotItem.lean) asks these of the state at which the shared chain ends.
`point_of_thr` (E2E/KeyPointEnd.lean) has them at a thread under `ChainAt` and `TailAt`. This file lays
those two at the key.

Main names.
  `tailLike_key`, `tailAt_key`: the members 9, 10, 11 of the description's shared chain are the
    library's two proximity tests and its closing sub-protocol.
  `chainAt_key`: the shared thread at the key begins at the kind's first state.
  `end_at_key`: the point and Omega's number at the thread's last border.
  `codes_at_key`: the codes there.

What stays open. That the thread stands at that border at any run. `nO`, `hO`: the description has a
second test on Omega's group: a premise on a public value. All of it stands behind `Thr`.

NOT IN FRONT OF A LAW OVER COINS: `end_at_key` and `codes_at_key` bear this label; the rule is at its home,
the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: `Thr` of `threadKey` ties that thread's
letters to a run's coins, of the first kind; `hs`, `scope`, `hO` read public files, of neither kind. None
of these is the term that the committer makes. None: the bar is flat. `tailLike_key`, `tailAt_key` and
`chainAt_key` name no coin.

Nothing on soundness, completeness, hiding or binding.

-/
import E2E.KeyPointEnd
import E2E.KeySharedQuiet
import E2E.KeyShapeSharedTies
import E2E.KeyPublic
import Johnson.Loose.H2K12.RoundsAtKeySeats

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace AtPublicFiles.KeyEndAtKey
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Shared (NumbersS MeaningS)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi descriptionFromSource sharedPar beforeSharedPoint sharedTests)
open _root_.Desc.K14 (St P14 first blocksOr)
open _root_.Desc.K14.Honest (Eight)
open AtPublicFiles.AtFiles (flat₂ flat₂_cut KeySourced)
open AtPublicFiles.AtFiles.Full (flatAt₂ pre_len₂)
open AtPublicFiles.KeyFile (KeyParts)
open AtPublicFiles.KeySharedThread (parKey sentKey threadKey sits_two plan_key)

/-- The members 9, 10, 11 of the description's shared chain. -/
theorem tailLike_key (c : OnBytes.Model.Verify.Chains) (P : LaterPlaces) {Q : P14}
    (e : sharedPar c (beforeSharedPoint P) = Q) (B : Eight Q) (nO : H2U.PlaceNums)
    (hO : P.O = some nO) :
    TailLike (flat₂ c P) (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      (blocksOr (sharedPar c (beforeSharedPoint P)) ++ sharedTests P) := by
  have hl := pre_len₂ c P e B
  have e9 : (flat₂ c P)[(H2K.JointK.keySharedPre c P).length]? = some (H2K.JointK.keyGu P) := by
    rw [flat₂_cut, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have e10 : (flat₂ c P)[(H2K.JointK.keySharedPre c P).length + 1]? =
      some (H2K.JointK.keyOmega nO) := by
    rw [flat₂_cut, hO, List.getElem?_append_right (by omega),
      show (H2K.JointK.keySharedPre c P).length + 1 - (H2K.JointK.keySharedPre c P).length = 1 by
        omega]
    rfl
  have e11 : (flat₂ c P)[(H2K.JointK.keySharedPre c P).length + 2]? =
      some (H2K.JointK.keySharedEnd c P) := by
    rw [flat₂_cut, hO, List.getElem?_append_right (by omega),
      show (H2K.JointK.keySharedPre c P).length + 2 - (H2K.JointK.keySharedPre c P).length = 2 by
        omega]
    rfl
  rw [hl] at e9 e10 e11
  exact ⟨⟨_, e9, rfl, rfl, rfl, rfl⟩, ⟨_, e10, rfl, rfl, rfl, rfl⟩, ⟨_, e11, rfl, rfl, rfl, rfl⟩⟩

/-- The same with the two tests' own tests on the plan. -/
theorem tailAt_key (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) {Q : P14}
    (e : sharedPar Xs.chains (beforeSharedPoint Pl) = Q) (B : Eight Q) (nO : H2U.PlaceNums)
    (hO : Pl.O = some nO) (hp : (descriptionFromSource Xs Nr Pl).planOk = true) :
    TailAt (flat₂ Xs.chains Pl) (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U)
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      (blocksOr (sharedPar Xs.chains (beforeSharedPoint Pl)) ++ sharedTests Pl) :=
  { tailLike_key Xs.chains Pl e B nO hO with
    plan₉ := H2K.JointK.keyPlan_U Xs Nr Pl hp
    plan₁₀ := H2K.JointK.keyPlan_O Xs Nr Pl hp nO hO }

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- The thread begins at the kind's first state, over the description's own list. -/
theorem chainAt_key :
    ChainAt (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) (parKey Xs Pl) Xs.chains
      (fun v => v.key) :=
  ⟨fun B => by
    rw [(sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1]
    exact flatAt₂ Xs.chains Pl rfl B, fun _ _ _ _ h => h⟩

/-- **What the last state notes**, in scope, wherever the thread stands at its last border.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem end_at_key {Z : VerifierAndGoals.PublicFiles} (hs : KeySourced Z Xs Nr Pl) (scope : VerifierAndGoals.InScope Z = true)
    (nO : H2U.PlaceNums) (hO : Pl.O = some nO) {k : Coins Bk} {e : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E' : Env}
    (hA : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 12 k e m E') :
    ∃ d, m.st.heard.head? = some d ∧ e.loc.psiSh = d.elems.map OnBytes.E.ofTriple ∧
      e.loc.psiSh.length = (parKey Xs Pl).par.S.kCol ∧ e.loc.oOmega = 2 := by
  obtain ⟨layO, hQ⟩ := plan_key hs scope
  obtain ⟨B⟩ := hQ.eight
  have hbs := (sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1
  have hL : TailAt (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
      (blocksOr (sharedPar Xs.chains (beforeSharedPoint Pl)) ++ sharedTests Pl) := by
    rw [hbs]
    exact tailAt_key Xs Nr Pl rfl B nO hO hs.named.plan
  exact AtPublicFiles.KeyPointEnd.point_of_thr hQ (chainAt_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) hL rfl hA

/-- **The codes there.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem codes_at_key (x : Xi) {k : Coins Bk} {e : St}
    {m : Mid (Common W₀ Rc TableKey) X₀} {E' : Env} (hx : m.st.input.key = x.key)
    (hA : Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 12 k e m E') :
    e.st.codes = (parKey Xs Pl).codes := by
  obtain ⟨-, -, -, -, hM, -, -⟩ := hA
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hfold⟩ := hM
  have hs₀ : s₀ = (descriptionFromSource Xs Nr Pl).start₂ ((descriptionFromSource Xs Nr Pl).pub x) := by
    have h : s₀ = first (parKey Xs Pl).codes m.st.input.key := hbeg
    rw [h, hx]
    rfl
  rw [hs₀] at hfold
  have hbs := (sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1
  exact AtPublicFiles.AtFiles.codes_shared _
    (fun b hb => hbs ▸ List.mem_of_mem_take hb) _ x _ _ _ hfold

end

end AtPublicFiles.KeyEndAtKey

#print axioms AtPublicFiles.KeyEndAtKey.tailLike_key
#print axioms AtPublicFiles.KeyEndAtKey.tailAt_key
#print axioms AtPublicFiles.KeyEndAtKey.chainAt_key
#print axioms AtPublicFiles.KeyEndAtKey.end_at_key
#print axioms AtPublicFiles.KeyEndAtKey.codes_at_key
