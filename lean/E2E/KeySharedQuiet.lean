-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
THE DEBT IS MOVED INTO NAMED PREMISES, NOT PAID.
E2E/KeySharedQuiet.lean: the shared chain's thread of the linear claim's letters at a key file
(`threadKey`, E2E/KeySharedThread.lean) brings what the statements on a thread over that chain ask
(E2E/KeyStateSide2.lean, KeyBehind.lean, KeyRowsLater.lean).

Main names.
  `over_key`: it is a thread over the chain. `begun_key`: it begins where the description starts
    the chain at x, where the input that the thread is about has x's key.
  `quiet_key`: it is quiet at the chain's front and end, where the letter `Kp` holds of a state and
    itself there.
  `owes_front`, `owes_seal`: the forward rows at the front and the end owe nothing.
  `fits_key`: it passes the tests with code, at a description that passes its test on the plan.
  `enters_key`: it stands at the frame's start, from what is left: the run's readiness, that the
    input is the letter `w`, that it has x's key, that `Vd` holds of it, and the one item open there.
  `stands_key`: so it stands at border 1, from that start and the premises named here.
  `ridesPast_front`: the riders at the front, under `CellsAlone`: the stored table's pin reads of
    the strings the stored table's cells alone. `ridesPast_seal`: at the end, where `Kp` says that
    the state stays; no premise on the meaning: no open item there reads the strings.

What stays open. `CellsAlone` is a premise on a letter, of a meaning that no file lays at a key.
The premises on `Kp` are premises on a letter: the value meant is the library's equation at the
front and the end, and no file here lays it. Nothing says that the thread holds at any run.
NOT IN FRONT OF A LAW OVER COINS: `begun_key`, `ridesPast_front`, `ridesPast_seal`, `enters_key` and
`stands_key` bear this label; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. This file's ground, of the first kind. At `enters_key`:
`R` under `hR`, the run's readiness at the index, the committer's coins, the instance and the run's
coins; `w` under `hw`, and with it `x` under `hx` and `Vd` under `hV`; `rest`, `Mg₀`, `ℓ` and
`K.stored` under `hI`. `hR` is of the second kind too: it says that the index is in range. At
`stands_key`: the same letters under `hT`, which is the thread at border 0. `begun_key` stands
behind the thread's clause on the input, which fixes the input, with its index, the committer's
coins and the key: `w` and `Vd` under it, `x` under `hw`. `ridesPast_front` and `ridesPast_seal`
stand behind the thread at a border. None of these letters is the term that the committer makes:
none: the bar is flat. `quiet_key`: the form in its end reads the state alone here. The other
statements have no premise that names a coin.

Nothing on soundness, completeness or hiding.

-/
import E2E.KeySharedThread
import E2E.KeySharedStands

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.KeySharedQuiet
open ProofFile.Honest ProofFile.Honest.K14
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.Shared (NumbersS MeaningS ItemS sharedPlaces)
open VerifiableInference.Desc.Key (Source LaterPlaces Xi)
open _root_.Desc.K14 (St)
open AtPublicFiles.KeyFile (KeyParts keyProver)
open AtPublicFiles.KeySharedThread (parKey sentKey threadKey lettersKey sits_two start_key)
open AtPublicFiles.KeyThread (OverShared Begun₂ QuietEnds₂)

/-- The stored table's pin reads of the strings the stored table's cells alone. -/
def CellsAlone {P₁ Wt : Type} (M : MeaningS St P₁ Wt) : Prop :=
  ∀ s (y y' : Strs) u, y.cell = y'.cell → M.pinT s y u → M.pinT s y' u

/-- **An item that is neither the stored table's pin nor the one near the fold reads no strings**,
at a meaning that the linear claim's maker has laid. -/
theorem holds_free {P₁ Wt : Type} (ℓ : WitLens Wt) (Q : _root_.Desc.K14.P14) (Nm : NumbersS)
    (M : MeaningS St P₁ Wt) (i : ItemS) (hi : i ≠ .pinT) (hn : i ≠ .nearU) (s : St) (y y' : Strs)
    (u : Wt) (h : ItemS.holdsSh Nm (mgWords ℓ Q Nm M) i s y u) :
    ItemS.holdsSh Nm (mgWords ℓ Q Nm M) i s y' u := by
  cases i with
  | pinT => exact absurd rfl hi
  | nearU => exact absurd rfl hn
  | _ => exact h

/-- What is open at the chain's front, and that at its end neither of those two is. -/
theorem open_front : fwdOpen SharedRows.start (SharedRows.rows true) 0 = [.pinT] := by decide

theorem open_seal : ∀ i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 11,
    i ≠ .pinT ∧ i ≠ .nearU := by decide

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk P₁ Wt : Type}
  (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (K : KeyParts W₀ Rc X₀ X Wk)
  (ℓ : WitLens Wt) (Nm : NumbersS) (Mg₀ : Common W₀ Rc TableKey → MeaningS St P₁ Wt)
  (tb : Fmt.TreeSource → Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Place × Table)
  (rest : Coins Bk → Common W₀ Rc TableKey → List Fmt.Drawn → Wt)
  (Kp : Nat → St → St → Prop) (Vd : Common W₀ Rc TableKey → Prop) (w : Common W₀ Rc TableKey)

/-- It is a thread over the chain. -/
theorem over_key : OverShared Xs Nr Pl (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) :=
  ⟨(sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1, rfl⟩

/-- It begins where the description starts the chain at x.
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem begun_key (x : Xi) (hw : w.key = x.key) :
    Begun₂ Xs Nr Pl x (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) := by
  intro k v h s₀ hv hb
  have e : v = w := hv.1
  have hb' : s₀ = (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).first v.key := hb
  rw [hb', e, hw]
  exact (start_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w x).symm

/-- **It is quiet at the chain's front and end.** -/
theorem quiet_key (hK : ∀ b ∈ [0, 11], ∀ s, Kp b s s) :
    QuietEnds₂ (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) where
  form := by
    intro b hb k s m m' h
    have hn : ¬(2 ≤ b + 1 ∧ b + 1 ≤ 9) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    refine ⟨?_, h.2⟩
    show (form2 (parKey Xs Pl) (fun _ _ => true) (b + 1) s &&
      (!decide ((sharedPlaces true).length ≤ b + 1) || true)) = true
    unfold form2
    rw [if_neg hn]
    simp
  rides := fun _ _ _ _ _ => trivial
  keeps := by
    intro b hb s
    have hn : ¬(1 ≤ b ∧ b ≤ 8) := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      omega
    show keepsAll (parKey Xs Pl) (sentKey Xs Pl) Kp b s s
    unfold keepsAll
    rw [if_neg hn]
    exact hK b hb s

/-- The forward row at the front owes nothing. -/
theorem owes_front : ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).row 0).owes = [] := by
  show (SharedRows.rows true 0).owes = []
  decide

/-- The forward row at the end owes nothing. -/
theorem owes_seal : ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).row 11).owes = [] := by
  show (SharedRows.rows true 11).owes = []
  decide

/-- **The riders at the front.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem ridesPast_front (hE : ∀ s s', Kp 0 s s' → s' = s) (hC : ∀ v, CellsAlone (Mg₀ v)) :
    RidesPast (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 0 := by
  intro k s m E s' ps i v _ hk hi _ _ hu
  have hk' : Kp 0 s s' := hk
  obtain rfl := hE s s' hk'
  have hi' : i ∈ fwdOpen SharedRows.start (SharedRows.rows true) 0 := hi
  rw [open_front] at hi'
  obtain rfl : i = .pinT := List.mem_singleton.1 hi'
  exact hC m.st.input _ ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).strs E)
    ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).strs (E.add ps)) v rfl hu

/-- **The riders at the end.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem ridesPast_seal (hE : ∀ s s', Kp 11 s s' → s' = s) :
    RidesPast (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 11 := by
  intro k s m E s' ps i v _ hk hi _ _ hu
  have hk' : Kp 11 s s' := hk
  obtain rfl := hE s s' hk'
  obtain ⟨h1, h2⟩ := open_seal i hi
  exact holds_free ℓ (parKey Xs Pl) Nm _ i h1 h2 _ _ _ v hu

/-- **It passes the tests with code.** -/
theorem fits_key (hp : (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).planOk = true) :
    (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).fits 12 = true := by
  have hbs := (sits_two Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).2.2.2.1
  refine AtPublicFiles.KeyThread.fits_of _ 12
    (by decide : fwdFit SharedRows.start (SharedRows.rows true) 12 = true) ?_
    (fun _ h => by cases h) (fun _ h => by cases h) ?_ (Nat.le_refl _)
  · intro x hx
    rw [hbs] at hx
    exact AtPublicFiles.KeyThread.lists_of_shaped ((planOk_all hp).2.1 x hx).2
  · intro j
    rw [hbs]
    exact (Nat.zero_add _).symm

/-- **It stands at the frame's start.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem enters_key {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ X}
    (hR : ready (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl) Bk (keyProver K) w₀ rc x k = .ok R)
    (hw : R.common = w) (hx : w.key = x.key) (hV : Vd w)
    (hI : (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).Items
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).opened 0) k
      ((VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).start₂ x) (R.start₂ (keyProver K))
      (envOf ((keyProver K).storedWords w₀ rc) (fun _ _ => none) [])) :
    Enters₂ (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl) (keyProver K)
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) w₀ rc x k R := by
  refine enters₂_of hR (fun _ => rfl) rfl rfl ?_ ?_ hI trivial ?_
  · show (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).start₂ x =
      (lettersKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).first R.common.key
    rw [hw, hx]
    exact start_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w x
  · refine ⟨?_, OnBytes.Means.InOrder.start _⟩
    show (form2 (parKey Xs Pl) (fun _ _ => true) 0
        ((VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl).start₂ x) &&
      (!decide ((sharedPlaces true).length ≤ 0) || true)) = true
    have hn : ¬(2 ≤ 0 ∧ 0 ≤ 9) := by omega
    unfold form2
    rw [if_neg hn]
    simp
  · show R.common = w ∧ Vd R.common
    rw [hw]
    exact ⟨rfl, hV⟩

/-- **It stands at border 1.**
NOT IN FRONT OF A LAW OVER COINS (the rule, and this statement's ground: this file's head). -/
theorem stands_key {Z : VerifierAndGoals.PublicFiles} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi TableKey Unit X₀ X} (hs : AtPublicFiles.AtFiles.KeySourced Z Xs Nr Pl)
    (scope : VerifierAndGoals.InScope Z = true) (hK : ∀ b ∈ [0, 11], ∀ s, Kp b s s)
    (hE : ∀ s s', Kp 0 s s' → s' = s) (hC : ∀ v, CellsAlone (Mg₀ v))
    (hbare : ∀ blk, (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).bs[0]? = some blk →
      ((threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w).hs.find? fun g =>
        g.place == blk.place) = none)
    (hT : Enters₂ (VerifiableInference.Desc.Key.descriptionFromSource Xs Nr Pl) (keyProver K)
      (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) w₀ rc x k R) :
    ∃ (s' : Johnson.RunOne.KeyRows23.St₂) (y : List Played × Mid (Common W₀ Rc TableKey) X₀),
      Thr (threadKey Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w) 1 k s' y.2
        ((envOf ((keyProver K).storedWords w₀ rc) (fun _ _ => none) []).add y.1) :=
  AtPublicFiles.KeyThread.stands₁_at Xs Nr Pl w₀ rc x (keyProver K) hs scope _
    (over_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w)
    (AtPublicFiles.KeyThread.behind₂ Xs Nr Pl hs scope (over_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w)
      (quiet_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w hK) 0 (by decide))
    (owes_front Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w)
    (ridesPast_front Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w hE hC)
    (fits_key Xs Nr Pl K ℓ Nm Mg₀ tb rest Kp Vd w hs.named.plan) hbare hT

end

end AtPublicFiles.KeySharedQuiet

#print axioms AtPublicFiles.KeySharedQuiet.holds_free
#print axioms AtPublicFiles.KeySharedQuiet.open_front
#print axioms AtPublicFiles.KeySharedQuiet.open_seal
#print axioms AtPublicFiles.KeySharedQuiet.over_key
#print axioms AtPublicFiles.KeySharedQuiet.begun_key
#print axioms AtPublicFiles.KeySharedQuiet.quiet_key
#print axioms AtPublicFiles.KeySharedQuiet.owes_front
#print axioms AtPublicFiles.KeySharedQuiet.owes_seal
#print axioms AtPublicFiles.KeySharedQuiet.ridesPast_front
#print axioms AtPublicFiles.KeySharedQuiet.ridesPast_seal
#print axioms AtPublicFiles.KeySharedQuiet.fits_key
#print axioms AtPublicFiles.KeySharedQuiet.enters_key
#print axioms AtPublicFiles.KeySharedQuiet.stands_key
