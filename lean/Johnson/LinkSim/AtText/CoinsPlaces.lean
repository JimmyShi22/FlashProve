-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/CoinsPlaces.lean: the image of the link prover's random values is 0
outside the places, and, where the list of stages is not empty, every value of the coins that is
0 outside the places is such an image.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. It proves two statements that Johnson/LinkSim/AtText/SpecCoins.lean states,
on the map coinsOf from the finite type of random values (LinkK) to the coins (LCoins). InPlaces P S
C, defined in Places.lean, says that the coins C are 0 outside the places.
  coinsIn      for all parameters P, sizes S and k in LinkK at P's list of stages,
               coinsOf k is 0 outside the places (InPlaces P S).
  coinsOnto    for all P and S, if P's list of stages is not empty, then every C in LCoins that
               is 0 outside the places is coinsOf k for some k.
So the two together say: where P has a stage, coinsOf maps LinkK onto the coins that are 0
outside the places.
SpecCoins.lean says why coinsOnto needs that premise.

How it fits. Johnson/LinkSim/AtText/CoinsDown.lean uses coinsIn and coinsOnto, with coinsAdd and
coinsInj (CoinsAdd.lean), to move a shift of the coins from LCoins down to LinkK.

Other names (namespace OnBytes.LinkSim.AtText).
  onNat_high, at2_out, freeAt_out, castW_ne
                 each part of the map gives 0 outside its sizes (castW_ne: at other sizes).
  onNat_recon, at2_recon, freeAt_recon, castW_recon
                 a function that is 0 outside the sizes is the image of its own values inside
                 them (castW_recon: every family of coefficients by name is castW of a family by
                 number).
  inSwitch_mid, inSwitch_last
                 the image of one switch's random values is 0 outside that switch's places:
                 for a switch that a fold follows, and for the last switch.
  LaidFrom       the coins K agree with the image of k from switch number j on.
  laid_tail, inBody_nil   steps of the recursion along the stages.
  inBody_of      along the stages, the image of k is 0 outside the places (InBody).
  body_onto      along the stages, coins that are 0 outside the places are the image of some k.
  coinsIn_at, coinsOnto_at   the two statements for a list of stages that equals P's.
castW_recon uses wNo_inj and wNo_onto (Johnson/Prover/Link/LinkCoinNo.lean). A hiding
polynomial in m variables has 2 m + 1 coefficients: a constant and two for each variable. wNo
gives them distinct numbers, and every number below 2 m + 1 belongs to one of them.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.CoinsAdd
import Johnson.LinkSim.AtText.PlacesProof

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open _root_.Desc.K15 (P15 p12Of)
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open Johnson.Top.H (onNat)

/-! ## Zeros outside the sizes -/

theorem onNat_high {n : ℕ} (c : Fin n → GE) {i : ℕ} (h : n ≤ i) : onNat c i = 0 :=
  dif_neg (not_lt.mpr h)

theorem at2_out {m n : ℕ} (c : Fin m → Fin n → GE) {r q : ℕ} (h : ¬(r < m ∧ q < n)) :
    at2 c r q = 0 := dif_neg h

theorem freeAt_out {s s' : Sg} (k : SwK GE s s') {i : ℕ}
    (h : ¬(carriedN s ≤ i ∧ i < 2 ^ s'.h * s'.Z.l)) : freeAt k i = 0 := by
  unfold freeAt
  split_ifs with h1
  · exact onNat_high _ (Nat.sub_le_sub_right (not_lt.mp fun h2 => h ⟨h1, h2⟩) _)
  · rfl

theorem castW_ne {s₁ σ : Sg} (h : s₁ ≠ σ) (w : Fin (2 * (s₁.h + s₁.g) + 1) → GE) :
    castW s₁ σ w = 0 := by
  unfold castW
  rw [dif_neg h]
  rfl

/-! ## A function that is 0 outside the sizes is the image of its own values -/

theorem onNat_recon (f : ℕ → GE) (n : ℕ) (h : ∀ i, n ≤ i → f i = 0) :
    onNat (fun x : Fin n => f x.val) = f := by
  funext i
  unfold onNat
  split_ifs with h1
  · rfl
  · exact (h i (not_lt.mp h1)).symm

theorem at2_recon (f : ℕ → ℕ → GE) (m n : ℕ) (h : ∀ r q, ¬(r < m ∧ q < n) → f r q = 0) :
    at2 (fun (x : Fin m) (y : Fin n) => f x.val y.val) = f := by
  funext r q
  unfold at2
  split_ifs with h1
  · rfl
  · exact (h r q h1).symm

theorem freeAt_recon {s s' : Sg} (f : ℕ → GE)
    (h : ∀ i, ¬(carriedN s ≤ i ∧ i < 2 ^ s'.h * s'.Z.l) → f i = 0) (mt : Fin (2 ^ (s'.h + s'.g)) →
      Fin s'.C.r → GE) (zt : Fin (2 ^ s'.h) → Fin s'.Z.r → GE) :
    freeAt (⟨mt, fun n => f (maskUsed s + n.val), zt⟩ : SwK GE s s') = f := by
  funext i
  by_cases hi : carriedN s ≤ i ∧ i < 2 ^ s'.h * s'.Z.l
  · have h1 : maskUsed s ≤ i := hi.1
    have h2 : i - maskUsed s < Fmt.M1.fillOf s.st s'.st :=
      Nat.sub_lt_sub_right h1 hi.2
    unfold freeAt onNat
    rw [if_pos h1, dif_pos h2]
    show f (maskUsed s + (i - maskUsed s)) = f i
    rw [Nat.add_sub_cancel' h1]
  · rw [freeAt_out _ hi, h i hi]

theorem castW_recon (s : Sg) (g : HIdx (sVars GE 2 (s.h + s.g)) → GE) :
    ∃ w : Fin (2 * (s.h + s.g) + 1) → GE, castW s s w = g := by
  refine ⟨fun n => g (Classical.choose (wNo_onto (s.h + s.g) n.val n.isLt)), funext fun x => ?_⟩
  rw [castW_self]
  exact congrArg g (wNo_inj _ _ _
    (Classical.choose_spec (wNo_onto (s.h + s.g) (wNo (s.h + s.g) x) (wNo_lt _ x))))

/-! ## Along the stages: into the places -/

theorem inSwitch_last {s s' : Sg} (sw : SwK GE s s') (wd : WordK GE s') :
    InSwitch s s' true (freeAt sw)
      { zeroPS with
        tM := at2 sw.mainTail, tZ := at2 sw.maskTail
        fM := fun r => if r = 0 then onNat wd.mask else fun _ => 0
        fT := fun r => if r = 0 then onNat wd.maskTail else fun _ => 0
        sM := onNat wd.main, sT := onNat wd.mainTail } (fun _ => 0) := by
  refine ⟨fun i h => freeAt_out sw h, fun _ => rfl, fun _ => rfl, fun b q h => at2_out _ h,
    fun b q h => at2_out _ h, fun b q h => ?_, fun b i h => ?_, fun i h => ?_, fun q h => ?_,
    fun _ _ => rfl⟩
  · show (if b = 0 then onNat wd.maskTail else fun _ => 0) q = 0
    split_ifs with h1
    · exact onNat_high _ (not_lt.mp fun h2 => h ⟨h1, h2⟩)
    · rfl
  · show (if b = 0 then onNat wd.mask else fun _ => 0) i = 0
    split_ifs with h1
    · exact onNat_high _ (not_lt.mp fun h2 => h ⟨rfl, h1, h2⟩)
    · rfl
  · exact onNat_high _ (not_lt.mp fun h2 => h ⟨rfl, h2⟩)
  · exact onNat_high _ (not_lt.mp fun h2 => h ⟨rfl, h2⟩)

theorem inSwitch_mid {s s' : Sg} (sw : SwK GE s s') (rd : RideK GE s') :
    InSwitch s s' false (freeAt sw)
      { zeroPS with tM := at2 sw.mainTail, tZ := at2 sw.maskTail, fT := at2 rd.tail }
      (fun σ => castW s' σ rd.W) := by
  refine ⟨fun i h => freeAt_out sw h, fun _ => rfl, fun _ => rfl, fun b q h => at2_out _ h,
    fun b q h => at2_out _ h, fun b q h => at2_out _ h, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, fun σ h => castW_ne (fun e => h ⟨rfl, e.symm⟩) _⟩

/-- From switch number j on, the coins K equal the image of the random values k under bodyFr,
bodyNew and bodyW (W: from number j + 1 on). -/
def LaidFrom (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (k : BodyK GE cur rest) (j : ℕ)
    (K : BCoins) : Prop :=
  (∀ i, K.fr (j + i) = bodyFr cur rest k i) ∧ (∀ i, K.new (j + i) = bodyNew cur rest k i) ∧
    ∀ σ i, K.W σ (j + 1 + i) = bodyW cur rest k σ i

theorem laid_tail {cur next n₂ : Fmt.M1.Stage} {rest : List Fmt.M1.Stage}
    {k : BodyK GE cur (next :: n₂ :: rest)} {j : ℕ} {K : BCoins}
    (h : LaidFrom cur (next :: n₂ :: rest) k j K) : LaidFrom next (n₂ :: rest) k.2.2 (j + 1) K := by
  refine ⟨fun i => ?_, fun i => ?_, fun σ i => ?_⟩
  · rw [show j + 1 + i = j + (i + 1) by omega]
    exact h.1 (i + 1)
  · rw [show j + 1 + i = j + (i + 1) by omega]
    exact h.2.1 (i + 1)
  · rw [show j + 1 + 1 + i = j + 1 + (i + 1) by omega]
    exact h.2.2 σ (i + 1)

theorem inBody_nil (cur : Fmt.M1.Stage) (j : ℕ) (K : BCoins) (hf : ∀ i, K.fr (j + i) = 0)
    (hn : ∀ i, K.new (j + i) = zPS) (hw : ∀ σ i, K.W σ (j + 1 + i) = 0) : InBody cur [] j K := by
  refine ⟨fun i hi => ?_, fun σ i hi => ?_⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact ⟨hf n, hn n⟩
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hi)
    exact hw σ n

theorem inBody_of : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (k : BodyK GE cur rest)
    (j : ℕ) (K : BCoins), LaidFrom cur rest k j K → InBody cur rest j K
  | cur, [], _, j, K, h => inBody_nil cur j K h.1 h.2.1 h.2.2
  | cur, [next], k, j, K, h => by
    refine ⟨?_, inBody_nil next (j + 1) K (fun i => ?_) (fun i => ?_) fun σ i => ?_⟩
    · have e1 : K.fr j = freeAt k.1 := h.1 0
      have e2 : K.new j = bodyNew cur [next] k 0 := h.2.1 0
      have e3 : (fun σ : Sg => K.W σ (j + 1)) =
          fun σ : Sg => (0 : HIdx (sVars GE 2 (σ.h + σ.g)) → GE) :=
        funext fun σ => h.2.2 σ 0
      rw [e1, e2, e3]
      exact inSwitch_last k.1 k.2
    · rw [show j + 1 + i = j + (i + 1) by omega]
      exact h.1 (i + 1)
    · rw [show j + 1 + i = j + (i + 1) by omega]
      exact h.2.1 (i + 1)
    · rw [show j + 1 + 1 + i = j + 1 + (i + 1) by omega]
      exact h.2.2 σ (i + 1)
  | cur, next :: n₂ :: rest, k, j, K, h => by
    refine ⟨?_, inBody_of next (n₂ :: rest) k.2.2 (j + 1) K (laid_tail h)⟩
    have e1 : K.fr j = freeAt k.1 := h.1 0
    have e2 : K.new j = bodyNew cur (next :: n₂ :: rest) k 0 := h.2.1 0
    have e3 : (fun σ => K.W σ (j + 1)) = fun σ => castW (sgOf next) σ k.2.1.W :=
      funext fun σ => h.2.2 σ 0
    rw [e1, e2, e3]
    exact inSwitch_mid k.1 k.2.1

/-! ## Along the stages: coins that are 0 outside the places are an image -/

theorem body_onto : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (j : ℕ) (K : BCoins),
    InBody cur rest j K → ∃ k : BodyK GE cur rest, LaidFrom cur rest k j K
  | _, [], j, K, h =>
    ⟨(), fun i => (h.1 (j + i) (Nat.le_add_right _ _)).1,
      fun i => (h.1 (j + i) (Nat.le_add_right _ _)).2,
      fun σ i => h.2 σ (j + 1 + i) (by omega)⟩
  | cur, [next], j, K, h => by
    obtain ⟨hs, ht⟩ := h
    refine ⟨((⟨fun b q => (K.new j).tM b.val q.val, fun n => K.fr j (maskUsed (sgOf cur) + n.val),
        fun b q => (K.new j).tZ b.val q.val⟩ : SwK GE (sgOf cur) (sgOf next)),
      (⟨fun q => (K.new j).sT q.val, fun i => (K.new j).sM i.val, fun i => (K.new j).fM 0 i.val,
        fun q => (K.new j).fT 0 q.val⟩ : WordK GE (sgOf next))), fun i => ?_, fun i => ?_,
      fun σ i => ?_⟩
    · cases i with
      | zero => exact (freeAt_recon (K.fr j) hs.fr _ _).symm
      | succ n => exact (ht.1 (j + (n + 1)) (by omega)).1
    · cases i with
      | zero =>
        refine ps_ext (funext fun i => hs.tabM i) (funext fun i => hs.tabZ i)
          (at2_recon _ _ _ hs.tM).symm (at2_recon _ _ _ hs.tZ).symm (funext fun b => ?_)
          (funext fun b => ?_)
          (onNat_recon _ _ fun i hi => hs.sM i fun h => absurd h.2 (not_lt.mpr hi)).symm
          (onNat_recon _ _ fun q hq => hs.sT q fun h => absurd h.2 (not_lt.mpr hq)).symm
        · show (K.new j).fM b = if b = 0 then onNat (fun i : Fin (sgOf next).Z.l =>
            (K.new j).fM 0 i.val) else fun _ => 0
          split_ifs with hb
          · rw [hb]
            exact (onNat_recon _ _ fun i hi =>
              hs.fM 0 i fun h => absurd h.2.2 (not_lt.mpr hi)).symm
          · exact funext fun i => hs.fM b i fun h => hb h.2.1
        · show (K.new j).fT b = if b = 0 then onNat (fun q : Fin (sgOf next).Z.r =>
            (K.new j).fT 0 q.val) else fun _ => 0
          split_ifs with hb
          · rw [hb]
            exact (onNat_recon _ _ fun q hq =>
              hs.fT 0 q fun h => absurd h.2 (not_lt.mpr hq)).symm
          · exact funext fun q => hs.fT b q fun h => hb h.1
      | succ n => exact (ht.1 (j + (n + 1)) (by omega)).2
    · cases i with
      | zero => exact hs.W σ fun h => Bool.noConfusion h.1
      | succ n => exact ht.2 σ (j + 1 + (n + 1)) (by omega)
  | cur, next :: n₂ :: rest, j, K, h => by
    obtain ⟨hs, ht⟩ := h
    obtain ⟨kt, hk⟩ := body_onto next (n₂ :: rest) (j + 1) K ht
    obtain ⟨w, hw⟩ := castW_recon (sgOf next) (K.W (sgOf next) (j + 1))
    refine ⟨((⟨fun b q => (K.new j).tM b.val q.val, fun n => K.fr j (maskUsed (sgOf cur) + n.val),
        fun b q => (K.new j).tZ b.val q.val⟩ : SwK GE (sgOf cur) (sgOf next)),
      (⟨w, fun b q => (K.new j).fT b.val q.val⟩ : RideK GE (sgOf next)), kt), fun i => ?_,
      fun i => ?_, fun σ i => ?_⟩
    · cases i with
      | zero => exact (freeAt_recon (K.fr j) hs.fr _ _).symm
      | succ n =>
        rw [show j + (n + 1) = j + 1 + n by omega]
        exact hk.1 n
    · cases i with
      | zero =>
        exact ps_ext (funext fun i => hs.tabM i) (funext fun i => hs.tabZ i)
          (at2_recon _ _ _ hs.tM).symm (at2_recon _ _ _ hs.tZ).symm
          (funext fun b => funext fun i => hs.fM b i fun h => Bool.noConfusion h.1)
          (at2_recon _ _ _ hs.fT).symm
          (funext fun i => hs.sM i fun h => Bool.noConfusion h.1)
          (funext fun q => hs.sT q fun h => Bool.noConfusion h.1)
      | succ n =>
        rw [show j + (n + 1) = j + 1 + n by omega]
        exact hk.2.1 n
    · cases i with
      | zero =>
        show K.W σ (j + 1) = castW (sgOf next) σ w
        by_cases hσ : sgOf next = σ
        · subst hσ
          exact hw.symm
        · rw [castW_ne hσ]
          exact hs.W σ fun h => hσ h.2.symm
      | succ n =>
        rw [show j + 1 + (n + 1) = j + 1 + 1 + n by omega]
        exact hk.2.2 σ n

/-! ## The statements -/

theorem coinsIn_at (P : P15) (S : Sz) : ∀ (l : List Fmt.M1.Stage), (p12Of P).nums.stages = l →
    ∀ k : LinkK GE S l, InPlaces P S (coinsOf S l k)
  | [], hl, _ =>
    ⟨fun _ _ _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl,
      fun f r h => absurd (hl.symm.trans h) (List.cons_ne_nil f r).symm⟩
  | first :: rest, hl, k => by
    refine ⟨fun a i q h => at2_out _ h, fun q h => onNat_high _ h, fun σ h => ?_,
      fun f r hfr => ?_⟩
    · exact castW_ne (fun e : sgOf first = σ => h (by rw [← e, sg0_first hl])) _
    · obtain ⟨rfl, rfl⟩ := List.cons.inj (hl.symm.trans hfr)
      refine inBody_of first rest k.2 0 _ ⟨fun i => ?_, fun i => ?_, fun σ i => ?_⟩
      · rw [Nat.zero_add]
        rfl
      · rw [Nat.zero_add]
        rfl
      · rw [show 0 + 1 + i = i + 1 by omega]
        rfl

/-- The image coinsOf k of any random values k is 0 outside the places (InPlaces P S). -/
theorem coinsIn : Spec.coinsIn := fun P S k => coinsIn_at P S _ rfl k

theorem coinsOnto_at (P : P15) (S : Sz) (C : LCoins) (hC : InPlaces P S C) :
    ∀ (l : List Fmt.M1.Stage), (p12Of P).nums.stages = l → l ≠ [] →
    ∃ k : LinkK GE S l, coinsOf S l k = C
  | [], _, h => absurd rfl h
  | first :: rest, hl, _ => by
    obtain ⟨kb, hb⟩ := body_onto first rest 0 C.body (hC.body first rest hl)
    obtain ⟨w, hw⟩ := castW_recon (sgOf first) (C.body.W (sgOf first) 0)
    refine ⟨((⟨fun a i q => C.tN a i.val q.val, C.pad, w, fun q => C.ψN q.val⟩ :
      FirstK GE S (sgOf first)), kb), lc_ext rfl (funext fun a => at2_recon _ _ _ (hC.tN a))
      (onNat_recon _ _ hC.psi) (funext fun σ => funext fun j => ?_) (funext fun j => ?_)
      (funext fun j => ?_)⟩
    · cases j with
      | zero =>
        show castW (sgOf first) σ w = C.body.W σ 0
        by_cases hσ : sgOf first = σ
        · subst hσ
          exact hw
        · rw [castW_ne hσ]
          exact (hC.W0 σ fun e : σ = sg0 P => hσ (by rw [e, sg0_first hl])).symm
      | succ j =>
        have e := hb.2.2 σ j
        rw [show 0 + 1 + j = j + 1 by omega] at e
        exact e.symm
    · have e := hb.2.1 j
      rw [Nat.zero_add] at e
      exact e.symm
    · have e := hb.1 j
      rw [Nat.zero_add] at e
      exact e.symm

/-- Where P has a stage, every C in LCoins that is 0 outside the places is coinsOf k for some k.
-/
theorem coinsOnto : Spec.coinsOnto := fun P S C hne hC => coinsOnto_at P S C hC _ rfl hne

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.inBody_of
#print axioms OnBytes.LinkSim.AtText.body_onto
#print axioms OnBytes.LinkSim.AtText.coinsIn
#print axioms OnBytes.LinkSim.AtText.coinsOnto
