-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/CoinsAdd.lean: the map from the link prover's random values to the coins
that its algorithm reads is additive and injective, and a sum of random values can be cancelled.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. It proves three statements that Johnson/LinkSim/AtText/SpecCoins.lean states,
on the map coinsOf S l from the finite type of random values (LinkK GE S l, at sizes S and a list l
of stages; Johnson/Prover/Link/LinkCoin.lean) to the coins (LCoins,
Johnson/Prover/Link/LinkAll.lean). GE is the extension field. The sum is taken entry by entry:
addLink on LinkK, addC on LCoins.
  coinsAdd     for all S, l and k, k' in LinkK S l, coinsOf S l (addLink S l k k') equals
               addC (coinsOf S l k) (coinsOf S l k').
  coinsInj     for all S and l, coinsOf S l is injective.
  coinsCancel  for all S, l and k, k', d in LinkK S l, if addLink S l k d = addLink S l k' d,
               then k = k'.
All three hold at all sizes and all lists of stages, with no premise.

How it fits. Johnson/LinkSim/AtText/CoinsDown.lean uses coinsAdd and coinsInj, with the two
statements of CoinsPlaces.lean, to move a shift of the coins from LCoins down to LinkK
(UpToShiftOn.comap, Johnson/LinkSim/UpToOn.lean). coinsCancel is used in the proof of homeExact
(Johnson/LinkSim/AtHome/Home.lean).

Other names (namespace OnBytes.LinkSim.AtText).
  lc_ext, sw_ext, ride_ext, word_ext, first_ext
              two values of one of these structures with equal fields are equal.
  onNat_add, at2_add, castW_add, freeAt_add, bodyW_add, bodyNew_add, bodyFr_add
              each part of the map is additive.
  addPS_zero  the sum of two zero values of PS is zero.
  onNat_inj, at2_inj, castW_inj, freeAt_inj, body_inj
              each part of the map determines the finite function that it extends
              (castW_inj at equal sizes; freeAt_inj: the field free alone; body_inj: a value
              of BodyK, from bodyFr, bodyNew and bodyW together).
  castW_self  at equal sizes, castW reads each coefficient at its number wNo.
  addC_cancel a sum in LCoins can be cancelled on the right.
castW_inj uses wNo_onto (Johnson/Prover/Link/LinkCoinNo.lean). wNo numbers the coefficients of
a hiding polynomial in m variables, which has a constant and two coefficients for each variable.
wNo_onto says that every number below 2 m + 1 is the number of some coefficient.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.SpecCoins

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link
open Johnson.Top.H (onNat)

theorem lc_ext {C C' : LCoins} (h1 : C.pad = C'.pad) (h2 : C.tN = C'.tN) (h3 : C.ψN = C'.ψN)
    (h4 : C.body.W = C'.body.W) (h5 : C.body.new = C'.body.new) (h6 : C.body.fr = C'.body.fr) :
    C = C' := by
  obtain ⟨p, t, y, ⟨w, n, f⟩⟩ := C
  obtain ⟨p', t', y', ⟨w', n', f'⟩⟩ := C'
  simp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  rfl

/-! ## Additive -/

theorem onNat_add {n : ℕ} (c c' : Fin n → GE) (i : ℕ) :
    onNat (fun x => c x + c' x) i = onNat c i + onNat c' i := by
  unfold onNat
  split_ifs
  · rfl
  · exact (add_zero _).symm

theorem at2_add {m n : ℕ} (c c' : Fin m → Fin n → GE) (r q : ℕ) :
    at2 (fun x y => c x y + c' x y) r q = at2 c r q + at2 c' r q := by
  unfold at2
  split_ifs
  · rfl
  · exact (add_zero _).symm

theorem castW_add (s₁ s : Sg) (w w' : Fin (2 * (s₁.h + s₁.g) + 1) → GE)
    (x : HIdx (sVars GE 2 (s.h + s.g))) :
    castW s₁ s (fun n => w n + w' n) x = castW s₁ s w x + castW s₁ s w' x := by
  unfold castW
  split_ifs
  · rfl
  · exact (add_zero _).symm

theorem freeAt_add {s s' : Sg} (k k' : SwK GE s s') (i : ℕ) :
    freeAt (addSw k k') i = freeAt k i + freeAt k' i := by
  unfold freeAt
  split_ifs
  · exact onNat_add k.free k'.free _
  · exact (add_zero _).symm

theorem addPS_zero : addPS zeroPS zeroPS = zeroPS :=
  ps_ext (funext fun _ => add_zero _) (funext fun _ => add_zero _)
    (funext fun _ => funext fun _ => add_zero _) (funext fun _ => funext fun _ => add_zero _)
    (funext fun _ => funext fun _ => add_zero _) (funext fun _ => funext fun _ => add_zero _)
    (funext fun _ => add_zero _) (funext fun _ => add_zero _)

theorem bodyW_add : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (k k' : BodyK GE cur rest)
    (σ : Sg) (j : ℕ) (x : HIdx (sVars GE 2 (σ.h + σ.g))),
    bodyW cur rest (addBody cur rest k k') σ j x = bodyW cur rest k σ j x + bodyW cur rest k' σ j x
  | _, [], _, _, _, _, _ => (add_zero _).symm
  | _, [_], _, _, _, _, _ => (add_zero _).symm
  | _, next :: _ :: _, k, k', σ, 0, x => castW_add (sgOf next) σ k.2.1.W k'.2.1.W x
  | _, next :: n₂ :: rest, k, k', σ, j + 1, x => bodyW_add next (n₂ :: rest) k.2.2 k'.2.2 σ j x

theorem bodyFr_add : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (k k' : BodyK GE cur rest)
    (j i : ℕ),
    bodyFr cur rest (addBody cur rest k k') j i = bodyFr cur rest k j i + bodyFr cur rest k' j i
  | _, [], _, _, _, _ => (add_zero _).symm
  | _, [_], k, k', 0, i => freeAt_add k.1 k'.1 i
  | _, [_], _, _, _ + 1, _ => (add_zero _).symm
  | _, _ :: _ :: _, k, k', 0, i => freeAt_add k.1 k'.1 i
  | _, next :: n₂ :: rest, k, k', j + 1, i => bodyFr_add next (n₂ :: rest) k.2.2 k'.2.2 j i

theorem bodyNew_add : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (k k' : BodyK GE cur rest)
    (j : ℕ),
    bodyNew cur rest (addBody cur rest k k') j =
      addPS (bodyNew cur rest k j) (bodyNew cur rest k' j)
  | _, [], _, _, _ => addPS_zero.symm
  | _, [_], k, k', 0 =>
    ps_ext (funext fun _ => (add_zero _).symm) (funext fun _ => (add_zero _).symm)
      (funext fun b => funext fun q => at2_add k.1.mainTail k'.1.mainTail b q)
      (funext fun b => funext fun q => at2_add k.1.maskTail k'.1.maskTail b q)
      (funext fun b => funext fun i => by
        show (if b = 0 then onNat (fun x => k.2.mask x + k'.2.mask x) else fun _ => 0) i =
          (if b = 0 then onNat k.2.mask else fun _ => 0) i +
            (if b = 0 then onNat k'.2.mask else fun _ => 0) i
        split_ifs
        · exact onNat_add _ _ i
        · exact (add_zero _).symm)
      (funext fun b => funext fun q => by
        show (if b = 0 then onNat (fun x => k.2.maskTail x + k'.2.maskTail x) else fun _ => 0) q =
          (if b = 0 then onNat k.2.maskTail else fun _ => 0) q +
            (if b = 0 then onNat k'.2.maskTail else fun _ => 0) q
        split_ifs
        · exact onNat_add _ _ q
        · exact (add_zero _).symm)
      (funext fun i => onNat_add k.2.main k'.2.main i)
      (funext fun q => onNat_add k.2.mainTail k'.2.mainTail q)
  | _, [_], _, _, _ + 1 => addPS_zero.symm
  | _, _ :: _ :: _, k, k', 0 =>
    ps_ext (funext fun _ => (add_zero _).symm) (funext fun _ => (add_zero _).symm)
      (funext fun b => funext fun q => at2_add k.1.mainTail k'.1.mainTail b q)
      (funext fun b => funext fun q => at2_add k.1.maskTail k'.1.maskTail b q)
      (funext fun _ => funext fun _ => (add_zero _).symm)
      (funext fun b => funext fun q => at2_add k.2.1.tail k'.2.1.tail b q)
      (funext fun _ => (add_zero _).symm) (funext fun _ => (add_zero _).symm)
  | _, next :: n₂ :: rest, k, k', j + 1 => bodyNew_add next (n₂ :: rest) k.2.2 k'.2.2 j

/-- coinsOf maps the entry-by-entry sum of two random values (addLink) to the sum of their images
(addC). -/
theorem coinsAdd : Spec.coinsAdd := by
  intro S l k k'
  cases l with
  | nil =>
    exact lc_ext (funext fun _ => (add_zero _).symm)
      (funext fun _ => funext fun _ => funext fun _ => (add_zero _).symm)
      (funext fun _ => (add_zero _).symm)
      (funext fun _ => funext fun _ => funext fun _ => (add_zero _).symm)
      (funext fun _ => addPS_zero.symm) (funext fun _ => funext fun _ => (add_zero _).symm)
  | cons first rest =>
    refine lc_ext rfl (funext fun a => funext fun i => funext fun q => at2_add _ _ i q)
      (funext fun q => onNat_add _ _ q) (funext fun σ => funext fun j => funext fun x => ?_)
      (funext fun j => bodyNew_add first rest k.2 k'.2 j)
      (funext fun j => funext fun i => bodyFr_add first rest k.2 k'.2 j i)
    cases j with
    | zero => exact castW_add (sgOf first) σ k.1.W k'.1.W x
    | succ j => exact bodyW_add first rest k.2 k'.2 σ j x

/-! ## Injective -/

theorem onNat_inj {n : ℕ} {c c' : Fin n → GE} (h : onNat c = onNat c') : c = c' := by
  funext i
  have e := congrFun h i.val
  unfold onNat at e
  rwa [dif_pos i.isLt, dif_pos i.isLt] at e

theorem at2_inj {m n : ℕ} {c c' : Fin m → Fin n → GE} (h : at2 c = at2 c') : c = c' := by
  funext r q
  have e := congrFun (congrFun h r.val) q.val
  unfold at2 at e
  rwa [dif_pos ⟨r.isLt, q.isLt⟩, dif_pos ⟨r.isLt, q.isLt⟩] at e

theorem castW_self (s : Sg) (w : Fin (2 * (s.h + s.g) + 1) → GE)
    (x : HIdx (sVars GE 2 (s.h + s.g))) :
    castW s s w x = w ⟨wNo (s.h + s.g) x, wNo_lt _ x⟩ := by
  unfold castW
  rw [dif_pos rfl]

theorem castW_inj {s : Sg} {w w' : Fin (2 * (s.h + s.g) + 1) → GE}
    (h : castW s s w = castW s s w') : w = w' := by
  funext n
  obtain ⟨x, hx⟩ := wNo_onto (s.h + s.g) n.val n.isLt
  have e := congrFun h x
  rw [castW_self, castW_self] at e
  have en : (⟨wNo (s.h + s.g) x, wNo_lt _ x⟩ : Fin (2 * (s.h + s.g) + 1)) = n := Fin.ext hx
  rwa [en] at e

theorem freeAt_inj {s s' : Sg} {k k' : SwK GE s s'} (h : freeAt k = freeAt k') :
    k.free = k'.free := by
  funext n
  have e := congrFun h (maskUsed s + n.val)
  unfold freeAt onNat at e
  have e1 : maskUsed s + n.val - maskUsed s = n.val := Nat.add_sub_cancel_left _ _
  rw [if_pos (Nat.le_add_right _ _), if_pos (Nat.le_add_right _ _),
    dif_pos (by rw [e1]; exact n.isLt), dif_pos (by rw [e1]; exact n.isLt)] at e
  have en : (⟨maskUsed s + n.val - maskUsed s, by rw [e1]; exact n.isLt⟩ :
      Fin (Fmt.M1.fillOf s.st s'.st)) = n := Fin.ext e1
  rwa [en] at e

theorem sw_ext {s s' : Sg} {k k' : SwK GE s s'} (h1 : k.mainTail = k'.mainTail)
    (h2 : k.free = k'.free) (h3 : k.maskTail = k'.maskTail) : k = k' := by
  cases k
  cases k'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem ride_ext {s : Sg} {k k' : RideK GE s} (h1 : k.W = k'.W) (h2 : k.tail = k'.tail) :
    k = k' := by
  cases k
  cases k'
  simp only at h1 h2
  subst h1 h2
  rfl

theorem word_ext {s : Sg} {k k' : WordK GE s} (h1 : k.mainTail = k'.mainTail)
    (h2 : k.main = k'.main) (h3 : k.mask = k'.mask) (h4 : k.maskTail = k'.maskTail) : k = k' := by
  cases k
  cases k'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem first_ext {S : Sz} {s₀ : Sg} {k k' : FirstK GE S s₀} (h1 : k.tail = k'.tail)
    (h2 : k.pad = k'.pad) (h3 : k.W = k'.W) (h4 : k.wTail = k'.wTail) : k = k' := by
  cases k
  cases k'
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

/-- Two values of BodyK whose images under bodyFr, bodyNew and bodyW are equal as functions (at
every index j, and for bodyW at all sizes σ too) are equal. -/
theorem body_inj : ∀ (cur : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (k k' : BodyK GE cur rest),
    (∀ j, bodyFr cur rest k j = bodyFr cur rest k' j) →
    (∀ j, bodyNew cur rest k j = bodyNew cur rest k' j) →
    (∀ σ j, bodyW cur rest k σ j = bodyW cur rest k' σ j) → k = k'
  | _, [], _, _, _, _, _ => rfl
  | _, [_], k, k', hf, hn, _ =>
    Prod.ext
      (sw_ext (at2_inj (congrArg PS.tM (hn 0))) (freeAt_inj (hf 0))
        (at2_inj (congrArg PS.tZ (hn 0))))
      (word_ext (onNat_inj (congrArg PS.sT (hn 0))) (onNat_inj (congrArg PS.sM (hn 0)))
        (onNat_inj (congrFun (congrArg PS.fM (hn 0)) 0))
        (onNat_inj (congrFun (congrArg PS.fT (hn 0)) 0)))
  | _, next :: n₂ :: rest, k, k', hf, hn, hw =>
    Prod.ext
      (sw_ext (at2_inj (congrArg PS.tM (hn 0))) (freeAt_inj (hf 0))
        (at2_inj (congrArg PS.tZ (hn 0))))
      (Prod.ext (ride_ext (castW_inj (hw (sgOf next) 0)) (at2_inj (congrArg PS.fT (hn 0))))
        (body_inj next (n₂ :: rest) k.2.2 k'.2.2 (fun j => hf (j + 1)) (fun j => hn (j + 1))
          fun σ j => hw σ (j + 1)))

/-- coinsOf S l is injective. -/
theorem coinsInj : Spec.coinsInj := by
  intro S l k k' h
  cases l with
  | nil => rfl
  | cons first rest =>
    refine Prod.ext (first_ext (funext fun a => at2_inj (congrFun (congrArg LCoins.tN h) a))
      (congrArg LCoins.pad h) (castW_inj ?_) (onNat_inj (congrArg LCoins.ψN h)))
      (body_inj first rest k.2 k'.2 (fun j => congrFun (congrArg (fun C => C.body.fr) h) j)
        (fun j => congrFun (congrArg (fun C => C.body.new) h) j) fun σ j => ?_)
    · exact congrFun (congrFun (congrArg (fun C => C.body.W) h) (sgOf first)) 0
    · exact congrFun (congrFun (congrArg (fun C => C.body.W) h) σ) (j + 1)

theorem addC_cancel {C C' Dl : LCoins} (h : addC C Dl = addC C' Dl) : C = C' := by
  refine lc_ext (funext fun a => add_right_cancel (congrFun (congrArg LCoins.pad h) a))
    (funext fun a => funext fun i => funext fun q =>
      add_right_cancel (congrFun (congrFun (congrFun (congrArg LCoins.tN h) a) i) q))
    (funext fun q => add_right_cancel (congrFun (congrArg LCoins.ψN h) q))
    (funext fun σ => funext fun j => funext fun x =>
      add_right_cancel (congrFun (congrFun (congrFun (congrArg (fun C => C.body.W) h) σ) j) x))
    (funext fun j => ?_)
    (funext fun j => funext fun i =>
      add_right_cancel (congrFun (congrFun (congrArg (fun C => C.body.fr) h) j) i))
  have e : addPS (C.body.new j) (Dl.body.new j) = addPS (C'.body.new j) (Dl.body.new j) :=
    congrFun (congrArg (fun C => C.body.new) h) j
  exact ps_ext (funext fun i => add_right_cancel (congrFun (congrArg PS.tabM e) i))
    (funext fun i => add_right_cancel (congrFun (congrArg PS.tabZ e) i))
    (funext fun b => funext fun q =>
      add_right_cancel (congrFun (congrFun (congrArg PS.tM e) b) q))
    (funext fun b => funext fun q =>
      add_right_cancel (congrFun (congrFun (congrArg PS.tZ e) b) q))
    (funext fun b => funext fun q =>
      add_right_cancel (congrFun (congrFun (congrArg PS.fM e) b) q))
    (funext fun b => funext fun q =>
      add_right_cancel (congrFun (congrFun (congrArg PS.fT e) b) q))
    (funext fun i => add_right_cancel (congrFun (congrArg PS.sM e) i))
    (funext fun q => add_right_cancel (congrFun (congrArg PS.sT e) q))

/-- Right cancellation for addLink: addLink S l k d = addLink S l k' d implies k = k'. -/
theorem coinsCancel : Spec.coinsCancel := by
  intro S l k k' d h
  refine coinsInj S l (addC_cancel (Dl := coinsOf S l d) ?_)
  rw [← coinsAdd, ← coinsAdd, h]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.coinsAdd
#print axioms OnBytes.LinkSim.AtText.coinsInj
#print axioms OnBytes.LinkSim.AtText.coinsCancel
