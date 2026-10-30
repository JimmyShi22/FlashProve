-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/InRun.lean: kind K5: where the kind's own readers return, the indices
that they read lie in the table and the heads' features are lawful: the readers, one by one. Tools
for Johnson/Desc/First/Att/Claims/InRunAll.lean. (The proofs of Johnson/Road/Rows take the same
facts from their run's return: u3at's test "internal-a-table-index", xl's two refusals.)

Main names:
  `wbind_some`: a bind that returns: both halves return. `RC.and`, `RC.mono`, `RC.foldlM_all`,
    `RC.forIn_mem` (`Yl`: a loop's step hands back "go on"), `RC.forM_mem`.
  `rc_u3at`, `rc_weighted`, `rc_shV`, `rc_overG`, `rc_plane`, `rc_xl`, `rc_readMaximum`,
    `rc_readDenominator`, `rc_readIndexBit`, `rc_readHead`, `rc_readGroup`; `InLongG`: InLong with
    the heads counted as the shape counts them.
All at i := inOld h, so that each condition stands in the plain record's own letters; the runs at a
record i of the kind's own and at stripIn i = inOld (oldOf S gL i) are one
(Johnson/Desc/First/Att/Claims/Seated.lean, Johnson/Desc/First/Att/Claims/Any.lean).
Used of OnBytes and Johnson/Road: plain records; Model.headFeat, cutLast, tenCell, eqTab (pure
functions); Rows.hiOf, planeFirst (plain definitions), cutLast_ok, headFeat_ok; cutLast_old,
headFeat_old (Johnson/Desc/First/Att/Claims/Claim4.lean). No routine in a context and no theorem on
a run.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.EndsAll
import Johnson.Desc.First.Att.Claims.PointsRows

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (tenOf)
open VerifiableInference.Desc.First.Att.P.Runs (W)

variable {α β σ : Type} {K : ℕ}

theorem wbind_some {r : W α} {k : α → W β} {acc : Array Aff} {x : β × Array Aff}
    (h : (r >>= k) K acc = some x) : ∃ y, r K acc = some y ∧ k y.1 K y.2 = some x := by
  simp only [Bind.bind, ReaderT.bind, StateT.bind] at h
  cases hr : r K acc with
  | none => simp [hr] at h
  | some y =>
    simp only [hr] at h
    exact ⟨y, rfl, h⟩

theorem RC.and {r : W α} {k : α → W β} {C D : Prop} (h1 : RC K r C) (h2 : ∀ a, RC K (k a) D) :
    RC K (r >>= k) (C ∧ D) := by
  intro acc x hx
  obtain ⟨y, e1, e2⟩ := wbind_some hx
  exact ⟨h1 acc y e1, h2 y.1 y.2 x e2⟩

theorem RC.mono {r : W α} {C D : Prop} (h : RC K r C) (f : C → D) : RC K r D :=
  fun acc x hx => f (h acc x hx)

theorem RC.foldlM_all {f : σ → α → W σ} {C : α → Prop} (h : ∀ s a, RC K (f s a) (C a)) (xs : List α)
    (s : σ) : RC K (xs.foldlM f s) (∀ a ∈ xs, C a) :=
  fun acc x hx a ha => RC.foldlM (fun s => h s a) ha s acc x hx

/-- A loop's step hands back "go on". -/
def Yl (K : ℕ) (r : W (ForInStep PUnit)) : Prop :=
  ∀ acc x, r K acc = some x → x.1 = ForInStep.yield PUnit.unit

theorem Yl.pure : Yl K (Pure.pure (ForInStep.yield PUnit.unit)) := by
  intro acc x hx
  simp only [Pure.pure, ReaderT.pure, StateT.pure, Option.some.injEq] at hx
  rw [← hx]

theorem Yl.bind {r : W α} {k : α → W (ForInStep PUnit)} (h : ∀ a, Yl K (k a)) : Yl K (r >>= k) := by
  intro acc x hx
  obtain ⟨y, _, e2⟩ := wbind_some hx
  exact h y.1 y.2 x e2

theorem RC.forIn_mem {f : α → PUnit → W (ForInStep PUnit)} {C : Prop} {a : α}
    (hy : ∀ a, Yl K (f a PUnit.unit)) (hC : RC K (f a PUnit.unit) C) :
    ∀ {xs : List α}, a ∈ xs → RC K (forIn xs PUnit.unit f) C
  | b :: xs, hm => by
    rw [List.forIn_cons]
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact RC.left hC
    · intro acc x hx
      obtain ⟨y, e1, e2⟩ := wbind_some hx
      have ey := hy b acc y e1
      rw [ey] at e2
      exact RC.forIn_mem hy hC hm' y.2 x e2

theorem RC.forM_mem {f : α → W PUnit} {C : Prop} {a : α} (hC : RC K (f a) C) :
    ∀ {xs : List α}, a ∈ xs → RC K (xs.forM f) C
  | b :: xs, hm => by
    show RC K (f b >>= fun _ => xs.forM f) C
    rcases List.mem_cons.1 hm with rfl | hm'
    · exact RC.left hC
    · exact RC.right fun _ => RC.forM_mem hC hm'

/-! ### the readers -/

variable (h : Attention.Heard)

theorem rc_u3at (t n : ℕ) : RC K (P.Runs.u3at (inOld h) t n) (n < (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.u3at
  refine RC.left ?_
  intro acc x hx
  unfold P.Runs.mustAs at hx
  by_cases hd : n < (h.t.tabLen.lookup t).getD 0
  · exact hd
  · have e : Decidable.decide (n < ((inOld h).t.tabLen.lookup t).getD 0) = false := decide_eq_false hd
    rw [e] at hx
    cases hx

theorem rc_weighted (n : ℕ) (w : Array E) (f : ℕ → W Aff) (C : ℕ → Prop) (hf : ∀ k, RC K (f k) (C k)) :
    RC K (P.Runs.weighted n w f) (∀ k < n, C k) := by
  unfold P.Runs.weighted
  exact (RC.foldlM_all (fun _ k => RC.left (hf k)) _ _).mono fun H k hk => H k (List.mem_range.2 hk)

theorem rc_shV (t off nl J lam j : ℕ) : RC K (P.Runs.shV (inOld h) t off nl J lam j)
    (∀ l < nl, off + (l * h.S.Lam + lam) * J + j < (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.shV
  exact rc_weighted _ _ _ _ fun l => rc_u3at h t _

theorem rc_overG (zg : Array E) (f : ℕ → W Aff) (C : ℕ → Prop) (hf : ∀ g, RC K (f g) (C g)) :
    RC K (P.Runs.overG (inOld h) zg f) (∀ g < h.S.G, C g) := by
  unfold P.Runs.overG
  exact rc_weighted _ _ _ _ hf

theorem rc_plane (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    RC K (P.Runs.plane (inOld h) t x lam a z isD)
      (∀ hi < (eqTab (z.extract 0 ((if isD then h.S.nD else h.S.nM) - h.S.cf.lmS))).size,
        Rows.planeFirst h.S x lam a isD >>> h.S.cf.lmS + hi < (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.plane
  exact rc_weighted _ _ _ _ fun hi => rc_u3at h t _

theorem rc_xl (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    RC K (P.Runs.xl (inOld h) t (tenOf X) lam hd zc)
      (headFeat X hd h.S.dh = .ok (hd * h.S.dh) ∧ ∀ ch < (hiOf h.S zc).size, ∀ l < X.nl,
        tenCell X l lam (hd * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.xl
  dsimp only
  rw [cutLast_old, headFeat_old]
  show RC K (match (Model.cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls).toOption with
    | some cut => _ | _ => _) _
  cases hc : Model.cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls with
  | error e => exact RC.never fun _ => rfl
  | ok cut =>
    show RC K (match (Model.headFeat X hd h.S.dh).toOption with | some j0 => _ | _ => _) _
    cases hj : Model.headFeat X hd h.S.dh with
    | error e => exact RC.never fun _ => rfl
    | ok j0 =>
      have ej := headFeat_ok hj
      obtain ⟨_, ec⟩ := cutLast_ok hc
      subst ej
      refine (rc_weighted _ _ _ _ fun ch => rc_weighted _ _ _ _ fun l => rc_u3at h t _).mono fun H => ⟨rfl, ?_⟩
      intro ch hch l hl
      refine H ch ?_ l hl
      rw [ec]
      exact hch

theorem rc_readMaximum (t : ℕ) (zg : Array E) (lam a : ℕ) :
    RC K (P.Runs.readMaximum (inOld h) t zg lam a) (∀ g < h.S.G, ∀ l < 4,
      h.S.oMr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a) < (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.readMaximum
  exact rc_overG h _ _ _ fun g => rc_shV h _ _ _ _ _ _

theorem rc_readDenominator (t : ℕ) (zg : Array E) (lam a : ℕ) :
    RC K (P.Runs.readDenominator (inOld h) t zg lam a) (∀ g < h.S.G, ∀ l < 4,
      h.S.oZr + (l * h.S.Lam + lam) * h.S.cf.H + (g * h.S.HA + a) < (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.readDenominator
  exact rc_overG h _ _ _ fun g => rc_shV h _ _ _ _ _ _

theorem rc_readIndexBit (t : ℕ) (zg : Array E) (lam a k : ℕ) :
    RC K (P.Runs.readIndexBit (inOld h) t zg lam a k) (∀ g < h.S.G, ∀ l < 1,
      h.S.oIb + (l * h.S.Lam + lam) * (h.S.cf.lt * h.S.cf.H) + (k * h.S.cf.H + g * h.S.HA + a) <
        (h.t.tabLen.lookup t).getD 0) := by
  unfold P.Runs.readIndexBit
  exact rc_overG h _ _ _ fun g => rc_shV h _ _ _ _ _ _

/-- InLong, with the heads counted as the shape counts them. -/
structure InLongG (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam : ℕ) (hdOf : ℕ → ℕ) (zc : Array E) :
    Prop where
  feat : ∀ g < h.S.G, headFeat X (hdOf g) h.S.dh = .ok (hdOf g * h.S.dh)
  inn : ∀ g < h.S.G, ∀ ch < (hiOf h.S zc).size, ∀ l < X.nl,
    tenCell X l lam (hdOf g * h.S.dh) / 2 ^ h.S.ls + ch < (h.t.tabLen.lookup t).getD 0

theorem InLongG.long {h : Attention.Heard} {t : ℕ} {X : TenAt} {lam : ℕ} {hdOf : ℕ → ℕ} {zc : Array E}
    (I : InLongG h t X lam hdOf zc) (hG : h.S.G = 2 ^ h.S.cf.lgk) : InLong h t X lam hdOf zc :=
  ⟨fun g hg => I.feat g (by rw [hG]; exact hg), fun g hg => I.inn g (by rw [hG]; exact hg)⟩

theorem rc_readHead (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    RC K (P.Runs.readHead (inOld h) t (tenOf X) zg zc lam a)
      (InLongG h t X lam (fun g => g * h.S.HA + a) zc) := by
  unfold P.Runs.readHead
  exact (rc_overG h _ _ _ fun g => rc_xl h t X lam _ zc).mono fun H =>
    ⟨fun g hg => (H g hg).1, fun g hg => (H g hg).2⟩

theorem rc_readGroup (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    RC K (P.Runs.readGroup (inOld h) t (tenOf X) zg zc lam) (InLongG h t X lam (fun g => g) zc) := by
  unfold P.Runs.readGroup
  exact (rc_overG h _ _ _ fun g => rc_xl h t X lam _ zc).mono fun H =>
    ⟨fun g hg => (H g hg).1, fun g hg => (H g hg).2⟩

end K5Law
