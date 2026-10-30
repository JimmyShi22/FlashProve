-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/Covered.lean: kind K5: every entry of the array of tables that a form
gathered by "first" or "second" names lies in the tables' part: it is entry number x < nW of array
number i.iU3, read at K columns (row x / K, place x % K). A form that named an entry outside the
part would be covered by no read of the smallness test.

Main names:
  `EntIn`, `Cov iU3 K nW f`: every entry that f names is such a one. Closed under ofConst, slot,
    ent, addMul, +, − and scale.
  `CV K C P r`: wherever r returns at K from forms that all meet C, what it returns meets P and the
    forms behind all meet C. The rules; `cv_…`: routine by routine. The bound comes from u3at's own
    test "internal-a-table-index".
  `LenIn i nW`: each table, from its first entry on, at its stored length, lies below nW. `len_in`:
    it holds of what tablesP itself makes (`Inv`, `IvQ`: every stored pair ends at or below the next
    free entry; the placing's last test: the next free entry is nW).
  `RowsCov i K nW`: a premise: the rows that the sumchecks leave (the record's fields row) name no
    entry outside the part. Not shown in this file or in what it imports.
  `reads_covered_K05`: LenIn → RowsCov → the two runs' return → ∀ f ∈ l₁ ++ l₂, Cov i.iU3 K nW f.
Limit: the key forms that "keys" hands on are not covered.
Used of OnBytes: the plain records Aff and Ent and the pure functions on them
(OnBytes/Model/Hide.lean). No routine in a context and no theorem on a run.
Not claimed: that a read is true.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Claims.InRun
import Johnson.Desc.First.Att.Claims.TablesSpec

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P.Runs (W JoinsP)

variable {α β σ : Type} {K : ℕ}

/-- An entry named by a form is entry number x < nW of array number iU3, read at K columns. -/
def EntIn (iU3 K nW : ℕ) (e : Ent) : Prop := ∃ x < nW, e.tree = iU3 ∧ e.row = x / K ∧ e.idx = x % K

/-- Every entry that the form names lies in the tables' part. -/
def Cov (iU3 K nW : ℕ) (f : Aff) : Prop := ∀ e ∈ f.ents.toList, EntIn iU3 K nW e

variable {iU3 nW : ℕ}

theorem cov_ofConst (v : E) : Cov iU3 K nW (Aff.ofConst v) := by
  intro e he; simp [Aff.ofConst] at he
theorem cov_slot (j : ℕ) : Cov iU3 K nW (Aff.slot j) := by
  intro e he; simp [Aff.slot] at he
theorem cov_ent {x : ℕ} (hx : x < nW) : Cov iU3 K nW (Aff.ent iU3 (x / K) (x % K)) := by
  intro e he
  have he' : e ∈ [({ tree := iU3, row := x / K, idx := x % K, coef := oneE } : Ent)] := he
  rw [List.mem_singleton] at he'
  subst he'
  exact ⟨x, hx, rfl, rfl, rfl⟩

theorem mem_foldl_push {γ : Type} (g : γ → γ) (b : List γ) : ∀ (a : Array γ) (e : γ),
    e ∈ (b.foldl (fun l x => l.push (g x)) a).toList → e ∈ a.toList ∨ ∃ x ∈ b, e = g x := by
  induction b with
  | nil => intro a e h; exact .inl h
  | cons y b ih =>
    intro a e h
    rcases ih (a.push (g y)) e h with h1 | ⟨x, hx, rfl⟩
    · rw [Array.toList_push, List.mem_append, List.mem_singleton] at h1
      rcases h1 with h1 | rfl
      · exact .inl h1
      · exact .inr ⟨y, List.mem_cons_self, rfl⟩
    · exact .inr ⟨x, List.mem_cons_of_mem _ hx, rfl⟩

theorem cov_addMul {a b : Aff} (ha : Cov iU3 K nW a) (hb : Cov iU3 K nW b) (k : E) :
    Cov iU3 K nW (Aff.addMul a b k) := by
  intro e he
  have he' := he
  unfold Aff.addMul at he'
  dsimp only at he'
  rw [← Array.foldl_toList] at he'
  rcases mem_foldl_push (fun x : Ent => { x with coef := mulE x.coef k }) _ _ _ he' with h1 | ⟨x, hx, rfl⟩
  · exact ha e h1
  · obtain ⟨y, hy, a1, a2, a3⟩ := hb x hx
    exact ⟨y, hy, a1, a2, a3⟩

theorem cov_add {a b : Aff} (ha : Cov iU3 K nW a) (hb : Cov iU3 K nW b) : Cov iU3 K nW (a + b) :=
  cov_addMul ha hb _
theorem cov_sub {a b : Aff} (ha : Cov iU3 K nW a) (hb : Cov iU3 K nW b) : Cov iU3 K nW (a - b) :=
  cov_addMul ha hb _
theorem cov_scale {a : Aff} (ha : Cov iU3 K nW a) (k : E) : Cov iU3 K nW (Aff.scale a k) :=
  cov_addMul (by intro e he; simp at he) ha _

/-- Wherever r returns at K from forms that all meet C: what it returns meets P, and the forms behind all meet C. -/
def CV (K : ℕ) (C : Aff → Prop) (P : α → Prop) (r : W α) : Prop :=
  ∀ acc x, r K acc = some x → (∀ f ∈ acc.toList, C f) → P x.1 ∧ ∀ f ∈ x.2.toList, C f

variable {C : Aff → Prop}

theorem CV.pure {P : α → Prop} {a : α} (h : P a) : CV K C P (Pure.pure a : W α) := by
  intro acc x hx ha
  simp only [Pure.pure, ReaderT.pure, StateT.pure, Option.some.injEq] at hx
  rw [← hx]
  exact ⟨h, ha⟩

theorem CV.bind {P : α → Prop} {Q : β → Prop} {r : W α} {k : α → W β} (h1 : CV K C P r)
    (h2 : ∀ a, P a → CV K C Q (k a)) : CV K C Q (r >>= k) := by
  intro acc x hx ha
  obtain ⟨y, e1, e2⟩ := wbind_some hx
  obtain ⟨p, c⟩ := h1 acc y e1 ha
  exact h2 y.1 p y.2 x e2 c

theorem CV.never {P : α → Prop} {r : W α} (h : ∀ acc, r K acc = none) : CV K C P r := by
  intro acc x hx; rw [h acc] at hx; cases hx

theorem CV.mono {P Q : α → Prop} {r : W α} (h : CV K C P r) (f : ∀ a, P a → Q a) : CV K C Q r :=
  fun acc x hx ha => ⟨f _ (h acc x hx ha).1, (h acc x hx ha).2⟩

theorem CV.lin {f : Aff} (h : C f) : CV K C (fun _ => True) (P.Runs.W.lin f) := by
  intro acc x hx ha
  have hx' : some (PUnit.unit, acc.push f) = some x := hx
  rw [← Option.some.inj hx']
  refine ⟨trivial, fun g hg => ?_⟩
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hg
  rcases hg with hg | rfl
  · exact ha g hg
  · exact h

theorem CV.mustAs (n : String) (b : Bool) : CV K C (fun _ => True) (P.Runs.mustAs n b) := by
  unfold P.Runs.mustAs
  cases b
  · exact CV.never fun _ => rfl
  · exact CV.pure trivial

theorem CV.need (x : Option α) : CV K C (fun a => x = some a) (P.Runs.W.need x) := by
  cases x with
  | none => exact CV.never fun _ => rfl
  | some a => exact CV.pure rfl

theorem CV.ite {P : α → Prop} {c : Prop} [Decidable c] {r r' : W α} (h : CV K C P r) (h' : CV K C P r') :
    CV K C P (if c then r else r') := by
  split
  · exact h
  · exact h'

theorem CV.foldlM {P : σ → Prop} {f : σ → α → W σ} (h : ∀ s a, P s → CV K C P (f s a)) :
    ∀ (xs : List α) (s : σ), P s → CV K C P (xs.foldlM f s)
  | [], s, hs => by rw [List.foldlM_nil]; exact CV.pure hs
  | a :: xs, s, hs => by
    rw [List.foldlM_cons]
    exact CV.bind (h s a hs) fun s' hs' => CV.foldlM h xs s' hs'

theorem CV.forM {f : α → W PUnit} (h : ∀ a, CV K C (fun _ => True) (f a)) :
    ∀ xs : List α, CV K C (fun _ => True) (xs.forM f)
  | [] => CV.pure trivial
  | a :: xs => by
    show CV K C _ (f a >>= fun _ => xs.forM f)
    exact CV.bind (h a) fun _ _ => CV.forM h xs

theorem CV.forIn {f : α → PUnit → W (ForInStep PUnit)} (h : ∀ a, CV K C (fun _ => True) (f a PUnit.unit)) :
    ∀ xs : List α, CV K C (fun _ => True) (forIn xs PUnit.unit f)
  | [] => by rw [List.forIn_nil]; exact CV.pure trivial
  | a :: xs => by
    rw [List.forIn_cons]
    refine CV.bind (h a) fun r _ => ?_
    cases r with
    | done b => exact CV.pure trivial
    | yield b => exact CV.forIn h xs

theorem CV.foldlM_mem {P : σ → Prop} {f : σ → α → W σ} :
    ∀ (xs : List α) (s : σ), (∀ s a, a ∈ xs → P s → CV K C P (f s a)) → P s → CV K C P (xs.foldlM f s)
  | [], s, _, hs => by rw [List.foldlM_nil]; exact CV.pure hs
  | a :: xs, s, h, hs => by
    rw [List.foldlM_cons]
    exact CV.bind (h s a List.mem_cons_self hs) fun s' hs' =>
      CV.foldlM_mem xs s' (fun s a ha => h s a (List.mem_cons_of_mem _ ha)) hs'

theorem CV.read {P : α → Prop} {k : ℕ → W α} (h : CV K C P (k K)) : CV K C P (read >>= k) :=
  fun acc x hx ha => h acc x hx ha

theorem CV.mustAs' (n : String) (b : Bool) : CV K C (fun _ => b = true) (P.Runs.mustAs n b) := by
  unfold P.Runs.mustAs
  cases b
  · exact CV.never fun _ => rfl
  · exact CV.pure rfl

/-! ### the readers -/

/-- Each table, from its first entry on, at its stored length, lies below nW. -/
def LenIn (i : P.Runs.In) (nW : ℕ) : Prop := ∀ t e, i.t.tabLen.lookup t = some e → t + e ≤ nW

variable {i : P.Runs.In}

local notation "CC" => Cov i.iU3 K nW

theorem cv_uEnt {x : ℕ} (hx : x < nW) : CV K CC CC (P.Runs.uEnt i.iU3 x) := by
  unfold P.Runs.uEnt
  exact CV.read (CV.bind (CV.mustAs _ _) fun _ _ => CV.pure (cov_ent hx))

theorem cv_u3at (hL : LenIn i nW) (t n : ℕ) : CV K CC CC (P.Runs.u3at i t n) := by
  unfold P.Runs.u3at
  refine CV.bind (CV.mustAs' _ _) fun _ hb => cv_uEnt ?_
  have hlt := of_decide_eq_true hb
  cases hl : i.t.tabLen.lookup t with
  | none => rw [hl] at hlt; simp at hlt
  | some e =>
    rw [hl] at hlt
    have := hL t e hl
    have hlt' : n < e := hlt
    omega

theorem cv_weighted (n : ℕ) (w : Array E) (f : ℕ → W Aff) (hf : ∀ k, CV K CC CC (f k)) :
    CV K CC CC (P.Runs.weighted n w f) := by
  unfold P.Runs.weighted
  exact CV.foldlM (fun s k hs => CV.bind (hf k) fun x hx => CV.pure (cov_addMul hs hx _)) _ _
    (cov_ofConst _)

theorem cv_plane (hL : LenIn i nW) (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    CV K CC CC (P.Runs.plane i t x lam a z isD) := by
  unfold P.Runs.plane
  exact cv_weighted _ _ _ fun _ => cv_u3at hL _ _

theorem cv_shV (hL : LenIn i nW) (t off nl J lam j : ℕ) : CV K CC CC (P.Runs.shV i t off nl J lam j) := by
  unfold P.Runs.shV
  exact cv_weighted _ _ _ fun _ => cv_u3at hL _ _

theorem cv_xl (hL : LenIn i nW) (t : ℕ) (X : P.Ten) (lam hd : ℕ) (zc : Array E) :
    CV K CC CC (P.Runs.xl i t X lam hd zc) := by
  unfold P.Runs.xl
  dsimp only
  cases P.cutLast (zc.extract 0 i.g.ldh) i.g.ls with
  | none => exact CV.never fun _ => rfl
  | some cut =>
    cases P.headFeat X hd i.g.dh with
    | none => exact CV.never fun _ => rfl
    | some j0 => exact cv_weighted _ _ _ fun _ => cv_weighted _ _ _ fun _ => cv_u3at hL _ _

theorem cv_overG (zg : Array E) (f : ℕ → W Aff) (hf : ∀ g, CV K CC CC (f g)) :
    CV K CC CC (P.Runs.overG i zg f) := by
  unfold P.Runs.overG
  exact cv_weighted _ _ _ hf

theorem cv_readDenominator (hL : LenIn i nW) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    CV K CC CC (P.Runs.readDenominator i t zg lam a) := by
  unfold P.Runs.readDenominator
  exact cv_overG _ _ fun _ => cv_shV hL _ _ _ _ _ _
theorem cv_readMaximum (hL : LenIn i nW) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    CV K CC CC (P.Runs.readMaximum i t zg lam a) := by
  unfold P.Runs.readMaximum
  exact cv_overG _ _ fun _ => cv_shV hL _ _ _ _ _ _
theorem cv_readIndexBit (hL : LenIn i nW) (t : ℕ) (zg : Array E) (lam a k : ℕ) :
    CV K CC CC (P.Runs.readIndexBit i t zg lam a k) := by
  unfold P.Runs.readIndexBit
  exact cv_overG _ _ fun _ => cv_shV hL _ _ _ _ _ _
theorem cv_readHead (hL : LenIn i nW) (t : ℕ) (X : P.Ten) (zg zc : Array E) (lam a : ℕ) :
    CV K CC CC (P.Runs.readHead i t X zg zc lam a) := by
  unfold P.Runs.readHead
  exact cv_overG _ _ fun _ => cv_xl hL _ _ _ _ _
theorem cv_readGroup (hL : LenIn i nW) (t : ℕ) (X : P.Ten) (zg zc : Array E) (lam : ℕ) :
    CV K CC CC (P.Runs.readGroup i t X zg zc lam) := by
  unfold P.Runs.readGroup
  exact cv_overG _ _ fun _ => cv_xl hL _ _ _ _ _

theorem cv_lessPieces {start : Aff} (hs : CC start) (pw : Array P.W1) (f : P.W1 → W Aff)
    (hf : ∀ w, CV K CC CC (f w)) : CV K CC CC (P.Runs.lessPieces start pw f) := by
  unfold P.Runs.lessPieces
  rw [← Array.foldlM_toList]
  exact CV.foldlM (fun s w hs => CV.bind (hf w) fun x hx => CV.pure (cov_addMul hs hx _)) _ _ hs

/-! ### the claims -/

/-- The rows that the sumchecks leave name no entry outside the part. -/
structure RowsCov (i : P.Runs.In) (K nW : ℕ) : Prop where
  units : ∀ k ∈ i.p.scores.toList, Cov i.iU3 K nW k.sc.row
  scE : Cov i.iU3 K nW i.p.d.scE.row
  vpm : Cov i.iU3 K nW i.p.d.vpm.row
  vpd : Cov i.iU3 K nW i.p.d.vpd.row
  scF : Cov i.iU3 K nW i.p.x.scF.row
  scd : Cov i.iU3 K nW i.p.x.scd.row
  scH : Cov i.iU3 K nW i.p.x.scH.row

local notation "TT" => fun _ => True

theorem cv_linPlanes (hL : LenIn i nW) (pc : P.RemP) : CV K CC TT (P.Runs.linPlanes i pc) := by
  unfold P.Runs.linPlanes
  exact CV.forM (fun x => CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_plane hL _ _ _ _ _ _)
    fun f hf => CV.lin hf) _

theorem cv_callKR (hL : LenIn i nW) (q : ℕ) : CV K CC TT (P.Runs.callKR i q) := by
  unfold P.Runs.callKR
  rw [← Array.foldlM_toList]
  exact CV.foldlM (fun v pc _ => CV.ite (CV.bind (cv_linPlanes hL pc) fun _ _ => CV.pure trivial)
    (CV.pure trivial)) _ _ trivial

theorem cv_claim3 (hL : LenIn i nW) (j : JoinsP) : CV K CC TT (P.Runs.claim3 i j) := by
  unfold P.Runs.claim3
  exact CV.foldlM (fun j x _ => CV.ite (CV.bind (cv_callKR hL x.2) fun _ _ => CV.pure trivial)
    (CV.pure trivial)) _ _ trivial

theorem cv_endValues (hL : LenIn i nW) (k : P.ScoreP) (tb : P.ScoreT) (rc : Array E) (b : ℕ) (w : P.W1) :
    CV K CC TT (P.Runs.endValues i k tb rc b w) := by
  unfold P.Runs.endValues
  exact CV.bind (cv_readHead hL _ _ _ _ _ _) fun q hq => CV.bind (CV.lin (cov_sub (cov_slot _) hq))
    fun _ _ => CV.bind (cv_readGroup hL _ _ _ _ _) fun kx hk => CV.lin (cov_sub (cov_slot _) hk)

theorem cv_unitKFD (hL : LenIn i nW) (n : ℕ) (k : P.ScoreP) (hr : CC k.sc.row) :
    CV K CC TT (P.Runs.unitKFD i n k) := by
  unfold P.Runs.unitKFD
  dsimp only
  refine CV.bind (CV.need _) fun tb _ => CV.bind (CV.need _) fun pc _ => CV.bind (cv_linPlanes hL pc)
    fun _ _ => CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readMaximum hL _ _ _ _) fun f hf =>
    CV.bind (CV.lin hf) fun _ _ => CV.bind (CV.lin (f := P.Runs.leftOf k.sc.row) hr) fun _ _ => ?_
  refine CV.forM (fun x => ?_) _
  exact cv_endValues hL k tb _ x.2 x.1

theorem cv_callKFD (hL : LenIn i nW) (hR : RowsCov i K nW) (q : ℕ) (c : P.CallG) :
    CV K CC TT (P.Runs.callKFD i q c) := by
  unfold P.Runs.callKFD
  refine CV.foldlM_mem _ _ (fun v x hx _ => CV.ite (CV.bind (cv_unitKFD hL x.2 x.1 (hR.units x.1 ?_))
    fun _ _ => CV.pure trivial) (CV.pure trivial)) trivial
  exact (List.mem_zipIdx hx).2.2 ▸ List.getElem_mem _

theorem cv_claim4 (hL : LenIn i nW) (hR : RowsCov i K nW) (j : JoinsP) :
    CV K CC TT (P.Runs.claim4 i j) := by
  unfold P.Runs.claim4
  exact CV.foldlM (fun j x _ => CV.ite (CV.bind (cv_callKFD hL hR x.2 x.1) fun _ _ => CV.pure trivial)
    (CV.pure trivial)) _ _ trivial

theorem cv_endValuesE (hL : LenIn i nW) (b : ℕ) (w : P.W1) : CV K CC TT (P.Runs.endValuesE i b w) := by
  unfold P.Runs.endValuesE
  dsimp only
  exact CV.bind (cv_readDenominator hL _ _ _ _) fun z hz => CV.bind (CV.lin (cov_sub (cov_slot _) hz))
    fun _ _ => CV.bind (cv_readHead hL _ _ _ _ _ _) fun o ho => CV.lin (cov_sub (cov_slot _) ho)

theorem cv_claim5 (hL : LenIn i nW) (hR : RowsCov i K nW) (j : JoinsP) :
    CV K CC TT (P.Runs.claim5 i j) := by
  unfold P.Runs.claim5
  dsimp only
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readDenominator hL _ _ _ _) fun zc hzc => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun rh hrh => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun rhp hrhp => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun r2 hr2 => ?_
  refine CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readHead hL _ _ _ _ _ _) fun r2p hr2p => ?_
  refine CV.bind (CV.lin hzc) fun _ _ => CV.bind (CV.lin hrh) fun _ _ => CV.bind (CV.lin hrhp) fun _ _ => ?_
  refine CV.bind (CV.forIn (fun k => ?_) _) fun _ _ => ?_
  · exact CV.bind (cv_lessPieces (cov_slot _) _ _ fun w => cv_readIndexBit hL _ _ _ _ _) fun f hf =>
      CV.bind (CV.lin hf) fun _ _ => CV.pure trivial
  refine CV.bind (CV.lin hr2) fun _ _ => CV.bind (CV.lin hr2p) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.d.scE.row) hR.scE) fun _ _ => ?_
  refine CV.bind (CV.forIn (fun b => ?_) _) fun _ _ => CV.pure trivial
  exact CV.bind (cv_endValuesE hL b _) fun _ _ => CV.pure trivial

theorem cv_valueProduct (hL : LenIn i nW) (sc : P.SumP) (hr : CC sc.row) (tS : ℕ) (pt : Array E)
    (isD : Bool) (tV : ℕ) : CV K CC TT (P.Runs.valueProduct i sc tS pt isD tV) := by
  unfold P.Runs.valueProduct
  refine CV.bind (CV.lin (f := P.Runs.leftOf sc.row) hr) fun _ _ =>
    CV.bind (CV.forIn (fun b => ?_) _) fun _ _ => CV.pure trivial
  dsimp only
  refine CV.bind (cv_plane hL _ _ _ _ _ _) fun p3 h3 => CV.bind (cv_plane hL _ _ _ _ _ _) fun p4 h4 => ?_
  refine CV.bind (CV.lin (cov_sub (cov_slot _) (cov_add (cov_add h3 (cov_ofConst _)) (cov_scale h4 _))))
    fun _ _ => CV.bind (cv_readGroup hL _ _ _ _ _) fun v hv => ?_
  exact CV.bind (CV.lin (cov_sub (cov_slot _) (cov_add (cov_ofConst _) hv))) fun _ _ => CV.pure trivial

theorem cv_claim6 (hL : LenIn i nW) (hR : RowsCov i K nW) : CV K CC TT (P.Runs.claim6 i) := by
  unfold P.Runs.claim6
  dsimp only
  exact CV.bind (CV.lin (cov_sub (cov_sub (cov_add (cov_slot _) (cov_slot _)) (cov_slot _))
    (cov_scale (cov_slot _) _))) fun _ _ => CV.bind (cv_valueProduct hL _ hR.vpm _ _ _ _) fun _ _ =>
    cv_valueProduct hL _ hR.vpd _ _ _ _

theorem cv_claim7 (hL : LenIn i nW) (hR : RowsCov i K nW) : CV K CC TT (P.Runs.claim7 i) := by
  unfold P.Runs.claim7
  dsimp only
  refine CV.bind (CV.forIn (fun b => ?_) _) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.x.scF.row) hR.scF) fun _ _ =>
    CV.bind (CV.forIn (fun b => ?_) _) fun _ _ =>
    CV.bind (CV.lin (f := P.Runs.leftOf i.p.x.scd.row) hR.scd) fun _ _ =>
    CV.bind (CV.forIn (fun lam => ?_) _) fun _ _ =>
    CV.bind (CV.forIn (fun b => ?_) _) fun _ _ => CV.pure trivial
  · exact CV.bind (cv_readMaximum hL _ _ _ _) fun m hm => CV.bind (CV.lin (cov_sub (cov_slot _) hm))
      fun _ _ => CV.pure trivial
  · exact CV.bind (cv_readHead hL _ _ _ _ _ _) fun q hq => CV.bind (CV.lin (cov_sub (cov_slot _) hq))
      fun _ _ => CV.pure trivial
  · exact CV.bind (cv_readGroup hL _ _ _ _ _) fun kx hk => CV.bind (CV.lin (cov_sub (cov_slot _) hk))
      fun _ _ => CV.pure trivial
  · refine CV.bind (CV.forIn (fun k => ?_) _) fun _ _ =>
      CV.bind (P := fun _ => True) (CV.pure trivial) fun _ _ => CV.pure trivial
    exact CV.bind (cv_readIndexBit hL _ _ _ _ _) fun bit hb => CV.bind (CV.lin (cov_sub (cov_slot _) hb))
      fun _ _ => CV.pure trivial

theorem cv_claim8 (hL : LenIn i nW) (hR : RowsCov i K nW) : CV K CC TT (P.Runs.claim8 i) := by
  unfold P.Runs.claim8
  dsimp only
  refine CV.bind (CV.lin (f := P.Runs.leftOf i.p.x.scH.row) hR.scH) fun _ _ =>
    CV.bind (CV.forIn (fun b => ?_) _) fun _ _ => CV.pure trivial
  refine CV.bind (CV.lin (cov_add (cov_sub (cov_slot _) (cov_slot _)) (cov_ofConst _))) fun _ _ => ?_
  refine CV.bind (P := Cov i.iU3 K nW) (CV.foldlM (fun s k hs => CV.bind (cv_readIndexBit hL _ _ _ _ _)
    fun bit hb => CV.pure (cov_addMul hs hb _)) _ _ (cov_slot _)) fun f hf => ?_
  exact CV.bind (CV.lin hf) fun _ _ => CV.pure trivial

/-- **Every entry of the array of tables that a form gathered by "first" or "second" names lies in the tables' part.** -/
theorem reads_covered_K05 {l₁ l₂ : List Aff} {j : JoinsP} (hL : LenIn i nW) (hR : RowsCov i K nW)
    (h1 : P.Runs.firstRun i K = some (l₁, j)) (h2 : P.Runs.secondRun i K = some l₂) :
    ∀ f ∈ l₁ ++ l₂, Cov i.iU3 K nW f := by
  unfold P.Runs.firstRun P.Runs.gather at h1
  unfold P.Runs.secondRun P.Runs.gather at h2
  simp only [Option.map_eq_some_iff] at h1 h2
  obtain ⟨_, ⟨y1, hy1, rfl⟩, e1⟩ := h1
  obtain ⟨_, ⟨y2, hy2, rfl⟩, e2⟩ := h2
  have c1 := (CV.bind (C := Cov i.iU3 K nW) (cv_claim3 hL _) fun j3 _ => CV.bind (cv_claim4 hL hR j3)
    fun j4 _ => cv_claim5 hL hR j4) #[] y1 hy1 (by simp)
  have c2 := (CV.bind (C := Cov i.iU3 K nW) (cv_claim6 hL hR) fun _ _ => CV.bind (cv_claim7 hL hR)
    fun _ _ => cv_claim8 hL hR) #[] y2 hy2 (by simp)
  have a1 : l₁ = y1.2.toList := (Prod.mk.inj e1).1.symm
  have a2 : l₂ = y2.2.toList := e2.symm
  intro f hf
  rcases List.mem_append.1 hf with h | h
  · exact c1.2 f (a1 ▸ h)
  · exact c2.2 f (a2 ▸ h)

/-! ### each table lies below the planned length: of tablesP's own output -/

open VerifiableInference.Desc.First.Att.P (Placed Fun1 Geo T TablesP LookIn Pts)

/-- Every stored pair (first entry, length) ends at or below the next free entry. -/
def Inv (s : Placed) : Prop := ∀ x ∈ s.tabLen, x.1 + x.2 ≤ s.next

def IvQ (r : T α) (Q : α → Placed → Prop) : Prop :=
  ∀ s a s', r s = some (a, s') → Inv s → Inv s' ∧ Q a s'

theorem IvQ.bind {r : T α} {k : α → T β} {Q0 : α → Placed → Prop} {Q : β → Placed → Prop}
    (h1 : IvQ r Q0) (h2 : ∀ a, IvQ (k a) Q) : IvQ (r >>= k) Q := by
  intro s b s' h hi
  obtain ⟨y, e1, e2⟩ := tbind_some h
  exact h2 y.1 y.2 b s' e2 (h1 s y.1 y.2 e1 hi).1

theorem IvQ.pure (a : α) : IvQ (Pure.pure a : T α) fun _ _ => True := by
  intro s b s' h hi
  have h' : some (a, s) = some (b, s') := h
  obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  exact ⟨hi, trivial⟩

theorem IvQ.lift (x : Option α) : IvQ (monadLift x : T α) fun _ _ => True := by
  intro s b s' h hi
  cases x with
  | none => cases h
  | some a =>
    have h' : some (a, s) = some (b, s') := h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨hi, trivial⟩

theorem IvQ.mono {r : T α} {Q Q' : α → Placed → Prop} (h : IvQ r Q) (f : ∀ a s, Q a s → Q' a s) : IvQ r Q' :=
  fun s a s' e hi => ⟨(h s a s' e hi).1, f a s' (h s a s' e hi).2⟩

local notation "T1" => fun _ _ => True

theorem iv_add (mats : Array (ℕ × ℕ)) (mat len : ℕ) (phi : Array E) (e : ℕ) :
    IvQ (P.add mats mat len phi e) T1 := by
  intro s a s' h hi
  obtain ⟨_, _, rfl⟩ := add_some h
  refine ⟨fun x hx => ?_, trivial⟩
  rcases List.mem_cons.1 hx with rfl | hx'
  · exact le_refl _
  · exact le_trans (hi x hx') (Nat.le_add_right _ _)

theorem iv_weights (n : ℕ) (f : Unit → Array E) : IvQ (P.T.weights n f) T1 := IvQ.pure _

theorem iv_getAs (n : String) (x : Option α) : IvQ (P.T.getAs n x) T1 := by
  cases x with
  | none => intro s a s' h; cases h
  | some v => exact IvQ.pure v

theorem iv_addRow (g : Geo) (mats : Array (ℕ × ℕ)) (psi : Unit → Array E) : IvQ (P.addRow g mats psi) T1 := by
  unfold P.addRow
  exact IvQ.bind (iv_weights _ _) fun _ => iv_add _ _ _ _ _

theorem iv_addLong (g : Geo) (mats : Array (ℕ × ℕ)) (mat : ℕ) (zc : Array E) (ptk : Unit → Array E)
    (e : ℕ) : IvQ (P.addLong g mats mat zc ptk e) T1 := by
  unfold P.addLong P.lng
  exact IvQ.bind (IvQ.bind (iv_weights _ _) fun _ => IvQ.bind (IvQ.lift _) fun _ =>
    IvQ.bind (iv_getAs _ _) fun _ => iv_weights _ _) fun _ => iv_add _ _ _ _ _

theorem iv_parts (mats : Array (ℕ × ℕ)) (len : ℕ) (phi : Array E) (w : ℕ) :
    ∀ (qs : List ℕ) (s s' : Placed) (u : PUnit),
      (qs.forM fun q => discard (P.add mats q len phi w)) s = some (u, s') → Inv s →
      Inv s' ∧ s.next ≤ s'.next
  | [], s, s', u, h, hi => by
    have h' : some (PUnit.unit, s) = some (u, s') := h
    obtain ⟨_, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨hi, le_refl _⟩
  | q0 :: qs, s, s', u, h, hi => by
    have h0 : ((discard (P.add mats q0 len phi w) : T PUnit) >>= fun _ =>
      qs.forM fun q => discard (P.add mats q len phi w)) s = some (u, s') := h
    obtain ⟨y, e1, e2⟩ := tbind_some h0
    obtain ⟨a, ea⟩ := discard_some (u := y.1) (s' := y.2) e1
    have i1 := (iv_add mats q0 len phi w s a y.2 ea hi).1
    obtain ⟨_, _, es⟩ := add_some ea
    obtain ⟨i2, n2⟩ := iv_parts mats len phi w qs y.2 s' u e2 i1
    refine ⟨i2, le_trans ?_ n2⟩
    rw [es]
    exact Nat.le_add_right _ _

theorem iv_addAs (g : Geo) (mats : Array (ℕ × ℕ)) (phi : Unit → Array E) : IvQ (P.addAs g mats phi) T1 := by
  intro s a s'' h hi
  unfold P.addAs P.T.weights P.T.placed P.T.total at h
  obtain ⟨y0, e0, h⟩ := tbind_some h
  have e0' : some (phi (), s) = some y0 := e0
  obtain rfl := Option.some.inj e0'
  obtain ⟨y1, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y1 := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  obtain ⟨i2, n2⟩ := iv_parts mats _ _ _ _ s y2.2 y2.1 e2 hi
  obtain ⟨y3, e3, h⟩ := tbind_some h
  have e3' : some (PUnit.unit, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some y3 := e3
  obtain rfl := Option.some.inj e3'
  have h' : some (s.next, Placed.mk y2.2.next ((s.next, y2.2.next - s.next) :: y2.2.tabLen) y2.2.funs) =
      some (a, s'') := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  refine ⟨fun x hx => ?_, trivial⟩
  rcases List.mem_cons.1 hx with rfl | hx'
  · show s.next + (y2.2.next - s.next) ≤ y2.2.next
    omega
  · exact i2 x hx'

theorem iv_mapML {ι : Type} (f : ι → T α) (hf : ∀ x, IvQ (f x) T1) : ∀ xs : List ι, IvQ (xs.mapM f) T1
  | [] => by rw [List.mapM_nil]; exact IvQ.pure _
  | x :: xs => by
    rw [List.mapM_cons]
    exact IvQ.bind (hf x) fun _ => IvQ.bind (iv_mapML f hf xs) fun _ => IvQ.pure _

theorem iv_mapM {ι : Type} (f : ι → T α) (hf : ∀ x, IvQ (f x) T1) (xs : Array ι) : IvQ (xs.mapM f) T1 := by
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  exact IvQ.bind (iv_mapML f hf xs.toList) fun _ => IvQ.pure _

theorem iv_tail (nW : ℕ) (n : String) (F : Placed → TablesP) :
    IvQ (P.T.placed >>= fun t => (monadLift (P.mustAs n (t.next == nW)) : T PUnit) >>= fun _ =>
      Pure.pure (F t)) fun r s => r = F s ∧ s.next = nW := by
  intro s r s' h hi
  obtain ⟨y, e1, h⟩ := tbind_some h
  have e1' : some (s, s) = some y := e1
  obtain rfl := Option.some.inj e1'
  obtain ⟨y2, e2, h⟩ := tbind_some h
  cases hb : (s.next == nW) with
  | false =>
    have e2' : (none : Option (PUnit × Placed)) = some y2 := by
      have : (monadLift (P.mustAs n (s.next == nW)) : T PUnit) s = none := by rw [hb]; rfl
      rw [← this]; exact e2
    cases e2'
  | true =>
    have e2' : some (PUnit.unit, s) = some y2 := by
      have : (monadLift (P.mustAs n (s.next == nW)) : T PUnit) s = some (PUnit.unit, s) := by rw [hb]; rfl
      rw [← this]; exact e2
    obtain rfl := Option.some.inj e2'
    have h' : some (F s, s) = some (r, s') := h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
    exact ⟨hi, rfl, by simpa using hb⟩

theorem iv_placeAll (g : Geo) (mats : Array (ℕ × ℕ)) (nW : ℕ) (lk : LookIn) (p : Pts) :
    IvQ (P.placeAll g mats nW lk p) fun t s => t.tabLen = s.tabLen ∧ s.next = nW := by
  unfold P.placeAll
  exact (IvQ.bind (IvQ.lift _) fun _ =>
    IvQ.bind (iv_addAs g mats _) fun tA => IvQ.bind (iv_addAs g mats _) fun tVM =>
    IvQ.bind (iv_addAs g mats _) fun tVD =>
    IvQ.bind (iv_mapM _ (fun k => iv_addRow g mats _) p.scores) fun tM =>
    IvQ.bind (iv_addRow g mats _) fun hW => IvQ.bind (iv_addRow g mats _) fun hX =>
    IvQ.bind (iv_addRow g mats _) fun hE => IvQ.bind (iv_addRow g mats _) fun hT =>
    IvQ.bind (iv_addRow g mats _) fun hPi => IvQ.bind (iv_addRow g mats _) fun hR2 =>
    IvQ.bind (IvQ.lift _) fun _ => IvQ.bind (iv_addLong g mats _ _ _ _) fun tO =>
    IvQ.bind (iv_mapM _ (fun k => IvQ.bind (iv_addLong g mats _ _ _ _) fun tQ =>
      IvQ.bind (iv_addLong g mats _ _ _ _) fun tK => IvQ.pure (tQ, tK)) p.scores) fun tQK =>
    IvQ.bind (iv_addLong g mats _ _ _ _) fun qO => IvQ.bind (iv_addLong g mats _ _ _ _) fun qVM =>
    IvQ.bind (iv_addLong g mats _ _ _ _) fun qVD => IvQ.bind (iv_addLong g mats _ _ _ _) fun qF =>
    IvQ.bind (iv_addLong g mats _ _ _ _) fun qKx => IvQ.bind (IvQ.lift _) fun _ =>
    IvQ.bind (iv_weights _ _) fun phiB0 => IvQ.bind (iv_add mats _ _ phiB0 _) fun tBit0 =>
    IvQ.bind (iv_weights _ _) fun phiB1 => IvQ.bind (iv_add mats _ _ phiB1 _) fun tBit1 =>
    IvQ.bind (iv_weights _ _) fun phiP => IvQ.bind (iv_add mats _ _ phiP _) fun tPin =>
    (iv_tail nW _ _).mono (by rintro t s ⟨rfl, en⟩; exact ⟨rfl, en⟩))

theorem lookup_mem {γ : Type} : ∀ {l : List (ℕ × γ)} {a : ℕ} {e : γ}, l.lookup a = some e → (a, e) ∈ l
  | (b, c) :: l, a, e, h => by
    rw [List.lookup_cons] at h
    cases hb : (a == b) with
    | true =>
      rw [hb] at h
      have : a = b := by simpa using hb
      subst this
      rw [Option.some.inj h]
      exact List.mem_cons_self
    | false =>
      rw [hb] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- **Of what tablesP itself makes: each table lies below the planned length nW.** -/
theorem len_in {nW' : ℕ} {mats : Array (ℕ × ℕ)} {lk : LookIn}
    (ht : P.tablesP i.g mats nW' lk i.p = some i.t) : LenIn i nW' := by
  unfold P.tablesP at ht
  have h' : (P.placeAll i.g mats nW' lk i.p {}).bind (fun y => some y.1) = some i.t := ht
  cases hr : P.placeAll i.g mats nW' lk i.p {} with
  | none => rw [hr] at h'; cases h'
  | some y =>
    rw [hr] at h'
    have e : y.1 = i.t := Option.some.inj h'
    obtain ⟨iv, et, en⟩ := iv_placeAll i.g mats nW' lk i.p {} y.1 y.2 hr (by intro x hx; cases hx)
    intro t e' hl
    rw [← e, et] at hl
    have := iv _ (lookup_mem hl)
    rw [en] at this
    exact this

end K5Law
