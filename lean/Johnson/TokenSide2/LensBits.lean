-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TokenSide2/LensBits.lean: THE FREE BITS WITHIN A WINDOW AS COINS WITH COORDINATES: members
of LeafLens (Johnson/TokenSide/TieTree.lean) and of RunLens (Johnson/TokenSide/Lens.lean) at the
very types of which the laws on the honest side's coins speak (SaltsLaw, RunLaw,
Johnson/WholeKey/CoinLaws.lean). Definitions whose fields are proved, and lemmas.

General definitions and lemmas. This file states no goal of the release.

  tabLens m ℓ     the free bits of a table's m salts (a tuple of m strings of ℓ bits, uniform). The
                  table's salts stand at the coordinates (0, false, 0, j), j < m.
  runLens ln nR nK nJ fill   the free bits of a compiled run's coins within the window (RunBits,
                  uniform). Outside the window a leaf's coordinate reads as the fixed string fill.
  ofWin           the coins that a compiled run is handed, as a function of the window alone.
  dress_eq_ofWin  the scheme's own dressing (dress, Johnson/WholeKey/Defs.lean) is that function.
  coRun_runLens   the coins that the tie on a compiled run reads off runLens are that function too.
  covers_inWin    a window that is wide enough for a wire holds all that a run reads.

The uniform laws are written with the list of the type's members as a letter (fu): Lean may find
more than one such list at a concrete type, and to compare two of them is costly.

-/
import Johnson.TokenSide.SpecSame
import Johnson.CoinsTie.Run

set_option autoImplicit false

noncomputable section

namespace OnBytes.TokenSide
open _root_.Compile hiding ON
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.CoinsTie

/-! ## At letters -/

section Letters
variable {A B C D Y Kk : Type}

/-- One entry of a uniform tuple. -/
theorem res_entry [Fintype Kk] [DecidableEq Kk] {fy : Fintype Y} [Nonempty Y]
    {fu : Fintype (Kk → Y)} (k₀ : Kk) :
    Resamples (@unif (Kk → Y) fu _) (@unif Y fy _) (fun x u => Function.update u k₀ x) :=
  Resamples.inst ((Resamples.self (@unif Y fy _)).pi (C := fun _ : Kk => Y) k₀)

/-- A coordinate of the fourth component of a uniform quadruple. -/
theorem res_fourth_at [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] [Fintype C] [Nonempty C]
    [Fintype D] [Nonempty D] {ν : PMF Y} {upd : Y → D → D} (h : Resamples (unif D) ν upd) :
    Resamples (unif (A × B × C × D)) ν (fun x u => (u.1, u.2.1, u.2.2.1, upd x u.2.2.2)) := by
  have h1 := h.snd (unif C)
  rw [← unif_prod] at h1
  have h2 := h1.snd (unif B)
  rw [← unif_prod] at h2
  have h3 := h2.snd (unif A)
  rw [← unif_prod] at h3
  exact h3

end Letters

/-! ## A table's salts -/

/-- where a table's salts stand among the coordinates -/
def InTab (m : ℕ) (i : ℕ) (b : Bool) (k j : ℕ) : Prop := i = 0 ∧ b = false ∧ k = 0 ∧ j < m

instance (m i : ℕ) (b : Bool) (k j : ℕ) : Decidable (InTab m i b k j) := by
  unfold InTab
  infer_instance

/-- **The free bits of a table's salts, as coins with coordinates.** -/
def tabLens (m ℓ : ℕ) {fu : Fintype (Fin m → Fin ℓ → Bool)} :
    LeafLens (Fin m → Fin ℓ → Bool) (@unif _ fu _) ℓ (InTab m) where
  get := fun ω i b k j => if h : InTab m i b k j then List.ofFn (ω ⟨j, h.2.2.2⟩) else []
  upd := fun i b k j u ω => if h : InTab m i b k j then Function.update ω ⟨j, h.2.2.2⟩ u else ω
  get_same := fun i b k j u ω h => by
    simp only [dif_pos h, Function.update_self]
  get_ne := fun i b k j u ω i' b' k' j' hne => by
    by_cases h : InTab m i b k j
    · by_cases h' : InTab m i' b' k' j'
      · simp only [dif_pos h, dif_pos h']
        rw [Function.update_of_ne fun e => hne ⟨h'.1.trans h.1.symm, h'.2.1.trans h.2.1.symm,
          h'.2.2.1.trans h.2.2.1.symm, congrArg Fin.val e⟩]
      · simp only [dif_neg h']
    · simp only [dif_neg h]
  law := fun i b k j h => by
    refine (res_entry (Kk := Fin m) (Y := Fin ℓ → Bool) ⟨j, h.2.2.2⟩).congr fun u ω => ?_
    simp only [dif_pos h]

theorem tabLens_get {m ℓ : ℕ} {fu : Fintype (Fin m → Fin ℓ → Bool)} (ω : Fin m → Fin ℓ → Bool)
    {j : ℕ} (hj : j < m) : (tabLens m ℓ (fu := fu)).get ω 0 false 0 j = List.ofFn (ω ⟨j, hj⟩) :=
  dif_pos (⟨rfl, rfl, rfl, hj⟩ : InTab m 0 false 0 j)

/-! ## The coins of a compiled run -/

variable {I X : Type} {lam : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- the coordinates within the window -/
def InWin (nR nK nJ dq : ℕ) : RunCo → Prop
  | .salt => True
  | .rs => True
  | .path n => n < dq
  | .leaf i _ k j => i < nR ∧ k < nK ∧ j < nJ

section RunLens
variable (ln : RunLen lam L) (nR nK nJ : ℕ) (fill : Bits)

/-- reading a coordinate -/
def getBits (u : RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq) : RunCo → Bits
  | .salt => List.ofFn u.1
  | .rs => List.ofFn u.2.2.1
  | .path n => if h : n < ln.dq then List.ofFn (u.2.2.2 ⟨n, h⟩) else []
  | .leaf i b k j =>
      if h : i < nR ∧ k < nK ∧ j < nJ then List.ofFn (u.2.1 ⟨i, h.1⟩ b ⟨k, h.2.1⟩ ⟨j, h.2.2⟩)
      else fill

/-- writing a coordinate -/
def updBits : (c : RunCo) → (Fin (lenRun ln c) → Bool) →
    RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq → RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq
  | .salt, x, u => setSalt x u
  | .rs, x, u => setRsalt x u
  | .path n, x, u =>
      if h : n < ln.dq then (u.1, u.2.1, u.2.2.1, Function.update u.2.2.2 ⟨n, h⟩ x) else u
  | .leaf i b k j, x, u =>
      if h : i < nR ∧ k < nK ∧ j < nJ then setLeaf ⟨i, h.1⟩ b ⟨k, h.2.1⟩ ⟨j, h.2.2⟩ x u else u

theorem getBits_same (c : RunCo) (x : Fin (lenRun ln c) → Bool)
    (u : RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq) (h : InWin nR nK nJ ln.dq c) :
    getBits ln nR nK nJ fill (updBits ln nR nK nJ c x u) c = List.ofFn x := by
  cases c with
  | salt => rfl
  | rs => rfl
  | path n =>
      have h' : n < ln.dq := h
      simp only [getBits, updBits, dif_pos h', Function.update_self]
      rfl
  | leaf i b k j =>
      have h' : i < nR ∧ k < nK ∧ j < nJ := h
      simp only [getBits, updBits, dif_pos h', leaf_setLeaf]
      rfl

theorem getBits_ne (c : RunCo) (x : Fin (lenRun ln c) → Bool)
    (u : RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq) (c' : RunCo) (hne : c' ≠ c) :
    getBits ln nR nK nJ fill (updBits ln nR nK nJ c x u) c' = getBits ln nR nK nJ fill u c' := by
  cases c with
  | salt =>
      cases c' with
      | salt => exact absurd rfl hne
      | rs => rfl
      | path n => rfl
      | leaf i b k j => rfl
  | rs =>
      cases c' with
      | salt => rfl
      | rs => exact absurd rfl hne
      | path n => rfl
      | leaf i b k j => rfl
  | path n =>
      by_cases h : n < ln.dq
      · cases c' with
        | salt => simp only [getBits, updBits, dif_pos h]
        | rs => simp only [getBits, updBits, dif_pos h]
        | path n' =>
            by_cases h' : n' < ln.dq
            · simp only [getBits, updBits, dif_pos h, dif_pos h']
              rw [Function.update_of_ne fun e => hne (congrArg RunCo.path (congrArg Fin.val e))]
            · simp only [getBits, dif_neg h']
        | leaf i b k j => simp only [getBits, updBits, dif_pos h]
      · simp only [updBits, dif_neg h]
  | leaf i b k j =>
      by_cases h : i < nR ∧ k < nK ∧ j < nJ
      · cases c' with
        | salt => simp only [getBits, updBits, dif_pos h, setLeaf]
        | rs => simp only [getBits, updBits, dif_pos h, setLeaf]
        | path n => simp only [getBits, updBits, dif_pos h, setLeaf]
        | leaf i' b' k' j' =>
            by_cases h' : i' < nR ∧ k' < nK ∧ j' < nJ
            · simp only [getBits, updBits, dif_pos h, dif_pos h']
              rw [leaf_setLeaf_ne fun e => hne (by
                have e1 := congrArg (fun z => z.1.val) e
                have e2 := congrArg (fun z => z.2.1) e
                have e3 := congrArg (fun z => z.2.2.1.val) e
                have e4 := congrArg (fun z => z.2.2.2.val) e
                simp only at e1 e2 e3 e4
                rw [e1, e2, e3, e4])]
            · simp only [getBits, dif_neg h']
      · simp only [updBits, dif_neg h]

/-- **The free bits of a compiled run's coins within a window, as coins with coordinates.** -/
def runLens {fu : Fintype (RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq)} :
    RunLens (RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq) (@unif _ fu _) ln
      (InWin nR nK nJ ln.dq) where
  get := getBits ln nR nK nJ fill
  upd := updBits ln nR nK nJ
  get_same := fun c x u h => getBits_same ln nR nK nJ fill c x u h
  get_ne := fun c x u c' h => getBits_ne ln nR nK nJ fill c x u c' h
  law := fun c h => by
    cases c with
    | salt => exact resamples_salt
    | rs => exact resamples_rsalt
    | path n =>
        have h' : n < ln.dq := h
        refine (Resamples.inst (res_fourth_at (res_entry (Kk := Fin ln.dq) (Y := Dig lam)
          ⟨n, h'⟩))).congr fun x u => ?_
        simp only [updBits, dif_pos h']
    | leaf i b k j =>
        have h' : i < nR ∧ k < nK ∧ j < nJ := h
        refine (resamples_leaf ⟨i, h'.1⟩ b ⟨k, h'.2.1⟩ ⟨j, h'.2.2⟩).congr fun x u => ?_
        simp only [updBits, dif_pos h']

end RunLens

/-! ## The coins that a run is handed, as a function of the window -/

/-- The coins that a compiled run is handed, out of the window of the coins that are drawn. -/
def ofWin (pad : Body L) (slot : ℕ) (start : ℕ → Bool → Bits → Bits) (rsw : Bits) (nR nK nJ : ℕ)
    (fill : Bits) (w : Bits × (Fin nR → Bool → Fin nK → Fin nJ → Bits) × Bits × List (Dig lam)) :
    Coins lam L :=
  ⟨w.1, fun i b k j => start i b w.1 ++
      if h : i < nR ∧ k < nK ∧ j < nJ then w.2.1 ⟨i, h.1⟩ b ⟨k, h.2.1⟩ ⟨j, h.2.2⟩ else fill,
    pad, slot, w.2.2.2, w.2.2.1 ++ rsw⟩

/-- The scheme's dressing reads the drawn coins within the window alone. -/
theorem dress_eq_ofWin (start : ℕ → Bool → Bits → Bits) (rtail : ℕ → Bits) (nR nK nJ : ℕ)
    (fill : Bits) (co : Coins lam L) {pad : Body L} {slot : ℕ} (hp : co.pad = pad)
    (hs : co.slot = slot) :
    dress start rtail nR nK nJ fill co =
      ofWin pad slot start (rtail slot) nR nK nJ fill (windowOf nR nK nJ co) := by
  subst hp
  subst hs
  unfold dress ofWin windowOf
  congr 1

theorem path_ofFn {dq : ℕ} (f : Fin dq → Dig lam) :
    ((List.range dq).map fun n => digOf lam (if h : n < dq then List.ofFn (f ⟨n, h⟩) else [])) =
      List.ofFn f := by
  refine List.ext_getElem (by simp) fun n h1 h2 => ?_
  have hn : n < dq := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn, dif_pos hn, digOf_ofFn]

/-- The coins that the tie on a compiled run reads off runLens. -/
theorem coRun_runLens (ln : RunLen lam L) (nR nK nJ : ℕ) (fill : Bits)
    {fu : Fintype (RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq)}
    (pre : ℕ → Bool → Bits → Bits) (u : RunBits lam nR nK nJ ln.sFS ln.fr ln.rs ln.dq) :
    coRun (runLens ln nR nK nJ fill (fu := fu)) pre u =
      ofWin ln.pad ln.slot pre ln.rsw nR nK nJ fill (windowBits u) := by
  unfold coRun ofWin windowBits
  congr 1
  exact path_ofFn u.2.2.2

/-! ## A window that is wide enough -/

theorem covers_inWin {K : ℕ} (nR nK nJ dq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ), FitsWin nR nK nJ s A W i →
      Covers (fun i b k j => InWin nR nK nJ dq (.leaf i b k j)) s A W i
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (w, W), i, h =>
    ⟨fun n d hn j hj => ⟨h.1,
        (by
          have h0 := (List.getElem?_eq_some_iff.mp hn).1
          have h1 := h.2.1
          omega),
        Nat.lt_of_lt_of_le hj (h.2.2.2.1 d (List.mem_of_getElem? hn))⟩,
      fun n d hn j hj => ⟨h.1,
        (by
          have h0 := (List.getElem?_eq_some_iff.mp hn).1
          have h1 := h.2.2.1
          omega),
        Nat.lt_of_lt_of_le hj (h.2.2.2.2.1 d (List.mem_of_getElem? hn))⟩,
      covers_inWin nR nK nJ dq s A W (i + 1) h.2.2.2.2.2⟩

/-- The window holds all that a run reads. -/
theorem coversRun_inWin {K : ℕ} (ln : RunLen lam L) (nR nK nJ : ℕ) (s : Shape) (A : RoundSplits s)
    (W : RoundsQueryLayout lam K s A) (h : FitsWin nR nK nJ s A W 0) :
    CoversRun (InWin nR nK nJ ln.dq) ln s A W :=
  ⟨trivial, trivial, fun _ hn => hn, covers_inWin nR nK nJ ln.dq s A W 0 h⟩

end OnBytes.TokenSide

#print axioms OnBytes.TokenSide.coRun_runLens
#print axioms OnBytes.TokenSide.dress_eq_ofWin
#print axioms OnBytes.TokenSide.coversRun_inWin
