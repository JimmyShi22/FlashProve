-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/CoinsTie/Run.lean: FROM THE LAWS ON THE HONEST SIDE's COINS (Johnson/WholeKey/CoinLaws.lean)
TO "each coin when it is needed" (Rom/Handle/Coins.lean).

General lemmas. This file states no goal of the release.

The laws say: of the coins that one draw from a list gives, the part within a window is distributed
as public strings with free bits that are uniform and independent. The calculus of
Rom/Handle/Coins.lean wants two things of coins: a law μ, and for each coordinate that a program
draws late the fact that it is independent of the rest (Resamples). This file gives both.

  setSalt, setLeaf, setRsalt, setPath      lay new free bits (or sibling digests) into the free bits
                                           of a compiled run's coins: the first salt; one leaf's
                                           salt; the string behind the slot's value; the digests.
  resamples_salt, _leaf, _rsalt, _path     each of these is uniform and independent of the rest.
  leaf_setLeaf, leaf_setLeaf_ne            what is read after setLeaf: the new bits at that leaf,
                                           the old ones at every other.
  coinsFirst_of_runLaw     a program that reads its coins within the window alone, behind one draw
                           from a list with the law RunLaw, may be compared at the free bits.
  coinsFirst_of_saltsLaw   the same for a table's salts and SaltsLaw. There a coordinate is an entry
                           of a uniform tuple: (Resamples.self _).pi j.
  toy_salt                 a small example of the whole way: the program that returns its first salt
                           is one draw of sFS bits.

Limits. That a program reads its coins within a window alone is a premise here (hloc). Where these
lemmas are called for the scheme, it holds by the scheme's text: the coins are cut to the window
before they are handed on (dress_eq_ofWin, Johnson/TokenSide2/LensBits.lean).

-/
import Johnson.WholeKey.CoinLaws
import Compile.DeferRun.Coins

set_option autoImplicit false

noncomputable section

namespace OnBytes.CoinsTie
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom Prob
open OnBytes.Prover OnBytes.WholeKey
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {lam nR nK nJ sFS ℓ ℓr dq : ℕ}

/-! ## The coordinates of a compiled run's free bits -/

/-- New bits for the first salt. -/
def setSalt (x : Fin sFS → Bool) (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) :
    RunBits lam nR nK nJ sFS ℓ ℓr dq := (x, u.2)

/-- New free bits for the salt of one leaf: round i, component b, tree k, leaf j. -/
def setLeaf (i : Fin nR) (b : Bool) (k : Fin nK) (j : Fin nJ) (x : Fin ℓ → Bool)
    (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) : RunBits lam nR nK nJ sFS ℓ ℓr dq :=
  (u.1, Function.update u.2.1 i (Function.update (u.2.1 i) b (Function.update (u.2.1 i b) k
    (Function.update (u.2.1 i b k) j x))), u.2.2)

/-- New free bits for the string behind the slot's value. -/
def setRsalt (x : Fin ℓr → Bool) (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) :
    RunBits lam nR nK nJ sFS ℓ ℓr dq := (u.1, u.2.1, x, u.2.2.2)

/-- New sibling digests. -/
def setPath (x : Fin dq → Dig lam) (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) :
    RunBits lam nR nK nJ sFS ℓ ℓr dq := (u.1, u.2.1, u.2.2.1, x)

/-! At letters first: at the concrete types Lean finds more than one list of a type's members, and
to compare two of them is costly. -/

section Letters
variable {A B C D Y K₁ K₂ K₃ K₄ : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
  [Fintype C] [Nonempty C] [Fintype D] [Nonempty D] [Fintype Y] [Nonempty Y]
  [Fintype K₁] [DecidableEq K₁] [Fintype K₂] [DecidableEq K₂] [Fintype K₃] [DecidableEq K₃]
  [Fintype K₄] [DecidableEq K₄]

theorem res_first : Resamples (unif (A × B × C × D)) (unif A) (fun x u => (x, u.2)) := by
  have h := (Resamples.self (unif A)).fst (unif (B × C × D))
  rw [← unif_prod] at h
  exact h

omit [Fintype Y] [Nonempty Y] in
theorem res_second {ν : PMF Y} {upd : Y → B → B} (h : Resamples (unif B) ν upd) :
    Resamples (unif (A × B × C × D)) ν (fun x u => (u.1, upd x u.2.1, u.2.2)) := by
  have h5 := h.fst (unif (C × D))
  rw [← unif_prod] at h5
  have h6 := h5.snd (unif A)
  rw [← unif_prod] at h6
  exact h6

theorem res_third :
    Resamples (unif (A × B × C × D)) (unif C) (fun x u => (u.1, u.2.1, x, u.2.2.2)) := by
  have h1 := (Resamples.self (unif C)).fst (unif D)
  rw [← unif_prod] at h1
  have h2 := h1.snd (unif B)
  rw [← unif_prod] at h2
  have h3 := h2.snd (unif A)
  rw [← unif_prod] at h3
  exact h3

theorem res_fourth :
    Resamples (unif (A × B × C × D)) (unif D) (fun x u => (u.1, u.2.1, u.2.2.1, x)) := by
  have h1 := (Resamples.self (unif D)).snd (unif C)
  rw [← unif_prod] at h1
  have h2 := h1.snd (unif B)
  rw [← unif_prod] at h2
  have h3 := h2.snd (unif A)
  rw [← unif_prod] at h3
  exact h3

theorem res_nest (i : K₁) (b : K₂) (k : K₃) (j : K₄) :
    Resamples (unif (K₁ → K₂ → K₃ → K₄ → Y)) (unif Y) (fun x u =>
      Function.update u i (Function.update (u i) b (Function.update (u i b) k
        (Function.update (u i b k) j x)))) := by
  have h1 := (Resamples.self (unif Y)).pi (C := fun _ : K₄ => Y) j
  have h2 := h1.pi (C := fun _ : K₃ => K₄ → Y) k
  have h3 := h2.pi (C := fun _ : K₂ => K₃ → K₄ → Y) b
  exact h3.pi (C := fun _ : K₁ => K₂ → K₃ → K₄ → Y) i

end Letters

/-! At the free bits of a compiled run. The lists of the types' members are letters (fu, fy), so
that these lemmas fit whichever lists Lean has found where they are used. -/

theorem resamples_salt {fu : Fintype (RunBits lam nR nK nJ sFS ℓ ℓr dq)}
    {fy : Fintype (Fin sFS → Bool)} :
    Resamples (@unif (RunBits lam nR nK nJ sFS ℓ ℓr dq) fu _) (@unif (Fin sFS → Bool) fy _)
      setSalt :=
  Resamples.inst res_first

theorem resamples_leaf {fu : Fintype (RunBits lam nR nK nJ sFS ℓ ℓr dq)}
    {fy : Fintype (Fin ℓ → Bool)} (i : Fin nR) (b : Bool) (k : Fin nK) (j : Fin nJ) :
    Resamples (@unif (RunBits lam nR nK nJ sFS ℓ ℓr dq) fu _) (@unif (Fin ℓ → Bool) fy _)
      (setLeaf i b k j) :=
  Resamples.inst (res_second (Resamples.inst (res_nest i b k j)))

theorem resamples_rsalt {fu : Fintype (RunBits lam nR nK nJ sFS ℓ ℓr dq)}
    {fy : Fintype (Fin ℓr → Bool)} :
    Resamples (@unif (RunBits lam nR nK nJ sFS ℓ ℓr dq) fu _) (@unif (Fin ℓr → Bool) fy _)
      setRsalt :=
  Resamples.inst res_third

theorem resamples_path {fu : Fintype (RunBits lam nR nK nJ sFS ℓ ℓr dq)}
    {fy : Fintype (Fin dq → Dig lam)} :
    Resamples (@unif (RunBits lam nR nK nJ sFS ℓ ℓr dq) fu _) (@unif (Fin dq → Dig lam) fy _)
      setPath :=
  Resamples.inst res_fourth

/-- After setLeaf that leaf has the new bits. -/
theorem leaf_setLeaf (i : Fin nR) (b : Bool) (k : Fin nK) (j : Fin nJ) (x : Fin ℓ → Bool)
    (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) : (setLeaf i b k j x u).2.1 i b k j = x := by
  simp only [setLeaf, Function.update_self]

/-- After setLeaf every other leaf has its old bits. -/
theorem leaf_setLeaf_ne {i i' : Fin nR} {b b' : Bool} {k k' : Fin nK} {j j' : Fin nJ}
    (h : (i', b', k', j') ≠ (i, b, k, j)) (x : Fin ℓ → Bool)
    (u : RunBits lam nR nK nJ sFS ℓ ℓr dq) :
    (setLeaf i b k j x u).2.1 i' b' k' j' = u.2.1 i' b' k' j' := by
  by_cases hi : i' = i
  · subst hi
    by_cases hb : b' = b
    · subst hb
      by_cases hk : k' = k
      · subst hk
        have hj : j' ≠ j := fun e => h (by rw [e])
        simp only [setLeaf, Function.update_self, Function.update_of_ne hj]
      · simp only [setLeaf, Function.update_self, Function.update_of_ne hk]
    · simp only [setLeaf, Function.update_self, Function.update_of_ne hb]
  · simp only [setLeaf, Function.update_of_ne hi]

/-! ## From the laws to the calculus -/

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {S : OSpec} {α : Type}

/-- A program that reads its coins within the window alone (and the fixed padding and slot), behind
one draw from a list with the law RunLaw: it is enough to compare it at the free bits. -/
theorem coinsFirst_of_runLaw {e : Enum (Coins lam L)} {pad : Body L} {slot : ℕ}
    (hl : RunLaw e nR nK nJ sFS ℓ ℓr dq pad slot) {prog : Coins lam L → OComp S α}
    {prog' : Bits × (Fin nR → Bool → Fin nK → Fin nJ → Bits) × Bits × List (Dig lam) → OComp S α}
    (hloc : ∀ co : Coins lam L, co.pad = pad → co.slot = slot →
      prog co = prog' (windowOf nR nK nJ co))
    {t : OComp S α}
    (h : CoinsFirst (unif (RunBits lam nR nK nJ sFS ℓ ℓr dq)) (fun u => prog' (windowBits u)) t) :
    CoinsFirst ((unif (Fin (e.n + 1))).map e.e) prog t := by
  refine CoinsFirst.map ?_
  have e1 : (fun a => prog (e.e a)) = fun a => prog' (windowOf nR nK nJ (e.e a)) :=
    funext fun a => hloc _ (hl.pad a) (hl.slot a)
  rw [e1]
  exact CoinsFirst.of_window (fun a => windowOf nR nK nJ (e.e a)) windowBits hl.law
    (CoinsFirst.inst h)

/-- The same for a table's salts. -/
theorem coinsFirst_of_saltsLaw {sl : Enum (ℕ → Bits)} {m : ℕ} {pre : Bits}
    (hl : SaltsLaw sl m pre ℓ) {prog : (ℕ → Bits) → OComp S α}
    {prog' : (Fin m → Bits) → OComp S α}
    (hloc : ∀ s : ℕ → Bits, prog s = prog' fun j => s j.val) {t : OComp S α}
    (h : CoinsFirst (unif (Fin m → Fin ℓ → Bool))
      (fun u => prog' fun j => pre ++ List.ofFn (u j)) t) :
    CoinsFirst ((unif (Fin (sl.n + 1))).map sl.e) prog t := by
  refine CoinsFirst.map ?_
  have e1 : (fun a => prog (sl.e a)) = fun a => prog' fun j => sl.e a j.val :=
    funext fun a => hloc _
  rw [e1]
  exact CoinsFirst.of_window (fun a => fun j : Fin m => sl.e a j.val)
    (fun (u : Fin m → Fin ℓ → Bool) => fun j => pre ++ List.ofFn (u j)) hl (CoinsFirst.inst h)

/-- A small example of the whole way: behind a draw with the law RunLaw, the program that returns
its first salt is one draw of sFS bits. -/
theorem toy_salt {e : Enum (Coins lam L)} {pad : Body L} {slot : ℕ}
    (hl : RunLaw e nR nK nJ sFS ℓ ℓr dq pad slot) :
    CoinsFirst (S := S) ((unif (Fin (e.n + 1))).map e.e) (fun co => .pure co.salt)
      (.sample (2 ^ sFS - 1) fun r => .pure (List.ofFn fun i : Fin sFS => r.val.testBit i)) := by
  refine coinsFirst_of_runLaw hl (prog' := fun w => .pure w.1) (fun _ _ _ => rfl) ?_
  refine DeferRun.coinsFirst_bits sFS (ft := inferInstance) resamples_salt
    (k' := fun x => .pure (List.ofFn x))
    fun x => ?_
  exact CoinsFirst.const _ (.pure (List.ofFn x))

end OnBytes.CoinsTie

#print axioms OnBytes.CoinsTie.resamples_leaf
#print axioms OnBytes.CoinsTie.coinsFirst_of_runLaw
#print axioms OnBytes.CoinsTie.coinsFirst_of_saltsLaw
#print axioms OnBytes.CoinsTie.toy_salt
