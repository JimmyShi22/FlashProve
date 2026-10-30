--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ProdV/Chain.lean: the grand product: the chain over all levels, for any text of
a level: from a level's law and a level's facts, as two named premises on a relation "the level
returns", to the law of a run of levels. Definitions, statements and proofs.

X: what a text has still to hear (a list of a view's rounds; a tape). `Lev m z order C F x o G y`:
the level with m variables, at the point z and the start form C, from the ledger F and x, returns
o, G, y. `P1Clean badE bad m z order C F x T'`: no bad eps, challenge or beta is drawn in that
level's masked sumcheck: the text's own sentence. `LawOf`: the level's law, with its public
premises behind the sets. `FactsOf`: what a level hands on. `Ran`: the run of n levels, as a
relation. `CleanRan`: no bad element was drawn, level by level. `AllClean`, `cleanRan_of_all`: the
same said of all levels at once, for a caller that holds the course. `ran_facts`, `ran_sound`: what
a run hands on; the chain's law.

The mask row stands in front of the families of bad sets; the entries of the virtual rows stand
behind them. The letters at which each level's sets are taken stand in front of that level's
rounds: m, the carried point, the ledger's next free slot, the carried form's two values at the
ledger in front. The error: the sum of the levels': n * n + (2 * m0 + 3) * n bad elements of K
(Johnson/Desc/First/ProdV/RunCount.lean).

Limits. LawOf is worth just what its letter P1Clean is worth: at "P1Clean := never" it is true and
empty. Whoever lays a text in must give a P1Clean that speaks of what a function reads off x: no
"there are" over mu, eps, the sent lists or the challenges. At "P1Clean := always" and "the level
always returns" LawOf is false (Johnson/Desc/First/ProdV/Silly.lean). The caller must close the
last form: its truth is a premise. A carried form's value is a letter of the sets: it is fixed in
front of the level's draws only where the form has no entry of a virtual row made behind them (the
grand product's own forms have none). The order of the letters, not time. Sets are counted: no
probability.
Not claimed: anything on an honest prover or on hiding.

-/
import Johnson.Desc.First.ProdV.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.ProdV
open OnBytes OnBytes.Model OnBytes.PscRun Polynomial
open OnBytes.Desc.First.P1 OnBytes.Desc.First.P2

theorem getD_push_self {α : Type} (a : Array α) (x d : α) : (a.push x).getD a.size d = x := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_pos rfl]
  rfl

theorem getD_push_lt {α : Type} (a : Array α) (x d : α) (j : ℕ) (h : j < a.size) :
    (a.push x).getD j d = a.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_push, if_neg (by omega),
    ← Array.getD_eq_getD_getElem?]

section
variable {K : Type} [Field K] (ρ : Reading K) {X : Type}

/-- "The level returns." -/
abbrev LevRel (X : Type) : Type :=
  ℕ → Array E → List ℕ → Aff → Fork → X → LevelOut → Fork → X → Prop

/-- "No bad element is drawn in the level's masked sumcheck". T': the start form on what was shown.
-/
abbrev P1CleanRel (K X : Type) [Field K] : Type :=
  (K → Finset K) → (K → K → List (K[X] × K) → K[X] → Finset K) →
    ℕ → Array E → List ℕ → Aff → Fork → X → E → Prop

/-- **The level's law**, as a premise on a text. -/
def LawOf (Lev : LevRel X) (Ok : X → Prop) (P1Clean : P1CleanRel K X) : Prop :=
  ∀ (m : ℕ) (z : Array E) (order : List ℕ) (A B : (ℕ → K) → K) (mask : ℕ → K)
    (nx : ℕ) (Cv T : K),
    ∃ (badE : K → Finset K) (bad : K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ mu, (badE mu).card ≤ 1) ∧ (∀ mu eps pre g, (bad mu eps pre g).card ≤ 2) ∧
      (orderOk m order = true → z.size = m → Step m A B →
      ∀ (entry : ℕ → ℕ → ℕ → K) (C : Aff) (F G H : Fork) (x y : X) (o : LevelOut) (T' : E),
        Ok x → Lev m z order C F x o G y → F.next = nx → Sized F → OnFilled F C →
        F.publicPart C = some T' → ρ.val T' = T → C.value ρ (F.worldOf ρ mask entry) = Cv →
        Later G H →
        o.row.value ρ (H.worldOf ρ mask entry) = 0 →
        (stepDown o).2.value ρ (H.worldOf ρ mask entry) = B (pt ρ (stepDown o).1) →
        P1Clean badE bad m z order C F x T' →
        ρ.val o.xi ∉ badLine (B (pcons 0 (pt ρ o.r))) (B (pcons 1 (pt ρ o.r)))
          ((G.worldOf ρ mask entry).slot o.sL) ((G.worldOf ρ mask entry).slot o.sR) →
        Cv = A (pt ρ z))

/-- **What a level hands on**, as a premise on a text. -/
def FactsOf (Lev : LevRel X) (Ok : X → Prop) : Prop :=
  ∀ (m : ℕ) (z : Array E) (order : List ℕ) (C : Aff) (F G : Fork) (x y : X) (o : LevelOut),
    Sized F → Ok x → Lev m z order C F x o G y →
    Later F G ∧ Sized G ∧ (stepDown o).1.size = m + 1 ∧ OnFilled G (stepDown o).2 ∧ Ok y ∧
      ∃ T', F.publicPart C = some T'

/-- The run of n levels with m0, m0 + 1, .. variables. -/
inductive Ran (Lev : LevRel X) (m0 : ℕ) (orders : ℕ → List ℕ) (s : Carried) (F : Fork) (x : X) :
    ℕ → Carried → Fork → X → Prop
  | zero : Ran Lev m0 orders s F x 0 s F x
  | succ {n : ℕ} {s1 : Carried} {F1 G : Fork} {x1 y : X} {o : LevelOut} :
    Ran Lev m0 orders s F x n s1 F1 x1 →
    Lev (m0 + n) s1.point (orders (m0 + n)) s1.form F1 x1 o G y →
    Ran Lev m0 orders s F x (n + 1)
      { rows := s1.rows.push o.row, point := (stepDown o).1, form := (stepDown o).2 } G y

/-- **What a run hands on.** -/
theorem ran_facts {Lev : LevRel X} {Ok : X → Prop} (hf : FactsOf Lev Ok) {m0 : ℕ}
    {orders : ℕ → List ℕ} {s : Carried} {F : Fork} {x : X} (hF : Sized F) (hx : Ok x)
    (hp : s.point.size = m0) (hC : OnFilled F s.form) {n : ℕ} {s' : Carried} {F' : Fork} {y : X}
    (h : Ran Lev m0 orders s F x n s' F' y) :
    Later F F' ∧ Sized F' ∧ s'.point.size = m0 + n ∧ OnFilled F' s'.form ∧ Ok y ∧
      s'.rows.size = s.rows.size + n ∧
      ∀ j, j < s.rows.size → s'.rows.getD j {} = s.rows.getD j {} := by
  induction h with
  | zero => exact ⟨Later.refl _, hF, hp, hC, hx, rfl, fun _ _ => rfl⟩
  | @succ n s1 F1 G x1 y o _ hl ih =>
    obtain ⟨l1, z1, _, _, k1, q1, r1⟩ := ih
    obtain ⟨l2, z2, p2, c2, k2, _⟩ := hf _ _ _ _ _ _ _ _ _ z1 k1 hl
    refine ⟨l1.trans l2, z2, by rw [p2]; omega, c2, k2, ?_, fun j hj => ?_⟩
    · show (s1.rows.push o.row).size = _
      rw [Array.size_push, q1]
      omega
    · show (s1.rows.push o.row).getD j {} = _
      rw [getD_push_lt _ _ _ _ (by omega), r1 j hj]

/-- No bad element is drawn in the run's levels. The sets of the level with m variables are taken
at m, the
carried point, the ledger's next free slot, and the carried form's two values at the ledger in
front. -/
inductive CleanRan (Lev : LevRel X) (P1Clean : P1CleanRel K X) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (P : ℕ → (ℕ → K) → K)
    (badE : ℕ → Array E → ℕ → K → K → K → Finset K)
    (bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K)
    (m0 : ℕ) (orders : ℕ → List ℕ) (s : Carried) (F : Fork) (x : X) :
    ℕ → Carried → Fork → X → Prop
  | zero : CleanRan Lev P1Clean mask entry P badE bad m0 orders s F x 0 s F x
  | succ {n : ℕ} {s1 : Carried} {F1 G : Fork} {x1 y : X} {o : LevelOut} {T' : E} :
    CleanRan Lev P1Clean mask entry P badE bad m0 orders s F x n s1 F1 x1 →
    Lev (m0 + n) s1.point (orders (m0 + n)) s1.form F1 x1 o G y →
    F1.publicPart s1.form = some T' →
    P1Clean
      (badE (m0 + n) s1.point F1.next (s1.form.value ρ (F1.worldOf ρ mask entry)) (ρ.val T'))
      (bad (m0 + n) s1.point F1.next (s1.form.value ρ (F1.worldOf ρ mask entry)) (ρ.val T'))
      (m0 + n) s1.point (orders (m0 + n)) s1.form F1 x1 T' →
    ρ.val o.xi ∉ badLine (P (m0 + n + 1) (pcons 0 (pt ρ o.r))) (P (m0 + n + 1) (pcons 1 (pt ρ o.r)))
      ((G.worldOf ρ mask entry).slot o.sL) ((G.worldOf ρ mask entry).slot o.sR) →
    CleanRan Lev P1Clean mask entry P badE bad m0 orders s F x (n + 1)
      { rows := s1.rows.push o.row, point := (stepDown o).1, form := (stepDown o).2 } G y

theorem CleanRan.ran {Lev : LevRel X} {P1Clean : P1CleanRel K X} {mask : ℕ → K}
    {entry : ℕ → ℕ → ℕ → K} {P : ℕ → (ℕ → K) → K}
    {badE : ℕ → Array E → ℕ → K → K → K → Finset K}
    {bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K}
    {m0 : ℕ} {orders : ℕ → List ℕ} {s : Carried} {F : Fork} {x : X} {n : ℕ} {s' : Carried}
    {F' : Fork} {y : X}
    (h : CleanRan ρ Lev P1Clean mask entry P badE bad m0 orders s F x n s' F' y) :
    Ran Lev m0 orders s F x n s' F' y := by
  induction h with
  | zero => exact Ran.zero
  | succ _ hl _ _ _ ih => exact Ran.succ ih hl

/-- No bad element is drawn at any level of the course from s, F, x, said of all levels at once:
wherever i levels
have returned and the next one returns, its draws are not bad. (A text is a function, so there is
one course.) -/
def AllClean (Lev : LevRel X) (P1Clean : P1CleanRel K X) (mask : ℕ → K)
    (entry : ℕ → ℕ → ℕ → K) (P : ℕ → (ℕ → K) → K)
    (badE : ℕ → Array E → ℕ → K → K → K → Finset K)
    (bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K)
    (m0 : ℕ) (orders : ℕ → List ℕ) (s : Carried) (F : Fork) (x : X) (n : ℕ) : Prop :=
  ∀ (i : ℕ) (s1 : Carried) (F1 G : Fork) (x1 y : X) (o : LevelOut) (T' : E), i < n →
    Ran Lev m0 orders s F x i s1 F1 x1 →
    Lev (m0 + i) s1.point (orders (m0 + i)) s1.form F1 x1 o G y →
    F1.publicPart s1.form = some T' →
    P1Clean
      (badE (m0 + i) s1.point F1.next (s1.form.value ρ (F1.worldOf ρ mask entry)) (ρ.val T'))
      (bad (m0 + i) s1.point F1.next (s1.form.value ρ (F1.worldOf ρ mask entry)) (ρ.val T'))
      (m0 + i) s1.point (orders (m0 + i)) s1.form F1 x1 T' ∧
    ρ.val o.xi ∉ badLine (P (m0 + i + 1) (pcons 0 (pt ρ o.r))) (P (m0 + i + 1) (pcons 1 (pt ρ o.r)))
      ((G.worldOf ρ mask entry).slot o.sL) ((G.worldOf ρ mask entry).slot o.sR)

/-- A course all of whose levels are clean is a clean course. -/
theorem cleanRan_of_all {Lev : LevRel X} {Ok : X → Prop} {P1Clean : P1CleanRel K X}
    (hf : FactsOf Lev Ok) {mask : ℕ → K}
    {entry : ℕ → ℕ → ℕ → K} {P : ℕ → (ℕ → K) → K}
    {badE : ℕ → Array E → ℕ → K → K → K → Finset K}
    {bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K}
    {m0 : ℕ} {orders : ℕ → List ℕ} {s : Carried} {F : Fork} {x : X} (hF : Sized F) (hx : Ok x)
    (hp : s.point.size = m0) (hC : OnFilled F s.form) {n : ℕ} {s' : Carried} {F' : Fork} {y : X}
    (h : Ran Lev m0 orders s F x n s' F' y) :
    AllClean ρ Lev P1Clean mask entry P badE bad m0 orders s F x n →
    CleanRan ρ Lev P1Clean mask entry P badE bad m0 orders s F x n s' F' y := by
  induction h with
  | zero => exact fun _ => CleanRan.zero
  | @succ n s1 F1 G x1 y o hprev hl ih =>
    intro hall
    obtain ⟨_, z1, _, _, k1, _, _⟩ := ran_facts hf hF hx hp hC hprev
    obtain ⟨_, _, _, _, _, T', hT'⟩ := hf _ _ _ _ _ _ _ _ _ z1 k1 hl
    obtain ⟨c1, c2⟩ := hall n s1 F1 G x1 y o T' (by omega) hprev hl hT'
    exact CleanRan.succ
      (ih fun i a b c d e f g hi => hall i a b c d e f g (by omega)) hl hT' c1 c2

/-- **THE GRAND PRODUCT: THE CHAIN's SOUNDNESS LAW**, for any text of a level that has the level's
law and
facts. -/
theorem ran_sound {Lev : LevRel X} {Ok : X → Prop} {P1Clean : P1CleanRel K X}
    (hlaw : LawOf ρ Lev Ok P1Clean) (hf : FactsOf Lev Ok) (m0 : ℕ) (orders : ℕ → List ℕ)
    (P : ℕ → (ℕ → K) → K) (mask : ℕ → K) :
    ∃ (badE : ℕ → Array E → ℕ → K → K → K → Finset K)
      (bad : ℕ → Array E → ℕ → K → K → K → K → List (K[X] × K) → K[X] → Finset K),
      (∀ m z nx Cv T mu, (badE m z nx Cv T mu).card ≤ 1) ∧
      (∀ m z nx Cv T mu eps pre g, (bad m z nx Cv T mu eps pre g).card ≤ 2) ∧
      ∀ (entry : ℕ → ℕ → ℕ → K) (n : ℕ) (s s' : Carried) (F F' H : Fork) (x y : X),
        (∀ i, i < n → orderOk (m0 + i) (orders (m0 + i)) = true) →
        (∀ i, i < n → Step (m0 + i) (P (m0 + i)) (P (m0 + i + 1))) →
        Ok x → Sized F → s.point.size = m0 → OnFilled F s.form →
        CleanRan ρ Lev P1Clean mask entry P badE bad m0 orders s F x n s' F' y →
        Later F' H →
        (∀ j, s.rows.size ≤ j → j < s'.rows.size →
          (s'.rows.getD j {}).value ρ (H.worldOf ρ mask entry) = 0) →
        s'.form.value ρ (H.worldOf ρ mask entry) = P (m0 + n) (pt ρ s'.point) →
        s.form.value ρ (F.worldOf ρ mask entry) = P m0 (pt ρ s.point) := by
  choose badE bad hE hB hrun using fun (m : ℕ) (z : Array E) (nx : ℕ) (Cv T : K) =>
    hlaw m z (orders m) (P m) (P (m + 1)) mask nx Cv T
  refine ⟨badE, bad, hE, hB, ?_⟩
  intro entry n s s' F F' H x y hok hP hx hF hp hC hclean hH hrows hlast
  have key : ∀ (n : ℕ) (s' : Carried) (F' : Fork) (y : X),
      CleanRan ρ Lev P1Clean mask entry P badE bad m0 orders s F x n s' F' y →
      (∀ i, i < n → orderOk (m0 + i) (orders (m0 + i)) = true) →
      (∀ i, i < n → Step (m0 + i) (P (m0 + i)) (P (m0 + i + 1))) →
      ∀ H : Fork, Later F' H →
      (∀ j, s.rows.size ≤ j → j < s'.rows.size →
        (s'.rows.getD j {}).value ρ (H.worldOf ρ mask entry) = 0) →
      s'.form.value ρ (H.worldOf ρ mask entry) = P (m0 + n) (pt ρ s'.point) →
      s.form.value ρ (F.worldOf ρ mask entry) = P m0 (pt ρ s.point) := by
    intro n s' F' y hclean
    induction hclean with
    | zero =>
      intro _ _ H hH _ hlast
      rw [← value_later ρ hH s.form hC mask entry]
      exact hlast
    | @succ n s1 F1 G x1 y o T' hprev hl hT' hc1 hc2 ih =>
      intro hok hP H hH hrows hlast
      obtain ⟨_, z1, p1, c1, k1, q1, _⟩ := ran_facts hf hF hx hp hC hprev.ran
      obtain ⟨l2, _, _, _, _, _⟩ := hf _ _ _ _ _ _ _ _ _ z1 k1 hl
      have hrow : o.row.value ρ (H.worldOf ρ mask entry) = 0 := by
        have := hrows s1.rows.size (by omega) (by
          show s1.rows.size < (s1.rows.push o.row).size
          rw [Array.size_push]
          omega)
        rwa [show (s1.rows.push o.row).getD s1.rows.size {} = o.row from
          getD_push_self _ _ _] at this
      have hmid : s1.form.value ρ (F1.worldOf ρ mask entry) = P (m0 + n) (pt ρ s1.point) :=
        hrun (m0 + n) s1.point F1.next (s1.form.value ρ (F1.worldOf ρ mask entry)) (ρ.val T')
          (hok n (by omega)) p1 (hP n (by omega)) entry s1.form F1 G H x1 y o T' k1 hl rfl z1 c1 hT'
          rfl
          rfl hH hrow hlast hc1 hc2
      refine ih (fun i hi => hok i (by omega)) (fun i hi => hP i (by omega)) H (l2.trans hH)
        (fun j hj1 hj2 => ?_) ?_
      · have := hrows j hj1 (by
          show j < (s1.rows.push o.row).size
          rw [Array.size_push]
          omega)
        rwa [show (s1.rows.push o.row).getD j {} = s1.rows.getD j {} from
          getD_push_lt _ _ _ _ hj2] at this
      · rw [value_later ρ (l2.trans hH) s1.form c1 mask entry]
        exact hmid
  exact key n s' F' y hclean hok hP H hH hrows hlast

end

end VerifiableInference.Desc.First.ProdV

#print axioms VerifiableInference.Desc.First.ProdV.ran_sound
