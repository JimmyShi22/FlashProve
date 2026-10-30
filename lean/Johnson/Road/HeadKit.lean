-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadKit.lean: tools for statements on the routines of the output head's check.

The check of the output head's sub-proof (OnBytes/Model/Head.lean and the files beside it) builds
its forms inside the type SubM: a routine takes the state of the sub-proof (Fork) and the context of
the block (Ctx) and either fails or returns a value, a state and a context. Many routines only read
the state. Others add claims to it. Loops are written with "for ... in [0:n]". This file has what a
statement on such a routine needs.

Main definitions: Ok (a routine succeeds, with this value, state and context), colsOf (the one
number that the readers take from the state), rdW (an entry of the vector of reads in a world),
Valid, Starts (an index lies in a table; a table's first entry), Inverse (a reading takes the
program's inverse to the inverse).
Main theorems: ok_pure, ok_bind, ok_lift, ok_get (how Ok passes through the monad); mustAs_ok,
getAs_ok, held_ok; ok_forIn_list, ok_forIn_range (a rule with an invariant for a loop),
loop_value (a loop that adds terms to a form); ok_uEnt, ok_tabAt, ok_U3at, U3at_value; ok_segOf,
ok_ewOf, ok_ewh; xbA_value, sh2_value, Sl_value, gapAt_value (what the readers' forms are worth);
ok_lin, lins_append, lins_cols (claims are added one after the other, and adding a claim does not
change what the readers take from the state); gl_inverse.

What is not claimed. Every theorem begins "if the routine succeeds": none says that it does. Nothing
is said about what a verifier's acceptance shows. The program does not import this file.
-/
import OnBytes.Model.Head
import OnBytes.Model.HideLaws
import OnBytes.Slice.ProgField
import Johnson.Road.FormsKeysKit

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading World Aff Fork SubM)

/-! ## A routine that succeeds -/

/-- The routine m, run from the state F and the context C, succeeds with the value a and leaves the
state G and the context D. -/
def Ok {α : Type} (m : SubM α) (F : Fork) (C : Ctx) (a : α) (G : Fork) (D : Ctx) : Prop :=
  m F C = .ok ((a, G), D)

/-- A routine that returns a value at once. -/
theorem ok_pure {α : Type} (a b : α) (F G : Fork) (C D : Ctx) :
    Ok (pure a : SubM α) F C b G D ↔ b = a ∧ G = F ∧ D = C := by
  have e : (pure a : SubM α) F C = .ok ((a, F), C) := rfl
  unfold Ok
  rw [e]
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- One routine after another: the second starts from what the first leaves. -/
theorem ok_bind {α β : Type} (m : SubM α) (f : α → SubM β) (F G : Fork) (C D : Ctx) (b : β) :
    Ok (m >>= f) F C b G D ↔ ∃ a F1 C1, Ok m F C a F1 C1 ∧ Ok (f a) F1 C1 b G D := by
  have e : (m >>= f) F C = (m F C).bind fun q => f q.1.1 q.1.2 q.2 := rfl
  unfold Ok
  rw [e]
  cases m F C with
  | error x =>
    constructor
    · intro h2
      simp [Except.bind] at h2
    · rintro ⟨a, F1, C1, h1, _⟩
      cases h1
  | ok q =>
    obtain ⟨⟨a, F1⟩, C1⟩ := q
    constructor
    · intro h2
      exact ⟨a, F1, C1, rfl, h2⟩
    · rintro ⟨a', F1', C1', h1, h2⟩
      cases h1
      exact h2

/-- A block that is run inside a routine: it does not see the state. -/
theorem ok_lift {α : Type} (x : Blk α) (F G : Fork) (C D : Ctx) (a : α) :
    Ok (liftM x : SubM α) F C a G D ↔ x C = .ok (a, D) ∧ G = F := by
  have e : (liftM x : SubM α) F C = (x C).bind fun q => .ok ((q.1, F), q.2) := rfl
  unfold Ok
  rw [e]
  cases x C with
  | error y => simp [Except.bind]
  | ok q =>
    obtain ⟨a', D'⟩ := q
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, rfl⟩
      cases h1
      rfl

/-- Reading the state. -/
theorem ok_get (F G H : Fork) (C D : Ctx) :
    Ok (get : SubM Fork) F C H G D ↔ H = F ∧ G = F ∧ D = C := by
  have e : (get : SubM Fork) F C = .ok ((F, F), C) := rfl
  unfold Ok
  rw [e]
  constructor
  · intro h
    cases h
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

/-- A public condition succeeds exactly if it holds, and leaves the context. -/
theorem mustAs_ok (n : String) (b : Bool) (C D : Ctx) (u : Unit) :
    Model.mustAs n b C = .ok (u, D) ↔ b = true ∧ D = C := by
  cases b
  · have e : Model.mustAs n false C = .error { name := n } := rfl
    rw [e]
    simp
  · have e : Model.mustAs n true C = .ok ((), C) := rfl
    rw [e]
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨-, rfl⟩
      rfl

/-- Unwrapping an optional value succeeds exactly if the value is there. -/
theorem getAs_ok {α : Type} (n : String) (x : Option α) (C D : Ctx) (a : α) :
    Model.Head.getAs n x C = .ok (a, D) ↔ x = some a ∧ D = C := by
  cases x with
  | none =>
    have e : Model.Head.getAs n (none : Option α) C = .error { name := n } := rfl
    rw [e]
    simp
  | some y =>
    have e : Model.Head.getAs n (some y) C = .ok (y, C) := rfl
    rw [e]
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, rfl⟩
      cases h1
      rfl

/-- Unwrapping a result succeeds exactly if the result is a value. -/
theorem held_ok {α : Type} (x : Except String α) (C D : Ctx) (a : α) :
    Model.Head.held x C = .ok (a, D) ↔ x = .ok a ∧ D = C := by
  cases x with
  | error s =>
    have e : Model.Head.held (Except.error s : Except String α) C = .error { name := s } := rfl
    rw [e]
    simp
  | ok y =>
    have e : Model.Head.held (Except.ok y : Except String α) C = .ok (y, C) := rfl
    rw [e]
    constructor
    · intro h
      cases h
      exact ⟨rfl, rfl⟩
    · rintro ⟨h1, rfl⟩
      cases h1
      rfl

/-! ## Loops -/

/-- A rule for a loop over the numbers s, s + 1, ..., s + k - 1. I x b F C says what holds before
the step with the number x, of the loop's value b, the state and the context. If every step below N
that succeeds goes on and keeps I, a loop that succeeds ends with I. -/
theorem ok_forIn_list {β : Type} (f : ℕ → β → SubM (ForInStep β))
    (I : ℕ → β → Fork → Ctx → Prop) (N : ℕ)
    (step : ∀ x b F1 C1 r F2 C2, x < N → I x b F1 C1 → Ok (f x b) F1 C1 r F2 C2 →
      ∃ b', r = ForInStep.yield b' ∧ I (x + 1) b' F2 C2) :
    ∀ (k s : ℕ) (b : β) (F : Fork) (C : Ctx) (b' : β) (G : Fork) (D : Ctx), s + k ≤ N →
      I s b F C → Ok (forIn (List.range' s k) b f) F C b' G D → I (s + k) b' G D
  | 0, s, b, F, C, b', G, D, _, h0, h => by
    have e : forIn (List.range' s 0) b f = (pure b : SubM β) := rfl
    rw [e, ok_pure] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact h0
  | k + 1, s, b, F, C, b', G, D, hN, h0, h => by
    rw [List.range'_succ, List.forIn_cons, ok_bind] at h
    obtain ⟨r, F1, C1, h1, h2⟩ := h
    obtain ⟨b1, rfl, hI⟩ := step s b F C r F1 C1 (by omega) h0 h1
    have h3 := ok_forIn_list f I N step k (s + 1) b1 F1 C1 b' G D (by omega) hI h2
    have e : s + 1 + k = s + (k + 1) := by omega
    rw [e] at h3
    exact h3

/-- The numbers of the loop "for x in [0:n]". -/
theorem range_list (n : ℕ) :
    List.range' ([:n] : Std.Legacy.Range).start ([:n] : Std.Legacy.Range).size
      ([:n] : Std.Legacy.Range).step = List.range' 0 n := by
  simp [Std.Legacy.Range.size]

/-- The rule for the loop "for x in [0:n]". -/
theorem ok_forIn_range {β : Type} (n : ℕ) (f : ℕ → β → SubM (ForInStep β))
    (I : ℕ → β → Fork → Ctx → Prop)
    (step : ∀ x b F1 C1 r F2 C2, x < n → I x b F1 C1 → Ok (f x b) F1 C1 r F2 C2 →
      ∃ b', r = ForInStep.yield b' ∧ I (x + 1) b' F2 C2)
    {b b' : β} {F G : Fork} {C D : Ctx} (h0 : I 0 b F C)
    (h : Ok (forIn [:n] b f) F C b' G D) : I n b' G D := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', range_list] at h
  have h3 := ok_forIn_list f I n step n 0 b F C b' G D (by omega) h0 h
  rw [Nat.zero_add] at h3
  exact h3

section Values

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- A loop that reads the state and adds a term to a form at each step: if step x adds g x to the
form's value, the loop adds the sum of the g x, and state and context are left as they were. What
each step that succeeds shows besides (P x) holds of all steps. -/
theorem loop_value (n : ℕ) (f : ℕ → Aff → SubM (ForInStep Aff)) (g : ℕ → K) (P : ℕ → Prop)
    {F : Fork} {C : Ctx}
    (step : ∀ x s r F2 C2, x < n → Ok (f x s) F C r F2 C2 →
      F2 = F ∧ C2 = C ∧ P x ∧ ∃ s', r = ForInStep.yield s' ∧ s'.value ρ W = s.value ρ W + g x)
    {s0 s : Aff} {G : Fork} {D : Ctx} (h : Ok (forIn [:n] s0 f) F C s G D) :
    G = F ∧ D = C ∧ (∀ x, x < n → P x) ∧ s.value ρ W = s0.value ρ W + ∑ x ∈ range n, g x := by
  refine ok_forIn_range n f
    (fun x s1 F1 C1 => F1 = F ∧ C1 = C ∧ (∀ y, y < x → P y) ∧
      s1.value ρ W = s0.value ρ W + ∑ y ∈ range x, g y)
    ?_ ?_ h
  · rintro x b F1 C1 r F2 C2 hx ⟨rfl, rfl, hP, hv⟩ hr
    obtain ⟨e1, e2, hp, s', rfl, hs⟩ := step x b r F2 C2 hx hr
    refine ⟨s', rfl, e1, e2, ?_, ?_⟩
    · intro y hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp hy with h1 | h1
      · exact hP y h1
      · rw [h1]
        exact hp
    · rw [hs, hv, Finset.sum_range_succ, add_assoc]
  · exact ⟨rfl, rfl, fun y hy => absurd hy (Nat.not_lt_zero y), by simp⟩

end Values

/-! ## What the readers take from the state -/

/-- The number of columns of array number t of the sub-proof's list; 0 if there is no such array. -/
def colsOf (F : Fork) (t : ℕ) : ℕ := ((F.trees[t]?).map (·.K)).getD 0

/-- An entry of a vector that is stored as an array: the routine leaves state and context, and the
form is the entry at the row and the column that the array's number of columns gives. -/
theorem ok_uEnt {t x : ℕ} {F G : Fork} {C D : Ctx} {a : Aff}
    (h : Ok (Model.uEnt t x) F C a G D) :
    G = F ∧ D = C ∧ a = Aff.ent t (x / colsOf F t) (x % colsOf F t) := by
  unfold Model.uEnt at h
  rw [ok_bind] at h
  obtain ⟨F0, F1, C1, h1, h2⟩ := h
  rw [ok_get] at h1
  obtain ⟨rfl, rfl, rfl⟩ := h1
  dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨u, F2, C2, h3, h4⟩ := h2
  rw [ok_lift, mustAs_ok] at h3
  obtain ⟨⟨_, rfl⟩, rfl⟩ := h3
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  exact ⟨rfl, rfl, rfl⟩

/-- The table with the name n begins at entry tb of the vector of reads. -/
def Starts (R : Model.Head.Run) (n : String) (tb : ℕ) : Prop :=
  ((R.t.tab.find? fun e => e.1 == n).map (·.2.1)) = some tb

/-- A table begins at entry tb and has more than i entries. -/
def Valid (R : Model.Head.Run) (tb i : ℕ) : Prop :=
  (R.t.tab.any fun e => e.2.1 == tb && decide (i < e.2.2)) = true

/-- The first entry of a table, by the table's name. -/
theorem ok_tabAt {R : Model.Head.Run} {n : String} {F G : Fork} {C D : Ctx} {tb : ℕ}
    (h : Ok (Model.Head.tabAt R n) F C tb G D) : G = F ∧ D = C ∧ Starts R n tb := by
  unfold Model.Head.tabAt at h
  rw [ok_lift, getAs_ok] at h
  exact ⟨h.2, h.1.2, h.1.1⟩

/-- An entry of a table of the reads, as the head's forms name it. -/
theorem ok_U3at {R : Model.Head.Run} {t i : ℕ} {F G : Fork} {C D : Ctx} {a : Aff}
    (h : Ok (Model.Head.U3at R t i) F C a G D) :
    G = F ∧ D = C ∧
      a = Aff.ent R.iU3 ((t + i) / colsOf F R.iU3) ((t + i) % colsOf F R.iU3) ∧ Valid R t i := by
  unfold Model.Head.U3at at h
  rw [ok_bind] at h
  obtain ⟨u, F1, C1, h1, h2⟩ := h
  rw [ok_lift, mustAs_ok] at h1
  obtain ⟨⟨hb, rfl⟩, rfl⟩ := h1
  obtain ⟨e1, e2, e3⟩ := ok_uEnt h2
  exact ⟨e1, e2, e3, hb⟩

section Reads

variable {K : Type} [Field K] (ρ : Reading K) (W : World K)

/-- Entry e of the vector of reads in the world W, if the vector is stored as array number iU3 with
K3 columns. -/
def rdW (iU3 K3 e : ℕ) : K := W.entry iU3 (e / K3) (e % K3)

/-- The form that names an entry of a table is worth that entry of the vector of reads. -/
theorem U3at_value {R : Model.Head.Run} {t i : ℕ} {F G : Fork} {C D : Ctx} {a : Aff}
    (h : Ok (Model.Head.U3at R t i) F C a G D) :
    G = F ∧ D = C ∧ Valid R t i ∧ a.value ρ W = rdW W R.iU3 (colsOf F R.iU3) (t + i) := by
  obtain ⟨e1, e2, e3, e4⟩ := ok_U3at h
  refine ⟨e1, e2, e4, ?_⟩
  rw [e3, Aff.value_ent]
  rfl

/-- Block kh of the residual stream: its limbs at radix 256. -/
theorem xbA_value (hρ : Numerals ρ) {R : Model.Head.Run} {t kh : ℕ} {F G : Fork} {C D : Ctx}
    {a : Aff} (h : Ok (Model.Head.xbA R t kh) F C a G D) :
    G = F ∧ D = C ∧ (∀ l, l < R.b.nl → Valid R t (R.b.cell l 0 / R.h.S2 + kh)) ∧
      a.value ρ W = ∑ l ∈ range R.b.nl, (256 : K) ^ l *
        rdW W R.iU3 (colsOf F R.iU3) (t + (R.b.cell l 0 / R.h.S2 + kh)) := by
  unfold Model.Head.xbA at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨r, F1, C1, h1, h2⟩ := h
  rw [ok_pure] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  obtain ⟨e1, e2, e3, e4⟩ := loop_value ρ W R.b.nl _
    (fun l => (256 : K) ^ l * rdW W R.iU3 (colsOf F R.iU3) (t + (R.b.cell l 0 / R.h.S2 + kh)))
    (fun l => Valid R t (R.b.cell l 0 / R.h.S2 + kh))
    (by
      intro x s r' F2 C2 _ hr
      replace hr : Ok (Model.Head.U3at R t (R.b.cell x 0 / R.h.S2 + kh) >>= fun u =>
          (pure PUnit.unit : SubM PUnit) >>= fun _ =>
            pure (ForInStep.yield (s.addMul u (Model.ofNat (256 ^ x))))) F C r' F2 C2 := hr
      rw [ok_bind] at hr
      obtain ⟨u, F3, C3, h3, h4⟩ := hr
      obtain ⟨rfl, rfl, hval, hv⟩ := U3at_value ρ W h3
      rw [ok_bind] at h4
      obtain ⟨_, F4, C4, h5, h6⟩ := h4
      rw [ok_pure] at h5 h6
      obtain ⟨_, rfl, rfl⟩ := h5
      obtain ⟨rfl, rfl, rfl⟩ := h6
      refine ⟨rfl, rfl, hval, _, rfl, ?_⟩
      rw [Aff.value_addMul, hv, hρ.ofNat, Nat.cast_pow, Nat.cast_ofNat])
    h1
  refine ⟨e1, e2, e3, ?_⟩
  rw [e4, Aff.value_empty, zero_add]

/-- Feature j of the clamped activations: its two limbs at radix 256. -/
theorem sh2_value (hρ : Numerals ρ) {R : Model.Head.Run} {t j : ℕ} {F G : Fork} {C D : Ctx}
    {a : Aff} (h : Ok (Model.Head.sh2 R t j) F C a G D) :
    G = F ∧ D = C ∧ Valid R t j ∧ Valid R t (R.h.d + j) ∧
      a.value ρ W = rdW W R.iU3 (colsOf F R.iU3) (t + j) +
        256 * rdW W R.iU3 (colsOf F R.iU3) (t + (R.h.d + j)) := by
  unfold Model.Head.sh2 at h
  rw [ok_bind] at h
  obtain ⟨u, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, v1, e1⟩ := U3at_value ρ W h1
  rw [ok_bind] at h2
  obtain ⟨u', F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, v2, e2⟩ := U3at_value ρ W h3
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  refine ⟨rfl, rfl, v1, v2, ?_⟩
  rw [Aff.value_add, Aff.value_scale, e1, e2, hρ.ofNat, Nat.cast_ofNat]

/-- A call and one of its segments, by the segment's name. -/
theorem ok_segOf {R : Model.Head.Run} {sn : String} {F G : Fork} {C D : Ctx}
    {x : ℕ × Model.CallD × Model.Seg} (h : Ok (Model.Head.segOf R sn) F C x G D) :
    G = F ∧ D = C ∧ Model.Head.callNo R.L sn = some x.1 ∧
      x.2.1 = R.L.calls.getD x.1 default ∧ (R.L.calls.getD x.1 default).seg? sn = some x.2.2 := by
  unfold Model.Head.segOf at h
  rw [ok_bind] at h
  obtain ⟨q, F1, C1, h1, h2⟩ := h
  rw [ok_lift, getAs_ok] at h1
  obtain ⟨⟨hq, rfl⟩, rfl⟩ := h1
  dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨g, F2, C2, h3, h4⟩ := h2
  rw [ok_lift, getAs_ok] at h3
  obtain ⟨⟨hg, rfl⟩, rfl⟩ := h3
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  exact ⟨rfl, rfl, hq, rfl, hg⟩

/-- The weights of a segment's entries. -/
theorem ok_ewOf {R : Model.Head.Run} {sn : String} {F G : Fork} {C D : Ctx} {ew : Array E}
    (h : Ok (Model.Head.ewOf R sn) F C ew G D) :
    G = F ∧ D = C ∧ ∃ q g, Model.Head.callNo R.L sn = some q ∧
      (R.L.calls.getD q default).seg? sn = some g ∧
      ew = Model.Layer.Env.ewFrom (Model.eqTab (Model.Head.zjOf R.L R.x.g1 q)) g := by
  unfold Model.Head.ewOf at h
  rw [ok_bind] at h
  obtain ⟨⟨q, c, g⟩, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, hq, _, hg⟩ := ok_segOf h1
  dsimp only at h2
  rw [ok_pure] at h2
  obtain ⟨rfl, rfl, rfl⟩ := h2
  exact ⟨rfl, rfl, q, g, hq, hg, rfl⟩

/-- The weights of a segment's blocks. -/
theorem ok_ewh {R : Model.Head.Run} {sn : String} {F G : Fork} {C D : Ctx} {wh : Array E}
    (h : Ok (Model.Head.ewh R sn) F C wh G D) :
    G = F ∧ D = C ∧ ∃ q g k, Model.Head.callNo R.L sn = some q ∧
      (R.L.calls.getD q default).seg? sn = some g ∧
      Model.cutLast (Model.Head.zjOf R.L R.x.g1 q) R.h.ls = .ok k ∧
      wh = Model.Layer.Env.ewhFrom R.h.S2 (Model.eqTab k.1) g := by
  unfold Model.Head.ewh at h
  rw [ok_bind] at h
  obtain ⟨⟨q, c, g⟩, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, hq, _, hg⟩ := ok_segOf h1
  dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨k, F2, C2, h3, h4⟩ := h2
  rw [ok_lift, held_ok] at h3
  obtain ⟨⟨hk, rfl⟩, rfl⟩ := h3
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  exact ⟨rfl, rfl, q, g, k, hq, hg, hk, rfl⟩

/-- A tensor of the matrix hf under a segment's block weights, read in the long table: nl limbs of J
features from feature OFF on, at radix 256. -/
theorem Sl_value (hρ : Numerals ρ) {R : Model.Head.Run} {sn : String} {OFF nl J : ℕ}
    {F G : Fork} {C D : Ctx} {a : Aff} (h : Ok (Model.Head.Sl R sn OFF nl J) F C a G D) :
    G = F ∧ D = C ∧ ∃ wh tb, Ok (Model.Head.ewh R sn) F C wh F C ∧ Starts R "hf@Z" tb ∧
      (∀ xh, xh < wh.size → ∀ l, l < nl → Valid R tb ((OFF + l * J) / R.h.S2 + xh)) ∧
      a.value ρ W = ∑ xh ∈ range wh.size, ∑ l ∈ range nl,
        ((256 : K) ^ l * ρ.val (wh.getD xh zeroE)) *
          rdW W R.iU3 (colsOf F R.iU3) (tb + ((OFF + l * J) / R.h.S2 + xh)) := by
  generalize hK : colsOf F R.iU3 = K3
  unfold Model.Head.Sl at h
  rw [ok_bind] at h
  obtain ⟨wh, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, _⟩ := ok_ewh h1
  rw [ok_bind] at h2
  obtain ⟨tb, F2, C2, h3, h4⟩ := h2
  obtain ⟨rfl, rfl, hst⟩ := ok_tabAt h3
  dsimp only at h4
  rw [ok_bind] at h4
  obtain ⟨r, F3, C3, h5, h6⟩ := h4
  rw [ok_pure] at h6
  obtain ⟨rfl, rfl, rfl⟩ := h6
  obtain ⟨e1, e2, e3, e4⟩ := loop_value ρ W wh.size _
    (fun xh => ∑ l ∈ range nl, ((256 : K) ^ l * ρ.val (wh.getD xh zeroE)) *
      rdW W R.iU3 K3 (tb + ((OFF + l * J) / R.h.S2 + xh)))
    (fun xh => ∀ l, l < nl → Valid R tb ((OFF + l * J) / R.h.S2 + xh))
    (by
      intro xh s r' F4 C4 _ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨s1, F5, C5, h7, h8⟩ := hr
      obtain ⟨rfl, rfl, i3, i4⟩ := loop_value ρ W nl _
        (fun l => ((256 : K) ^ l * ρ.val (wh.getD xh zeroE)) *
          rdW W R.iU3 K3 (tb + ((OFF + l * J) / R.h.S2 + xh)))
        (fun l => Valid R tb ((OFF + l * J) / R.h.S2 + xh))
        (by
          intro l s2 r2 F6 C6 _ hq
          try dsimp only at hq
          rw [ok_bind] at hq
          obtain ⟨u, F7, C7, h9, h10⟩ := hq
          obtain ⟨rfl, rfl, hval, hv⟩ := U3at_value ρ W h9
          rw [hK] at hv
          rw [ok_bind] at h10
          obtain ⟨_, F8, C8, h11, h12⟩ := h10
          rw [ok_pure] at h11 h12
          obtain ⟨_, rfl, rfl⟩ := h11
          obtain ⟨rfl, rfl, rfl⟩ := h12
          refine ⟨rfl, rfl, hval, _, rfl, ?_⟩
          rw [Aff.value_addMul, hv, hρ.scaleNat, Nat.cast_pow, Nat.cast_ofNat])
        h7
      try dsimp only at h8
      rw [ok_bind] at h8
      obtain ⟨_, F9, C9, h13, h14⟩ := h8
      rw [ok_pure] at h13 h14
      obtain ⟨_, rfl, rfl⟩ := h13
      obtain ⟨rfl, rfl, rfl⟩ := h14
      exact ⟨rfl, rfl, i3, _, rfl, i4⟩)
    h5
  refine ⟨e1, e2, wh, tb, h1, hst, e3, ?_⟩
  rw [e4, Aff.value_empty, zero_add]

/-- One of the six numbers of the cost ledger, read in a table of the matrix hr: each digit is its
cell plus 128 times the sum of the table's weights. -/
theorem gapAt_value (hρ : Numerals ρ) {R : Model.Head.Run} {P : String} {i : ℕ} {wsum : E}
    {F G : Fork} {C D : Ctx} {a : Aff} (h : Ok (Model.Head.gapAt R P i wsum) F C a G D) :
    G = F ∧ D = C ∧ ∃ tb, Starts R ("hr@" ++ P) tb ∧
      (∀ l, l < (Model.ledG.getD i (0, 0)).2 →
        Valid R tb (Model.ledNR R.h.XL + (Model.ledG.getD i (0, 0)).1 + l)) ∧
      a.value ρ W = ∑ l ∈ range (Model.ledG.getD i (0, 0)).2, (256 : K) ^ l *
        (rdW W R.iU3 (colsOf F R.iU3)
          (tb + (Model.ledNR R.h.XL + (Model.ledG.getD i (0, 0)).1 + l)) + 128 * ρ.val wsum) := by
  unfold Model.Head.gapAt at h
  rw [ok_bind] at h
  obtain ⟨tb, F1, C1, h1, h2⟩ := h
  obtain ⟨rfl, rfl, hst⟩ := ok_tabAt h1
  dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨r, F2, C2, h3, h4⟩ := h2
  rw [ok_pure] at h4
  obtain ⟨rfl, rfl, rfl⟩ := h4
  obtain ⟨e1, e2, e3, e4⟩ := loop_value ρ W (Model.ledG.getD i (0, 0)).2 _
    (fun l => (256 : K) ^ l * (rdW W R.iU3 (colsOf F1 R.iU3)
      (tb + (Model.ledNR R.h.XL + (Model.ledG.getD i (0, 0)).1 + l)) + 128 * ρ.val wsum))
    (fun l => Valid R tb (Model.ledNR R.h.XL + (Model.ledG.getD i (0, 0)).1 + l))
    (by
      intro l s r' F3 C3 _ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨u, F4, C4, h5, h6⟩ := hr
      obtain ⟨rfl, rfl, hval, hv⟩ := U3at_value ρ W h5
      rw [ok_bind] at h6
      obtain ⟨_, F5, C5, h7, h8⟩ := h6
      rw [ok_pure] at h7 h8
      obtain ⟨_, rfl, rfl⟩ := h7
      obtain ⟨rfl, rfl, rfl⟩ := h8
      refine ⟨rfl, rfl, hval, _, rfl, ?_⟩
      rw [Aff.value_addMul, Aff.value_add, Aff.value_ofConst, hv, hρ.ofNat, hρ.scaleNat,
        Nat.cast_pow, Nat.cast_ofNat, Nat.cast_ofNat])
    h3
  refine ⟨e1, e2, tb, hst, e3, ?_⟩
  rw [e4, Aff.value_empty, zero_add]

end Reads

/-! ## Claims -/

/-- Adding a claim succeeds exactly where the step on the state does, and leaves the context. -/
theorem ok_lin (f : Aff) (F G : Fork) (C D : Ctx) (u : Unit) :
    Ok (SubM.lin f) F C u G D ↔ F.lin f = some G ∧ D = C :=
  Model.SubM.lin_run f F G C D

/-- Two lists of claims, one after the other. -/
theorem lins_append (F : Fork) (l1 l2 : List Aff) :
    F.lins (l1 ++ l2) = (F.lins l1).bind fun G => G.lins l2 := by
  unfold Fork.lins
  rw [List.foldlM_append]
  rfl

/-- The number of columns of an array can be read off what the arrays hold beside their weights. -/
theorem colsOf_frame (F : Fork) (t : ℕ) :
    colsOf F t = (((Model.treesFrame F.trees)[t]?).map fun p => p.1.K).getD 0 := by
  unfold colsOf Model.treesFrame
  rw [Array.getElem?_map]
  cases F.trees[t]? <;> rfl

/-- Adding a claim changes no array's number of columns, and there is still one coefficient for each
slot. -/
theorem lin_cols {F G : Fork} {f : Aff} (hs : F.LS.size = F.ns) (h : F.lin f = some G) :
    G.LS.size = G.ns ∧ ∀ t, colsOf G t = colsOf F t := by
  obtain ⟨_, _, _, _, h5, h6⟩ :=
    Fork.lin_total Reading.gl ⟨fun _ => 0, fun _ _ _ => 0⟩ F G f hs h
  refine ⟨h5, fun t => ?_⟩
  rw [colsOf_frame, colsOf_frame, h6]

/-- The same for a list of claims. -/
theorem lins_cols : ∀ (l : List Aff) {F G : Fork}, F.LS.size = F.ns → F.lins l = some G →
    G.LS.size = G.ns ∧ ∀ t, colsOf G t = colsOf F t
  | [], F, G, hs, h => by
    have e : F = G := by simpa [Fork.lins] using h
    subst e
    exact ⟨hs, fun _ => rfl⟩
  | f :: l, F, G, hs, h => by
    unfold Fork.lins at h
    rw [List.foldlM_cons] at h
    cases hq : F.lin f with
    | none => simp [hq] at h
    | some F1 =>
      rw [hq] at h
      have h2 : F1.lins l = some G := by simpa [Fork.lins] using h
      obtain ⟨s1, c1⟩ := lin_cols hs hq
      obtain ⟨s2, c2⟩ := lins_cols l s1 h2
      exact ⟨s2, fun t => by rw [c2, c1]⟩

/-! ## The inverse -/

/-- A reading that takes the program's inverse to the inverse of K. The laws of a reading do not
give this. -/
def Inverse {K : Type} [Field K] (ρ : Reading K) : Prop := ∀ x : E, ρ.val (invE x) = (ρ.val x)⁻¹

/-- The reading in the library's extension field takes inverses to inverses. -/
theorem gl_inverse : Inverse Reading.gl := fun x => Slice.readE_inv x

#print axioms ok_bind
#print axioms ok_forIn_range
#print axioms loop_value
#print axioms xbA_value
#print axioms sh2_value
#print axioms Sl_value
#print axioms gapAt_value
#print axioms ok_ewh
#print axioms lins_cols
#print axioms gl_inverse

end OnBytes.Road.Hd
