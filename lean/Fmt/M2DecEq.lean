-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2DecEq.lean: the second toy (a chain of three links): the decision that runs is the decision
with every row of every closing written out: decWith blocks P V = decLit blocks drawL P V, for all
sizes P and all views V, no condition.

Theorems. Core Lean. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

The verifier's decision is a function of the sizes (`Par`, Fmt/M2Types.lean) and of a view (`View`,
Fmt/M1Types.lean). At the closing of a group (the oracle messages that are tested together) the
verifier sums all open rows, linear claims on the group's tables, into one.
A block is the function of one step of the protocol; `blocks` (Fmt/M2All.lean) is the record of
these functions. A draw is a position that the verifier has drawn; `drawL` (Fmt/M2Loc.lean) makes
the rows of one draw.
The decision that runs (Fmt/M2Dec.lean: `decWith`, at the blocks of Fmt/M2All.lean) never writes the
rows of a closing out. Its meaning (Fmt/M2Close.lean: decLit) lays every open row on the group's
tables, in the text's order, and sums them under the powers of the batching element.
The frame is what both decisions share: the pass through the rounds of the chain of links (`decBy`,
`goLinks`, Fmt/M2Dec.lean), which takes the way of batching as an argument. `decLit` is the whole
decision with `batchLit` (Fmt/M2Close.lean) in the place of `batch` (Fmt/M2Dec.lean).
Fmt/M2BatchEq.lean shows that one closing is its meaning under conditions on sizes: there `batch` =
`batchLit`. Here: at every closing that the frame makes these conditions hold, or the frame has
refused before.

Main names:
  `Ok`, `ok_of`: what the proof takes from the frame's test on sizes (`sizesOK`): at least one link;
    `P.C.l` and `P.Z.l` are powers of two; `P.C.l` is at least 4.
  `sizes_mid`, `sizes_last`: under `Ok P` and the lengths that the readers of rounds hand out, the
    sum in front of the draws has its tables' sizes, at a link after the first and at the last
    group.
  `call_first`, `call_mid`, `call_last`: `batch` = `batchLit` at the closing of the first link, of a
    later link and of the last group; the last two under the same hypotheses.
  `links_eq`: under `Ok P` and the hypotheses of its statement, the pass through the links
    (`goLinks`) gives the same with `batch` and with `batchLit`.
  `Spec.dec_eq`, `dec_eq`: the title's equation.

Why no condition is left:
  If the frame's test on sizes fails, both decisions are "no".
  Else a main row has `P.C.l` = 2^(`P.V` + 1) ≥ 4 places; `P.V` is the number of variables of a
    link's sum-check.
  The frame reads a round only with its numbers of elements.
  So the shared point (one point for all sampled messages of the prover's message) has as many
    coordinates as the largest cube needs (`readFirst_len`). Each sampled message reads the first
    coordinates of the point, as many as its own cube has (`cubeOf`, Fmt/M2Types.lean).
  And a link's three rows are made at `P.V` challenges (`readSub_some`).
  So every row in front of the draws has, at the carrying message and at the second sending, a form
    no longer than that member's table (the sizes of the blocks' forms: Fmt/M2Sizes.lean). The head
    of Fmt/M2Loc.lean says what these two members are.
  The carried claim (the claim carried over from the former link), which comes first, has exactly
    that size (`sizes_mid`, `sizes_last`).
  The proof then goes by induction through the links (`links_eq`).

Limits: this file does not say that `decLit` is what the programs (the C++ implementation that comes
with this Lean code) decide. The last proximity test is the same text in both decisions: nothing is
shown on it here (its code switch: Fmt/M1CsEq.lean). This file says nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M2BatchEq
import Fmt.M2Sizes

set_option autoImplicit false

namespace Fmt.M2.DecEq
open Fmt.M1 Fmt.M1.CsEq Fmt.M2.CloseEq Fmt.M2.LocEq Fmt.M2.BatchEq Fmt.M2.Sizes

/-! ## What the readers of rounds hand out -/

theorem nextN_some (ns ne np : Nat) (rs : Rs) (v : M1.RV) (rs' : Rs)
    (h : nextN ns ne np rs = some (v, rs')) :
    v.sent.length = ns ∧ v.els.length = ne ∧ v.poss.length = np := by
  unfold nextN at h
  cases rs with
  | nil => cases h
  | cons a rs0 =>
      simp only at h
      by_cases hc : (a.sent.length == ns && a.els.length == ne && a.poss.length == np) = true
      · rw [if_pos hc] at h
        have e : a = v := congrArg (·.1) (Option.some.inj h)
        subst e
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        exact ⟨hc.1.1, hc.1.2, hc.2⟩
      · rw [if_neg hc] at h
        cases h

theorem seedOf_len (na : Nat) (rs : Rs) (z : List E) (b : E)
    (rs' : Rs) (h : seedOf na rs = some (z, b, rs')) : z.length = na := by
  unfold seedOf at h
  cases hn : nextN 0 (na + 1) 0 rs with
  | none => rw [hn] at h; cases h
  | some x =>
      obtain ⟨v, r⟩ := x
      rw [hn] at h
      have e : v.els.take na = z := congrArg (·.1) (Option.some.inj h)
      rw [← e, List.length_take, (nextN_some _ _ _ _ _ _ hn).2.1]
      omega

theorem takeRounds_len :
    ∀ (n : Nat) (rs : Rs) (qs : List (E × E)) (g : List E) (rs' : Rs),
      takeRounds n rs = some (qs, g, rs') → g.length = n
  | 0, _, _, g, _, h => by
      have e : ([] : List E) = g := congrArg (·.2.1) (Option.some.inj h)
      rw [← e]
      rfl
  | n + 1, rs, qs, g, rs', h => by
      unfold takeRounds at h
      split at h
      · rename_i a b g0 po rs1 hh
        cases ht : takeRounds n rs1 with
        | none => rw [ht] at h; cases h
        | some x =>
            obtain ⟨q1, g1, r1⟩ := x
            rw [ht] at h
            have e : g0 :: g1 = g := congrArg (·.2.1) (Option.some.inj h)
            rw [← e, List.length_cons, takeRounds_len n rs1 q1 g1 r1 ht]
      · cases h

theorem readFirst_len (P : Par) (m : Nat) (rs : Rs) (z : List E) (beta : E) (ys : List E)
    (xs : List Nat) (rs' : Rs) (h : readFirst P m rs = some (z, beta, ys, xs, rs')) :
    z.length = seedLen (lg P.C.l) (lg P.Z.l) (memsOf P.links m) := by
  unfold readFirst at h
  simp only at h
  cases hs : seedOf (seedLen (lg P.C.l) (lg P.Z.l) (memsOf P.links m)) rs with
  | none => rw [hs] at h; cases h
  | some x =>
      obtain ⟨z0, b0, r0⟩ := x
      rw [hs] at h
      simp only at h
      cases hn : nextN ((memsOf P.links m).filter (·.sampled)).length 0
          (if m == 1 then 0 else P.t) r0 with
      | none => rw [hn] at h; cases h
      | some y =>
          obtain ⟨v, r1⟩ := y
          rw [hn] at h
          have e : z0 = z := congrArg (·.1) (Option.some.inj h)
          rw [← e]
          exact seedOf_len _ _ _ _ _ hs

/-- a link's three rows come from the block, at as many challenges as the sum-check has variables -/
theorem readSub_some (B : Blocks) (P : Par) (rs : Rs) (F : Form3 × Form3 × Form3)
    (rs' : Rs) (h : readSub B P rs = some (F, rs')) :
    ∃ (zeta : List E) (mu : E) (qs : List (E × E)) (p v : E × E) (eps : E)
        (gamma : List E) (bY : E),
      gamma.length = P.V ∧ F = B.psc P.fld P.V P.C.l P.Z.l zeta mu qs p v eps gamma bY := by
  unfold readSub at h
  split at h
  · split at h
    · split at h
      · rename_i qs gamma rs5 ht
        split at h
        · split at h
          · exact ⟨_, _, qs, _, _, _, gamma, _, takeRounds_len _ _ _ _ _ ht,
              (congrArg (·.1) (Option.some.inj h)).symm⟩
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

/-! ## The size of a sum -/

theorem size_fold (f : Fld) (x : E) (j : Nat) :
    ∀ (rows : List MRow) (s : MRow × E), ((rows.foldl (stM f x) s).1.main.getD j #[]).size =
      rows.foldl (fun a R => max a (R.main.getD j #[]).size) (s.1.main.getD j #[]).size
  | [], _ => rfl
  | R :: rows, s => by
      show (((rows.foldl (stM f x) (stM f x s R)).1.main.getD j #[]).size) =
        rows.foldl (fun a R => max a (R.main.getD j #[]).size)
          (max (s.1.main.getD j #[]).size (R.main.getD j #[]).size)
      rw [size_fold f x j rows (stM f x s R)]
      show rows.foldl _ ((axpyL f s.1.main s.2 R.main).getD j #[]).size = _
      rw [axpyL_getD, size_axpy]

theorem foldmax_const (g : MRow → Nat) (N : Nat) :
    ∀ rows : List MRow, (∀ R ∈ rows, g R ≤ N) → rows.foldl (fun a R => max a (g R)) N = N
  | [], _ => rfl
  | R :: rows, h => by
      show rows.foldl (fun a R => max a (g R)) (max N (g R)) = N
      rw [Nat.max_eq_left (h R (List.mem_cons_self ..))]
      exact foldmax_const g N rows fun R' h' => h R' (List.mem_cons_of_mem _ h')

/-- The size of a sum whose first row has N entries at member j, and no row more. -/
theorem size_sum (f : Fld) (x w : E) (j N : Nat) (R0 : MRow) (rows : List MRow)
    (h0 : (R0.main.getD j #[]).size = N) (hall : ∀ R ∈ rows, (R.main.getD j #[]).size ≤ N) :
    ((sumMFrom f x w (R0 :: rows)).1.main.getD j #[]).size = N := by
  rw [sumMFrom_fold, size_fold]
  show rows.foldl (fun a R => max a (R.main.getD j #[]).size) (max 0 (R0.main.getD j #[]).size) = N
  rw [h0, Nat.zero_max]
  exact foldmax_const (fun R => (R.main.getD j #[]).size) N rows hall

theorem oneAt_getD (n i : Nat) (v : Array E) (j : Nat) :
    (oneAt n i v).getD j #[] = if j < n then (if j == i then v else #[]) else #[] := by
  show ((List.range n).map fun j => if j == i then v else #[]).getD j #[] = _
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases h : j < n
  · rw [List.getElem?_range h, if_pos h]
    rfl
  · rw [List.getElem?_eq_none (by rw [List.length_range]; omega), if_neg h]
    rfl

theorem oneAt_size_ne (n i : Nat) (v : Array E) (j : Nat) (h : j ≠ i) :
    ((oneAt n i v).getD j #[]).size = 0 := by
  rw [oneAt_getD]
  have e : (j == i) = false := by simp [h]
  by_cases hj : j < n
  · rw [if_pos hj, e]
    rfl
  · rw [if_neg hj]
    rfl

theorem oneAt_size_le (n i : Nat) (v : Array E) (j : Nat) :
    ((oneAt n i v).getD j #[]).size ≤ v.size := by
  rw [oneAt_getD]
  by_cases hj : j < n
  · rw [if_pos hj]
    by_cases e : (j == i) = true
    · rw [if_pos e]
      exact Nat.le_refl _
    · rw [if_neg e]
      exact Nat.zero_le _
  · rw [if_neg hj]
    exact Nat.zero_le _

/-- A sample row has a main form at one member only, and that form is this member's (`B.sample`). -/
theorem samplesGo_mem (B : Blocks) (P : Par) (n : Nat) (z : List E) (beta : E) :
    ∀ (ms : List Mem) (i : Nat) (ys : List E) (R : MRow), R ∈ samplesGo B P n z beta ms i ys →
      ∃ (k : Nat) (mem : Mem) (y : E),
        ms[k]? = some mem ∧ R.main = oneAt n (i + k) (B.sample P.fld P.C.l P.Z.l mem z beta y).1
  | [], _, _, _, h => by cases h
  | m :: ms, i, ys, R, h => by
      unfold samplesGo at h
      by_cases hs : m.sampled = true
      · rw [if_pos hs] at h
        cases ys with
        | nil => cases h
        | cons y ys' =>
            simp only [List.mem_cons] at h
            rcases h with h | h
            · exact ⟨0, m, y, rfl, by rw [h]; rfl⟩
            · obtain ⟨k, mem, y', h1, h2⟩ := samplesGo_mem B P n z beta ms (i + 1) ys' R h
              exact ⟨k + 1, mem, y', h1, by rw [h2, Nat.add_assoc, Nat.add_comm 1 k]⟩
      · rw [if_neg hs] at h
        obtain ⟨k, mem, y', h1, h2⟩ := samplesGo_mem B P n z beta ms (i + 1) ys R h
        exact ⟨k + 1, mem, y', h1, by rw [h2, Nat.add_assoc, Nat.add_comm 1 k]⟩

theorem samples_size (B : Blocks) (P : Par) (m : Nat) (z : List E) (beta : E)
    (ys : List E) (j N : Nat)
    (h : ∀ mem y,
      (memsOf P.links m)[j]? = some mem → (B.sample P.fld P.C.l P.Z.l mem z beta y).1.size ≤ N) :
    ∀ R ∈ samplesM B P m z beta ys, (R.main.getD j #[]).size ≤ N := by
  intro R hR
  obtain ⟨k, mem, y, h1, h2⟩ := samplesGo_mem B P _ z beta _ 0 ys R hR
  rw [h2, Nat.zero_add]
  by_cases e : j = k
  · subst e
    exact Nat.le_trans (oneAt_size_le _ _ _ _) (h mem y h1)
  · rw [oneAt_size_ne _ _ _ _ e]
    exact Nat.zero_le _

/-! ## A sampled member's cube is within the shared point -/

theorem foldmax_ge (g : Mem → Nat) :
    ∀ (l : List Mem) (a : Nat),
      a ≤ l.foldl (fun a m => max a (g m)) a ∧ ∀ x ∈ l, g x ≤ l.foldl (fun a m => max a (g m)) a
  | [], a => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | y :: l, a => by
      have ih := foldmax_ge g l (max a (g y))
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) ih.1, fun x hx => ?_⟩
      rcases List.mem_cons.1 hx with e | e
      · rw [e]
        exact Nat.le_trans (Nat.le_max_right _ _) ih.1
      · exact ih.2 x e

theorem cube_le (a b : Nat) (ms : List Mem) (mem : Mem) (h : mem ∈ ms) (hs : mem.sampled = true) :
    cubeOf a b mem ≤ seedLen a b ms :=
  (foldmax_ge (cubeOf a b) (ms.filter (·.sampled)) 0).2 mem (List.mem_filter.2 ⟨h, hs⟩)

/-! ## The toy's groups -/

theorem memsOf_mid (L m : Nat) (h1 : 2 ≤ m) (h2 : m ≤ L) :
    memsOf L m = [memG, memP false, memB m, memP (decide (m < L))] := by
  unfold memsOf
  have e : (m == 1) = false := by simp; omega
  rw [e]
  simp [h2]

theorem memsOf_last (L m : Nat) (h1 : 2 ≤ m) (h2 : L < m) : memsOf L m = [memG] := by
  unfold memsOf
  have e : (m == 1) = false := by simp; omega
  rw [e]
  simp
  omega

/-! ## What the frame's test on sizes gives -/

structure Ok (P : Par) : Prop where
  hL : 1 ≤ P.links
  hl : P.C.l = 2 ^ Nat.log2 P.C.l
  hz : P.Z.l = 2 ^ Nat.log2 P.Z.l
  h2 : 2 ≤ Nat.log2 P.C.l

theorem ok_of (B : Blocks) (P : Par) (h : sizesOK B P = true) : Ok P := by
  unfold sizesOK at h
  simp only [Bool.and_eq_true] at h
  have q := h.1.1.1.1.1.1.1.1.1
  exact ⟨of_decide_eq_true q.1.1.1, by simpa [lg] using q.1.1.2,
    by simpa [lg] using q.1.2, by simpa [lg] using q.2⟩

theorem Ok.four {P : Par} (o : Ok P) : 4 ≤ P.C.l := by
  rw [o.hl]
  show 2 ^ 2 ≤ _
  exact Nat.pow_le_pow_right (by decide) o.h2

theorem Ok.hV {P : Par} (o : Ok P) : P.C.l = 2 ^ (P.V + 1) := by
  have e : P.V + 1 = Nat.log2 P.C.l := by
    unfold Par.V
    have := o.h2
    omega
  rw [e]
  exact o.hl

/-! ## The rows in front -/

theorem frontRows_form (B : Blocks) (P : Par) (kept : Bool) (w : Wait) :
    ∃ X : List LRow,
      frontRows B P kept w = B.carried P.fld P.C P.Z kept w.S :: X ∧
      ∀ r ∈ X, ∃ Q y, r = B.oldRow P.fld P.C P.Z Q y := by
  unfold frontRows
  split
  · exact ⟨_, rfl, fun r hr => ⟨_, _, by simpa using hr⟩⟩
  · exact ⟨[], rfl, fun r hr => by cases hr⟩

theorem pscM_mid (P : Par) (m : Nat) (F : Form3 × Form3 × Form3) (h : (m == 1) = false) :
    pscM P m F =
      [⟨oneAt (memsOf P.links m).length 3 F.1.1,
          oneAt (memsOf P.links m).length 2 F.1.2.1,
          F.1.2.2⟩,
        ⟨oneAt (memsOf P.links m).length 1 F.2.1.1,
          oneAt (memsOf P.links m).length 2 F.2.1.2.1,
          F.2.1.2.2⟩,
        ⟨oneAt (memsOf P.links m).length 2 F.2.2.1,
          oneAt (memsOf P.links m).length 2 F.2.2.2.1,
          F.2.2.2.2⟩] := by
  unfold pscM
  simp [h]

theorem clogG : clog memG.rows = 1 := by decide
theorem clogP (k : Bool) : clog (memP k).rows = 0 := by cases k <;> decide

/-- The sum in front of the draws has its tables' sizes, at a link after the first: under `Ok P`,
for a shared point of the length that `readFirst` gives (`hz`) and three rows made at V challenges
(`hF`). -/
theorem sizes_mid (P : Par) (o : Ok P) (m : Nat) (h1 : 2 ≤ m) (h2 : m ≤ P.links) (w : Wait)
    (z : List E) (beta : E) (ys : List E)
    (hz : z.length = seedLen (lg P.C.l) (lg P.Z.l) (memsOf P.links m)) (F : Form3 × Form3 × Form3)
    (hF : ∃ (zeta : List E) (mu : E) (qs : List (E × E)) (p v : E × E) (eps : E)
          (gamma : List E) (bY : E),
        gamma.length = P.V ∧ F = blocks.psc P.fld P.V P.C.l P.Z.l zeta mu qs p v eps gamma bY)
    (theta : E) :
    ((frontSum P m w (pscM P m F ++ samplesM blocks P m z beta ys) theta).1.main.getD 0 #[]).size =
      2 * P.C.l ∧
    ((frontSum P m w (pscM P m F ++ samplesM blocks P m z beta ys) theta).1.main.getD 1 #[]).size =
      P.C.l := by
  have hms := memsOf_mid P.links m h1 h2
  have hn : (memsOf P.links m).length = 4 := by rw [hms]; rfl
  have hk : decide (m - 1 < P.links) = true := decide_eq_true (by omega)
  have hm1 : (m == 1) = false := by simp; omega
  obtain ⟨X, hX, hXr⟩ := frontRows_form blocks P (decide (m - 1 < P.links)) w
  obtain ⟨zeta, mu, qs, p, v, eps, gamma, bY, hg, rfl⟩ := hF
  have hpsc := size_psc_main P.fld P.V P.C.l P.Z.l zeta mu qs p v eps gamma bY hg o.hV
  unfold frontSum
  rw [hX, List.map_cons, List.cons_append]
  constructor
  · apply size_sum
    · rw [toM_main, if_pos (by omega)]
      exact size_carried_g _ _ _ _ _
    · intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hR
        obtain ⟨Q, y, rfl⟩ := hXr r hr
        rw [toM_main, if_pos (by omega)]
        exact Nat.le_of_eq (size_oldSample_g _ _ _ _ _)
      · rcases List.mem_append.1 hR with hR | hR
        · rw [pscM_mid P m _ hm1] at hR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with rfl | rfl | rfl
          · rw [oneAt_size_ne _ _ _ _ (by omega)]; exact Nat.zero_le _
          · rw [oneAt_size_ne _ _ _ _ (by omega)]; exact Nat.zero_le _
          · rw [oneAt_size_ne _ _ _ _ (by omega)]; exact Nat.zero_le _
        · refine samples_size blocks P m z beta ys 0 _ (fun mem y hmem => ?_) R hR
          rw [hms] at hmem
          have e : memG = mem := Option.some.inj hmem
          subst e
          show (sampleOf P.fld P.C.l P.Z.l memG z beta y).1.size ≤ _
          rw [size_sample_main _ _ _ _ _ _ _ o.hl
                (by rw [hz, hms]; exact cube_le _ _ _ _ (by simp) rfl), clogG]
          omega
  · apply size_sum
    · rw [toM_main, if_pos (by omega)]
      show (carried P.fld P.C P.Z _ w.S).p.size = _
      rw [size_carried_p, hk]
      rfl
    · intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hR
        obtain ⟨Q, y, rfl⟩ := hXr r hr
        rw [toM_main, if_pos (by omega)]
        exact Nat.le_of_eq (size_oldSample_p _ _ _ _ _)
      · rcases List.mem_append.1 hR with hR | hR
        · rw [pscM_mid P m _ hm1] at hR
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hR
          rcases hR with rfl | rfl | rfl
          · rw [oneAt_size_ne _ _ _ _ (by omega)]; exact Nat.zero_le _
          · exact Nat.le_trans (oneAt_size_le _ _ _ _) (Nat.le_of_eq hpsc.2.1)
          · rw [oneAt_size_ne _ _ _ _ (by omega)]; exact Nat.zero_le _
        · refine samples_size blocks P m z beta ys 1 _ (fun mem y hmem => ?_) R hR
          rw [hms] at hmem
          have e : memP false = mem := Option.some.inj hmem
          subst e
          show (sampleOf P.fld P.C.l P.Z.l (memP false) z beta y).1.size ≤ _
          rw [size_sample_main _ _ _ _ _ _ _ o.hl
                (by rw [hz, hms]; exact cube_le _ _ _ _ (by simp) rfl), clogP]
          omega

/-- The same at the last group, which has one member: the second size is 0. -/
theorem sizes_last (P : Par) (o : Ok P) (w : Wait) (z : List E) (beta : E) (ys : List E)
    (hz : z.length = seedLen (lg P.C.l) (lg P.Z.l) (memsOf P.links (P.links + 1))) (theta : E) :
    ((frontSum P (P.links + 1) w (samplesM blocks P (P.links + 1) z beta ys) theta).1.main.getD
        0 #[]).size = 2 * P.C.l ∧
    ((frontSum P (P.links + 1) w (samplesM blocks P (P.links + 1) z beta ys) theta).1.main.getD
        1 #[]).size = 0 := by
  have hms := memsOf_last P.links (P.links + 1) (by have := o.hL; omega) (by omega)
  have hn : (memsOf P.links (P.links + 1)).length = 1 := by rw [hms]; rfl
  obtain ⟨X, hX, hXr⟩ := frontRows_form blocks P (decide (P.links + 1 - 1 < P.links)) w
  unfold frontSum
  rw [hX, List.map_cons, List.cons_append]
  constructor
  · apply size_sum
    · rw [toM_main, if_pos (by omega)]
      exact size_carried_g _ _ _ _ _
    · intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hR
        obtain ⟨Q, y, rfl⟩ := hXr r hr
        rw [toM_main, if_pos (by omega)]
        exact Nat.le_of_eq (size_oldSample_g _ _ _ _ _)
      · refine samples_size blocks P _ z beta ys 0 _ (fun mem y hmem => ?_) R hR
        rw [hms] at hmem
        have e : memG = mem := Option.some.inj hmem
        subst e
        show (sampleOf P.fld P.C.l P.Z.l memG z beta y).1.size ≤ _
        rw [size_sample_main _ _ _ _ _ _ _ o.hl
              (by rw [hz, hms]; exact cube_le _ _ _ _ (by simp) rfl), clogG]
        omega
  · apply size_sum
    · rw [toM_main, if_neg (by omega)]
      rfl
    · intro R hR
      rcases List.mem_append.1 hR with hR | hR
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hR
        rw [toM_main, if_neg (by omega)]
        exact Nat.le_refl _
      · refine samples_size blocks P _ z beta ys 1 _ (fun mem y hmem => ?_) R hR
        rw [hms] at hmem
        cases hmem

/-! ## At every closing that the frame makes, the fast closing is its meaning -/

theorem call_first (P : Par) (V : M1.View) (m : Nat) (F : Form3 × Form3 × Form3)
    (S : List MRow) (theta : E) :
    batch blocks P V m none (pscM P m F ++ S) theta =
      batchLit blocks drawL P V m none (pscM P m F ++ S) theta :=
  batch_none blocks drawL P V m _ theta (by unfold pscM; simp)

theorem call_mid (P : Par) (o : Ok P) (V : M1.View) (m : Nat) (h1 : 2 ≤ m) (h2 : m ≤ P.links)
    (w : Wait) (z : List E) (beta : E) (ys : List E)
    (hz : z.length = seedLen (lg P.C.l) (lg P.Z.l) (memsOf P.links m)) (F : Form3 × Form3 × Form3)
    (hF : ∃ (zeta : List E) (mu : E) (qs : List (E × E)) (p v : E × E) (eps : E)
          (gamma : List E) (bY : E),
        gamma.length = P.V ∧ F = blocks.psc P.fld P.V P.C.l P.Z.l zeta mu qs p v eps gamma bY)
    (theta : E) :
    batch blocks P V m (some w) (pscM P m F ++ samplesM blocks P m z beta ys) theta =
      batchLit blocks drawL P V m (some w) (pscM P m F ++ samplesM blocks P m z beta ys) theta := by
  have hs := sizes_mid P o m h1 h2 w z beta ys hz F hF theta
  have hk : decide (m - 1 < P.links) = true := decide_eq_true (by omega)
  exact batch_some P V m w _ theta (by rw [memsOf_mid P.links m h1 h2]; exact Nat.succ_pos _)
    (fun _ => by have := o.four; omega) hs.1 (by rw [hs.2, hk]; rfl)

theorem call_last (P : Par) (o : Ok P) (V : M1.View) (w : Wait) (z : List E) (beta : E)
    (ys : List E) (hz : z.length = seedLen (lg P.C.l) (lg P.Z.l) (memsOf P.links (P.links + 1)))
    (theta : E) :
    batch blocks P V (P.links + 1) (some w) (samplesM blocks P (P.links + 1) z beta ys) theta =
      batchLit blocks drawL P V (P.links + 1) (some w)
        (samplesM blocks P (P.links + 1) z beta ys) theta := by
  have hs := sizes_last P o w z beta ys hz theta
  have hk : decide (P.links + 1 - 1 < P.links) = false := decide_eq_false (by omega)
  exact batch_some P V _ w _ theta
    (by rw [memsOf_last P.links _ (by have := o.hL; omega) (by omega)]; decide)
    (fun _ => by have := o.four; omega) hs.1 (by rw [hs.2, hk]; rfl)

/-! ## Through the links -/

theorem links_eq (P : Par) (o : Ok P) (V : M1.View) :
    ∀ (todo m : Nat) (prev : Option (KSRow × Option (Array E × E))) (rs : Rs) (log : List E), m +
          todo = P.links + 1 →
      1 ≤ m → (prev = none ↔ m = 1) →
      goLinks blocks P V (batch blocks P V) todo m prev rs log =
        goLinks blocks P V (batchLit blocks drawL P V) todo m prev rs log
  | 0, _, _, _, _, _, _, _ => rfl
  | todo + 1, m, prev, rs, log, hm, h1, hp => by
      unfold goLinks
      cases e1 : readFirst P m rs with
      | none => rfl
      | some x1 =>
          obtain ⟨z, beta, ys, xs, rs2⟩ := x1
          simp only
          cases e2 : readSub blocks P rs2 with
          | none => rfl
          | some x2 =>
              obtain ⟨F, rs3⟩ := x2
              simp only
              have hz := readFirst_len P m rs z beta ys xs rs2 e1
              have hF := readSub_some blocks P rs2 F rs3 e2
              have call : ∀ theta,
                  batch blocks P V m (prev.map fun S => ⟨S.1, xs, S.2⟩)
                      (pscM P m F ++ samplesM blocks P m z beta ys) theta =
                    batchLit blocks drawL P V m (prev.map fun S => ⟨S.1, xs, S.2⟩)
                      (pscM P m F ++ samplesM blocks P m z beta ys) theta := by
                intro theta
                cases prev with
                | none => exact call_first P V m F _ theta
                | some S =>
                    have hne : m ≠ 1 := fun e => by
                      have := hp.2 e
                      cases this
                    exact call_mid P o V m (by omega) (by omega) _ z beta ys hz F hF theta
              split
              · rw [call]
                split
                · split
                  · split
                    · exact links_eq P o V todo (m + 1) _ _ _ (by omega) (by omega)
                        ⟨fun h => (by cases h), fun h => (by omega)⟩
                    · rfl
                  · rfl
                · rfl
              · rfl

def Spec.dec_eq : Prop := ∀ (P : Par) (V : M1.View), decWith blocks P V = decLit blocks drawL P V

/-- Proves `Spec.dec_eq`: the decision that runs is the decision with every row of every closing
written out. -/
theorem dec_eq : Spec.dec_eq := by
  intro P V
  unfold decWith decLit decBy
  cases hs : sizesOK blocks P with
  | false => rfl
  | true =>
      have o := ok_of blocks P hs
      rw [links_eq P o V P.links 1 none V.rounds [] (by omega)
          (Nat.le_refl _) ⟨fun _ => rfl, fun _ => rfl⟩]
      simp only [Bool.true_and]
      split
      · rename_i S rs lg0 _
        cases e1 : readFirst P (P.links + 1) rs with
        | none => rfl
        | some x1 =>
            obtain ⟨z, beta, ys, xs, rs2⟩ := x1
            simp only
            have hz := readFirst_len P _ rs z beta ys xs rs2 e1
            split
            · rw [call_last P o V _ z beta ys hz]
            · rfl
      · rfl

end Fmt.M2.DecEq
