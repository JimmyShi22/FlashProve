-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/HeadLookMet.lean: all hypotheses of the theorem on the output head's link can be met
together, the lookup's own claims among them.

The theorem head_link_of_port (Johnson/Road/HeadLinkPort.lean) has a bundle of hypotheses on
integer matrices Mz, a world W and functions fn on the calls' columns.
Johnson/Road/HeadLinkMet.lean shows that the bundle can be met but for two clauses of the
hypothesis ClaimsHold: the lookup's claims that read mask entries alone, and its three claims on
the planes of the counts. This file meets these two beside the rest: for a true request for the
next token and a run of the verifier's routines on it there are Mz, W and fn that meet all of it
(link_met_all), and head_link_of_port applies to them (link_met_fits).

How.
 1. The lookup's claims that read mask entries alone are claims that sumchecks leave. Each has a
    slot of its own, and they can be met in the order of their slots by a change of slots that no
    other hypothesis speaks of (hear_rows and chain_solve, Johnson/Road/HeadRowForm.lean).
 2. The first claim on the planes is the claim of the leaves' sumcheck: the same. The second says
    what the slot of the bits' end value holds: that slot is free. The third has no slot: the counts
    add up to the number of keys that are not padding. It is met by the entries: matsB has, for the
    matrix of the counts, the 32 bits of that number in the first column (count_zero, over pin_read:
    the table "bH-pin" is true of that matrix).
 3. The three forms on the planes are named through a routine and a state. They are written out
    (planes_of): they depend on the run and on the number of columns of the array of the reads
    alone, so one choice of slots serves every state of the walk (planes_spec).
 4. The rest of the bundle is met as in Johnson/Road/HeadLinkMet.lean (linkWorld_of).
 5. A control. The same tools meet all the lookup's claims for any functions on the calls' columns
    and over any cells (premise_free, premise_of_cells), so the lookup's step, which is a hypothesis
    of head_link_of_port, is false in some world (step_fails).

Main definitions: bitsMat, matsB, keysOf, entAt, planeN, atForm, countForm, HeardOrder, baseSlots.
Main theorems: gl_nat, bits_sum; sameZ_matsB, matsB_small; shape_tests, pad_shape, hear_numbers;
foldlM_reads, planes_of; pin_read, bits_column, count_zero, planes_spec; linkWorld_of;
heardOrder_of_hear, solve_heard; link_met_free (the same with any values under the slots of which
head_link_of_port does not speak), link_met_all,
link_met_fits; seg_met_all, seg_met_fits (the same for head_link_seg of
Johnson/Road/HeadLinkSeg.lean, with the hypothesis LentH met by choice); premise_free,
premise_of_cells, step_fails.

What stays a hypothesis in link_met_all: what stays one in link_met of
Johnson/Road/HeadLinkMet.lean, and nothing else: the public side, "the routines succeed" (layout,
planH2, hear on a view, tablesOf), the request of the run is the instance's, the final
normalisation's numbers are lawful, and the request is a true one under the policy 0, 0, 0. That
one run, one index and one instance meet these together (hear returns this record on some view;
the record's request is the instance's; the instance is a true request) is taken, not shown: if
they excluded each other, the witness would be empty.

What is not claimed. The world is made for the hypotheses: it is not the world of a prover's
messages. The matrix of the counts does not hold the counts of the keys: it holds one number that
has the right sum, and the two product trees of the lookup are not computed; their claims are met
by the slots of the hiding polynomials. So this is a witness that the hypotheses do not exclude
each other, and no more. Read the other way round, the tools show that for a world whose slots are
chosen after the challenges the named claims exclude nothing (point 5): that a prover cannot reach
such a world is a matter of the order of commitments and draws, which no statement here holds. The
claims of the sub-proof that head_link_of_port does not name are not looked at. That the walk
succeeds is a hypothesis of link_met_fits alone. Nothing on what a verifier's acceptance shows.
The program does not import this file.
-/
import Johnson.Road.HeadLinkMet
import Johnson.Road.HeadRowForm

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM Row5)

/-! ## 1. Words and bits -/

/-- A word reads as its number. -/
theorem gl_word (w : UInt64) : Reading.gl.val (ofF w) = ((w.toNat : ℕ) : Cb.Gl.E) := by
  show Slice.toE (ofF w).triple = _
  rw [ofF_triple, Slice.toE_ofF]
  unfold Slice.toF
  rw [map_natCast]

/-- The word of a number below 2^64 reads as the number. -/
theorem gl_nat {n : ℕ} (h : n < 2 ^ 64) : Reading.gl.val (ofF n.toUInt64) = (n : Cb.Gl.E) := by
  have e : n.toUInt64.toNat = n := UInt64.toNat_ofNat_of_lt' h
  rw [gl_word, e]

/-- The low k bits of a number, each with its weight, add up to the number modulo 2^k. -/
theorem bits_sum (N : ℕ) : ∀ k, ∑ i ∈ range k, 2 ^ i * (N / 2 ^ i % 2) = N % 2 ^ k
  | 0 => by simp [Nat.mod_one]
  | k + 1 => by rw [Finset.sum_range_succ, bits_sum N k, Nat.mod_pow_succ]

/-! ## 2. Matrices with a matrix of counts -/

/-- A matrix that holds the low 32 bits of N in its first column, bit r in row r, and 0
elsewhere. -/
def bitsMat (N r c : ℕ) : ℤ := if c = 0 ∧ r < 32 then ((N / 2 ^ r % 2 : ℕ) : ℤ) else 0

/-- The matrices matsFrom of Johnson/Road/HeadLinkMet.lean, with bitsMat N for matrix number 6, the
planes of the lookup's counts. -/
def matsB (tz : Head.Cells ℤ) (N a r c : ℕ) : ℤ :=
  if a = 6 then bitsMat N r c else matsFrom tz a r c

/-- If the cells are small, all entries of these matrices are below 2^18 in absolute value. -/
theorem matsB_small {tz : Head.Cells ℤ} (hS : Head.Small tz) (N a r c : ℕ) :
    |matsB tz N a r c| < 2 ^ 18 := by
  unfold matsB
  by_cases h : a = 6
  · rw [if_pos h]
    unfold bitsMat
    by_cases h2 : c = 0 ∧ r < 32
    · rw [if_pos h2]
      have k : N / 2 ^ r % 2 < 2 := Nat.mod_lt _ (by norm_num)
      rw [abs_of_nonneg (by positivity)]
      have k' : ((N / 2 ^ r % 2 : ℕ) : ℤ) < 2 := by exact_mod_cast k
      linarith
    · rw [if_neg h2]
      norm_num
  · rw [if_neg h]
    exact matsFrom_small hS a r c

section Cells

variable {h : Model.Head.Shape} {L : Model.Head.HL} {b : Model.Head.Border}

/-- The cells that the verifier's rule reads in these matrices are the cells tz: no cell is read in
matrix number 6. -/
theorem sameZ_matsB (Nu : NumH h L) (Bd : BorderH b) (tz : Head.Cells ℤ) (N : ℕ) :
    Policy.SameMain (cellsH h L b (matsB tz N)) tz where
  hf := fun φ hφ i hi => by
    have hφ' : φ < 1232768 := hφ
    show cellIn (matsB tz N) 0 L.k (L.m / h.T) h.T φ i = tz.hf φ i
    rw [Nu.k, Nu.fc, Nu.T]
    show matsB tz N (0 + φ / 64 / 4816) (φ % 64 * 1024 + i) (φ / 64 % 4816) = tz.hf φ i
    have h6 : ¬ 0 + φ / 64 / 4816 = 6 := by omega
    unfold matsB
    rw [if_neg h6]
    exact matsFrom_at_hf tz hφ hi
  hd := fun φ hφ i hi => by
    have hφ' : φ < 10240 := hφ
    show cellIn (matsB tz N) h.NHf L.kD (L.mD / h.T) h.T φ i = tz.hd φ i
    rw [Nu.NHf, Nu.kD, Nu.fcD, Nu.T]
    show matsB tz N (4 + φ / 16 / 640) (φ % 16 * 1024 + i) (φ / 16 % 640) = tz.hd φ i
    have h6 : ¬ 4 + φ / 16 / 640 = 6 := by omega
    unfold matsB
    rw [if_neg h6]
    exact matsFrom_at_hd tz hφ hi
  hr := fun φ hφ i hi => by
    have hφ' : φ < 120 := hφ
    show cellIn (matsB tz N) (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i = tz.hr φ i
    rw [Nu.NHf, Nu.kR, Nu.fcR, Nu.T]
    show matsB tz N (4 + 1 + φ / 8 / 15) (φ % 8 * 1024 + i) (φ / 8 % 15) = tz.hr φ i
    have h6 : ¬ 4 + 1 + φ / 8 / 15 = 6 := by omega
    unfold matsB
    rw [if_neg h6]
    exact matsFrom_at_hr tz hφ hi
  x := fun φ hφ i hi => by
    have hφ' : φ < 25600 := hφ
    show cellIn (matsB tz N) (h.NHf + 3) b.kxb (b.mxb / h.T) h.T (b.cell (φ / h.d) (φ % h.d)) i =
      tz.x φ i
    rw [Nu.NHf, Bd.kxb, Nu.T, Bd.fc, Nu.d, Bd.cell]
    have e : fX (φ / 5120) (φ % 5120) = φ := by
      show 5120 * (φ / 5120) + φ % 5120 = φ
      exact Nat.div_add_mod φ 5120
    rw [e]
    show matsB tz N (4 + 3 + φ / 64 / 400) (φ % 64 * 1024 + i) (φ / 64 % 400) = tz.x φ i
    have h6 : ¬ 4 + 3 + φ / 64 / 400 = 6 := by omega
    unfold matsB
    rw [if_neg h6]
    exact matsFrom_at_x tz hφ hi

/-- Cells that agree over the integers agree when cells and entries are read in a ring. -/
theorem sameMain_cast {K : Type} [CommRing K] {Mz : Mats ℤ} {tz : Head.Cells ℤ}
    (S : Policy.SameMain (cellsH h L b Mz) tz) :
    Policy.SameMain (cellsH h L b fun a r c => ((Mz a r c : ℤ) : K)) (tz.cast K) :=
  ⟨fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.hf φ hφ i hi),
    fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.hd φ hφ i hi),
    fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.hr φ hφ i hi),
    fun φ hφ i hi => congrArg (fun z : ℤ => (z : K)) (S.x φ hφ i hi)⟩

end Cells

/-! ## 3. Numbers of the lookup -/

/-- Three tests of Forest.shape: there is a call; a tree has depth ten at least; there are fewer
than 2^32 keys. -/
theorem shape_tests {calls : Array Model.Call} {lid : ℕ} {fo : Model.Forest.Shape}
    (h : Model.Forest.shape calls lid = .ok fo) : 1 ≤ fo.NC ∧ fo.dT + fo.rK < 32 := by
  unfold Model.Forest.shape at h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨e1, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨e4, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r, -, h⟩ := ok_of_bind h
  obtain ⟨callOf, first, free⟩ := r
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  refine ⟨?_, Nat.not_le.mp e4⟩
  show 1 ≤ calls.size
  by_contra hc
  exact e1 (by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl (by omega))

/-- The numbers that the lookup's routine keeps are those of Forest.shape, with the numbers of
padding keys filled in. -/
theorem pad_shape {calls : Array Model.Call} {pub : Array ℕ} {lid : ℕ} {F G : Fork} {C D : Ctx}
    {g : Model.Forest.Heard} (h : Ok (Model.Forest.pad calls pub lid) F C g G D) :
    ∃ h0, Model.Forest.shape calls lid = .ok h0 ∧ g.shape = { h0 with pub := pub } := by
  unfold Model.Forest.pad at h
  obtain ⟨h0, _, _, k, h⟩ := bind_ok h
  obtain ⟨e0, -, -⟩ := subGet_ok k
  obtain ⟨_, _, _, -, h⟩ := bind_ok h
  obtain ⟨slot0, _, _, -, h⟩ := bind_ok h
  obtain ⟨o1, _, _, -, h⟩ := bind_ok h
  obtain ⟨o2, _, _, -, h⟩ := bind_ok h
  obtain ⟨o3, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨theta, alpha, a⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨t, _, _, -, h⟩ := bind_ok h
  obtain ⟨keys, _, _, -, h⟩ := bind_ok h
  obtain ⟨table, _, _, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨leaves, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨zb0, leaves'⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨r5, _, _, -, h⟩ := bind_ok h
  obtain ⟨bits, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨zb1, bits'⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨sBit, bits''⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨vBit, _, _, -, h⟩ := bind_ok h
  obtain ⟨⟨bitsRow, p'⟩, _, _, -, h⟩ := bind_ok h
  obtain ⟨s, _, _, -, h⟩ := bind_ok h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨-, h⟩ := must_bind h
  obtain ⟨rfl, -, -⟩ := pure_ok h
  exact ⟨h0, ok_of_toOption e0, rfl⟩

/-- The number of keys that are not padding, in what was heard. -/
def keysOf (R : Model.Head.Run) : ℕ := 2 ^ R.x.g1.shape.v - R.x.g1.shape.padding

/-- In what hear returns there is a call, and the number of keys is below 2^32. -/
theorem hear_numbers {R : Model.Head.Run} {plain : Array E} {F G : Fork} {C D : Ctx}
    (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F C R.x G D) :
    1 ≤ R.x.g1.shape.NC ∧ keysOf R < 2 ^ 32 := by
  obtain ⟨yTok, F1, C1, F2, C2, g1, F3, C3, Zl, F4, C4, PV, F5, C5, sW, gp, wpl, F6, C6, sPv, omV,
    tV, F7, C7, qN, qH, tN, F8, C8, tH, rs, F9, C9, _, _, k3, _, _, _, _, _, _, _, _, _, ex⟩ :=
    hear_steps hx
  obtain ⟨h0, e1, e2⟩ := pad_shape k3
  obtain ⟨t1, t2⟩ := shape_tests e1
  have eg : R.x.g1 = g1 := by rw [ex]
  unfold keysOf
  rw [eg, e2]
  refine ⟨t1, ?_⟩
  have k1 : (2 : ℕ) ^ (h0.dT + h0.rK) < 2 ^ 32 := Nat.pow_lt_pow_right (by norm_num) t2
  show 2 ^ (h0.dT + h0.rK) - _ < 2 ^ 32
  omega

/-! ## 4. The three forms on the planes, written out -/

/-- The form that names entry x of the table of the reads that begins at entry t, if the array of
the reads has K3 columns. -/
def entAt (R : Model.Head.Run) (K3 t x : ℕ) : Aff :=
  Aff.ent R.iU3 ((t + x) / K3) ((t + x) % K3)

/-- An entry of a table on the matrix of the counts: the routine leaves state and context. -/
theorem planeCol_ok {R : Model.Head.Run} {t x : ℕ} {F G : Fork} {C D : Ctx} {a : Aff}
    (h : Ok (planeCol R t x) F C a G D) :
    G = F ∧ D = C ∧ a = entAt R (colsOf F R.iU3) t x ∧ (Valid R t x ∧ x < R.L.kb) := by
  unfold planeCol at h
  obtain ⟨hb, h⟩ := must_bind h
  obtain ⟨e1, e2, e3, e4⟩ := ok_U3at h
  exact ⟨e1, e2, e3, e4, of_decide_eq_true hb⟩

/-- A loop whose steps read a form by a routine that leaves state and context, and go on with a
function of it: the loop leaves both, and returns the fold of the function over the forms. -/
theorem foldlM_reads (m : ℕ → SubM Aff) (v : ℕ → Aff) (st : Aff → Aff → ℕ → Aff) (P : ℕ → Prop)
    (F : Fork) (C : Ctx)
    (hm : ∀ col x G D, Ok (m col) F C x G D → G = F ∧ D = C ∧ x = v col ∧ P col) :
    ∀ (l : List ℕ) (f0 a : Aff) (G : Fork) (D : Ctx),
      Ok (l.foldlM (fun f col => m col >>= fun x => pure (st f x col)) f0) F C a G D →
      G = F ∧ D = C ∧ a = l.foldl (fun f col => st f (v col) col) f0 ∧ ∀ col ∈ l, P col
  | [], f0, a, G, D, h => by
    rw [List.foldlM_nil] at h
    obtain ⟨e1, e2, e3⟩ := pure_ok h
    exact ⟨e2, e3, e1, fun _ hc => by cases hc⟩
  | c :: l, f0, a, G, D, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨f1, F1, C1, h1, h2⟩ := bind_ok h
    obtain ⟨x, F2, C2, k1, k2⟩ := bind_ok h1
    obtain ⟨a1, a2, a3, p⟩ := hm c x F2 C2 k1
    obtain ⟨b1, b2, b3⟩ := pure_ok k2
    rw [b1, b2, b3, a1, a2, a3] at h2
    obtain ⟨e1, e2, e3, e4⟩ := foldlM_reads m v st P F C hm l _ a G D h2
    refine ⟨e1, e2, e3, fun col hc => ?_⟩
    rcases List.mem_cons.mp hc with r | r
    · rw [r]
      exact p
    · exact e4 col r

/-- The number of columns of the matrix of the counts that the lookup reads. -/
def planeN (R : Model.Head.Run) : ℕ :=
  R.x.g1.shape.NC * 2 ^ (R.x.g1.shape.kT + 5 - R.h.lmbH)

/-- The planes' value at the point zb e, as a form on the table that begins at t. -/
def atForm (R : Model.Head.Run) (K3 e t : ℕ) : Aff :=
  (List.range (planeN R)).foldl
    (fun (f : Aff) col => Aff.addMul f (entAt R K3 t col)
      (mulE
        ((Model.eqTab ((R.x.g1.zb e).extract R.x.g1.shape.kT
          (R.x.g1.shape.kT + R.x.g1.shape.cK))).getD
            (col / 2 ^ (R.x.g1.shape.kT + 5 - R.h.lmbH)) zeroE)
        ((Model.eqTab ((R.x.g1.zb e).extract 0 (R.x.g1.shape.kT + 5 - R.h.lmbH))).getD
            (col % 2 ^ (R.x.g1.shape.kT + 5 - R.h.lmbH)) zeroE)))
    (Aff.ofConst zeroE)

/-- The sum of the counts less the number of keys, as a form on the table that begins at t. -/
def countForm (R : Model.Head.Run) (K3 t : ℕ) : Aff :=
  (List.range (planeN R)).foldl (fun (f : Aff) col => f + entAt R K3 t col)
    (Aff.ofConst (negE (ofF (keysOf R).toUInt64)))

/-- The routine planesAt, with reads in the table that begins at t, leaves state and context and
returns the form atForm. -/
theorem planesAt_ok {R : Model.Head.Run} {e t : ℕ} {bit : ℕ → ℕ → SubM Aff}
    {F G : Fork} {C D : Ctx} {a : Aff}
    (h : Ok (Model.Forest.planesAt R.x.g1 R.h.lmbH e bit) F C a G D)
    (hbit : ∀ col, bit e col = planeCol R t col) :
    G = F ∧ D = C ∧ a = atForm R (colsOf F R.iU3) e t := by
  unfold Model.Forest.planesAt at h
  try dsimp only at h
  obtain ⟨e1, e2, e3, _⟩ := foldlM_reads (fun col => bit e col)
    (fun col => entAt R (colsOf F R.iU3) t col)
    (fun f x col => Aff.addMul f x
      (mulE
        ((Model.eqTab ((R.x.g1.zb e).extract R.x.g1.shape.kT
          (R.x.g1.shape.kT + R.x.g1.shape.cK))).getD
            (col / 2 ^ (R.x.g1.shape.kT + 5 - R.h.lmbH)) zeroE)
        ((Model.eqTab ((R.x.g1.zb e).extract 0 (R.x.g1.shape.kT + 5 - R.h.lmbH))).getD
            (col % 2 ^ (R.x.g1.shape.kT + 5 - R.h.lmbH)) zeroE)))
    (fun col => Valid R t col ∧ col < R.L.kb) F C
    (fun col x G D hk => by
      have hk' : Ok (bit e col) F C x G D := hk
      rw [hbit] at hk'
      exact planeCol_ok hk') _ _ _ _ _ h
  exact ⟨e1, e2, e3⟩

/-- The claim that pscRow returns is Psc.rowForm. -/
theorem pscRow_form {p : Model.Psc} {S0 : E} {kept : Aff} {x : Aff × Model.Psc} {F G : Fork}
    {C D : Ctx} (h : Ok (Model.pscRow p S0 kept) F C x G D) : x.1 = p.rowForm S0 kept := by
  unfold Model.pscRow at h
  rw [ok_bind] at h
  obtain ⟨_, F1, C1, h1, h⟩ := h
  rw [ok_bind] at h
  obtain ⟨_, F2, C2, h2, h⟩ := h
  rw [ok_pure] at h
  rw [h.1]

/-- **The three forms on the planes, written out.** They depend on the run and on the number of
columns of the array of the reads alone. With them: the routine pscRow has succeeded on the leaves'
sumcheck; every column that the sum of the counts reads is an entry of its table and a column of the
matrix; and the matrix has 32 rows at least. -/
theorem planes_of {R : Model.Head.Run} {F : Fork} {C : Ctx} {A : Array Aff}
    (h : PlanesOf R F C A) :
    ∃ tB0 tB1 tP, Starts R "bH-bits-0" tB0 ∧ Starts R "bH-bits-1" tB1 ∧ Starts R "bH-pin" tP ∧
      A = #[R.x.g1.leaves.rowForm oneE
              (Aff.scale (atForm R (colsOf F R.iU3) 0 tB0) R.x.g1.leavesA),
            Aff.slot R.x.g1.sBit - atForm R (colsOf F R.iU3) 1 tB1,
            countForm R (colsOf F R.iU3) tP] ∧
      (∃ x F' C' G' D', Ok (Model.pscRow R.x.g1.leaves oneE
        (Aff.scale (atForm R (colsOf F R.iU3) 0 tB0) R.x.g1.leavesA)) F' C' x G' D') ∧
      (∀ col ∈ List.range (planeN R), Valid R tP col ∧ col < R.L.kb) ∧ 5 ≤ R.h.lmbH := by
  obtain ⟨tB0, tB1, tP, G, D, s0, s1, s2, h⟩ := h
  unfold Model.Forest.planeClaims at h
  try dsimp only at h
  obtain ⟨hb, h⟩ := subMust_bind h
  obtain ⟨at0, F1, C1, h1, h⟩ := bind_ok h
  obtain ⟨a1, a2, a3⟩ := planesAt_ok (t := tB0) h1 (fun _ => rfl)
  rw [a1, a2] at h
  obtain ⟨at1, F2, C2, h2, h⟩ := bind_ok h
  obtain ⟨b1, b2, b3⟩ := planesAt_ok (t := tB1) h2 (fun _ => rfl)
  rw [b1, b2] at h
  obtain ⟨cnt, F3, C3, h3, h⟩ := bind_ok h
  obtain ⟨c1, c2, c3, pv⟩ := foldlM_reads (planeCol R tP)
    (fun col => entAt R (colsOf F R.iU3) tP col) (fun f x _ => f + x)
    (fun col => Valid R tP col ∧ col < R.L.kb) F C (fun col x G D hk => planeCol_ok hk)
    _ _ _ _ _ h3
  rw [c1, c2] at h
  obtain ⟨⟨lr, p'⟩, F4, C4, h4, h⟩ := bind_ok h
  obtain ⟨e5, -, -⟩ := pure_ok h
  have e6 : lr = _ := pscRow_form h4
  have h5 : 5 ≤ R.h.lmbH := by
    by_contra hc
    have e : Model.Forest.planeCols R.x.g1.shape R.h.lmbH = .error "forest-planes" := by
      have hcnd : (decide (R.h.lmbH < 5) || decide (R.h.lmbH > R.x.g1.shape.kT + 5)) = true := by
        simp only [Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl (by omega)
      unfold Model.Forest.planeCols
      rw [if_pos hcnd]
      rfl
    rw [e] at hb
    simp [Except.toBool] at hb
  rw [a3] at h4 e6
  refine ⟨tB0, tB1, tP, s0, s1, s2, ?_, ⟨_, _, _, _, _, h4⟩, pv, h5⟩
  rw [e5, e6, b3, c3]
  rfl

/-- A sum of forms under weights, added to a form, reads what they read. -/
theorem below_foldl_addMul {K : Type} [Field K] {ρ : Reading K} (v : ℕ → Aff) (c : ℕ → E) {n : ℕ}
    (hv : ∀ col, Below ρ (v col) n) : ∀ (l : List ℕ) (f0 : Aff), Below ρ f0 n →
    Below ρ (l.foldl (fun f col => Aff.addMul f (v col) (c col)) f0) n
  | [], _, h0 => h0
  | x :: l, f0, h0 => by
    rw [List.foldl_cons]
    exact below_foldl_addMul v c hv l _ (h0.addMul (hv x) (c x))

/-- The forms on the planes' values read no slot. -/
theorem below_atForm {K : Type} [Field K] (ρ : Reading K) (R : Model.Head.Run) (K3 e t n : ℕ) :
    Below ρ (atForm R K3 e t) n :=
  below_foldl_addMul (fun col => entAt R K3 t col) _ (fun _ => below_ent ρ _ _ _ n) _ _
    (below_const ρ _ _)

/-- The value of a sum of forms that is added to a form. -/
theorem foldl_add_value {K : Type} [Field K] (ρ : Reading K) (W : World K) (v : ℕ → Aff) :
    ∀ (l : List ℕ) (f0 : Aff), (l.foldl (fun (f : Aff) col => f + v col) f0).value ρ W =
      f0.value ρ W + (l.map fun col => (v col).value ρ W).sum
  | [], f0 => by simp
  | x :: l, f0 => by
    rw [List.foldl_cons, foldl_add_value ρ W v l, Aff.value_add, List.map_cons, List.sum_cons]
    ring

/-- A sum over the numbers below n of a function that is 0 but at 0. -/
theorem sum_at_zero {K : Type} [Field K] (g : ℕ → K) {n : ℕ} (hn : 0 < n)
    (h : ∀ c, c < n → c ≠ 0 → g c = 0) : ((List.range n).map g).sum = g 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
  have e : ((List.range m).map (g ∘ Nat.succ)).sum = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
    have k := List.mem_range.mp hc
    exact h (c + 1) (by omega) (Nat.succ_ne_zero c)
  rw [e, add_zero]

/-! ## 5. The table of the counts' sum -/

section Pin

variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **The table "bH-pin" is true of matrix number 6**: if every record of the list of tables holds
what it says of its matrix, entry e of that table is the sum of column e of the matrix under the
weights of the rows. The hypotheses are those of trueH_of_holds (Johnson/Road/HeadReads.lean), which
says the like of the twelve tables on cells. -/
theorem pin_read {R : Model.Head.Run} {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ}
    {H0 : Model.Head.HPlanH2} (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM) (N : NumH R.h R.L)
    {F G : Fork} {C D : Ctx}
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F C R.t G D) {tl : Model.HTailF2}
    (hm : tl.mats = R.hp.tl.mats) (hNM : tl.NM = R.hp.tl.NM) {K3 : ℕ} {M : Mats K}
    (H : ∀ Fn ∈ R.t.funs, Holds ρ W tl R.iU3 K3 M Fn) {tb e : ℕ}
    (hs : Starts R "bH-pin" tb) (hv : Valid R tb e) (he : e < R.L.kb) :
    W.entry R.iU3 ((tb + e) / K3) ((tb + e) % K3) =
      ∑ i ∈ range (2 ^ R.h.lmbH),
        ρ.val ((Model.Forest.phiP R.h.lmbH).getD i zeroE) * M 6 i e := by
  obtain ⟨sid, p1, p2⟩ := planH2_mats hpl
  obtain ⟨z0, zf, _⟩ := matsH_at R.L R.b (1 + NGr) sid N.NHf
  have z6 : ((Model.Head.matsH R.h R.L R.b (1 + NGr) sid).getD 6 {}).m = 2 ^ R.h.lmbH ∧
      ((Model.Head.matsH R.h R.L R.b (1 + NGr) sid).getD 6 {}).k = R.L.kb := by
    unfold Model.Head.matsH
    rw [N.NHf]
    exact ⟨rfl, rfl⟩
  rw [← p1, ← hm0, ← hm] at z0 zf z6
  have hN8 : tl.NM = 8 := by rw [hNM, hN0, p2, ← p1, ← hm0, ← hm, z0]
  obtain ⟨ZV, lowN, qFC, qROW, b0, b1, _, _, _, _, -, -, hf⟩ := tables_of_ok ht
  rw [← hm] at hf
  have hn := asksH_names R.h R.L R.x ZV (Model.longPoint lowN.2 R.x.tN.r)
    (Model.Head.costWeights R.cov (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)).1
    (Model.Head.costWeights R.cov (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)).2.2 qFC qROW b0 b1
  have uF : ∀ (phi : Array E) (nm : String),
      Uni tl.mats (0, R.h.NHf, 2 ^ R.h.la, phi, nm) R.L.m R.L.k := by
    intro phi nm q hq
    have hq' : q < 4 := by
      have h0 : q < R.h.NHf := hq
      rw [N.NHf] at h0
      exact h0
    have e := zf q hq'
    rw [← Nat.zero_add q] at e
    exact e
  have uB : Uni tl.mats (R.h.NHf + 1 + 1, 1, 2 ^ R.h.lmbH, Model.Forest.phiP R.h.lmbH, "bH-pin")
      (2 ^ R.h.lmbH) R.L.kb := by
    intro q hq
    have e : q = 0 := by
      have h0 : q < 1 := hq
      omega
    subst e
    show (tl.mats.getD (R.h.NHf + 1 + 1 + 0) {}).m = _ ∧
      (tl.mats.getD (R.h.NHf + 1 + 1 + 0) {}).k = _
    rw [N.NHf]
    exact z6
  have hU : ∀ a ∈ asksH R.h R.L R.x ZV (Model.longPoint lowN.2 R.x.tN.r)
      (Model.Head.costWeights R.cov (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)).1
      (Model.Head.costWeights R.cov (Model.Head.ztOf R.h R.L R.x.g1 R.x.qH)).2.2 qFC qROW b0 b1,
      ∃ m k, Uni tl.mats a m k := by
    intro a ha
    unfold asksH at ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
    · exact ⟨_, _, uF _ _⟩
    · exact ⟨_, _, uF _ _⟩
    all_goals exact ⟨_, _, uni_one _ _ rfl⟩
  have h4 := N.NHf
  have nB : R.h.NHf + 1 + 1 + 1 ≤ tl.NM := by omega
  have key := short_read H hU hn hf
    (a := (R.h.NHf + 1 + 1, 1, 2 ^ R.h.lmbH, Model.Forest.phiP R.h.lmbH, "bH-pin"))
    (mem_drop 14 _ rfl) uB nB hs hv
  rw [key]
  refine sum_congr rfl fun i _ => ?_
  have hp : 0 < 2 ^ R.h.lmbH := Nat.two_pow_pos _
  have e1 : 2 ^ R.h.lmbH / 2 ^ R.h.lmbH = 1 := Nat.div_self hp
  show ρ.val ((Model.Forest.phiP R.h.lmbH).getD i zeroE) *
      M (R.h.NHf + 1 + 1 + e / (2 ^ R.h.lmbH / 2 ^ R.h.lmbH) / R.L.kb)
        (e % (2 ^ R.h.lmbH / 2 ^ R.h.lmbH) * 2 ^ R.h.lmbH + i)
        (e / (2 ^ R.h.lmbH / 2 ^ R.h.lmbH) % R.L.kb) = _
  have e2 : R.h.NHf + 1 + 1 + e / 1 / R.L.kb = 6 := by
    rw [Nat.div_one, Nat.div_eq_of_lt he]
    omega
  have e3 : e % 1 * 2 ^ R.h.lmbH + i = i := by
    rw [Nat.mod_one, Nat.zero_mul, Nat.zero_add]
  have e4 : e / 1 % R.L.kb = e := by
    rw [Nat.div_one, Nat.mod_eq_of_lt he]
  rw [e1, e2, e3, e4]

end Pin

/-- The weight of row i of the matrix of the counts reads as 2^(i mod 32). -/
theorem phiP_value {lm i : ℕ} (hi : i < 2 ^ lm) :
    Reading.gl.val ((Model.Forest.phiP lm).getD i zeroE) = (2 : Cb.Gl.E) ^ (i % 32) := by
  have e : (Model.Forest.phiP lm).getD i zeroE = ofF (2 ^ (i % 32)).toUInt64 := by
    unfold Model.Forest.phiP
    simp [Array.getD, hi]
  have h32 : i % 32 < 32 := Nat.mod_lt _ (by norm_num)
  have hlt : 2 ^ (i % 32) < 2 ^ 64 := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [e, gl_nat hlt, Nat.cast_pow, Nat.cast_ofNat]

/-- A column of bitsMat N under these weights: N in the first column, 0 in the others. -/
theorem bits_column {lm : ℕ} (h5 : 5 ≤ lm) {N : ℕ} (hN : N < 2 ^ 32) (c : ℕ) :
    ∑ i ∈ range (2 ^ lm), Reading.gl.val ((Model.Forest.phiP lm).getD i zeroE) *
      ((bitsMat N i c : ℤ) : Cb.Gl.E) = if c = 0 then (N : Cb.Gl.E) else 0 := by
  by_cases hc : c = 0
  · rw [if_pos hc]
    have h32 : 32 ≤ 2 ^ lm := by
      have k : 2 ^ 5 ≤ 2 ^ lm := Nat.pow_le_pow_right (by norm_num) h5
      omega
    have e1 : ∑ i ∈ range (2 ^ lm), Reading.gl.val ((Model.Forest.phiP lm).getD i zeroE) *
        ((bitsMat N i c : ℤ) : Cb.Gl.E) =
        ∑ i ∈ range 32, Reading.gl.val ((Model.Forest.phiP lm).getD i zeroE) *
        ((bitsMat N i c : ℤ) : Cb.Gl.E) := by
      refine (Finset.sum_subset (Finset.range_mono h32) fun i _ hi => ?_).symm
      have k : ¬ (c = 0 ∧ i < 32) := fun q => hi (Finset.mem_range.mpr q.2)
      unfold bitsMat
      rw [if_neg k, Int.cast_zero, mul_zero]
    have e2 : ∑ i ∈ range 32, Reading.gl.val ((Model.Forest.phiP lm).getD i zeroE) *
        ((bitsMat N i c : ℤ) : Cb.Gl.E) =
        ((∑ i ∈ range 32, 2 ^ i * (N / 2 ^ i % 2) : ℕ) : Cb.Gl.E) := by
      rw [Nat.cast_sum]
      refine sum_congr rfl fun i hi => ?_
      have k := Finset.mem_range.mp hi
      rw [phiP_value (by omega), Nat.mod_eq_of_lt k]
      unfold bitsMat
      rw [if_pos ⟨hc, k⟩]
      simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Int.cast_natCast]
    rw [e1, e2, bits_sum, Nat.mod_eq_of_lt hN]
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun i _ => ?_
    have k : ¬ (c = 0 ∧ i < 32) := fun q => hc q.1
    unfold bitsMat
    rw [if_neg k, Int.cast_zero, mul_zero]

/-! ## 6. The three claims on the planes -/

section Planes

variable {R : Model.Head.Run} {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ}
  {H0 : Model.Head.HPlanH2} {F2 G2 : Fork} {C2 D2 : Ctx} {tl0 : Model.HTailF2} {K3 : ℕ}
  {tz : Head.Cells ℤ}

/-- With the bits of the number of keys in the matrix of the counts, the claim that the counts add
up to that number holds. -/
theorem count_zero (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM) (Nu : NumH R.h R.L)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM) {W : World Cb.Gl.E}
    (H : ∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 K3
      (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn)
    {tP : ℕ} (s2 : Starts R "bH-pin" tP)
    (pv : ∀ col ∈ List.range (planeN R), Valid R tP col ∧ col < R.L.kb) (h5 : 5 ≤ R.h.lmbH)
    (hNC : 1 ≤ R.x.g1.shape.NC) (hN : keysOf R < 2 ^ 32) :
    (countForm R K3 tP).value Reading.gl W = 0 := by
  have hn : 0 < planeN R := Nat.mul_pos hNC (Nat.two_pow_pos _)
  have ev : ∀ col, col < planeN R → (entAt R K3 tP col).value Reading.gl W =
      if col = 0 then (keysOf R : Cb.Gl.E) else 0 := by
    intro col hc
    obtain ⟨v1, v2⟩ := pv col (List.mem_range.mpr hc)
    unfold entAt
    rw [Aff.value_ent, pin_read hpl hm0 hN0 Nu ht hm hNM H s2 v1 v2]
    have e6 : ∀ i, ((matsB tz (keysOf R) 6 i col : ℤ) : Cb.Gl.E) =
        ((bitsMat (keysOf R) i col : ℤ) : Cb.Gl.E) := fun i => by
      unfold matsB
      rw [if_pos rfl]
    refine (sum_congr rfl fun i _ => ?_).trans (bits_column h5 hN col)
    show _ * ((matsB tz (keysOf R) 6 i col : ℤ) : Cb.Gl.E) = _
    rw [e6]
  have es := sum_at_zero (fun col => (entAt R K3 tP col).value Reading.gl W) hn
    (fun c hc h0 => by
      show (entAt R K3 tP c).value Reading.gl W = 0
      rw [ev c hc, if_neg h0])
  have h64 : keysOf R < 2 ^ 64 := Nat.lt_trans hN (by norm_num)
  unfold countForm
  rw [foldl_add_value, Aff.value_ofConst, gl_numerals.neg, gl_nat h64, es]
  show -(keysOf R : Cb.Gl.E) + (entAt R K3 tP 0).value Reading.gl W = 0
  rw [ev 0 hn, if_pos rfl]
  ring

/-- **The three claims on the planes can be met.** ent: entries in which every record of the list
of tables holds what it says of the matrices matsB. There are a list lrs of forms in the order of
their slots, from m1 on and below m2, and a value vB such that in every world with these entries
in which the forms of lrs are 0 and the slot of the bits' end value holds vB, any three forms that
planeClaims returns from a state of the walk are 0. (In the proof lrs is the claim of the leaves'
sumcheck, or empty if planeClaims returns from no such state.) -/
theorem planes_spec {F : Fork} (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM) (Nu : NumH R.h R.L)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM) {ent : ℕ → ℕ → ℕ → Cb.Gl.E}
    (H : ∀ σ : ℕ → Cb.Gl.E, ∀ Fn ∈ R.t.funs, Holds Reading.gl ⟨σ, ent⟩ tl0 R.iU3 (colsOf F R.iU3)
      (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn)
    (hNC : 1 ≤ R.x.g1.shape.NC) (hN : keysOf R < 2 ^ 32) {C0 : Aff} {m1 m2 : ℕ}
    (hlv : PscAt R.x.g1.leaves m2 C0 m1) (hl0 : Below Reading.gl C0 m1) :
    ∃ (lrs : List Aff) (vB : Cb.Gl.E), RowChain Reading.gl lrs m1 m2 ∧
      ∀ σ : ℕ → Cb.Gl.E, (∀ f ∈ lrs, f.value Reading.gl ⟨σ, ent⟩ = 0) → σ R.x.g1.sBit = vB →
        ∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A →
          ∀ f ∈ A, f.value Reading.gl ⟨σ, ent⟩ = 0 := by
  have hm12 : m1 ≤ m2 := by
    have k := hlv.room
    omega
  by_cases hP : ∃ F6 c6 A, Walk.Kept F F6 ∧ PlanesOf R F6 c6 A
  · obtain ⟨Fa, ca, Aa, ka, pa⟩ := hP
    obtain ⟨tB0, tB1, tP, s0, s1, s2, _, ⟨x, F', C', G', D', hrow⟩, pv, h5⟩ := planes_of pa
    rw [ka.2 R.iU3] at hrow
    obtain ⟨j, hi, t1, t2, T⟩ := pscRow_tri Reading.gl hrow hlv hl0
      ((below_atForm Reading.gl R (colsOf F R.iU3) 0 tB0 m1).scale _)
    rw [pscRow_form hrow] at T
    refine ⟨[_], (atForm R (colsOf F R.iU3) 1 tB1).value Reading.gl ⟨fun _ => 0, ent⟩,
      chain_one t1 T t2, ?_⟩
    intro σ hz hb F6 c6 A k6 p6 f hf
    obtain ⟨u0, u1, u2, r0, r1, r2, hA, _, _, _⟩ := planes_of p6
    rw [k6.2 R.iU3, Starts.unique r0 s0, Starts.unique r1 s1, Starts.unique r2 s2] at hA
    rw [hA] at hf
    have hf' : f = R.x.g1.leaves.rowForm oneE
          (Aff.scale (atForm R (colsOf F R.iU3) 0 tB0) R.x.g1.leavesA) ∨
        f = Aff.slot R.x.g1.sBit - atForm R (colsOf F R.iU3) 1 tB1 ∨
        f = countForm R (colsOf F R.iU3) tP := by
      simpa using hf
    rcases hf' with e | e | e
    · rw [e]
      exact hz _ (List.mem_singleton.mpr rfl)
    · rw [e, Aff.value_sub, Aff.value_slot,
        below_atForm Reading.gl R (colsOf F R.iU3) 1 tB1 0 (fun _ => 0) σ ent
          (fun k hk => absurd hk (Nat.not_lt_zero k))]
      show σ R.x.g1.sBit - _ = 0
      rw [hb]
      exact sub_self _
    · rw [e]
      exact count_zero hpl hm0 hN0 Nu ht hm hNM (H σ) s2 pv h5 hNC hN
  · exact ⟨[], 0, hm12, fun σ _ _ F6 c6 A k6 p6 => absurd ⟨F6, c6, A, k6, p6⟩ hP⟩

end Planes

/-! ## 7. The bundle, from matrices and slots -/

/-- The bundle LinkWorld of Johnson/Road/HeadLinkMet.lean, for any integer matrices Mz in which the
verifier's rule reads the library's honest cells tz, any world in which the tables hold what they
say of Mz, and slots that hold the values slotsFor at the two slots of the lookup's end, at the
slots of the sums of limb products and of the row products, and at the first slots of two sumchecks.
This is the second half of the proof of link_met_end there, with the matrices and the other slots
left free. -/
theorem linkWorld_of {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x)) {tz : Head.Cells ℤ}
    (hl : Top.LayersGive κ tbs i.val x.prompt tz)
    (hL : Policy.LedgerHead.RF (F := Cb.Gl.E) (npOf R.h) (outE i) (Cm.reqOf x) tz)
    {Mz : Mats ℤ} (SmZ : Policy.SameMain (cellsH R.h R.L R.b Mz) tz)
    (hsmall : ∀ a r c, |Mz a r c| < 2 ^ 18) {w : ℕ → Array ℕ}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hfn : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvE R Mz i x) (padKeyE R q) (fn q))
    {W : World Cb.Gl.E}
    (hHolds : ∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 (colsOf F R.iU3)
      (fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) Fn)
    {sL : ℕ} {tau : E}
    (hEnd : R.x.g1.cEnd =
      Aff.scale (Aff.slot sL) (subE oneE tau) + Aff.scale (Aff.slot (sL + 1)) tau)
    (Ord : SlotOrder R sL) {a b : Cb.Gl.E}
    (hab : (1 - Reading.gl.val tau) * a + Reading.gl.val tau * b = joinRest R fn (keyPtE R))
    (hσ : ∀ k, (k = sL ∨ k = sL + 1 ∨ (R.x.sW ≤ k ∧ k < R.x.sW + 9) ∨
        (R.x.sPv ≤ k ∧ k < R.x.sPv + 7) ∨ k = R.x.tN.sCl ∨ k = R.x.tH.sCl) → W.slot k =
      slotsFor R (cellsE R Mz) (outE i) (Cm.reqOf x) (posE R) (pt Reading.gl R.x.PV) sL a b k) :
    LinkWorld R tl0 F κ tbs i x Mz W fn := by
  have Nu := numH_of_layout hFull hy
  have Sm : Policy.SameMain (cellsE R Mz) (tz.cast Cb.Gl.E) := sameMain_cast SmZ
  have h2 : (2 : Cb.Gl.E) ≠ 0 := Policy.two_ne_GlE
  have hc := iw_23 gl_numerals gl_inverse h2 (R := R) hsh
  have Xh := View.heardFits_of_view hd hx
  have hPs := View.PV_size hd hx
  have o1 := Ord.b
  have o2 := Ord.c
  have o3 := Ord.d
  have A := callsAt_of_run Reading.gl hy Xh (callsLaid_of_layout hy)
  have T := trueH_of_holds hpl hm0 hN0 hFull Nu Bd ht hm hNM hHolds
  have X := linesFit_of_run hy Xh Reading.gl (R := R) rfl rfl rfl hFull.lt hFull.d hFull.V hsh
    hFull.XL Y (reqOf_ok x) T
  have hPV := shortAt_of_sum hPs T.hrPV
  have hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsE R Mz) l j a) s) (pt Reading.gl R.x.PV) := by
    intro s hs
    rw [hσ (R.x.sW + s) (by omega)]
    exact slotsFor_W Ord hs
  have hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsE R Mz) n a) j) (pt Reading.gl R.x.PV) := by
    intro j hj
    rw [hσ (R.x.sPv + j) (by omega)]
    exact slotsFor_P Ord hj
  have S : SlotsHold Reading.gl W R (cellsE R Mz) (outE i) (Cm.reqOf x) (posE R) := by
    intro q hq
    obtain ⟨_, _, _, _, a5⟩ := A q hq
    refine ⟨fun g hg hname => ?_, ?_⟩
    · obtain ⟨f1, f2⟩ := (a5 g hg).1
      rw [hname] at f1 f2
      have eq : q = R.x.qH := Option.some.inj (f1.symm.trans Xh.qH)
      subst eq
      rw [hσ R.x.tH.sCl (by omega), slotsFor_H Ord,
        mul_inv_cancel_left₀ (pow_ne_zero _ h2)]
      unfold hdPart
      rw [f2]
    · by_cases hqN : q = R.x.qN
      · subst hqN
        rw [if_pos rfl, hσ R.x.tN.sCl (by omega), slotsFor_N Ord]
        rfl
      · refine nf_absent hqN fun g hg hname => ?_
        obtain ⟨f1, _⟩ := (a5 g hg).1
        rw [hname] at f1
        exact hqN (Option.some.inj (f1.symm.trans Xh.qN))
  have idns := idns_same Sm hL
  have keys := lookup_met gl_numerals hy hF hsh hTs
    (segsFit_of_layout hy hFull.lt hFull.d hFull.V hFull.XL) hc Sm hL hw hfn
  have hJ : joinWorth Reading.gl W R fn (keyPtE R) = 0 := by
    rw [joinWorth_rest, hEnd, Aff.value_add, Aff.value_scale, Aff.value_scale, Aff.value_slot,
      Aff.value_slot, hσ sL (by omega), hσ (sL + 1) (by omega), slotsFor_sL,
      slotsFor_sR,
      Reading.gl.sub, Reading.gl.one, hab, sub_self]
  exact {
    holds := hHolds
    small := hsmall
    Kf := fun q w' hw' => by
      have e : w' = w q := Option.some.inj (hw'.symm.trans (hw q))
      rw [e]
      exact hfn q
    claimsL := fun q5 hq5 k hk => by
      rw [ledger_idn_plain gl_numerals hq5 hPV hk hW hP]
      refine Blocks.ext_zero_of_forall (fun a ha => idns a ?_ k hk) _
      rw [hFull.lt] at ha
      exact ha
    claimsJ := fun F4 c4 KF k4 hKF => by
      have X4 := X
      rw [← k4.2 R.iU3] at X4
      rw [joinForm_worth gl_numerals _ X4 A S hw hfn hKF]
      exact hJ
    slots := S
    hW := hW
    hP := hP
    stepP := fun _ => idns
    stepL := fun _ _ _ _ _ _ _ => keys
    layers := ⟨hl.ok, fun a ha j hj => by
      rw [Cm.Seg.xv_same SmZ.plain hj ha]
      exact hl.stream a ha j hj⟩ }

/-! ## 8. All claims that sumchecks leave -/

/-- The order of the slots that hear returns, with five limbs (hear_slots in
Johnson/Road/HeadSlots.lean). -/
structure HeardOrder (R : Model.Head.Run) : Prop where
  a : R.x.sW + 9 < R.x.wpl.sL
  b : R.x.wpl.sR = R.x.wpl.sL + 1
  c : R.x.sPv = R.x.wpl.sL + 2
  d : R.x.tV.sCl = R.x.sPv + 7
  e : R.x.tV.sCl + 2 ≤ R.x.tV.sEnd
  f : R.x.tN.sCl = R.x.tV.sEnd + 4
  g : R.x.tN.sCl + 2 ≤ R.x.tN.sEnd
  h : R.x.tH.sCl = R.x.tN.sEnd + 2
  i : R.x.tH.sCl + 2 ≤ R.x.tH.sEnd

/-- What hear returns has its slots in this order, with five limbs. -/
theorem heardOrder_of_hear {R : Model.Head.Run} {plain : Array E} {F G : Fork} {C D : Ctx}
    (hXL : R.h.XL = 5) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F C R.x G D) :
    HeardOrder R := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := hear_slots_five hXL hx
  obtain ⟨_, b2, _, _, _, _, b7, b8, b9, _⟩ := hear_slots hx
  exact ⟨a1, b2, a2, a3, a4, a5, b7, b8, b9⟩

/-- **All claims that the sumchecks of what was heard leave can be met together**, with the forms of
a further list lrs on the slots of the leaves' sumcheck, whatever the entries hold, by a change of
slots that keeps: the two slots that the end of the lookup's key side reads; the slot of the bits'
end value and all up to the last sum of limb products; the end values of the product layer, the row
products and the claimed sum of their sumcheck; the end values of each token sumcheck and the
claimed sum of the next. -/
theorem solve_heard {R : Model.Head.Run} (hXL : R.h.XL = 5) (HO : HeardOrder R)
    {l1 l2 : List Aff} {bRow : Aff} {cL : ℕ} {tau : E} {Cl : Aff} {m1 m2 : ℕ}
    (HR : HeardRows Reading.gl R.h.XL R.x l1 l2 bRow cL tau Cl m1 m2) {lrs : List Aff}
    (cl : RowChain Reading.gl lrs m1 m2) (σ : ℕ → Cb.Gl.E) (ent : ℕ → ℕ → ℕ → Cb.Gl.E) :
    ∃ σ' : ℕ → Cb.Gl.E,
      (∀ k, (k = cL ∨ k = cL + 1 ∨ (R.x.g1.sBit ≤ k ∧ k < R.x.sW + 9) ∨
        (R.x.wpl.sL ≤ k ∧ k ≤ R.x.tV.sCl) ∨ (R.x.tV.sEnd ≤ k ∧ k ≤ R.x.tN.sCl) ∨
        (R.x.tN.sEnd ≤ k ∧ k ≤ R.x.tH.sCl) ∨ R.x.tH.sEnd ≤ k) → σ' k = σ k) ∧
      (∀ f ∈ R.x.g1.rows, f.value Reading.gl ⟨σ', ent⟩ = 0) ∧
      (∀ f ∈ lrs, f.value Reading.gl ⟨σ', ent⟩ = 0) ∧
      R.x.wpl.row.value Reading.gl ⟨σ', ent⟩ = 0 ∧ R.x.tV.rowU.value Reading.gl ⟨σ', ent⟩ = 0 ∧
      R.x.tN.rowU.value Reading.gl ⟨σ', ent⟩ = 0 ∧
      R.x.tH.rowU.value Reading.gl ⟨σ', ent⟩ = 0 := by
  have e9 : Model.ledNS R.h.XL = 9 := by
    rw [hXL]
    rfl
  have cw := HR.w
  rw [e9] at cw
  have b1 := chain_le _ _ _ HR.c2
  have b2 := HR.leaves.room
  have b3 := chain_le _ _ _ HR.c3
  have b4 := HR.bit
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := HO
  obtain ⟨σ1, s1, z1⟩ := chain_solve _ _ _ HR.c1 σ ent
  obtain ⟨σ2, s2, z2⟩ := chain_solve _ _ _ HR.c2 σ1 ent
  obtain ⟨σ3, s3, z3⟩ := chain_solve _ _ _ cl σ2 ent
  obtain ⟨σ4, s4, z4⟩ := chain_solve _ _ _ HR.c3 σ3 ent
  obtain ⟨σ5, s5, z5⟩ := chain_solve _ _ _ cw σ4 ent
  obtain ⟨σ6, s6, z6⟩ := chain_solve _ _ _ HR.tV σ5 ent
  obtain ⟨σ7, s7, z7⟩ := chain_solve _ _ _ HR.tN σ6 ent
  obtain ⟨σ8, s8, z8⟩ := chain_solve _ _ _ HR.tH σ7 ent
  have one : ∀ f : Aff, f ∈ [f] := fun f => List.mem_singleton.mpr rfl
  refine ⟨σ8, fun k hk => ?_, fun f hf => ?_, fun f hf => ?_, ?_, ?_, ?_, z8 _ (one _)⟩
  · rw [s8 k (by omega), s7 k (by omega), s6 k (by omega), s5 k (by omega), s4 k (by omega),
      s3 k (by omega), s2 k (by omega), s1 k (by omega)]
  · have hf' : f ∈ l1 ++ l2 ++ [bRow] := by
      rw [← HR.rows]
      exact Array.mem_def.mp hf
    rcases List.mem_append.mp hf' with h12 | h3
    · rcases List.mem_append.mp h12 with h1 | h2
      · rw [chain_below _ _ _ HR.c1 f h1 σ1 σ8 ent fun k hk => by
          rw [s8 k (by omega), s7 k (by omega), s6 k (by omega), s5 k (by omega),
            s4 k (by omega), s3 k (by omega), s2 k (by omega)]]
        exact z1 f h1
      · rw [chain_below _ _ _ HR.c2 f h2 σ2 σ8 ent fun k hk => by
          rw [s8 k (by omega), s7 k (by omega), s6 k (by omega), s5 k (by omega),
            s4 k (by omega), s3 k (by omega)]]
        exact z2 f h2
    · rw [chain_below _ _ _ HR.c3 f h3 σ4 σ8 ent fun k hk => by
        rw [s8 k (by omega), s7 k (by omega), s6 k (by omega), s5 k (by omega)]]
      exact z4 f h3
  · rw [chain_below _ _ _ cl f hf σ3 σ8 ent fun k hk => by
      rw [s8 k (by omega), s7 k (by omega), s6 k (by omega), s5 k (by omega), s4 k (by omega)]]
    exact z3 f hf
  · rw [chain_below _ _ _ cw _ (one _) σ5 σ8 ent fun k hk => by
      rw [s8 k (by omega), s7 k (by omega), s6 k (by omega)]]
    exact z5 _ (one _)
  · rw [chain_below _ _ _ HR.tV _ (one _) σ6 σ8 ent fun k hk => by
      rw [s8 k (by omega), s7 k (by omega)]]
    exact z6 _ (one _)
  · rw [chain_below _ _ _ HR.tN _ (one _) σ7 σ8 ent fun k hk => s8 k (by omega)]
    exact z7 _ (one _)

/-! ## 9. The whole -/

/-- Values for the slots: vB under the slot of the bits' end value; σx under the end values of the
product layer, the claimed sum of the products' sumcheck and the end values of the three token
sumchecks; σl elsewhere. -/
def baseSlots (R : Model.Head.Run) (vB : Cb.Gl.E) (σx σl : ℕ → Cb.Gl.E) (k : ℕ) : Cb.Gl.E :=
  if k = R.x.g1.sBit then vB
  else if (R.x.wpl.sL ≤ k ∧ k < R.x.sPv) ∨ k = R.x.tV.sCl ∨
      (R.x.tV.sEnd ≤ k ∧ k < R.x.tN.sCl) ∨ (R.x.tN.sEnd ≤ k ∧ k < R.x.tH.sCl) ∨
      R.x.tH.sEnd ≤ k then σx k
  else σl k

/-- The value under the slot of the bits' end value. -/
theorem baseSlots_bit (R : Model.Head.Run) (vB : Cb.Gl.E) (σx σl : ℕ → Cb.Gl.E) :
    baseSlots R vB σx σl R.x.g1.sBit = vB := by
  unfold baseSlots
  rw [if_pos rfl]

/-- The values under the slots of the second kind. -/
theorem baseSlots_x (R : Model.Head.Run) (vB : Cb.Gl.E) (σx σl : ℕ → Cb.Gl.E) {k : ℕ}
    (n1 : ¬ k = R.x.g1.sBit)
    (hk : (R.x.wpl.sL ≤ k ∧ k < R.x.sPv) ∨ k = R.x.tV.sCl ∨
      (R.x.tV.sEnd ≤ k ∧ k < R.x.tN.sCl) ∨ (R.x.tN.sEnd ≤ k ∧ k < R.x.tH.sCl) ∨
      R.x.tH.sEnd ≤ k) : baseSlots R vB σx σl k = σx k := by
  unfold baseSlots
  rw [if_neg n1, if_pos hk]

/-- The values under all other slots. -/
theorem baseSlots_l (R : Model.Head.Run) (vB : Cb.Gl.E) (σx σl : ℕ → Cb.Gl.E) {k : ℕ}
    (n1 : ¬ k = R.x.g1.sBit)
    (n2 : ¬ ((R.x.wpl.sL ≤ k ∧ k < R.x.sPv) ∨ k = R.x.tV.sCl ∨
      (R.x.tV.sEnd ≤ k ∧ k < R.x.tN.sCl) ∨ (R.x.tN.sEnd ≤ k ∧ k < R.x.tH.sCl) ∨
      R.x.tH.sEnd ≤ k)) : baseSlots R vB σx σl k = σl k := by
  unfold baseSlots
  rw [if_neg n1, if_neg n2]

/-- **All hypotheses of head_link_of_port on matrices, world and functions can be met together,
with the four claims that the head's own sumchecks leave, and with any values under the slots of
which that theorem does not speak.** There are matrices Mz and functions fn such that for any
values σx there is a world that meets the bundle LinkWorld and the lookup's other claims, in which
the four claims are 0, and whose slots hold σx at: the two end values of the product layer; the
claimed sum of the products' sumcheck; the end values of the first two token sumchecks; and every
slot from the first end value of the third token sumcheck on. -/
theorem link_met_free {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) :
    ∃ (Mz : Mats ℤ) (fn : ℕ → ℕ → ℕ → Cb.Gl.E), ∀ σx : ℕ → Cb.Gl.E, ∃ W : World Cb.Gl.E,
      LinkWorld R tl0 F κ tbs i x Mz W fn ∧
      (∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0) ∧
      (∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A → ∀ f ∈ A, f.value Reading.gl W = 0) ∧
      (R.x.wpl.row.value Reading.gl W = 0 ∧ R.x.tV.rowU.value Reading.gl W = 0 ∧
        R.x.tN.rowU.value Reading.gl W = 0 ∧ R.x.tH.rowU.value Reading.gl W = 0) ∧
      ∀ k, ((R.x.wpl.sL ≤ k ∧ k < R.x.sPv) ∨ k = R.x.tV.sCl ∨
        (R.x.tV.sEnd ≤ k ∧ k < R.x.tN.sCl) ∨ (R.x.tN.sEnd ≤ k ∧ k < R.x.tH.sCl) ∨
        R.x.tH.sEnd ≤ k) → W.slot k = σx k := by
  have Nu := numH_of_layout hFull hy
  have hpol : (⟨0, 0, 0⟩ : AcceptancePolicy).OK := ⟨by norm_num, by norm_num, by norm_num⟩
  obtain ⟨hl, hL0⟩ := Top.ledger_hyps_met (p := Cb.Gl.p) hn hpol i x htrue
  generalize Head.N.honCells (npOf R.h) (XK ppref κ tbs i.val x.prompt (2 * ppref.layers))
    i.val.H (Req.of ⟨0, 0, 0⟩ x) = tz at hl hL0
  have hL : Policy.LedgerHead.RF (F := Cb.Gl.E) (npOf R.h) (outE i) (Cm.reqOf x) tz :=
    Down.ledgerRF_gl.2 hL0
  obtain ⟨hNC, hN⟩ := hear_numbers hx
  obtain ⟨l1, l2, bRow, cL, tau, Cl, m1, m2, HR⟩ := hear_rows Reading.gl hx
  have HO := heardOrder_of_hear hFull.XL hx
  have b1 := chain_le _ _ _ HR.c2
  have b2 := HR.leaves.room
  have b3 := chain_le _ _ _ HR.c3
  have b4 := HR.bit
  have Ord := slotOrder_of_hear hFull.XL hx (sL := cL) (by omega)
  choose w hw using marks_of_layout (R := R) hy
  choose fn hfn using fun q =>
    exists_keyFn (hw q) (kvE R (matsB tz (keysOf R)) i x) (padKeyE R q)
  obtain ⟨a, b, hab⟩ := solve_two (Reading.gl.val tau) (joinRest R fn (keyPtE R))
  obtain ⟨W0, _, hH0⟩ := holdsH_met Reading.gl ht hm (colsOf F R.iU3)
    (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) (fun _ => 0)
  have hH : ∀ σ : ℕ → Cb.Gl.E, ∀ Fn ∈ R.t.funs, Holds Reading.gl ⟨σ, W0.entry⟩ tl0 R.iU3
      (colsOf F R.iU3) (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn :=
    fun σ Fn hFn => holds_of_entry rfl (hH0 Fn hFn)
  obtain ⟨lrs, vB, cl, hplanes⟩ := planes_spec hpl hm0 hN0 Nu ht hm hNM hH hNC hN HR.leaves
    HR.leaves0
  refine ⟨matsB tz (keysOf R), fn, fun σx => ?_⟩
  obtain ⟨σ', ag, zr, zl, zw, zV, zN, zH⟩ := solve_heard hFull.XL HO HR cl
    (baseSlots R vB σx (slotsFor R (cellsE R (matsB tz (keysOf R))) (outE i) (Cm.reqOf x) (posE R)
      (pt Reading.gl R.x.PV) cL a b)) W0.entry
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := HO
  refine ⟨⟨σ', W0.entry⟩, ?_, zr, hplanes σ' zl ?_, ⟨zw, zV, zN, zH⟩, fun k hk => ?_⟩
  · refine linkWorld_of hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hm hNM i x Y hl hL
      (sameZ_matsB Nu Bd tz (keysOf R)) (matsB_small hL.small (keysOf R)) hw hfn (hH σ') HR.cEnd
      Ord hab fun k hk => ?_
    show σ' k = _
    rw [ag k (by omega)]
    exact baseSlots_l R vB σx _ (by omega) (by omega)
  · rw [ag R.x.g1.sBit (by omega)]
    exact baseSlots_bit R vB σx _
  · show σ' k = σx k
    rw [ag k (by omega)]
    exact baseSlots_x R vB σx _ (by omega) hk

/-- **All hypotheses of head_link_of_port on matrices, world and functions can be met together.**
See the head of this file. -/
theorem link_met_all {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) :
    ∃ Mz W fn, LinkWorld R tl0 F κ tbs i x Mz W fn ∧
      (∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0) ∧
      ∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A → ∀ f ∈ A, f.value Reading.gl W = 0 := by
  obtain ⟨Mz, fn, h⟩ := link_met_free (F := F) (tl0 := tl0) hy hFull hsh hF hTs Bd hpl hm0 hN0 hd
    hx ht hm hNM hn i x Y htrue
  obtain ⟨W, B, h1, h2, _, _⟩ := h fun _ => 0
  exact ⟨Mz, W, fn, B, h1, h2⟩

/-- head_link_of_port applies to what link_met_all gives, if the walk succeeds. The conclusion is
known beforehand, since the request is a true one: the theorem shows only that the statements fit
each other letter by letter. -/
theorem link_met_fits {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4) (Bd : BorderH R.b)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) (pol : AcceptancePolicy) :
    RinfR ppref κ (npOf R.h) tbs pol i x := by
  obtain ⟨Mz, W, fn, B, hrows, hplanes⟩ := link_met_all (F := F) hy hFull hsh hF hTs Bd hpl hm0
    hN0 hd hx ht hm hNM hn i x Y htrue
  exact B.fits hrows hplanes hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx ht hs hT hwalk hm hNM hn hr
    he Y pol

/-- **All hypotheses of head_link_seg (Johnson/Road/HeadLinkSeg.lean) on matrices, world and
functions can be met together**: the bundle LinkWorld, all four clauses of ClaimsHold, and LentH.
The lists Mg of the layers' groups are made from Mz: every matrix of every list is the head's copy
of the stream. So LentH holds by choice: nothing is said on the matrices of the layers' own
sub-proofs. -/
theorem seg_met_all {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4)
    {hyL : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hlay : Model.Layer.layout hyL pc = .ok y) (Sw : Switches hyL) (Z : Sized hyL All.DF)
    (Z2 : Sized2 hyL All.DF) (hb : R.b = Model.Verify.borderOf y)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) :
    ∃ (Mz : Mats ℤ) (W : World Cb.Gl.E) (fn : ℕ → ℕ → ℕ → Cb.Gl.E) (Mg : ℕ → Mats ℤ),
      LinkWorld R tl0 F κ tbs i x Mz W fn ∧ ClaimsHold W R F ∧ LentH R.h y Mz (Mg 11) := by
  have Bd : BorderH R.b := by
    rw [hb]
    exact borderH_of_layout hlay Sw Z Z2
  obtain ⟨Mz, W, fn, B, h1, h2⟩ := link_met_all (F := F) hy hFull hsh hF hTs Bd hpl hm0 hN0 hd hx
    ht hm hNM hn i x Y htrue
  exact ⟨Mz, W, fn, fun _ _ r c => Mz (R.h.NHf + 3) r c, B, ⟨B.claimsL, B.claimsJ, h1, h2⟩,
    fun _ _ _ _ => rfl⟩

/-- head_link_seg applies to what seg_met_all gives, if the walk succeeds: the library's segment of
the head holds at the stacked matrices. What is shown is that the statements fit each other letter
by letter. The matrices for attention are 0 here; head_link_seg takes any. -/
theorem seg_met_fits {R : Model.Head.Run} {tl tl' tl0 : Model.HTailF2}
    {wo : Model.WsForkOut} {Lc Lc' : Model.LinkCtx} {F G F0 F1 F2 G2 : Fork}
    {C D C0 C1 C2 D2 : Ctx} {plain : Array E}
    {g : Model.Settings} {O : Model.Head.Owner} {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h) (hsh : R.h.digSh = 8)
    (hF : R.h.famF = 24) (hTs : R.h.tabS = 4)
    {hyL : Model.Layer.Shape} {pc : List (List String)} {y : Model.Layer.Lay}
    (hlay : Model.Layer.layout hyL pc = .ok y) (Sw : Switches hyL) (Z : Sized hyL All.DF)
    (Z2 : Sized2 hyL All.DF) (hb : R.b = Model.Verify.borderOf y)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hs : F.LS.size = F.ns) (hT : Walk.Keeps (tl.objectsF R.t.funs))
    (hwalk : Walk.OkL (Model.Head.walk R tl wo) Lc F C tl' Lc' G D)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024)
    (Y : ReqFits R HeadSizes.ref (Cm.reqOf x))
    (htrue : RinfR ppref κ (npOf R.h) tbs ⟨0, 0, 0⟩ i x) :
    ∃ (Mz : Mats ℤ) (Mg : ℕ → Mats ℤ),
      (Cm.Seg.TS.segHeadY (npOf R.h)).Holds Cm.Seg.TS.fmtRef x
        (fun r c => (((Cm.Idx.ofIndex i).mat r c : ℤ) : Cb.Gl.F))
        (Cb.Partition.castM (E := Cb.Gl.E) (stackedH y Mg (fun _ _ _ => 0) Mz)) := by
  obtain ⟨Mz, W, fn, Mg, B, cl, hlent⟩ := seg_met_all (F := F) (tl0 := tl0) (κ := κ)
    (tbs := tbs) hy hFull hsh hF hTs hlay Sw Z Z2 hb hpl hm0 hN0 hd hx ht hm hNM hn i x Y htrue
  exact ⟨Mz, Mg, head_link_seg hy hFull hsh hF hTs hlay Sw Z Z2 hb Mg (fun _ _ _ => 0) hpl hm0 hN0
    hd hx ht hs hT hwalk i x hr he Y hlent hm hNM B.holds B.small B.Kf cl B.slots B.hW B.hP
    B.stepP B.stepL⟩

/-! ## 10. A control: the claims alone exclude nothing -/

/-- **The premise of the lookup's step can be met for any functions on the calls' columns, over any
cells.** tz: any integer cells; fn: any functions. There is a world in which every table holds what
it says of the matrices matsB tz, all the lookup's claims that read mask entries alone are 0, any
three forms on the planes are 0, the claim on the calls' key vectors is worth 0 in the meaning that
joinForm_worth gives it for fn, and the four claims that the head's own sumchecks leave are 0. So
these claims, for a world that is chosen after the challenges, say nothing on fn or on the cells. -/
theorem premise_free {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    (tz : Head.Cells ℤ) (fn : ℕ → ℕ → ℕ → Cb.Gl.E) :
    ∃ W : World Cb.Gl.E,
      (∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 (colsOf F R.iU3)
        (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn) ∧
      (∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0) ∧
      (∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A → ∀ f ∈ A, f.value Reading.gl W = 0) ∧
      joinWorth Reading.gl W R fn (keyPtE R) = 0 ∧
      (R.x.wpl.row.value Reading.gl W = 0 ∧ R.x.tV.rowU.value Reading.gl W = 0 ∧
        R.x.tN.rowU.value Reading.gl W = 0 ∧ R.x.tH.rowU.value Reading.gl W = 0) := by
  have Nu := numH_of_layout hFull hy
  obtain ⟨hNC, hN⟩ := hear_numbers hx
  obtain ⟨l1, l2, bRow, cL, tau, Cl, m1, m2, HR⟩ := hear_rows Reading.gl hx
  have HO := heardOrder_of_hear hFull.XL hx
  have b1 := chain_le _ _ _ HR.c2
  have b2 := HR.leaves.room
  have b3 := chain_le _ _ _ HR.c3
  have b4 := HR.bit
  obtain ⟨a, b, hab⟩ := solve_two (Reading.gl.val tau) (joinRest R fn (keyPtE R))
  obtain ⟨W0, _, hH0⟩ := holdsH_met Reading.gl ht hm (colsOf F R.iU3)
    (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) (fun _ => 0)
  have hH : ∀ σ : ℕ → Cb.Gl.E, ∀ Fn ∈ R.t.funs, Holds Reading.gl ⟨σ, W0.entry⟩ tl0 R.iU3
      (colsOf F R.iU3) (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn :=
    fun σ Fn hFn => holds_of_entry rfl (hH0 Fn hFn)
  obtain ⟨lrs, vB, cl, hplanes⟩ := planes_spec hpl hm0 hN0 Nu ht hm hNM hH hNC hN HR.leaves
    HR.leaves0
  obtain ⟨σ', ag, zr, zl, zw, zV, zN, zH⟩ := solve_heard hFull.XL HO HR cl
    (baseSlots R vB (fun _ => 0)
      (Function.update (Function.update (fun _ => 0) cL a) (cL + 1) b)) W0.entry
  obtain ⟨o1, o2, o3, o4, o5, o6, o7, o8, o9⟩ := HO
  have nLR : cL ≠ cL + 1 := by omega
  have eL : (⟨σ', W0.entry⟩ : World Cb.Gl.E).slot cL = a := by
    show σ' cL = a
    rw [ag cL (by omega), baseSlots_l R vB _ _ (k := cL) (by omega) (by omega), upd_other _ nLR,
      upd_self]
  have eR : (⟨σ', W0.entry⟩ : World Cb.Gl.E).slot (cL + 1) = b := by
    show σ' (cL + 1) = b
    rw [ag (cL + 1) (by omega), baseSlots_l R vB _ _ (k := cL + 1) (by omega) (by omega),
      upd_self]
  refine ⟨⟨σ', W0.entry⟩, hH σ', zr, hplanes σ' zl ?_, ?_, zw, zV, zN, zH⟩
  · rw [ag R.x.g1.sBit (by omega)]
    exact baseSlots_bit R vB _ _
  · rw [joinWorth_rest, HR.cEnd, Aff.value_add, Aff.value_scale, Aff.value_scale, Aff.value_slot,
      Aff.value_slot, eL, eR, Reading.gl.sub, Reading.gl.one, hab, sub_self]

/-- The same for the functions of any cells: for any integer cells tz, index and instance there are
a world and the calls' functions of the keys that are read in the matrices matsB tz, with the
premise of the lookup's step. Nothing is asked of the keys: they may lie outside their tables. -/
theorem premise_of_cells {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 : Fork}
    {C0 C1 C2 D2 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    (tz : Head.Cells ℤ) (i : Index ppref) (x : Instance ppref) :
    ∃ (W : World Cb.Gl.E) (fn : ℕ → ℕ → ℕ → Cb.Gl.E),
      (∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 (colsOf F R.iU3)
        (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn) ∧
      (∀ q w, (R.L.calls.getD q default).segs.foldlM
          (fun w g => Model.Head.markColumns R w g)
          (Array.replicate (R.L.calls.getD q default).J 0) = some w →
        KeyFn (R.L.calls.getD q default).segs w (R.L.calls.getD q default).J
          (kvE R (matsB tz (keysOf R)) i x) (padKeyE R q) (fn q)) ∧
      (∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0) ∧
      (∀ F6 c6 A, Walk.Kept F F6 → PlanesOf R F6 c6 A → ∀ f ∈ A, f.value Reading.gl W = 0) ∧
      joinWorth Reading.gl W R fn (keyPtE R) = 0 := by
  choose w hw using marks_of_layout (R := R) hy
  choose fn hfn using fun q =>
    exists_keyFn (hw q) (kvE R (matsB tz (keysOf R)) i x) (padKeyE R q)
  obtain ⟨W, h1, h2, h3, h4, _⟩ := premise_free (F := F) hy hFull hpl hm0 hN0 hx ht hm hNM tz fn
  refine ⟨W, fn, h1, fun q w' hw' => ?_, h2, h3, h4⟩
  have e : w' = w q := Option.some.inj (hw'.symm.trans (hw q))
  rw [e]
  exact hfn q

/-- The reading of a word lies in the base field: its second coordinate is 0. -/
theorem gl_word_c1 (w : UInt64) : (Reading.gl.val (ofF w)).c1 = 0 := by
  show (Slice.toE (ofF w).triple).c1 = 0
  rw [ofF_triple]
  exact Slice.toF_zero

/-- **The lookup's step is false in some world**: a control beside the witness. A: three forms on
the planes that planeClaims returns from a state of the walk. There are a world, in which every
table holds what it says of the matrices matsB tz, and functions fn such that all claims that the
lookup leaves hold and yet a value of fn is no row of its call's table: fn is constant, with a
value outside the base field. So the hypothesis StepLookup is no consequence of the claims: what
could make it hold for a prover's world is the order of commitments and draws, which no statement
here holds. -/
theorem step_fails {R : Model.Head.Run} {tl0 : Model.HTailF2} {F F0 F1 F2 G2 F6 : Fork}
    {C0 C1 C2 D2 c6 : Ctx} {plain : Array E} {g : Model.Settings} {O : Model.Head.Owner}
    {NGr lkW : ℕ} {H0 : Model.Head.HPlanH2} {A : Array Aff}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hFull : FullH R.h)
    (hpl : Model.Head.planH2 g R.h R.L R.b O NGr lkW = .ok H0)
    (hm0 : R.hp.tl.mats = H0.tl.mats) (hN0 : R.hp.tl.NM = H0.tl.NM)
    (hd : C0.ch.dry = false) (hx : Ok (Model.Head.hear R.h R.L R.hp R.cov plain) F0 C0 R.x F1 C1)
    (ht : Ok (Model.Head.tablesOf R.h R.L R.hp R.cov R.x) F2 C2 R.t G2 D2)
    (hm : tl0.mats = R.hp.tl.mats) (hNM : tl0.NM = R.hp.tl.NM)
    (k6 : Walk.Kept F F6) (p6 : PlanesOf R F6 c6 A) (tz : Head.Cells ℤ) :
    ∃ (W : World Cb.Gl.E) (fn : ℕ → ℕ → ℕ → Cb.Gl.E),
      (∀ Fn ∈ R.t.funs, Holds Reading.gl W tl0 R.iU3 (colsOf F R.iU3)
        (fun a r c => ((matsB tz (keysOf R) a r c : ℤ) : Cb.Gl.E)) Fn) ∧
      LookupMeans W R A ∧ joinWorth Reading.gl W R fn (keyPtE R) = 0 ∧
      ¬ StepLookup W R A fn (keyPtE R) := by
  have Xh := View.heardFits_of_view hd hx
  obtain ⟨W, h1, h2, h3, h4, _⟩ := premise_free (F := F) hy hFull hpl hm0 hN0 hx ht hm hNM tz
    (fun _ _ _ => (⟨0, 1, 0⟩ : Cb.Gl.E))
  refine ⟨W, _, h1, ⟨h2, h3 F6 c6 A k6 p6⟩, h4, fun hS => ?_⟩
  have hJ : 0 < (R.L.calls.getD R.x.qN default).J := by
    rw [(callsLaid_of_layout hy R.x.qN (callNo_lt Xh.qN)).1]
    exact Nat.two_pow_pos _
  have hT : 0 < nT := by
    show 0 < 1024
    norm_num
  obtain ⟨u, _, e⟩ := hS ⟨h2, h3 F6 c6 A k6 p6⟩ h4 R.x.qN 0 hJ 0 hT
  have e1 : (1 : Cb.Gl.F) = 0 :=
    (congrArg (fun z : Cb.Gl.E => z.c1) e).trans (gl_word_c1 _)
  exact one_ne_zero e1

#print axioms pin_read
#print axioms planes_of
#print axioms count_zero
#print axioms planes_spec
#print axioms linkWorld_of
#print axioms solve_heard
#print axioms link_met_free
#print axioms link_met_all
#print axioms link_met_fits
#print axioms seg_met_all
#print axioms seg_met_fits
#print axioms premise_free
#print axioms premise_of_cells
#print axioms step_fails

end OnBytes.Road.Hd
