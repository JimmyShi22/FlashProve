-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/KeyLookup/PortSim.lean: what the program's sumcheck hands on, read as linear forms on
a type of entries, and a first stretch of a lookup in which that reading is the plain function of
the flat rounds.

The program's sumcheck computes on machine words (`Psc.run`, OnBytes/Iop/Psc.lean). It has a copy of
its text over the field (`PscF.run`, `PscF.outOf`, OnBytes/Slice/KeyPscRun.lean), and
OnBytes/Slice/BlkPscRead.lean proves that the first, read in the field, is the second
(`read_run`), for a summand that reads as a summand over the field (`SummandReads`). There a mask
form is a list of (mask entry, coefficient). The description of a lookup in the library's types has
its claims and rows as functions on a type J of entries, and its output is a plain function of the
flat rounds (Cb/Pv/KeyLookup/Flat.lean). This file reads the first in the form of the second.

  rdMF sl f     a mask form f as a function on J; sl says where a mask entry stands in J
  flatY h       what was heard in a sumcheck that shows values, as flat rounds
  sProd, sTie1, sTie, sBits, sLeaves   the five summands of a lookup, over the field, each with the
                theorem that the program's summand reads as it
  onValue c     a claim on a value, as a sum without variables
  complete_eq, walk_snd, walk_cons, walk_one   UNDER EQUALITY WEIGHTS: the coefficient that is not
                sent is the running claim less z times the sum of the others; the product of the
                polynomials psi is 1; the weights of the first polynomial's coefficients are, round
                by round, the powers 1, 2, .. of the challenge, and in the last round's group the
                constant's 1 stands first
  part_step     ONE STEP OF THE PARTS' ROOTS: what `PscF.outOf` hands on at the claim on the product
                of the roots that are left, at the summand "product of two values", read by rdMF, is
                what `Parts.stepAcc` computes from the flat rounds, at the places of the five fresh
                mask entries

Limits. One stretch's one step. Nothing on how the steps are joined, nothing on the program's
blocks, nothing on soundness.

-/
import OnBytes.Slice.BlkPscRead
import OnBytes.Iop.Lkp
import Cb.Pv.KeyLookup.PartsRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.PortSim

open OnBytes OnBytes.Slice

variable {J : Type} [DecidableEq J] (sl : Slot → J)

/-- A mask form as a function on the entries. -/
def rdMF (f : PscF.MaskForm) : J → GE := fun j => (f.map fun t => Parts.one (sl t.1) t.2 j).sum

/-- The empty form. -/
theorem rdMF_nil (j : J) : rdMF sl [] j = 0 := rfl

/-- A form's first term. -/
theorem rdMF_cons (t : Slot × GE) (f : PscF.MaskForm) (j : J) :
    rdMF sl (t :: f) j = Parts.one (sl t.1) t.2 j + rdMF sl f j := by
  unfold rdMF
  rw [List.map_cons, List.sum_cons]

/-- Two forms in a row. -/
theorem rdMF_append (f g : PscF.MaskForm) (j : J) :
    rdMF sl (f ++ g) j = rdMF sl f j + rdMF sl g j := by
  unfold rdMF
  rw [List.map_append, List.sum_append]

/-- A factor comes out of a form with one term. -/
theorem one_mulP (i j : J) (c x : GE) : Parts.one i (c * x) j = c * Parts.one i x j := by
  unfold Parts.one
  by_cases h : j = i
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, mul_zero]

/-- A form times a factor. -/
theorem rdMF_scale (c : GE) (f : PscF.MaskForm) (j : J) :
    rdMF sl (PscF.scaleForm c f) j = c * rdMF sl f j := by
  induction f with
  | nil => exact (mul_zero c).symm
  | cons t f ih =>
    have e : PscF.scaleForm c (t :: f) = (t.1, c * t.2) :: PscF.scaleForm c f := rfl
    rw [e, rdMF_cons, rdMF_cons, ih, one_mulP, mul_add]

/-- What was heard in a sumcheck that shows values, as flat rounds. -/
def flatY (h : PscF.Heard) : List (Flat.RV GE) :=
  ([h.mu], [h.eps]) :: ((h.rounds.map fun r => (r.1, [r.2])) ++ [(h.values, [])])

/-! ## Under equality weights -/

/-- The sum of products with a constant list. -/
theorem dot_replicate (z : GE) : ∀ (n : ℕ) (s : List GE), s.length ≤ n →
    PscF.dot (List.replicate n z) s = z * s.sum
  | _, [], _ => by rw [PscF.dot_nil_right, List.sum_nil, mul_zero]
  | 0, _ :: _, h => absurd h (by simp)
  | n + 1, a :: s, h => by
    rw [List.replicate_succ, PscF.dot_cons, dot_replicate z n s (by simpa using h), List.sum_cons]
    ring

/-- **The coefficient that is not sent**: the running claim less z times the sum of the others. -/
theorem complete_eq (z : GE) (d : ℕ) (sent : List GE) (R : GE) (hs : sent.length + 1 ≤ d) :
    (PscF.Weight.equality z d).complete sent R = (R - z * sent.sum) :: sent := by
  show [] ++ (R - PscF.dot ((1 : GE) :: List.replicate (d - 1) z) ([] ++ 0 :: sent)) * 1 :: sent = _
  rw [List.nil_append, List.nil_append, PscF.dot_cons, dot_replicate z (d - 1) sent (by omega)]
  congr 1
  ring

/-- The weights' polynomials psi are all the constant 1. -/
def AllEq (l : List (PscF.Weight × GE)) : Prop := ∀ p ∈ l, p.1.psi = [1]

/-- The walk at one round. -/
theorem walk_one (w : PscF.Weight) (g : GE) :
    PscF.hidingWalk [(w, g)] = (PscF.powers 1 g w.d, PscF.polyAt w.psi g) := rfl

/-- The walk at a round that is not the last. -/
theorem walk_two (w : PscF.Weight) (g : GE) (p : PscF.Weight × GE)
    (l : List (PscF.Weight × GE)) :
    PscF.hidingWalk ((w, g) :: p :: l) =
      (PscF.powers ((PscF.hidingWalk (p :: l)).2 * g) g (w.d - 1) ++ (PscF.hidingWalk (p :: l)).1,
        (PscF.hidingWalk (p :: l)).2 * PscF.polyAt w.psi g) := rfl

/-- **The product of the polynomials psi is 1.** -/
theorem walk_snd : ∀ l : List (PscF.Weight × GE), AllEq l → (PscF.hidingWalk l).2 = 1
  | [], _ => rfl
  | [(w, g)], h => by
    rw [walk_one, h (w, g) List.mem_cons_self]
    show (0 : GE) * g + 1 = 1
    ring
  | (w, g) :: p :: l, h => by
    rw [walk_two, walk_snd (p :: l) fun q hq => h q (List.mem_cons_of_mem _ hq),
      h (w, g) List.mem_cons_self]
    show (1 : GE) * (0 * g + 1) = 1
    ring

/-- **The weights, round by round**: a round that is not the last gives the powers 1, 2, .. of its
challenge. -/
theorem walk_cons (w : PscF.Weight) (g : GE) (p : PscF.Weight × GE) (l : List (PscF.Weight × GE))
    (h : AllEq (p :: l)) :
    (PscF.hidingWalk ((w, g) :: p :: l)).1 =
      PscF.powers g g (w.d - 1) ++ (PscF.hidingWalk (p :: l)).1 := by
  rw [walk_two, walk_snd (p :: l) h, _root_.one_mul]

/-! ## The summands -/

/-- The product of two shown maps. -/
def sProd : PscF.Summand := ⟨2, 0, 2, fun _ y => [y.getD 0 0 * y.getD 1 0]⟩

/-- The first step of the tie: y0 - a y1^2 y2. -/
def sTie1 (a : GE) : PscF.Summand :=
  ⟨3, 0, 3, fun _ y => [y.getD 0 0 - a * y.getD 1 0 * y.getD 1 0 * y.getD 2 0]⟩

/-- A later step of the tie: y0^2 y1. -/
def sTie : PscF.Summand := ⟨2, 0, 3, fun _ y => [y.getD 0 0 * y.getD 0 0 * y.getD 1 0]⟩

/-- y^2 - y. -/
def sBits : PscF.Summand := ⟨1, 0, 2, fun _ y => [y.getD 0 0 * y.getD 0 0 - y.getD 0 0]⟩

/-- The leaves of the table's tree: 1 + bit · factor; the bits are a kept map. -/
def sLeaves (factor : List GE → GE) : PscF.Summand := ⟨0, 1, 0, fun p _ => [1, factor p]⟩

/-- The program's product of two shown maps reads as `sProd`. -/
theorem sProd_reads : SummandReads Lkp.summandProduct sProd where
  shown := rfl
  kept := rfl
  degree := rfl
  coeffs := fun _ y => by
    show [readE (mulE (y.getD 0 zeroE) (y.getD 1 zeroE))] =
      [(y.map readE).getD 0 0 * (y.map readE).getD 1 0]
    rw [readE_mul, read_getD, read_getD]

/-- The program's summand of the tie's first step reads as `sTie1`. -/
theorem sTie1_reads (a : E) : SummandReads (Lkp.summandTieFirst a) (sTie1 (readE a)) where
  shown := rfl
  kept := rfl
  degree := rfl
  coeffs := fun _ y => by
    show [readE (subE (y.getD 0 zeroE)
      (mulE (mulE (mulE a (y.getD 1 zeroE)) (y.getD 1 zeroE)) (y.getD 2 zeroE)))] =
      [(y.map readE).getD 0 0 - readE a * (y.map readE).getD 1 0 * (y.map readE).getD 1 0 *
        (y.map readE).getD 2 0]
    rw [readE_sub, readE_mul, readE_mul, readE_mul, read_getD, read_getD, read_getD]

/-- The program's summand of the tie's later steps reads as `sTie`. -/
theorem sTie_reads : SummandReads Lkp.summandTie sTie where
  shown := rfl
  kept := rfl
  degree := rfl
  coeffs := fun _ y => by
    show [readE (mulE (mulE (y.getD 0 zeroE) (y.getD 0 zeroE)) (y.getD 1 zeroE))] =
      [(y.map readE).getD 0 0 * (y.map readE).getD 0 0 * (y.map readE).getD 1 0]
    rw [readE_mul, readE_mul, read_getD, read_getD]

/-- The program's summand of the bits reads as `sBits`. -/
theorem sBits_reads : SummandReads Lkp.summandBits sBits where
  shown := rfl
  kept := rfl
  degree := rfl
  coeffs := fun _ y => by
    show [readE (subE (mulE (y.getD 0 zeroE) (y.getD 0 zeroE)) (y.getD 0 zeroE))] =
      [(y.map readE).getD 0 0 * (y.map readE).getD 0 0 - (y.map readE).getD 0 0]
    rw [readE_sub, readE_mul, read_getD]

/-- The program's summand of the leaves reads as `sLeaves`, if its factor of a bit reads as
`factor`. -/
theorem sLeaves_reads (S : Lkp.Public) (theta alpha : E) (order : List ℕ) (factor : List GE → GE)
    (hf : ∀ p, readE (Lkp.leavesFactor S theta alpha (Lkp.byVariable p order)) =
      factor (p.map readE)) :
    SummandReads (Lkp.summandLeaves S theta alpha order) (sLeaves factor) where
  shown := rfl
  kept := rfl
  degree := rfl
  coeffs := fun p _ => by
    show [readE oneE, readE (Lkp.leavesFactor S theta alpha (Lkp.byVariable p order))] =
      [1, factor (p.map readE)]
    rw [readE_one, hf]

/-- A claim on a value, as a sum without variables. -/
def onValue (c : PscF.PointClaim) : PscF.Claim := ⟨[], c.masks, c.value⟩

/-- The claim that stands for none. -/
def noClaim : PscF.PointClaim := ⟨[], [], 0⟩

/-! ## A step of the parts' roots -/

/-- What a step of the parts' roots hands on, field by field. -/
theorem part_out (rest : PscF.PointClaim) (s0 s1 s2 s3 s4 : Slot) (mu eps q1 q2 be v0 v1 : GE) :
    PscF.outOf (onValue rest) sProd [s0, s1, s2, s3, s4]
        ⟨mu, eps, [([q1, q2], be)], [v0, v1]⟩ =
      { point := []
        rowMasks := [(s0, 1), (s1, 1 * be), (s2, 1 * be * be)] ++
          PscF.scaleForm (eps * (0 * be + 1)) rest.masks
        rowMaps := []
        rowTarget := PscF.polyAt ((PscF.Weight.atZero 3).complete [q1, q2]
          (mu + eps * rest.value)) be - eps * (v0 * v1)
        ends := [⟨[], [(s3, be)], v0⟩, ⟨[], [(s4, be)], v1⟩]
        eps := eps
        beta := some be } := rfl

/-- **One step of the parts' roots.** -/
theorem part_step (rest : PscF.PointClaim) (s0 s1 s2 s3 s4 : Slot) (mu eps q1 q2 be v0 v1 : GE)
    (l : ℕ) (a : Parts.Acc GE J) (hm : a.mf = rdMF sl rest.masks) (ht : a.tg = rest.value) :
    let o := PscF.outOf (onValue rest) sProd [s0, s1, s2, s3, s4]
      ⟨mu, eps, [([q1, q2], be)], [v0, v1]⟩
    Parts.stepAcc (sl s0) (sl s1) (sl s2) (sl s3) (sl s4) l a
        (flatY ⟨mu, eps, [([q1, q2], be)], [v0, v1]⟩) =
      { mf := rdMF sl (o.ends.getD 1 noClaim).masks
        tg := (o.ends.getD 1 noClaim).value
        roots := fun i => if i = l then
          ⟨rdMF sl (o.ends.getD 0 noClaim).masks, (o.ends.getD 0 noClaim).value⟩ else a.roots i
        rows := a.rows ++ [⟨rdMF sl o.rowMasks, o.rowTarget⟩] } := by
  intro o
  have eo := part_out rest s0 s1 s2 s3 s4 mu eps q1 q2 be v0 v1
  have e1 : rdMF sl (o.ends.getD 1 noClaim).masks = Parts.one (sl s4) be := by
    funext j
    show rdMF sl [(s4, be)] j = _
    rw [rdMF_cons, rdMF_nil, add_zero]
  have e0 : rdMF sl (o.ends.getD 0 noClaim).masks = Parts.one (sl s3) be := by
    funext j
    show rdMF sl [(s3, be)] j = _
    rw [rdMF_cons, rdMF_nil, add_zero]
  have er : rdMF sl o.rowMasks = fun j => Parts.one (sl s1) be j + Parts.one (sl s2) (be ^ 2) j +
      Parts.one (sl s0) 1 j + eps * a.mf j := by
    funext j
    show rdMF sl ([(s0, 1), (s1, 1 * be), (s2, 1 * be * be)] ++
      PscF.scaleForm (eps * (0 * be + 1)) rest.masks) j = _
    rw [rdMF_append, rdMF_scale, rdMF_cons, rdMF_cons, rdMF_cons, rdMF_nil, hm]
    have p2 : (1 : GE) * be * be = be ^ 2 := by ring
    have p1 : (1 : GE) * be = be := _root_.one_mul be
    rw [p2, p1]
    dsimp only
    ring
  have et : o.rowTarget = mu + eps * a.tg + q1 * be + q2 * be ^ 2 - eps * (v0 * v1) := by
    show PscF.polyAt ((PscF.Weight.atZero 3).complete [q1, q2] (mu + eps * rest.value)) be -
      eps * (v0 * v1) = _
    rw [ht]
    simp only [PscF.Weight.complete, PscF.Weight.atZero, PscF.Weight.equality, List.take_zero,
      List.drop_zero, List.nil_append, PscF.polyAt_cons, PscF.polyAt_nil, PscF.dot_cons,
      PscF.dot_nil_left, List.replicate]
    ring
  rw [e1, e0, er, et]
  rfl

end Lk6.PortSim

#print axioms Lk6.PortSim.rdMF_nil
#print axioms Lk6.PortSim.rdMF_cons
#print axioms Lk6.PortSim.rdMF_append
#print axioms Lk6.PortSim.one_mulP
#print axioms Lk6.PortSim.rdMF_scale
#print axioms Lk6.PortSim.dot_replicate
#print axioms Lk6.PortSim.complete_eq
#print axioms Lk6.PortSim.walk_one
#print axioms Lk6.PortSim.walk_two
#print axioms Lk6.PortSim.walk_snd
#print axioms Lk6.PortSim.walk_cons
#print axioms Lk6.PortSim.sProd_reads
#print axioms Lk6.PortSim.sTie1_reads
#print axioms Lk6.PortSim.sTie_reads
#print axioms Lk6.PortSim.sBits_reads
#print axioms Lk6.PortSim.sLeaves_reads
#print axioms Lk6.PortSim.part_out
#print axioms Lk6.PortSim.part_step
