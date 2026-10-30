-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailRngOnToy.lean: a written caller of the kind "the draw of the matrix of a smallness
test with a condition that is carried": the kind is not empty.

A theorem on all callers of a kind that meet the kind's condition says nothing if there is no such
caller. Here is one, closed: nothing in it is a letter. Its sizes are those of the toy of
Cb/Pv/Tail/Toy.lean: one matrix with one cell and one column, one read, one combination. Its field
is the library's field Cb.Gl.E. Its committed messages are one plain oracle message with two
entries, the symbol and the read (`Cb.Tw.sigId`, Cb/Pv/Lookup/Know/TwSig.lean). Its statements are
the two truth values, and the condition that is carried holds at one of them alone. Definitions,
statements and proofs.

Main names:
  `toySg`, `toyCaller`, `toyOn`: the signature, the caller of the draw, the caller with its
    condition.
  `toyOn_mem`: it meets the kind's condition.
  `toyOn_shape`: its block has a round.
  `tailRngOn_some`: so the kind has a caller that meets its condition and whose block has a round.
  `toyOn_sizes`: the caller has one matrix, one column, one read and one combination.
  `toyOn_cond`: the condition holds at one statement and fails at another.
  `toyOn_in`: at the message with the symbol 1 and the read 1 there is a cell.
  `toyOn_tooth`: at the message with the symbol 1 and the read 2 there is none.
  `toyOn_joint`: at the statement "true" and the first of these messages the joint before the draw
    is met: its condition and its relation hold, whatever the further witness.
  `toyOn_out`: at that message and the drawn entry 1 the digits 1 and 1 meet all clauses of the
    relation behind the draw.
  `toyOn_eps`: the block's error is 2 of the 4 values that can be drawn.

Limits: a toy: its sizes are no sizes of a model, and its oracle message has the plainest code, in
which the word is the message.
-/
import Johnson.Top.H.TailRngOn
import Cb.Pv.Tail.Toy
import Cb.Pv.Lookup.Know.TwSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj.TailRow
open KObj Iop Prob Hiop Cb IOR TWhole VerifiableInference.OnPublicFiles

/-- One plain oracle message with two entries: the symbol and the read. -/
@[reducible] def toySg : Sig Cb.Gl.E := Cb.Tw.sigId Cb.Gl.E Unit fun _ => Fin 2

/-- The caller of the draw at the toy's sizes. -/
@[reducible] def toyCaller : TailCaller where
  s := Cb.Pv.Tail.Toy.sz
  Sg := toySg
  X := Bool
  Ex := Cb.Pv.Tail.Toy.eNone
  Wp := Cb.Pv.Tail.Dig Cb.Gl.E Cb.Pv.Tail.Toy.sz
  w := fun _ _ _ _ => 1
  sym := fun m _ _ _ => m () (0 : Fin 2)
  tab := fun m _ _ _ => m () (1 : Fin 2)
  dig := fun Z => Z
  ride := fun _ _ _ => True

/-- The caller with a condition on its statements: the statement is "true". -/
@[reducible] def toyOn : TailCallerOn := ⟨toyCaller, fun a => a.1 = true⟩

theorem toyOn_mem : KTailRngOn.mem toyOn := Cb.Pv.Tail.Toy.sz_ok

theorem toyOn_shape : (KTailRngOn.blk toyOn).R.shape ≠ [] := by
  show [IOR.drawRound (Cb.Pv.Tail.Dr toyOn.c.s)] ≠ []
  exact List.cons_ne_nil _ _

/-- The kind has a caller that meets its condition and whose block has a round. -/
theorem tailRngOn_some : ∃ c : KTailRngOn.ι, KTailRngOn.mem c ∧ (KTailRngOn.blk c).R.shape ≠ [] :=
  ⟨toyOn, toyOn_mem, toyOn_shape⟩

theorem toyOn_sizes : toyOn.c.s.NM = 1 ∧ toyOn.c.s.k 0 = 1 ∧ toyOn.c.s.nr 0 = 1 ∧
    toyOn.c.s.tau = 1 := ⟨rfl, rfl, rfl, rfl⟩

theorem toyOn_cond : toyOn.on (true, ()) ∧ ¬ toyOn.on (false, ()) :=
  ⟨rfl, fun h => Bool.noConfusion h⟩

/-- The message with the symbol x and the read y. -/
def toyMsg (x y : Cb.Gl.E) : toySg.Msg := fun _ j => if j = (0 : Fin 2) then x else y

/-- At the symbol 1 and the read 1 there is a cell. -/
theorem toyOn_in : Cb.Pv.Tail.relIn toyOn.c.letters true (toyMsg 1 1) := fun _ _ =>
  ⟨fun _ => 1, fun _ => by norm_num, fun i' => by
      show (1 : Cb.Gl.E) = ((Alg.pack ((4 : ℕ) : ℤ) (fun _ : Fin 1 => (1 : ℤ)) i' : ℤ) : Cb.Gl.E)
      rw [Cb.Pv.Tail.Toy.pack_one (fun _ : Fin 1 => (1 : ℤ)) i', Int.cast_one],
    fun _ => by
      show (1 : Cb.Gl.E) = ∑ _i : Fin 1, (1 : Cb.Gl.E) * (((1 : ℤ) : ℤ) : Cb.Gl.E)
      simp⟩

/-- At the symbol 1 and the read 2 there is none. -/
theorem toyOn_tooth : ¬ Cb.Pv.Tail.relIn toyOn.c.letters true (toyMsg 1 2) := fun h => by
  obtain ⟨a, -, hp, hr⟩ := h (⟨0, Nat.one_pos⟩ : Fin 1) (⟨0, Nat.one_pos⟩ : Fin 1)
  have e1 : (1 : Cb.Gl.E) = ((Alg.pack ((4 : ℕ) : ℤ) (show Fin 1 → ℤ from a)
      ((⟨0, by decide⟩ : Fin (Alg.symRows 1)) : ℕ) : ℤ) : Cb.Gl.E) :=
    hp (⟨0, by decide⟩ : Fin (Alg.symRows 1))
  rw [Cb.Pv.Tail.Toy.pack_one] at e1
  have e2 : (2 : Cb.Gl.E) =
      ∑ i : Fin 1, (1 : Cb.Gl.E) * (((show Fin 1 → ℤ from a) i : ℤ) : Cb.Gl.E) :=
    hr (⟨0, Nat.one_pos⟩ : Fin 1)
  simp only [Finset.univ_unique, Finset.sum_singleton, one_mul] at e2
  have e3 : (2 : Cb.Gl.E) = 1 := e2.trans e1.symm
  have e4 : (1 : Cb.Gl.E) = 0 := by
    have : (1 : Cb.Gl.E) + 1 = 1 + 0 := by rw [add_zero, one_add_one_eq_two]; exact e3
    exact add_left_cancel this
  exact one_ne_zero e4

/-- The joint before the draw is met at the toy. -/
theorem toyOn_joint (Z : toyOn.c.Wp) :
    toyOn.A.on (true, ()) ∧ toyOn.A.relR (true, ()) (toyMsg 1 1, Z) :=
  ⟨⟨trivial, rfl⟩, trivial, toyOn_in⟩

/-- The packing of one cell, over the library's field. -/
theorem toyPack (a : Fin 1 → Cb.Gl.E) (i' : Fin (Alg.symRows 1)) :
    Alg.pack ((4 : ℕ) : ℤ) a i' = a 0 := by
  have h : (i' : ℕ) = 0 := by
    have := i'.2
    unfold Alg.symRows at this
    omega
  rw [h]
  simp [Alg.pack, Alg.lane]

/-- The digits 1 and 1. -/
def toyDig : Cb.Pv.Tail.Dig Cb.Gl.E Cb.Pv.Tail.Toy.sz := ⟨fun _ _ _ => 1, fun _ _ _ => 1⟩

/-- The combination that these digits give is 1. -/
theorem toyComb (μ : Fin 1) (u : Fin 1) (i : Fin 1) :
    Cb.Pv.Tail.comb (s := Cb.Pv.Tail.Toy.sz) toyDig μ u i = 1 := by
  show (1 : Cb.Gl.E) + ((2 : ℕ) : Cb.Gl.E) * 1 - ((2 : ℕ) : Cb.Gl.E) = 1
  ring

/-- The relation behind the draw can hold. -/
theorem toyOn_out : Cb.Pv.Tail.relOut toyOn.c.letters true (Cb.Pv.Tail.Toy.dr (true, false))
    (toyMsg 1 1) toyDig :=
  ⟨fun _ _ _ => ⟨⟨1, by norm_num, by simp [toyDig]⟩, ⟨1, by norm_num, by simp [toyDig]⟩⟩,
    fun μ u i' => by
      show ∑ _c : Fin 1, (((1 : ℤ) : ℤ) : Cb.Gl.E) * (1 : Cb.Gl.E) =
        Alg.pack ((4 : ℕ) : ℤ) (Cb.Pv.Tail.comb (s := Cb.Pv.Tail.Toy.sz) toyDig μ u) i'
      rw [toyPack, toyComb]
      simp,
    fun μ u _ => by
      show ∑ _c : Fin 1, (((1 : ℤ) : ℤ) : Cb.Gl.E) * (1 : Cb.Gl.E) =
        ∑ i : Fin 1, (1 : Cb.Gl.E) * Cb.Pv.Tail.comb (s := Cb.Pv.Tail.Toy.sz) toyDig μ u i
      simp [toyComb]⟩

/-- The block's error: 2 of 4. -/
theorem toyOn_eps : TWhole.errList (KTailRngOn.blk toyOn).err = [2] ∧
    Fintype.card (Cb.Pv.Tail.Dr toyOn.c.s) = 4 := by
  have h : Fintype.card (Cb.Pv.Tail.Dr Cb.Pv.Tail.Toy.sz) = 4 := Cb.Pv.Tail.Toy.toy_eps.2
  refine ⟨?_, h⟩
  show [Fintype.card (Cb.Pv.Tail.Dr Cb.Pv.Tail.Toy.sz) / 2 ^ 1] = [2]
  rw [h]
  norm_num

end KObj.TailRow

#print axioms KObj.TailRow.toyOn_mem
#print axioms KObj.TailRow.toyOn_shape
#print axioms KObj.TailRow.tailRngOn_some
#print axioms KObj.TailRow.toyOn_sizes
#print axioms KObj.TailRow.toyOn_cond
#print axioms KObj.TailRow.toyOn_in
#print axioms KObj.TailRow.toyOn_tooth
#print axioms KObj.TailRow.toyOn_joint
#print axioms KObj.TailRow.toyOn_out
#print axioms KObj.TailRow.toyOn_eps
