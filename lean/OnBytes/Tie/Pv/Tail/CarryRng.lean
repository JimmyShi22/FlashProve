-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/CarryRng.lean: the written round in which the matrix of a smallness test is
drawn, carried to the typed round.

In the protocol that a file holds, a verifier message is the round's hash blocks, with test bits
where the round asks for work. The format's sampler makes typed values from the blocks
(OnBytes/Slice/Draws.lean: wRound, valsOf, chalTo). In the round RNG these are pairs of bits, one
for each entry of the matrix, and nothing else. The typed block (Cb/Pv/Tail/Block.lean) draws a
value of Dr s: for each matrix, combination and column a coefficient. This file has the maps from
the written round to the typed one in the form that OnBytes/Slice/Carry.lean asks for, the bound on
how many written messages go to one matrix, and the tie to the record of what was drawn that the
Lean verifier's routines read. Definitions, statements and proofs.

Main names:
  `OnlyTrits d n`: the written round d draws n entries of a matrix and nothing else.
    `onlyTrits_of`: so it is if the entry has no position and no element and the kind is "entries".
  `bitsL`, `bitsL_inj`: the pairs of bits among the typed values; they determine the values.
  `matOf s d h v`: the typed challenge of the typed values v, by the verifier's index
    (flatPort, OnBytes/Tie/Pv/Tail/Draw.lean). `matOf_inj`.
  `carryRng s d h`: the maps: the prover's message goes to the empty message; a verifier message
    goes to nothing if the test of work fails, else to the matrix.
  `carryRng_fib`: at most w written verifier messages go to one matrix, where w is the sampler's
    own bound on how many strings of blocks give one value.
  `drawn_trits`: the list of entries in the format's record of what was drawn is the list of the
    typed challenge (listOf). `drawn_view`: so for the record that the kit with hash blocks makes
    of a written verifier message: the one that stands in the view that the verifier's routines
    read.
  `carryRng_tr`, `rng_out`: a written transcript whose test of work passes has an image, and on it
    the typed block puts out the statement with that matrix.

Limits: that the verifier's routine lays the record's list of entries into its own record of the
smallness test is read off the text (drawMatrixF, OnBytes/Model/Tail.lean) and not proved here. That
a file's accept has passed the round's test of work is for whoever cuts the file's run. The round
here is wRound d; a file whose rounds are laid by another function has the same verifier messages
only if that function says so.
-/
import OnBytes.Slice.Draws
import OnBytes.Tie.Pv.Tail.Draw
import Cb.Pv.Tail.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop Prob OnBytes.Slice Cb.Pv.Tail

/-- The written round draws n entries of a matrix and nothing else. -/
def OnlyTrits (d : Run.PQ.RD) (n : ℕ) : Prop := Fmt.dsOf d.entry d.kind = [.trits n]

theorem onlyTrits_of (d : Run.PQ.RD) (h1 : d.entry.poss = 0) (h2 : d.entry.drawE = 0)
    (h3 : d.entry.drawNZ = 0) (hk : d.kind = .entries) : OnlyTrits d d.entry.trits := by
  unfold OnlyTrits Fmt.dsOf Fmt.dsElems
  simp [h1, h2, h3, hk]

/-- The pairs of bits among the typed values of such a list of draws. -/
def bitsL {ds : List Fmt.Draw} {n : ℕ} (h : ds = [.trits n]) (v : Run.Vals .two ds) :
    Fin n → Prob.Coef := (h ▸ v : Run.Vals .two [.trits n]).1

theorem bitsL_inj {ds : List Fmt.Draw} {n : ℕ} (h : ds = [.trits n]) :
    Function.Injective (bitsL h) := by
  subst h
  intro a b e
  exact Prod.ext e rfl

/-- An entry of the matrix from its pair of bits, in the two files' words. -/
theorem trit_eq (b : Prob.Coef) : Run.trit b = b.val := by
  obtain ⟨x, y⟩ := b
  cases x <;> cases y <;> rfl

/-- The list of entries in the format's record. -/
theorem collect_bitsL {ds : List Fmt.Draw} {n : ℕ} (h : ds = [.trits n]) (v : Run.Vals .two ds) :
    (Fmt.collect (Run.outAll .two ds v)).trits = List.ofFn fun j => (bitsL h v j).val := by
  subst h
  show (List.ofFn fun j => Run.trit (v.1 j)) ++ [] = _
  rw [List.append_nil]
  exact congrArg List.ofFn (funext fun j => trit_eq (v.1 j))

section
variable (s : Size) (d : Run.PQ.RD) (h : OnlyTrits d (s.columns * s.tau))

/-- The typed challenge of the typed values. -/
def matOf (v : Run.Vals .two (Fmt.dsOf d.entry d.kind)) : Dr s := (flatPort s).symm (bitsL h v)

theorem matOf_inj : Function.Injective (matOf s d h) := fun _ _ e =>
  bitsL_inj h ((flatPort s).symm.injective e)

/-- The maps from the written round to the typed round. -/
def carryRng : Carry [wRound d] [IOR.drawRound (Dr s)] :=
  (fun _ => ((), ()), fun _ c => chalTo d (matOf s d h) c, fun _ _ => ())

/-- At most w written verifier messages go to one matrix. -/
theorem carryRng_fib (hlog : d.entry.logN ≤ 64) :
    (carryRng s d h).Fib (((Run.bsRound .two d.entry d.kind).w, ()) : ℕ × Unit) :=
  ⟨fun _ c' => chalTo_fib d (matOf s d h) (matOf_inj s d h) hlog c', fun _ _ => trivial⟩

/-- The format's record of what was drawn holds the list of the typed challenge. -/
theorem drawn_trits (v : Run.Vals .two (Fmt.dsOf d.entry d.kind)) :
    (Run.drawnOf .two d.entry d.kind v).trits.toArray = listOf (matOf s d h v) := by
  show (Fmt.collect (Run.outAll .two _ v)).trits.toArray = _
  rw [collect_bitsL h v]
  apply Array.toList_inj.1
  show _ = (Array.ofFn fun j => (flatPort s ((flatPort s).symm (bitsL h v)) j).val).toList
  rw [Array.toList_ofFn, Equiv.apply_symm_apply]

/-- The same of the record that the kit with hash blocks makes of a written verifier message. -/
theorem drawn_view (c : (wRound d).Chal) :
    ((Run.ckP .two).dr d.entry d.kind (GChal.old (b := d.entry.work) c)).trits.toArray =
      listOf (matOf s d h (valsOf d c)) :=
  drawn_trits s d h (valsOf d c)

/-- A written transcript whose test of work passes has an image. -/
theorem carryRng_tr (m : (wRound d).Msg) (c : (wRound d).Chal)
    (hp : GChal.pass (b := d.entry.work) c = true) :
    (carryRng s d h).tr ((m, c, ()) : Tr [wRound d]) =
      some ((((), ()), matOf s d h (valsOf d c), ()) : Tr [IOR.drawRound (Dr s)]) := by
  show (chalTo d (matOf s d h) c).bind _ = _
  unfold chalTo
  rw [if_pos hp]
  rfl

/-- On the image the typed block puts out the statement with that matrix. -/
theorem rng_out {K : Type} [CommRing K] (Λ : Letters K s) (x : Λ.X) (y : Λ.E.Str)
    (c : (wRound d).Chal) :
    (R Λ).red.out (x, y) ((((), ()), matOf s d h (valsOf d c), ()) : Tr [IOR.drawRound (Dr s)]) =
      some ((x, matOf s d h (valsOf d c)), y) := rfl

end

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.onlyTrits_of
#print axioms OnBytes.Tie.Pv.Tail.carryRng_fib
#print axioms OnBytes.Tie.Pv.Tail.drawn_view
#print axioms OnBytes.Tie.Pv.Tail.carryRng_tr
#print axioms OnBytes.Tie.Pv.Tail.rng_out
