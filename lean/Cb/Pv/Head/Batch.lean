-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Batch.lean: hidden scalars are sent and one drawn element batches them, as one kind of
block, with its soundness property.

What the verifier's routine does (SubM.claimsIn n, then SubM.batch n, OnBytes/Model/Hide.lean). The
prover sends n scalars, each a hidden value plus the mask entry of its slot. One element is drawn,
and its powers 1, x, x^2 and so on are the weights of the n hidden values in the sum from which the
next sumcheck starts.

The joints. Each hidden value is meant to be a certain function of the entries: its true value. What
the caller claims of the n values is a letter phi. Before the block: phi holds of the true values.
After it: phi holds of the n hidden values (what was sent, less the mask entries), and the hidden
values under the weights add up to the same as the true values under the weights. That last equation
is what the next sumcheck is about.

HBat is the soundness property, for a written list of numbers n: for each fixed tuple of entries, if
what stands after the block holds then what stands before it holds, except for at most n - 1 values
of the drawn element. hBat proves it for every list.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the first element of this block (in a row of blocks: of the first block) is drawn.
That is the caller's to show.

What is not claimed. That the routine computes this block's output from the same bytes. The two
facts of format that a link of a chain owes beside its soundness are not stated here. Nothing on
hiding.


-/
import Cb.G6.Cut
import Cb.G6.Johnson.Layers.Rounds
import Ior.FrameProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Bat
open Iop Prob Finset Johnson.L5.Layers TWhole

section
variable {E : Type} [Field E] [Fintype E]

/-- The round: n scalars, then one element of the field. -/
@[reducible] def batRound (E : Type) [Field E] [Fintype E] (n : ℕ) : Round :=
  { Orc := Unit, Pos := Empty, Sym := fun _ => Unit, rd := fun _ p => p.elim,
    Plain := Fin n → E, Chal := E, dOrc := (), dPlain := 0 }

def batRound_point (n : ℕ) : (batRound E n).IsPoint where
  finPos := inferInstanceAs (Fintype Empty)
  decPos := inferInstanceAs (DecidableEq Empty)
  ofSyms := fun _ => ()
  rd_ofSyms := fun _ p => p.elim
  ofSyms_rd := fun _ => rfl
  zero := fun _ => ()

/-- The block: it hands on the statement, what was sent and what was drawn. -/
def batR (E : Type) [Field E] [Fintype E] (X : Type) (n : ℕ) (Ex : ExtSpec) :
    IOR X Ex ((X × (Fin n → E)) × E) Ex where
  shape := [batRound E n]
  blinded := fun _ => true
  extReads := fun _ => ∅
  reads := fun _ => ∅
  out := fun x _ τ => some ((x, τ.plains.1), τ.rho.1)
  imp := fun y _ => y
  srcE := fun _ q => {q}
  srcO := fun _ _ => ∅
  tie := fun _ _ => ∅

/-- The error, as a count of drawn elements. -/
def batErr (E : Type) [Field E] [Fintype E] (X : Type) (n : ℕ) (Ex : ExtSpec) :
    Err (batR E X n Ex).shape :=
  ((n - 1, ()) : Err [batRound E n])

end

/-- What stands around the block and rides through it. -/
structure BatFrame (E : Type) (n : ℕ) where
  /-- what is public before the block -/
  X : Type
  /-- the entries: cells of committed arrays, and the mask row -/
  J : Type
  Kc : Type
  /-- the committed messages -/
  M : Type
  Wp : Type
  Ex : ExtSpec
  /-- what else is claimed of statement, oracles and witness -/
  A0 : IOR.Rels Kc X Ex (M × Wp)
  /-- the entries of the committed messages -/
  msg : M → J → E
  /-- the place of the mask entry of each of the n scalars -/
  msk : Fin n → J
  /-- the true values -/
  tv : X → (J → E) → Fin n → E
  /-- what the caller claims of the n values -/
  phi : X → (Fin n → E) → (J → E) → Prop

section
variable {E : Type} [Field E] [Fintype E] {n : ℕ}

/-- The hidden values: what was sent, less the mask entries. -/
def BatFrame.hid (Fr : BatFrame E n) (sent : Fin n → E) (m : Fr.J → E) : Fin n → E :=
  fun j => sent j - m (Fr.msk j)

/-- The joint before the block. -/
def batIn (Fr : BatFrame E n) : IOR.Rels Fr.Kc Fr.X Fr.Ex (Fr.M × Fr.Wp) where
  rel := fun x y w => Fr.A0.rel x y w ∧ Fr.phi x (Fr.tv x (Fr.msg w.1)) (Fr.msg w.1)
  relR := fun a w => Fr.A0.relR a w ∧ Fr.phi a.1 (Fr.tv a.1 (Fr.msg w.1)) (Fr.msg w.1)
  on := Fr.A0.on
  core := Fr.A0.core

/-- What the joint after the block says of a statement x, what was sent, what was drawn and the
entries. -/
def BatFrame.After (Fr : BatFrame E n) (x : Fr.X) (sent : Fin n → E) (c : E) (m : Fr.J → E) :
    Prop :=
  Fr.phi x (Fr.hid sent m) m ∧
    ∑ j : Fin n, c ^ (j : ℕ) * Fr.hid sent m j = ∑ j : Fin n, c ^ (j : ℕ) * Fr.tv x m j

/-- The joint after the block. -/
def batOut (Fr : BatFrame E n) :
    IOR.Rels Fr.Kc ((Fr.X × (Fin n → E)) × E) Fr.Ex (Fr.M × Fr.Wp) where
  rel := fun b y w => Fr.A0.rel b.1.1 y w ∧ Fr.After b.1.1 b.1.2 b.2 (Fr.msg w.1)
  relR := fun b w => Fr.A0.relR (b.1.1.1, b.2) w ∧ Fr.After b.1.1.1 b.1.1.2 b.1.2 (Fr.msg w.1)
  on := fun b => Fr.A0.on (b.1.1.1, b.2)
  core := Fr.A0.core

end

/-- The soundness property of the batch, at the numbers of a written list. -/
def HBat (E : Type) [Field E] [Fintype E] (sizes : List ℕ) : Prop :=
  ∀ n ∈ sizes, ∀ (Fr : BatFrame E n) (m : Fr.M),
    (batR E Fr.X n Fr.Ex).red.Know (batIn Fr).on (fun a wp => (batIn Fr).relR a (m, wp))
      (fun b wp => (batOut Fr).relR b (m, wp)) (fun _ _ wp => wp) (batErr E Fr.X n Fr.Ex)

section
variable {E : Type} [Field E] [Fintype E] {n : ℕ}

theorem bat_out (Fr : BatFrame E n) (a : Fr.X × Fr.Ex.Str) (τ : Tr (batR E Fr.X n Fr.Ex).shape)
    (b : ((Fr.X × (Fin n → E)) × E) × Fr.Ex.Str)
    (hb : (batR E Fr.X n Fr.Ex).red.out a τ = some b) :
    b = (((a.1, τ.plains.1), τ.rho.1), a.2) := by
  obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb
  exact Prod.ext (Option.some.inj h1).symm h2

theorem bat_know (Fr : BatFrame E n) (m : Fr.M) :
    (batR E Fr.X n Fr.Ex).red.Know (batIn Fr).on (fun a wp => (batIn Fr).relR a (m, wp))
      (fun b wp => (batOut Fr).relR b (m, wp)) (fun _ _ wp => wp) (batErr E Fr.X n Fr.Ex) := by
  intro a _ s
  refine le_trans (cnt_mono fun c hc => ?_)
    (cnt_badPow fun j => Fr.hid s.2 (Fr.msg m) j - Fr.tv a.1 (Fr.msg m) j)
  by_contra hn
  refine hc ?_
  intro b wp hb hB
  rw [bat_out Fr a _ b hb] at hB
  obtain ⟨h1, h2, h3⟩ := hB
  have h3' : ∑ j : Fin n, c ^ (j : ℕ) * Fr.hid s.2 (Fr.msg m) j =
      ∑ j : Fin n, c ^ (j : ℕ) * Fr.tv a.1 (Fr.msg m) j := h3
  have z : ∑ j : Fin n, c ^ (j : ℕ) *
      (Fr.hid s.2 (Fr.msg m) j - Fr.tv a.1 (Fr.msg m) j) = 0 := by
    simp only [mul_sub, sum_sub_distrib]
    exact sub_eq_zero.2 h3'
  have a0 := zero_of_pow hn z
  have e : Fr.hid s.2 (Fr.msg m) = Fr.tv a.1 (Fr.msg m) :=
    funext fun j => sub_eq_zero.1 (congrFun a0 j)
  have h2' : Fr.phi a.1 (Fr.hid s.2 (Fr.msg m)) (Fr.msg m) := h2
  rw [e] at h2'
  exact ⟨h1, h2'⟩

/-- The four items of a block's soundness side. -/
theorem bat_knowAt (Fr : BatFrame E n) :
    KnowAt (batR E Fr.X n Fr.Ex) (batIn Fr) (batOut Fr) (fun _ _ _ wp => wp)
      (batErr E Fr.X n Fr.Ex) where
  point := ⟨(batRound_point n, ())⟩
  isLocal :=
    { out := fun x _ _ τ τ' h1 h2 _ _ => by
        show some ((x, τ.plains.1), τ.rho.1) = some ((x, τ'.plains.1), τ'.rho.1)
        rw [h1, h2]
      imp := fun _ _ _ _ q _ _ h _ => h q (Finset.mem_singleton_self q) }
  onOut := fun a τ b ha hb => by
    rw [bat_out Fr a τ b hb]
    exact ha
  know := bat_know Fr

/-- The soundness property holds, for every list of numbers. -/
theorem hBat (sizes : List ℕ) : HBat E sizes := fun _ _ Fr m => bat_know Fr m

/-- The block's error is the written number. -/
theorem bat_nums (X : Type) (Ex : ExtSpec) : errList (batErr E X n Ex) = [n - 1] := rfl

end

end Cb.Pv.Head.Bat

#print axioms Cb.Pv.Head.Bat.bat_know
#print axioms Cb.Pv.Head.Bat.bat_knowAt
#print axioms Cb.Pv.Head.Bat.hBat
