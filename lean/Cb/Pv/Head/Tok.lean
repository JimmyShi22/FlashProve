-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Tok.lean: the token sumcheck of a sub-proof, as one kind of block, with its soundness
property.

What the verifier's routine does (OnBytes/Model/Tsc.lean, tscIn and tscRounds, with pscEnds and
pscRow of OnBytes/Model/Psc.lean). The prover sends one scalar for a hidden sum and, in the same
message, the sum of a hiding polynomial. One element is drawn. Then comes one round for each
variable: two scalars, one drawn element. The variables are the bits of a position, under the
equality polynomial at a public point, and then, in one use, the bits of a further index, each at
the coordinate 1/2. Then a round in one more variable: two scalars, and a drawn element that is
never 0. Then the end values, after which nothing is drawn. The summand is a sum of products of two
maps under public weights, and the end values are the values of the maps at the drawn point.

What is here. TokKind holds the public numbers of one such sumcheck: numbers of rounds, number of
end values, which products are added, and the slot of the first scalar. All other slots, the list
of rounds and the list of errors are computed from these. TokWorld says what the entries are that
claims read, where the mask entry of a slot lies among them, and which tables the maps extend.
tokT is the sumcheck as a value of the library's builder (Cb/Part/LdPartPsc.lean). tokR is the block
on the routine's own rounds: short messages, and the scalar for the sum in the first message
(Cb/Pv/Lay/Ride.lean).

The joints. What the caller claims of the sum is a letter psi, a property of a scalar and the
entries. Before the block: psi holds of the true sum plus the mask entry of the first slot. After
it: psi holds of the scalar that was sent, and the block's output claims hold: the row on the hiding
polynomial's coefficients, and for each end value that the map at the drawn point plus the last
drawn element times the value's mask entry is what was sent.

HTok is the soundness property, for a written list of kinds: for each fixed tuple of entries, if
what stands after the block holds then what stands before it holds, except for at most 1, then 2 for
each variable, then 2 (of the elements other than 0), then 0 values of the drawn elements.
hTok proves it for every list.

The property speaks of each fixed tuple of entries. It is of use only where all entries in J are
committed before the first element of this block (in a row of blocks: of the first block) is drawn.
That is the caller's to show.

The coordinate 1/2 is the inverse of 2: it is a half only where 2 is not 0 in the field.

What is not claimed. The block rejects nothing (tok_out, Cb/Pv/Head/TokMeans.lean). Its output
claims are tested later: the verifier adds them to the sub-proof's claims and batches all of these
under one drawn element. That step is no part of this block, and its error is not among this block's
errors. That the routine computes this block's output from the same bytes is not claimed, nor that
the tables are what the later claims of a sub-proof read. The two facts of format that a link of a
chain owes beside its soundness are not stated here. Nothing on hiding.


-/
import Cb.Pv.Lay.Ride
import Cb.G6.Pick
import Cb.Part.LdPartPscProofs
import Cb.Ld.LdPscProofsOur
import Blocks.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head.Tok
open Iop Prob Finset Johnson.L5.Layers Johnson.L5.Door TWhole

/-! ## The public numbers -/

/-- The public numbers of one token sumcheck. -/
structure TokKind where
  /-- the rounds over the bits of a position -/
  lt : ℕ
  /-- the further rounds, over the bits of an index that is summed without weights -/
  more : ℕ
  /-- the number of end values -/
  shown : ℕ
  /-- the products of two maps that the summand adds, in the order of their weights -/
  pairs : List (Fin shown × Fin shown)
  /-- the slot of the scalar that is sent for the sum -/
  sCl : ℕ

namespace TokKind

/-- the number of variables, without the last one -/
def vars (k : TokKind) : ℕ := k.lt + k.more
/-- the number of products -/
def np (k : TokKind) : ℕ := k.pairs.length
/-- the first slot of the hiding polynomial's coefficients -/
def first (k : TokKind) : ℕ := k.sCl + 1
/-- the slot of the first end value -/
def sEnd (k : TokKind) : ℕ := k.sCl + 1 + (2 * k.vars + 3)
/-- the number of slots that the sumcheck takes -/
def slots (k : TokKind) : ℕ := 1 + (2 * k.vars + 3) + k.shown
/-- The rounds: the name of the plan's entry, the scalars sent, the elements drawn. -/
def rounds (k : TokKind) : List (String × ℕ × ℕ) :=
  ("PSC epsilon", 2, 1) :: (List.replicate k.vars ("PSC round", 2, 1) ++
    [("PSC Y", 2, 1), ("PSC values", k.shown, 0)])
/-- The errors, round by round, as counts of drawn elements. -/
def errs (k : TokKind) : List ℕ := 1 :: ((List.replicate k.vars 2 ++ [2]) ++ [0])

end TokKind

/-! ## What is public, and the entries -/

/-- What is public before the sumcheck's first message. -/
structure TokSt (E Pb : Type) (k : TokKind) where
  /-- the point over the positions -/
  zt : Fin k.lt → E
  /-- the weights of the products -/
  om : Fin k.np → E
  /-- whatever else is public and the tables or the caller's claim read -/
  pb : Pb

/-- The coordinate of the equality polynomial for each variable: the point's, then 1/2. -/
def TokSt.pt {E Pb : Type} [Field E] {k : TokKind} (st : TokSt E Pb k) : Fin k.vars → E :=
  fun i => if h : (i : ℕ) < k.lt then st.zt ⟨i, h⟩ else 2⁻¹

/-- The entries that claims read, and how the sumcheck reads them. -/
structure TokWorld (E : Type) (k : TokKind) where
  /-- further public data -/
  Pb : Type
  /-- the entries: cells of committed arrays, and the mask row -/
  J : Type
  [finJ : Fintype J]
  [decJ : DecidableEq J]
  /-- the place of the mask entry of a slot -/
  msk : ℕ → J
  /-- The table that each map extends. Its index is the position times 2^more plus the further
  index; coordinate 0 of a point belongs to the top bit. -/
  tab : Pb → (J → E) → Fin k.shown → ℕ → E

attribute [instance] TokWorld.finJ TokWorld.decJ

/-- The slot of a coefficient of the hiding polynomial, from the slot b on: by variable, then by
degree from 1 up; the last variable begins with the constant. -/
def wPos {E : Type} : (l : List (PFmt E)) → ℕ → PIdx l → ℕ
  | [], b, _ => b
  | [_], b, .inl t => b + 1 + t
  | [_], b, .inr _ => b
  | _ :: _ :: _, b, .inl t => b + t
  | f :: g :: l, b, .inr i => wPos (g :: l) (b + f.n) i

section
variable {E : Type} [Field E]

/-- An extension over g coordinates has degree at most 1 in each. -/
theorem degLE_ext (g : ℕ) (v : ℕ → E) :
    Alg.DegLE (fun _ : Fin g => 1) (fun z : Fin g → E => Blocks.ext g v (Blocks.nat z)) := by
  unfold Blocks.ext
  refine Alg.DegLE.sum _ fun X _ => ?_
  simp only [Blocks.eqN_nat]
  exact (Alg.DegLE.eqk _).mul_const _

/-- The summand as a sum of terms over maps. -/
@[reducible] def tokSm (k : TokKind) (W : TokWorld E k) : LdPartSm E (TokSt E W.Pb k) W.J where
  k := k.vars
  A := Fin k.shown
  F := fun st m a z => Blocks.ext k.vars (W.tab st.pb m a) (Blocks.nat z)
  terms := (List.finRange k.np).map fun j =>
    ⟨fun st _ => st.om j, [(k.pairs.get j).1, (k.pairs.get j).2]⟩
  w := fun st i => some (st.pt i)

variable [Fintype E]

/-- What the sumcheck adds: degree 2 in each variable and in the last one; the mask entry of the
first slot comes in with the claim; the places of its own mask entries. -/
@[reducible] noncomputable def tokMk (k : TokKind) (W : TokWorld E k) : LdPartMk (tokSm k W) :=
  ⟨fun _ => 2, 2, fun _ j => if j = W.msk k.sCl then 1 else 0,
    fun i => W.msk (wPos _ k.first i), fun a => W.msk (k.sEnd + a)⟩

theorem tok_ok (k : TokKind) (W : TokWorld E k) : (tokSm k W).OK (tokMk k W) (fun _ _ => 1) where
  map := fun st m a => degLE_ext k.vars (W.tab st.pb m a)
  fit := fun t ht => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 ht
    exact ⟨fun _ => 0, fun st => Alg.DegLE.const _ _, fun _ => by simp⟩
  plain := fun _ _ h => by simp at h
  dy := fun t ht => by
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 ht
    simp

/-- The sumcheck, as a value of the library's builder. -/
noncomputable abbrev tokT (k : TokKind) (W : TokWorld E k) : PscOur E := (tokSm k W).our (tokMk k W)

theorem tok_conds (k : TokKind) (W : TokWorld E k) :
    (tokT k W).VarsOK ∧ (tokT k W).ValInj ∧ (tokT k W).DegX ∧ (tokT k W).DegY :=
  ldPartPsc_ok E _ _ _ _ _ (tok_ok k W)

/-- In every round the constant coefficient is the one that is not sent, and that is lawful. -/
theorem tok_eq0 (k : TokKind) (W : TokWorld E k) : Eq0 (tokT k W).par :=
  our_eq0 (tokT k W) fun st => ldPart_eq0 k.vars (fun _ => 2) (TokSt.pt (k := k) st)

/-! ## The block, its joints, its errors -/

/-- The block, on the routine's rounds. -/
noncomputable def tokR (k : TokKind) (W : TokWorld E k) (Ex : ExtSpec) :
    IOR (TokSt E W.Pb k) Ex ((TokSt E W.Pb k × E) × (tokT k W).par.Out) Ex :=
  Cb.Pv.Lay.rideR (tokT k W).par (F₀ (tokT k W).par) id Ex

/-- The errors, as counts of drawn elements. -/
noncomputable def tokErr (k : TokKind) (W : TokWorld E k) (Ex : ExtSpec) :
    Err (tokR k W Ex).shape :=
  ((1, errS (tokT k W).par) : Err (shapeR (tokT k W).par))

/-- What stands around the block and rides through it. -/
structure TokFrame (E : Type) (k : TokKind) (W : TokWorld E k) where
  Kc : Type
  /-- the committed messages -/
  M : Type
  Wp : Type
  Ex : ExtSpec
  /-- what else is claimed of state, oracles and witness -/
  A0 : IOR.Rels Kc (TokSt E W.Pb k) Ex (M × Wp)
  /-- the entries of the committed messages -/
  msg : M → W.J → E
  /-- what the caller claims of the scalar for the sum -/
  psi : TokSt E W.Pb k → E → (W.J → E) → Prop

/-- The joint before the block: the caller's claim holds of the true sum plus its mask entry. -/
noncomputable def tokIn (k : TokKind) (W : TokWorld E k) (Fr : TokFrame E k W) :
    IOR.Rels Fr.Kc (TokSt E W.Pb k) Fr.Ex (Fr.M × Fr.Wp) :=
  Cb.Pv.Lay.rideIn (tokT k W).par id Fr.Ex (fun w : Fr.M × Fr.Wp => Fr.msg w.1) Fr.A0 Fr.psi

/-- The joint after the block: the caller's claim holds of the scalar that was sent, and the
block's output claims hold. -/
noncomputable def tokOut (k : TokKind) (W : TokWorld E k) (Fr : TokFrame E k W) :
    IOR.Rels Fr.Kc ((TokSt E W.Pb k × E) × (tokT k W).par.Out) Fr.Ex (Fr.M × Fr.Wp) :=
  Cb.Pv.Lay.rideOut (tokT k W).par id Fr.Ex (fun w : Fr.M × Fr.Wp => Fr.msg w.1) Fr.A0 Fr.psi

end

/-! ## The soundness property -/

/-- The soundness property of the token sumcheck, at the kinds of a written list. -/
def HTok (E : Type) [Field E] [Fintype E] (sizes : List TokKind) : Prop :=
  ∀ k ∈ sizes, ∀ (W : TokWorld E k) (Fr : TokFrame E k W) (m : Fr.M),
    (tokR k W Fr.Ex).red.Know (tokIn k W Fr).on (fun a wp => (tokIn k W Fr).relR a (m, wp))
      (fun b wp => (tokOut k W Fr).relR b (m, wp)) (fun _ _ wp => wp) (tokErr k W Fr.Ex)

section
variable {E : Type} [Field E] [Fintype E]

/-- The four items of a block's soundness side. -/
theorem tok_knowAt (k : TokKind) (W : TokWorld E k) (Fr : TokFrame E k W) :
    KnowAt (tokR k W Fr.Ex) (tokIn k W Fr) (tokOut k W Fr) (fun _ _ _ wp => wp)
      (tokErr k W Fr.Ex) := by
  obtain ⟨hV, hI, hX, hY⟩ := tok_conds k W
  exact Cb.Pv.Lay.ride_knowAt (tokT k W).par (F₀ (tokT k W).par) id Fr.Ex Fr.M Fr.Wp Fr.Kc Fr.A0
    Fr.msg Fr.psi ((psc_our_ok E (tokT k W)).1 hV) (psc_our_deg E (tokT k W) hX hY)
    ((psc_our_ok E (tokT k W)).2 hI)

/-- The soundness property holds, for every list of kinds. -/
theorem hTok (sizes : List TokKind) : HTok E sizes :=
  fun k _ W Fr m => (tok_knowAt k W Fr).know m

end

end Cb.Pv.Head.Tok

#print axioms Cb.Pv.Head.Tok.tok_knowAt
#print axioms Cb.Pv.Head.Tok.hTok
