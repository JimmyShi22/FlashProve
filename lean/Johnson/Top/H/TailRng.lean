-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/TailRng.lean: the kind "the draw of the matrix of a smallness test" as a value of
`BaseKind` and of `KObj.KFam`, with its hypothesis and the proof of it.

Nothing new is proved: the proof is `Cb.Pv.Tail.knowAt` (Cb/Pv/Tail/Know.lean), which rests on the
library's count for the range check (Alg/Range.lean). The round: the prover sends nothing; the
verifier draws, for each matrix, combination and column, a coefficient, that is two bits: 0 with two
of the four values, 1 and -1 with one each. Before the round: there are small integer cells whose
packing is the committed symbols and whose weighted sums are the committed reads. Behind it: there
are digits in their tables that meet every tie and every read at the drawn matrix.
Main names:
  `TailCaller`: who calls the draw: the sizes s, a signature `Sg` whose messages are the committed
    ones, the explicit statement, the further oracles, the further witness, and the readings: the
    reads' weights off the statement, the symbols and the reads off the messages, the digits off the
    witness. Data alone: no field is a proof.
  `TailCaller.letters`: the letters of Cb/Pv/Tail/Block.lean.
  `kTailRng L`: the kind at a written list L of callers.
  `TailOK L`: at each caller the two digits together do not reach beyond twice the shift
    (`Cb.Pv.Tail.Size.OK`): a condition on public data.
  `tailRng_knowAt`, `tailRng_good`: all four facts; every block of the lifted kind has
    `KObj.BK.Good`.
  `HTailRng`, `hTailRng`: closed: for every list of callers that meets the condition the kind is
    knowledge sound; its proof.
  `KTailRng`, `KTailRng_good`: the kind as a family of blocks, whoever calls it.
  `KTailRng_fills`: at an assignment of kinds to the families of the first proof chain
    (Johnson/E/KObj/Plan0.lean) that has this kind at the family rng, that family's hypothesis
    holds.
Limits: the messages of `Sg` are what is committed before the matrix is drawn: the symbols and the
reads. The digits' message is sent behind the draw and must not be among them: here the digits are
read off the further witness. A caller that puts them among the messages gets a true statement about
another protocol. That the digits are in their tables is a clause of the joint behind the round, to
be had from the lookup on the digits. It is not said which caller stands at which place of a proof
file, nor how the joints meet a neighbour's. That the round and its error are those of the Lean
verifier's plan, and which drawn bits are which coefficient, is in OnBytes/Tie/Pv/Tail/.
-/
import Johnson.Top.KindKnowAt
import Johnson.E.KObj.Plan0
import Cb.Pv.Tail.Know
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR TWhole

/-- Who calls the draw of the matrix: data alone. The messages of `Sg` are those committed before
the draw. -/
structure TailCaller : Type 1 where
  /-- the public numbers -/
  s   : Cb.Pv.Tail.Size
  /-- the signature: the committed messages are its -/
  Sg  : Sig Cb.Gl.E
  /-- the explicit statement, the further oracles, the further witness -/
  X   : Type
  Ex  : ExtSpec
  Wp  : Type
  /-- the weights of a read on the rows of cells -/
  w   : X → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.m μ) → Cb.Gl.E
  /-- the committed symbols: matrix, row of symbols, column -/
  sym : Sg.Msg → ∀ μ : Fin s.NM, Fin (Alg.symRows (s.m μ)) → Fin (s.k μ) → Cb.Gl.E
  /-- the committed reads: matrix, read, column -/
  tab : Sg.Msg → ∀ μ : Fin s.NM, Fin (s.nr μ) → Fin (s.k μ) → Cb.Gl.E
  /-- the digits, a part of the further witness -/
  dig : Wp → Cb.Pv.Tail.Dig Cb.Gl.E s
  /-- what else the joint says -/
  ride : X × Ex.Str → Sg.Msg → Wp → Prop

/-- The letters of the block. -/
@[reducible] def TailCaller.letters (c : TailCaller) : Cb.Pv.Tail.Letters Cb.Gl.E c.s where
  X := c.X
  M := c.Sg.Msg
  E := c.Ex
  W := c.Wp
  w := c.w
  sym := c.sym
  tab := c.tab
  dig := c.dig
  ride := c.ride

/-- The kind, at a written list of callers. -/
@[reducible] noncomputable def kTailRng (L : List TailCaller) : BaseKind.{1} Cb.Gl.E where
  Size := TailCaller
  sizes := L
  Sg := fun c => c.Sg
  Kc := fun _ => Unit
  St := fun c => c.X
  St' := fun c => c.X × Cb.Pv.Tail.Dr c.s
  Wp := fun c => c.Wp
  Wp' := fun c => c.Wp
  E₀ := fun c => c.Ex
  E₀' := fun c => c.Ex
  R := fun c => Cb.Pv.Tail.R c.letters
  A := fun c => Cb.Pv.Tail.A c.letters
  B := fun c => Cb.Pv.Tail.B c.letters
  ext := fun _ _ _ _ wp => wp
  ε := fun c => Cb.Pv.Tail.eps c.letters

/-- The condition on each caller's public numbers. -/
def TailOK (L : List TailCaller) : Prop := ∀ c ∈ L, c.s.OK

/-- All four facts at once. -/
theorem tailRng_knowAt (L : List TailCaller) (h : TailOK L) : (kTailRng L).KnowAtAll :=
  fun c hc => Cb.Pv.Tail.knowAt c.letters (h c hc)

/-- Every block of the kind, lifted over its caller's signature, has the property that the spine
asks. -/
theorem tailRng_good (L : List TailCaller) (h : TailOK L) :
    ∀ c ∈ L, ((kTailRng L).toKind.block c).Good :=
  BaseKind.good_of_knowAt (tailRng_knowAt L h)

/-- The hole of the kind, closed: knowledge soundness alone, for every list of callers that meets
the condition. -/
def HTailRng : Prop := ∀ L : List TailCaller, TailOK L → (kTailRng L).Know

/-- Its discharge. -/
theorem hTailRng : HTailRng := fun L h => BaseKind.know_of_knowAt (tailRng_knowAt L h)

end VerifiableInference.OnPublicFiles

namespace KObj
open VerifiableInference.OnPublicFiles

/-- The draw of the matrix of a smallness test, whoever calls it. -/
noncomputable def KTailRng : KFam.{1} where
  ι := TailCaller
  mem := fun c => c.s.OK
  src := fun c => (kTailRng [c]).toKind.src c
  dst := fun c => (kTailRng [c]).toKind.dst c
  blk := fun c => (kTailRng [c]).toKind.block c

theorem KTailRng_good : KTailRng.Good := fun c hc =>
  tailRng_good [c] (fun c' h' => by rw [List.mem_singleton.1 h']; exact hc) c
    (List.mem_singleton.2 rfl)

/-- The hypothesis of the family rng, where this kind stands at it. -/
theorem KTailRng_fills (K : PFam → KFam.{1}) (h : K .rng = KTailRng) : (K .rng).Good := by
  rw [h]
  exact KTailRng_good

end KObj

#print axioms VerifiableInference.OnPublicFiles.hTailRng
#print axioms VerifiableInference.OnPublicFiles.tailRng_good
#print axioms KObj.KTailRng_good
#print axioms KObj.KTailRng_fills
