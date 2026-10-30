-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/K14BatchLinearConstraintsSecondPart.lean: the first block of a proof file's last chain: the second part of
the kind K14. Definitions with code. No theorem.

This chain has three names: "the last chain" and "the third chain" in these files, "the second
chain" in the format (Johnson/Desc/Block.lean: the field `second`; the refusal "the second chain's
start") and in the program `verify-on-bytes`.

What happens. Nobody sends, nothing is drawn, nothing is read. Omega, which the shared chain has
sent and sampled, comes into this chain's statement with its sample rows and its pad, and joins the
request's own group, of which W is a member. The row (Dot), the claim's row weights g on Omega
against W at the shared point psi, is laid on that group as its last open row.

The taking-over calls the plain ground's `adoptP`, `elsewhereP` and `joinP`
(Johnson/Desc/First/Base/Ground.lean). Omega's tree keeps the number and the source that it has in
the shared chain's book. A view has no root: under which root Omega's columns are opened is held by
the compiler, by the source that the declared rounds name (Johnson/Desc/Third/TakenSources.lean).

Main names:
  `P₁₄`, `p₁₄Z`: the public parameters: the codes, the shape of the test on the table, the answers
    to a sample; made of what the planner has sized, alone. The field `samples` is read by no
    definition of these six files.
  `start₃F`: the chain's start in the shape of `FileDescription.start₃`.
  `takeOver`: Omega is taken over. `batchLinearConstraintsSecondPart`: the block.

Limits.
(1) That the shared chain has tested Omega is not asked. Of the shared statement `takeOver` asks
that Omega is there and is sampled there; the plain ground's further clauses (the same rows, degree,
answers and codes) compare it with the copy that was just made of it. If no test has begun on
Omega's group there, the row that ties Omega to the table was never tested, and (Dot) says nothing.
It is refused only by the shared chain's own last block, where that is laid.
(2) Omega is asked to have the plan's shape `p.S.omega`, as W is asked to have `p.S.w`. The tree's
shape laid here is not compared with the shared book's. That the one part of Omega's tree there is
Omega is not asked.
(3) No clause asks that the row (Eval) lies on the own group.
(4) The start and the block each take a `P₁₄`: that it is the same one is not asked here. `last`
(Johnson/Desc/Third/Chain.lean) makes both of one p: a description is to take the chain from there.
(5) Of g `linDotRow` asks that each vector has as many variables as the matrix has row bits;
`tensorBelow`, which cuts each vector to the matrix's rows, can refuse too. The plain ground's
`addRowP` asks `Tensor.ok` of the vectors as they are cut and laid, not of g itself.
(6) Which messages beside W are members of the own group is not asked.
(7) The block hands the state on without the two ends, so a second such block is refused.
Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.State
import Johnson.Desc.First.Base.Ground
import Johnson.Desc.Block

set_option autoImplicit false
set_option relaxedAutoImplicit false

open OnBytes
open Desc.Plain (DState)
open VerifiableInference.Desc.Ground (adoptP elsewhereP joinP addRowP)

namespace VerifiableInference.Desc.Third

/-- The public parameters of K14's second part and of the chain's start. -/
structure P₁₄ where
  codes : Codes
  S : Params.LinShape
  samples : Nat

/-- At what the planner has sized. -/
def p₁₄Z (s : Params.Setting) (codes : Codes) (x : Params.LinSized) : P₁₄ :=
  { codes := codes, S := x.shape, samples := s.samples }

/-- What the start is handed of the first chain's last state: its statement, its book, the roots
received, the numbers of W, of the own group and of the mask as that chain's own record names them,
and the list of pending rows. -/
structure FirstEnd₃ where
  st : Statement
  book : TreeBook
  roots : Nat
  w : Nat
  own : Nat
  mask : Option Nat
  pending : List TensorRow

/-- **The third chain's start**, in the shape of FileDescription.start₃. first: what is taken of the first
chain's last state, or nothing where its record names no W: then the start refuses. shared: of the
shared chain's last state its statement, its book, the shared point, Omega's number. It reads
nothing of the instance. -/
def start₃F {XiPub S₁ S₂ : Type} (p : P₁₄) (first : S₁ → Option FirstEnd₃)
    (shared : S₂ → SharedOut) : XiPub → S₁ → S₂ → Except String S₃ := fun _ e₁ e₂ =>
  match first e₁ with
  | none => .error "the first chain's end names no W"
  | some f => start₃E p.codes p.S f.st f.book f.roots f.w f.own f.mask f.pending (shared e₂)

/-- **Omega is taken over** from the shared chain's end o and joins the group own. Returns its
number here. Nine named steps. The first four are linAdopt's own in `verify-on-bytes`
(OnBytes/Iop/Lin.lean:311-317, but for ":314-316", on the source's form). Then: Omega has the plan's
shape; the plain ground's adoptP; the look-up of the new message's number; elsewhereP and joinP. -/
def takeOver (S : Params.LinShape) (own : Nat) (o : SharedOut) (d : DState Loc₃) :
    Except String (Nat × DState Loc₃) := do
  let q ← named "Omega: it has a place in the shared chain's book" o.book.place[o.omega]?
  let t ← named "Omega: its tree is in the shared chain's book" o.book.trees[q.1]?
  need "Omega: it has a tree to itself" (t.parts.size == 1)
  let y ← named "Omega: it is in the shared chain's statement" o.st.oracles[o.omega]?
  need "Omega: it has the plan's shape" (decide (y.shape = S.omega))
  let a ← named "Omega: its tree comes in"
    (adoptP d #[{ shape := y.shape, leafClass := S.omegaLeafClass }] #[(t.number, t.src)])
  let mine ← named "Omega: its number here" a.1[0]?
  let d₁ ← named "Omega: it is sampled there, under the same shape and codes"
    (elsewhereP a.2 mine o.st o.omega)
  let d₂ ← named "Omega: it joins the own group" (joinP d₁ own mine false)
  pure (mine, d₂)

/-- **K14, second part**: Omega is taken over and joins the own group; the row (Dot) is laid as that
group's last open row. On the plan: the codes' message lengths are powers of two; the shape is
lawful at the codes; it does not split the row (Dot). It hands the state on without the two ends, so
a second such block is refused. -/
def batchLinearConstraintsSecondPart {Cl : Type} (p : P₁₄) : Block S₃ Cl :=
  { name := "K14, second part", place := ⟨3, none, 0, .K14⟩
    planOk := p.codes.lengthsOk && linOk p.codes p.S && plainArm p.S
    rounds := [], oracles := [], before := []
    decide := fun s _ _ => do
      let x ← named "the two ends are at hand" s.loc.border
      need "the shape does not split the row (Dot)" (plainArm p.S)
      need "no root is received yet, and the first own tree's number counts just one tree more"
        (firstStepB s.roots s.loc.firstTree s.book)
      let a ← takeOver p.S s.loc.own x.shared (s.withCols [])
      let dot ← named "the row (Dot) can be made"
        (linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S))
      let b ← named "the row (Dot) is laid" (addRowP a.2 s.loc.own dot)
      pure { st := b.st, book := b.book, roots := b.roots
             loc := { s.loc with border := none, omega := a.1 } }
    claims := [], after := [] }

end VerifiableInference.Desc.Third
