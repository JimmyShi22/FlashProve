-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkJoin.lean: THE LAW OF A LINK ON THE ROAD OF MOVES: THE JOINING. A
STATEMENT: definitions of type Prop; NOTHING IS PROVED HERE.
What is asked: (1) of the third block it
is asked only that a yes of its step is a yes of the one equation's (`hb₃`): not
that it BE that block, which no segment of the driver's meets: the driver writes the place, and the
batching kind's `closeOf` lays another test on the plan.
(2) The condition at j + 3 is a letter, on3, with its clause `hon3`: the
closing kind's law asks a promise of the block behind. (3) The four clauses
on what the second and the third piece carry (`hcq`, `hce`, `htabq`, `htab`) take the condition at
their own boundary, as the first piece's do. (4) The conditions at j
+ 1 and j + 2 are two free letters on the statement, on1 and on2, handed on piece by piece (`h01`,
`h12`): not «reached from a state with on0», which no table of conditions on the statement
alone can give. What the second and the third piece's laws spend of them is asked by name: `hs1`;
`hN`, `inside` (at on2).

Why. The rule that joins the chains to a file (`proofSound_at_descB`,
Johnson/Desc/Plain/BothAtDesc.lean) takes, of the first chain, one premise for each block of the
description: ONE PIECE A BLOCK (`OfDesc`). The batching kind's law on the road of moves
(`k9_row_atS`, Johnson/Desc/First/Batch/Law/RowAtS.lean) speaks of a piece at ONE block that holds
the draw and all that adds or writes behind it. A segment as the driver lays it has TWO blocks
there: the batching (place n + 1) and the frame's block of the runs behind the batching (place n +
2). So the law is owed for three pieces in a row: the batching's, that of the runs behind it, the
one equation's.

What is said.
  `onJ`, `relJ`: the conditions and the relations at the four boundaries j .. j + 3; at every other
    number they are not used (`onJ` says True there, `relJ` its last arm). At j: the batching kind's
    own: all coefficients of the moves' terms are 0 at the data, and the open rows hold. AT j + 1,
    BETWEEN THE TWO BLOCKS: the moves behind the batching return some state t from here, and the
    ledger's one sum, read at t, is 0 at the data, WHICH ARE READ AT THE STATE HERE; the open rows
    hold; ctx. At j + 2 and j + 3: the batching kind's own (its j + 1 and j + 2), each with ctx.
  `JoinAsks`: what the statement takes: the premises of `k9_row_atS`, with the moves in two lists,
    two blocks and three pieces. Of the middle piece's rounds, of what lies behind them and of its
    error NOTHING is asked: it has no round, and no transcript of it is bad.
  `InMoves`: **THE STATEMENT, in moves**: ms₁: the moves of the batching's block behind its draw;
    ms₂: the moves of the block behind it, all quiet; either list may be empty. Each move owes
    `MoveOk` and `MoveDoor`, as in `k9_row_atS`; «full» is asked behind ms₁ ++ ms₂ alone; the test
    on the exponents at the terms of ms₁ ++ ms₂. Then the three pieces are good in a row between
    `onJ` and `relJ`, the batching's at the cap 128.
  `AtTheDriver`: **THE ROW**: of the segment that the driver makes of a record H of the kinds'
    blocks: which block stands where (`SegShape`); and `InMoves`' conclusion for the pieces at the
    places n + 1, n + 2, n + 3 of the segment's own flat list, where the batching is a draw with the
    moves ms₁, the frame's block is the moves ms₂, and the closing's first block is the one
    equation.

WHO PAYS `MoveOk`. Every run of the link's order owes `RunOk` (through `steps_moveOk`,
Johnson/Desc/First/Batch/Law/Steps.lean). IN FORM, under named premises on the shared letters, none
counted: the smallness test's equations: `k8_runOk` (Batch/Law/K8Run.lean; but for its first four
claims) · the layers' «front», «back»: `k4_front_runOk`, `k4_back_runOk` (Link/Law/K4Run.lean) · the
merge's: `k11_runOk` (Link/Law/K11Run.lean) · «objects», «planes» and «join» (the last is stated by
the calling kind's block, attention's or the head's; its text is the lookups':
Johnson/Desc/First/Look/K3Runs.lean): K3's files' to show. By a reading of the runs'
texts, no theorem, the runs that lay hiding coefficients behind the draw are among these. THE
ORDER's OTHER RUNS (Johnson/Desc/First/Driver/Chain.lean: `orderCuts`: «guests»; attention's
«first», «keys», «second»; the head's «norm», «policy», «logits») owe `RunOk` all the same: no payer
of theirs is named here. The runs behind the batching (`orderAfterOf`: «K8.lsTail»,
«free-slot», «K8.tests») owe `QuietOk`: `k8_lsTail_quietOk` (Batch/Law/K8Step.lean) is typed; for
the other two none is named here.

Limits. A STATEMENT. That a record of the protocol has a batching that is a draw with moves (`hb₁`),
a frame's block that is the moves ms₂ (`hb₂`) and, first in its closing, a block whose yes is the
one equation's (`hb₃`), are premises: shown of no record. All three start from a yes: a block behind
a guard that only adds refusals meets them if the bare block does. `hon3` is a premise too: at the
real link on3 is what the closing kind's law asks in front of itself; who shows that the three
blocks hand it on is open. «Reached from a state with on0» (`at1`, `at2`) is one instance of on1 and
on2: the toys' members take it. The closing's other two blocks (the closing kind's; the batching
kind's «shut», whose law is `shut_goodIn`, Johnson/Desc/First/Batch/Law/ShutLaw.lean, under its
premises hb · hext · hhands · hcarry, which a caller must bring) are not
in it. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Law.RowAtS
import Johnson.Desc.First.Batch.Law.MovesRow
import Johnson.Desc.First.Link.Law.Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Lens Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open _root_.Run (ckP)
open _root_.Iop (Err)

variable {α W Cl : Type} {F : Frame}

/-- AN INSTANCE OF on1: reached from a state with on0 by a yes of the first piece. -/
def at1 (on0 : S × F.E.Str → Prop) (pb : Piece (ckP .two) F S Cl W) (b' : S × F.E.Str) : Prop :=
  ∃ a τ, on0 a ∧ pb.ior.red.out a τ = some b'

/-- AN INSTANCE OF on2: reached from a state with on0 by a yes of the first piece and one of the
second. -/
def at2 (on0 : S × F.E.Str → Prop) (pb pq : Piece (ckP .two) F S Cl W) (b' : S × F.E.Str) : Prop :=
  ∃ b τ', at1 on0 pb b ∧ pq.ior.red.out b τ' = some b'

/-- The conditions at the four boundaries: four letters on the statement. -/
def onJ (on0 on1 on2 on3 : S × F.E.Str → Prop) (j : ℕ) : ℕ → S × F.E.Str → Prop := fun i b' =>
  if i = j then on0 b'
  else if i = j + 1 then on1 b'
  else if i = j + 2 then on2 b'
  else if i = j + 3 then on3 b'
  else True

/-- The relations at the four boundaries. -/
def relJ (O : Others S (α × Option Pub9) Cb.Gl.E)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (N : ℕ)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop)
    (j : ℕ) : ℕ → S × F.E.Str → W → Prop := fun i a w =>
  if i = j then
    (∃ y, boundAt atS tabOf ctx a w y ∧ ∀ x ∈ termsOf (O.fixed a.1) y (ms₁ ++ ms₂) 0, x.2 = 0) ∧
      GroupHoldsAt atS Reading.gl N a.1 (tabOf a w)
  else if i = j + 1 then
    ((∃ t, MovesYes atS (ms₂.map (·.move)) a.1 t [] ∧
        oneK atS Reading.gl t t (dataAt atS a.1 (tabOf a w)) = 0) ∧
      GroupHoldsAt atS Reading.gl N a.1 (tabOf a w)) ∧ ctx a w
  else if i = j + 2 then
    (oneK atS Reading.gl a.1 a.1 (dataAt atS a.1 (tabOf a w)) = 0 ∧
      GroupHoldsAt atS Reading.gl N a.1 (tabOf a w)) ∧ ctx a w
  else GroupHoldsAt atS Reading.gl N a.1 (tabOf a w) ∧ ctx a w

/-- What the statement takes, for blocks b₁ (a draw with the moves ms₁), b₂ (the moves ms₂) and b₃
(the one equation, in whatever dress) and the three pieces. -/
structure JoinAsks (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N : ℕ) (b₁ b₂ b₃ : Block S Cl)
    (pb pq pe : Piece (ckP .two) F S Cl W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E)
    (ctx : S × F.E.Str → W → Prop) : Prop where
  /-- φ does not see what the batching's lens writes -/
  hφ : ∀ s a, φ (atS.set s a) = φ s
  hd : d ≤ 2 ^ 60
  /-- ONE DUTY A MOVE: here the runs' payers go in -/
  hms : ∀ m ∈ ms₁ ++ ms₂, MoveOk Reading.gl atS (O9 φ Ok Fu) (Fx9 φ Ok) m
  hkd : ∀ m ∈ ms₁ ++ ms₂, MoveDoor atS m.move
  /-- the moves behind the batching add nothing -/
  quiet : ∀ m ∈ ms₂, ∃ h, m.move = .quiet h
  /-- the batching's block is a draw with the moves ms₁; the block behind it is the moves ms₂ -/
  hb₁ : DrawMoves atS p (ms₁.map (·.move)) b₁
  hb₂ : IsMoves atS (ms₂.map (·.move)) b₂
  /-- A YES OF THE THIRD BLOCK's STEP IS A YES OF THE ONE EQUATION's, WITH THE SAME RETURN. Its
  name, its place and its test on the plan are free (the driver writes the place; whoever lays the
  block may dress it), and so is a guard that only adds refusals -/
  hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
    (K9.oneEquation (Cl := Cl) atS pw).step ft s rs cols = .ok x
  /-- "full" is asked behind the last move alone -/
  hend : ∀ s s' cls, good9 s → MovesYes atS ((ms₁ ++ ms₂).map (·.move)) s s' cls →
    good9 s' ∧ Fu s'
  /-- the test on the exponents -/
  hok : ∀ s y, k9OnA s = true ∧ Ok (fixed9 φ s) →
    Desc.TermsOk Cb.Gl.E (termsOf (fixed9 φ s) y (ms₁ ++ ms₂) 0) d
  hpb : pb.b = below b₁
  hpq : pq.b = below b₂
  hpe : pe.b = below b₃
  hextb : ∀ a τ w, pb.ext a τ w = w
  hextq : ∀ a τ w, pq.ext a τ w = w
  hexte : ∀ a τ w, pe.ext a τ w = w
  hds : pb.ds = [k9Round p]
  hbk : pb.back = []
  hcap : pb.err = Err.cap 128 (uLT (ckP .two) pb.ds)
  hready : ∀ a, on0 a → k9OnA a.1 = true ∧ Ok (fixed9 φ a.1)
  /-- THE CONDITIONS ARE HANDED ON, piece by piece -/
  h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b'
  h12 : ∀ b τ c, on1 b → pq.ior.red.out b τ = some c → on2 c
  /-- what the block behind the three asks in front of itself -/
  hon3 : ∀ c τ e, on2 c → pe.ior.red.out c τ = some e → on3 e
  /-- ALL THAT THE SECOND PIECE's LAW SPENDS OF THE CONDITION IN FRONT OF IT: a part is there -/
  hs1 : ∀ b, on1 b → (atS.get? b.1).isSome = true
  /-- THE PIN -/
  hpin : ∀ a w w', on0 a → ctx a w → ctx a w' → tabOf a w = tabOf a w'
  hcb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → ctx b' w → ctx a w
  hcq : ∀ a τ b' w, on1 a → pq.ior.red.out a τ = some b' → ctx b' w → ctx a w
  hce : ∀ a τ b' w, on2 a → pe.ior.red.out a τ = some b' → ctx b' w → ctx a w
  htabb : ∀ a τ b' w, on0 a → pb.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  htabq : ∀ a τ b' w, on1 a → pq.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  htab : ∀ a τ b' w, on2 a → pe.ior.red.out a τ = some b' → tabOf b' w = tabOf a w
  /-- ALL THAT THE THIRD PIECE's LAW SPENDS OF THE CONDITION IN FRONT OF IT: these two -/
  hN : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → a.d.st.oracles.size ≤ N
  inside : ∀ s, on2 s → ∀ a, atS.get? s.1 = some a → ∀ born name r,
    reqArray a.L.check.rows.layout born name = some r → ∀ bl ∈ r.blocks, Inside r bl

/-- **THE JOINING, IN MOVES.** -/
def InMoves : Prop :=
  ∀ (α W Cl : Type) (F : Frame) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (p pw : Where) (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N j : ℕ)
    (b₁ b₂ b₃ : Block S Cl) (pb pq pe : Piece (ckP .two) F S Cl W)
    (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E) (ctx : S × F.E.Str → W → Prop),
    JoinAsks φ Ok Fu p pw ms₁ ms₂ d N b₁ b₂ b₃ pb pq pe on0 on1 on2 on3 tabOf ctx →
    EachGoodIn (onJ on0 on1 on2 on3 j) (relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx j) j [pb, pq, pe]

/-- **THE ROW**: at the segment that the driver makes. n: the number of its hearing blocks. -/
def AtTheDriver : Prop :=
  ∀ (Cl : Type) (H : First.Blocks S Cl) (l : ℕ) (sub : First.ModelPart) (L : Link S Cl),
    First.linkAt H l sub = some L →
    Shape.SegShape H l sub L ∧
    ∀ (α W : Type) (F : Frame) (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
      (p pw : Where) (ms₁ ms₂ : List (Termed S (α × Option Pub9) Cb.Gl.E)) (d N i : ℕ)
      (ps : List (Piece (ckP .two) F S Cl W)) (pb pq pe : Piece (ckP .two) F S Cl W)
      (b₃ : Block S Cl) (on0 on1 on2 on3 : S × F.E.Str → Prop)
      (tabOf : S × F.E.Str → W → ℕ → OnBytes.Part → ℕ → Cb.Gl.E)
      (ctx : S × F.E.Str → W → Prop),
      ps.map (·.b) = L.blocksInOrder.map below →
      ps[(First.kindsBeforeBatching sub (l == 0)).length + 1]? = some pb →
      ps[(First.kindsBeforeBatching sub (l == 0)).length + 2]? = some pq →
      ps[(First.kindsBeforeBatching sub (l == 0)).length + 3]? = some pe →
      L.close.head? = some b₃ →
      JoinAsks φ Ok Fu p pw ms₁ ms₂ d N L.batchB L.behindB b₃ pb pq pe on0 on1 on2 on3 tabOf ctx →
      EachGoodIn (onJ on0 on1 on2 on3 (i + ((First.kindsBeforeBatching sub (l == 0)).length + 1)))
        (relJ (O9 φ Ok Fu) ms₁ ms₂ N tabOf ctx (i + ((First.kindsBeforeBatching sub (l == 0)).length + 1)))
        (i + ((First.kindsBeforeBatching sub (l == 0)).length + 1)) [pb, pq, pe]

end VerifiableInference.Desc.LinkJoin
