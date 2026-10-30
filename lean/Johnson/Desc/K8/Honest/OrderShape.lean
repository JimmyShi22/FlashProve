-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/OrderShape.lean: THE SMALLNESS TEST: THE GUARD OF ORDER, AND ALL THAT IS
ASKED IN FRONT OF THE DRAW OF THE MATRIX (`Order.orderOk`, `Order.front`:
Johnson/Desc/First/K8/Order.lean), ARE READ OFF SHAPES: a second text of each, with code, on the
shapes of the test's data, of the link's context and of the chain's statement
(Johnson/Desc/First/Shape/Tail.lean, Calls.lean; Johnson/Desc/Ground/Shape/Core.lean), and the laws
that the two texts agree at every argument. Lemmas on the verifier's own text; none of the library's
goals.

  `liesAtB`, `sentInFrontB`, `namedNowB`, `answeredB`, `fixedB`   the guard's five readers, each
                   with the shape's field in the place of the record's field of that name
  `orderB t L st`   THE GUARD OF ORDER ON SHAPES
  `frontB t L st`   ALL THREE TESTS IN FRONT OF THE DRAW, as one Bool: the list of tables is closed;
                   one shape a matrix; the guard of order
  `liesAt_sh`, `sentInFront_sh`, `namedNow_sh`, `answered_sh`, `fixed_sh`   each reader agrees
  **`order_sh`**   orderB (tailSh tl) (linkSh L) (stSh S) = Order.orderOk tl L S
  **`front_sh`**   Order.front tl L S returns just where frontB says yes at the three shapes
So the guard is a function of the three shapes. BY ITS TEXT it reads: of the test's data the arrays'
numbers and how many matrices there are (and, in front of the draw, whether the list is closed and
how many shapes there are); of the link's context its number, its moments, its table of arrays, the
layout, the request's shape and the frame's book-keeping of messages; of the statement whether a
message's sample is answered: numbers, Bools, names and public items: no field element and no byte
string, by their types. That no number among them is made of a value is not shown here.
Limits. THAT THE GUARD SAYS YES AT ANY STATE IS NOT SAID. General in tl, L and S: which of them a
caller hands in is the caller's. Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.K8.Order
import Johnson.Desc.First.Shape.Tail
import Johnson.Desc.First.Shape.Calls
import Johnson.Desc.Ground.Shape.Core

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.K8 (Order.Lies Order.liesAt Order.sentInFront Order.namedNow
  Order.answered Order.fixed Order.orderOk Order.front)
open VerifiableInference.Desc.First.Shape (TailSh tailSh LinkSh linkSh FrameSh frameSh)
open VerifiableInference.Desc.Ground.Sh (StSh stSh orc_get)

/-- (1) (2), on the shape of the link's context. -/
def liesAtB (L : LinkSh) (array : Nat) : Option Order.Lies := do
  let named ← L.arrayOf[array]?
  let laid ← (L.check.rows.layout.link.getD named.1 []).find? fun A => A.name == named.2
  let m ← (← L.check.frame.shape.link[named.1]?).messages[laid.message]?
  pure ⟨named.1, laid.message, m.moment, m.life⟩

/-- (3). -/
def sentInFrontB (L : LinkSh) (w : Order.Lies) : Bool :=
  if w.born == L.link then decide (w.moment < L.moments)
  else decide (w.born < L.link) && decide (L.link ≤ w.born + w.life)

/-- Under which number the statement has the message now, on the shape of the frame of the calls. -/
def namedNowB (f : FrameSh) (w : Order.Lies) : Option Nat :=
  match f.next with
  | .laterOrClose =>
    if w.born == f.link then f.own[w.message]?
    else
      match (f.groups.getD f.link {}).born.idxOf? (w.born, w.message) with
      | none => none
      | some i => f.keptBefore[i]?
  | _ => none

/-- (4). -/
def answeredB (L : LinkSh) (st : StSh) (w : Order.Lies) : Bool :=
  match namedNowB L.check.frame w with
  | none => false
  | some o =>
    match st.oracles[o]? with
    | none => false
    | some x => x.sampled

/-- (1) to (4), of one array. -/
def fixedB (L : LinkSh) (st : StSh) (array : Nat) : Bool :=
  match liesAtB L array with
  | none => false
  | some w => sentInFrontB L w && answeredB L st w

/-- **The guard of order, on shapes.** -/
def orderB (t : TailSh) (L : LinkSh) (st : StSh) : Bool :=
  L.check.link == L.link && decide (L.link < L.check.links) && t.gtTree.size == t.NM &&
    t.gtTree.all (fixedB L st) &&
    (List.range 4).all fun n =>
      match t.ix.U.getD n none with
      | none => true
      | some u => fixedB L st u

/-- **All that is asked in front of the draw, on shapes.** -/
def frontB (t : TailSh) (L : LinkSh) (st : StSh) : Bool :=
  t.funClosed && t.shp.size == t.NM && orderB t L st

theorem liesAt_sh (L : LinkCtx) (array : Nat) : liesAtB (linkSh L) array = Order.liesAt L array :=
  rfl

theorem sentInFront_sh (L : LinkCtx) (w : Order.Lies) :
    sentInFrontB (linkSh L) w = Order.sentInFront L w := rfl

theorem namedNow_sh (f : ReqFrame) (w : Order.Lies) :
    namedNowB (frameSh f) w = Order.namedNow f w := rfl

theorem answered_sh (L : LinkCtx) (S : Statement) (w : Order.Lies) :
    answeredB (linkSh L) (stSh S) w = Order.answered L S w := by
  unfold answeredB Order.answered
  have e : namedNowB (linkSh L).check.frame w = Order.namedNow L.check.frame w := rfl
  rw [e]
  cases Order.namedNow L.check.frame w with
  | none => rfl
  | some o =>
    dsimp only
    rw [orc_get]
    cases S.oracles[o]? <;> rfl

theorem fixed_sh (L : LinkCtx) (S : Statement) (array : Nat) :
    fixedB (linkSh L) (stSh S) array = Order.fixed L S array := by
  unfold fixedB Order.fixed
  rw [liesAt_sh]
  cases Order.liesAt L array with
  | none => rfl
  | some w =>
    dsimp only
    rw [sentInFront_sh, answered_sh]

/-- **The guard of order is read off the three shapes.** -/
theorem order_sh (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    orderB (tailSh tl) (linkSh L) (stSh S) = Order.orderOk tl L S := by
  have e : fixedB (linkSh L) (stSh S) = Order.fixed L S := funext (fixed_sh L S)
  unfold orderB Order.orderOk
  rw [e]
  rfl

/-- **So is all that is asked in front of the draw.** -/
theorem front_sh (tl : HTailF2) (L : LinkCtx) (S : Statement) :
    Order.front tl L S = .ok () ↔ frontB (tailSh tl) (linkSh L) (stSh S) = true := by
  unfold frontB Order.front
  rw [order_sh]
  have e1 : (tailSh tl).funClosed = tl.funClosed := rfl
  have e2 : (tailSh tl).shp = tl.shp := rfl
  have e3 : (tailSh tl).NM = tl.NM := rfl
  rw [e1, e2, e3]
  cases tl.funClosed <;> cases h2 : (tl.shp.size == tl.NM) <;> cases Order.orderOk tl L S <;>
    simp [bne, h2]

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.liesAt_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.sentInFront_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.namedNow_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.answered_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.fixed_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.order_sh
#print axioms VerifiableInference.Desc.First.K8.Honest.front_sh
