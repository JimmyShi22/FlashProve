-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormNextLaws.lean: THE FORM's HALF: THE FOLD's FRONT AT ANY STAGE, behind a
batching (foldFront_at: from StageFront, Johnson/Prover/Link/FormNext.lean); and the fold keeps «in
order» and «statement and book in step».

Main names.
  FoldFront.move  FoldFront reads of the plan two look-ups, and of the carried record its statement,
    what is passed on, and its note of the mask.
  testFront_of    StageFront is TestFront at a made-up plan and a made-up carried record.
  foldFront_at    THE FOLD's FRONT AT ANY STAGE.
  inOrder_foldT, step_foldT   the fold keeps «in order» and «in step».

How. foldFront_first (Johnson/Prover/Link/FormFirst.lean) at the plan whose list of codes is #[i,
n], then FoldFront.move: no proof is typed twice.

Limits. StageFront is a premise. Nothing on a switch: Johnson/Prover/Link/FormNextSwitch.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormNext
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- FoldFront reads of the plan two look-ups, and of the carried record three parts. -/
theorem FoldFront.move {p p' : P12} {j j' : Nat} {cur : Fmt.M1.Stage} {t t' : T12} {row : GroupRow}
    {L : GroupLayout} {c : IoppStage} {n : Nat × Nat} {id : Nat}
    (H : FoldFront p' j' cur t' row L c n id) (hs : t.st = t'.st) (hp : t.pass = t'.pass)
    (hm : t.mask = t'.mask) (h1 : stageAt p j cur = some c) (h2 : p.idx[j + 1]? = some n) :
    FoldFront p j cur t row L c n id :=
  ⟨hp.trans H.pass, h1, h2, by rw [hs]; exact H.shape, hm.trans H.mask,
    by rw [hs]; exact H.maskFits, by rw [hs]; exact H.spend, by rw [hs]; exact H.rowFits,
    by rw [hs]; exact H.group⟩

/-- StageFront is TestFront at a made-up plan and a made-up carried record. -/
theorem testFront_of (p : P12) {S : Statement} {g : Nat} {G : Group} {cur nxt : Fmt.M1.Stage}
    {i n : Nat × Nat} {id : Nat} (H : StageFront S g G cur nxt i n id) :
    TestFront { p with idx := [i, n] } cur nxt
      { st := S, book := ⟨#[], #[]⟩, roots := 0, g := g, pass := .nothing, mask := some id } G i n
      id :=
  ⟨H.group, H.order, H.dense, rfl, rfl, H.code, H.maskCode, H.base, H.maskC, H.base1, H.mask1,
    H.layK, H.layH, H.main, H.noKept, rfl, H.fresh, H.stage, H.stage1, H.vars⟩

/-- **THE FOLD's FRONT AT ANY STAGE**, behind a batching. -/
theorem foldFront_at (p : P12) (j : Nat) {S : Statement} {g : Nat} {G : Group}
    {cur nxt : Fmt.M1.Stage} {i n : Nat × Nat} {id : Nat} (x : E) (row : GroupRow) (t : T12)
    (H : StageFront S g G cur nxt i n id) (h0 : p.idx[j]? = some i) (h1 : p.idx[j + 1]? = some n)
    (hc : Bat.combine (begun S g G) g ⟨layoutOf S G, runRows S G⟩ x = some row)
    (hs : t.st = begun S g G) (hp : t.pass = .claim row (layoutOf S G)) (hm : t.mask = some id) :
    FoldFront p j cur t row (layoutOf S G) ⟨i.1, i.2, cur.k, cur.h⟩ n id :=
  (foldFront_first (testFront_of p H) x row hc).move hs hp hm
    (by
      unfold stageAt
      rw [h0]
      rfl) h1

/-- **The fold keeps the statement in order.** -/
theorem inOrder_foldT (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat)
    (id : Nat) (rs : List Fmt.RoundView) (h : InOrder t.st) : InOrder (foldT t row L c n id rs).st :=
  (h.onOracle id (fun x => { x with spentAsMask := true }) (fun _ => rfl) fun _ => rfl).withGroup
    n.1 n.2

/-- **The fold keeps statement and book in step.** -/
theorem step_foldT (t : T12) (row : GroupRow) (L : GroupLayout) (c : IoppStage) (n : Nat × Nat)
    (id : Nat) (rs : List Fmt.RoundView) (h : t.st.oracles.size = t.book.place.size) :
    (foldT t row L c n id rs).st.oracles.size = (foldT t row L c n id rs).book.place.size := by
  show (t.st.oracles.modify id _).size = t.book.place.size
  rw [Array.size_modify]
  exact h

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.FoldFront.move
#print axioms Johnson.Prover.Link.testFront_of
#print axioms Johnson.Prover.Link.foldFront_at
#print axioms Johnson.Prover.Link.inOrder_foldT
#print axioms Johnson.Prover.Link.step_foldT
