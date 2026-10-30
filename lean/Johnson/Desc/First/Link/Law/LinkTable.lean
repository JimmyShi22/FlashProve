-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkTable.lean: THE LAW OF A LINK AS THREE CORE LAWS IN THE TABLE's
LETTERS: `LinkOwes` (LinkOwes.lean) laid into the batching kind's `cores_table`
(Johnson/Desc/First/Batch/Law/CoresTable.lean), at the link's own two moves. One structure of four
more debts, and one theorem.

Why. `link_cores` (LinkCores.lean) ends in relations in the batching kind's own coin. The table of
conditions between blocks ties each block by its own items: the forms of the runs that the table
lists, the ledger's one sum behind the runs that follow the batching, the one sum, the group's last
row. `cores_table` says the three cores in these words, for whatever moves stand behind the draw, if
their terms are a list of runs' terms in a row. At a link that is `terms_link` (LinkExps.lean).

What is said. `TableOwes`: four debts beside `LinkOwes`, each with the role that owes it in its
docstring: in front of the third piece a part is there; the move behind the batching leaves the
book; behind it the one sum can be taken on the own rows; and, for each item that the table lists,
some runs of the link (several, one or none) whose terms' coefficients, in a row, are the values of
that item's forms. `link_table`: **from `LinkOwes` at the letters «Ok and C» and «on0, the
book-keeping, and C», at the tables read off the witness (`tabAt`), with `TableOwes`, h01 and the
three clauses on Rw: the three pieces are good, each between its own two relations in the table's
letters.**

Limits. AN IMPLICATION: shown of no record of the protocol. `items` is a free list: for the table's
tie it must be all the names that the table lists at the segment's sort; the table's items that are
no forms (the worth of the planes and of the keys at the lookup on the digits) are not reached by
this law. hR1, hR2, hR3 have no payer here (under duties of their own:
Johnson/Desc/First/Batch/Law/RowsRide.lean). The ties to the table's items themselves are not here.
Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkOwes
import Johnson.Desc.First.Link.Law.LinkExps
import Johnson.Desc.First.Batch.Law.CoresTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open _root_.Run (ckP)

variable {α W : Type} {F : Frame}

/-- **FOUR DEBTS MORE, FOR THE TABLE's LETTERS.** -/
structure TableOwes (L : Link S Claim) (φ : S → α)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (on0 on1 on2 : S × F.E.Str → Prop)
    (Rd : K9.Readers) (own : List (ℕ × ℕ)) (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String)) :
    Prop where
  /-- OWES the choice of the conditions on1 and on2, with the batching kind's law: in front of the
  third piece a part is there -/
  hs2 : ∀ c, on2 c → (atS.get? c.1).isSome = true
  /-- OWES each kind's law, an entry of the order behind the batching at a time: the frame's move
  leaves the book -/
  hbook₂ : ∀ m ∈ (moves₂ (α := α) L).map (·.move), MoveBook m
  /-- OWES the batching kind's law with the table of conditions: behind the frame's move the one sum
  can be taken on the own rows -/
  htin : ∀ a t, on1 a → MovesYes atS ((moves₂ (α := α) L).map (·.move)) a.1 t [] →
    K9.totalIn own t = true
  /-- OWES the assembly of the kinds' laws: for each item that the table lists: SOME RUNS OF THE
  LINK (several, one or none), each with its values, which are its terms' coefficients; EACH VALUE
  OF THAT ITEM's FORMS, at the world of the own rows, IS AMONG THEM (an inclusion, not an equation
  of lists: a run may have terms that the item's reader does not list: the approximate range proof's
  run has four numbered terms in front of its single equations, and the reader of that item lists
  the single equations alone; the core law spends no more than the inclusion) -/
  hitems : ∀ a w, on0 a → ∀ e ∈ items, ∃ (b : K9.Part) (R : K9.Read)
    (rs : List (TermedRun S (α × Option Pub9) GQ ×
      (α × Option Pub9 → Bound GQ → List GQ))),
    atS.get? a.1 = some b ∧
    (∀ x ∈ rs, x.1 ∈ rlOf L tmOf lenOf ∧
      ∀ n y, (x.1.tm n (fixed9 φ a.1) y).map (·.2) = x.2 (fixed9 φ a.1) y) ∧
    Rd.forms e.1 e.2 a.1 = some R ∧ K9.formsIn Rd own e.1 e.2 a.1 = true ∧
    ∀ f ∈ R.forms, f.value Reading.gl (worldOwn b R.late (dataQ own b (rdW w))) ∈
      rs.flatMap fun x => x.2 (fixed9 φ a.1) (dataQ own b (rdW w))

/-- **THE LAW OF A LINK AS THREE CORE LAWS IN THE TABLE's LETTERS.** -/
theorem link_table (C : α × Option Pub9 → Prop) (Rw : S × F.E.Str → Prop)
    (l : ℕ) (sub : First.ModelPart) (L : Link S Claim) (h : SegAt l sub L) (φ : S → α)
    (Ok : α × Option Pub9 → Prop) (Fu : S → Prop) (p pw : Where)
    (tmOf : ℕ × String → ℕ → α × Option Pub9 → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
    (lenOf : ℕ × String → α × Option Pub9 → ℕ) (d N : ℕ) (b₃ : Block S Claim)
    (pb pq pe : Piece (ckP .two) F S Claim W) (on0 on1 on2 on3 : S × F.E.Str → Prop)
    (ctx : S × F.E.Str → W → Prop) (Rd : K9.Readers) (own : List (ℕ × ℕ))
    (rdW : W → ℕ × ℕ → MsgQ) (items : List (ℕ × String))
    (A : LinkOwes sub L φ (fun q => Ok q ∧ C q) Fu p pw tmOf lenOf d N b₃ pb pq pe
      (fun a => (on0 a ∧ k9OnA a.1 = true) ∧ C (fixed9 φ a.1)) on1 on2 on3
      (fun a w => tabAt own (rdW w) a.1) ctx)
    (T : TableOwes L φ tmOf lenOf on0 on1 on2 Rd own rdW items)
    (h01 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → on1 b')
    (hR1 : ∀ a τ b', on0 a → pb.ior.red.out a τ = some b' → Rw b' → C (fixed9 φ a.1))
    (hR2 : ∀ a τ b', on1 a → pq.ior.red.out a τ = some b' → Rw b' → Rw a)
    (hR3 : ∀ a τ b', on2 a → pe.ior.red.out a τ = some b' → Rw a) :
    pb.GoodIn on0 on1 (fun a w => ∀ e ∈ items, formsQ Rd own e.1 e.2 a.1 (rdW w))
        (fun b w =>
          (totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own b.1 (rdW w) ∧ Rw b) ∧
            ctx b w) ∧
      pq.GoodIn on1 on2
        (fun a w => totalBQ (K9L.afterOf ((moves₂ (α := α) L).map (·.move))) own a.1 (rdW w) ∧ Rw a)
        (fun b w => totalQ own b.1 (rdW w) ∧ Rw b) ∧
      pe.GoodIn on2 on3 (fun a w => totalQ own a.1 (rdW w) ∧ Rw a)
        (fun e w => rowEqQ own N e.1 (rdW w)) :=
  cores_table C Rw φ Ok Fu p pw (moves₁ L (rlOf L tmOf lenOf)) (moves₂ L) (rlOf L tmOf lenOf)
    (fun q y => terms_link q y L (rlOf L tmOf lenOf)) d N L.batchB L.behindB b₃ pb pq pe on0 on1 on2
    on3 ctx Rd own rdW items (joinAsks_of_runs (runsAsk_of_owes h A)) h01 hR1 hR2 hR3 T.hs2
    T.hbook₂ T.htin T.hitems

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.link_table
