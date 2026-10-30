-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Slice/KeyProxGp.lean: the proximity test on a group of sent messages, as a step that ends
the claim "all members decode and all rows hold".

OnBytes/Slice/KeyProx.lean makes a proximity test a step and proves its statement from a claim W,
"the relation before the batching has a witness". OnBytes/Slice/KeyExit.lean proves, for a group of
sent messages with seats in a stage: unless all members decode and all rows hold of the decodings,
that relation has no witness; and it states the batching of n rows at any stage. This file joins
the two. The rows are a list in the state. The batching's error count depends on the number of rows,
so that number n is a part of the data, and the step's statement is for states whose list has n
rows.

Main definitions.
 `RowAt`        a row on a stage's tables: a target and a vector.
 `GProx`        the data: stage, group, chain, the batching's round and count, the number of rows,
                and how the members' words, the rows and two more words are read off a state.
 `GProx.prox`   the test of OnBytes/Slice/KeyProx.lean that these data make.
 `GProx.Hold`, `GProx.Rows`   a row holds of the members' messages; all members decode and all rows
                in the state's list hold.
 `GProx.Claim`  if the list has as many rows as are batched, `Rows`.
 `GProx.OK`     what is asked: of the group and the radius; the batching's statement; the blocks'.
Main theorems.
 `GProx.holds`  the data make a test whose statements hold.
 `GProx.rows_fin`   the rows of a list of n rows, as n rows.
 `GProx.exit`   a witness before the batching gives `Rows`, if the list has n rows.
 `GProx.sem`    the test ends `Claim`.
Not claimed. That `GProx.OK` holds of any data. Nothing on the sizes of the error counts.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.KeyProx
import OnBytes.Slice.KeyExit

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

/-- A row on a stage's tables: a target, and a vector on the entries of the message. -/
abbrev RowAt (s : Sg) : Type := GE × (s.cIn.J → GE)

/-- The data of a proximity test on a group of sent messages, seen from states X. -/
structure GProx (X : Type) where
  /-- the first stage, the group with its seats in it, the rounds after the batching -/
  s : Sg
  G : Gp s
  c : Chain s
  /-- the batching's round and error count, and the number of rows that are batched -/
  dA : PQ.RD
  εa : ℕ
  n : ℕ
  /-- the members' sent words, and the rows put aside -/
  words : X → G.Words
  rows : X → List (RowAt s)
  /-- the first tree's fresh mask rows, which may come in the chain's first prover message, and its
  masking word -/
  z : X → c.Msg0 → s.cFr.Word
  g : X → s.cIn.Word

namespace GProx

variable {X X' : Type} (P : GProx X)

/-- The targets of the first n rows of the list. -/
def tg (x : X) : Fin P.n → GE := fun b => ((P.rows x).getD b.val (0, 0)).1

/-- The vectors of the first n rows of the list. -/
def vs (x : X) : Fin P.n → P.s.cIn.J → GE := fun b => ((P.rows x).getD b.val (0, 0)).2

/-- The test: the batching makes one row of the n rows, under the powers of the element that is
drawn; the first word is the group's word. -/
def prox : Prox X where
  s := P.s
  c := P.c
  dA := P.dA
  εa := P.εa
  q x c := sumRow P.s (P.tg x) (P.vs x) (drawnE P.dA c)
  y x := P.G.word (P.words x)
  z := P.z
  g := P.g

/-- A row holds of the members' messages. -/
def Hold (m : P.G.Msgs) (r : RowAt P.s) : Prop :=
  ∑ k : P.G.J, r.2 (P.G.ent k) * m k.1 k.2 = r.1

/-- All members decode, and all rows in the state's list hold of the decodings. -/
def Rows (x : X) : Prop :=
  ∃ m : P.G.Msgs, (∀ i, P.G.fix (P.words x) i = some (m i)) ∧ ∀ r ∈ P.rows x, P.Hold m r

/-- The claim that the test ends: if the list has as many rows as are batched, `Rows`. -/
def Claim (x : X) : Prop := (P.rows x).length = P.n → P.Rows x

/-- The relation before the batching has a witness. -/
def W (x : X) : Prop :=
  ∃ w, ConL P.s.cIn.N P.c.rad (Slf.All fun _ : Fin P.n => (Slf.idf (E := GE) (J := P.s.cIn.J)))
    ((P.tg x, P.vs x), P.G.word (P.words x)) w

/-- What is asked of the data. -/
structure OK (d : ℕ) : Prop where
  grp : P.G.OK P.c.rad d
  bat : BatSemAt P.s P.c.rad P.n P.dA P.εa
  chain : P.c.Holds

variable {P}

/-- The batching's statement in the form of a step, and the blocks' statements. -/
theorem holds {d : ℕ} (h : P.OK d) : P.prox.Holds P.W := by
  refine ⟨fun x hx => ?_, h.chain⟩
  refine h.bat [] () (P.G.word (P.words x)) (P.tg x) (P.vs x) (fun w hw => hx ⟨w, hw⟩) _ ?_ ?_
  · intro m c τ hc hp
    have hp' : (GChal.pass (b := P.dA.entry.work) c && true) = true := hp
    rw [hc] at hp'
    cases hp'
  · intro m c hno
    exact fun _ _ hw => hw.elim hno

/-- If all rows of a list of n rows hold, the first n rows of the list hold. -/
theorem rows_fin (x : X) (m : P.G.Msgs) (hr : ∀ r ∈ P.rows x, P.Hold m r)
    (hn : (P.rows x).length = P.n) : P.G.RowsHold m (P.tg x) (P.vs x) := by
  intro b
  have hb : b.val < (P.rows x).length := by
    rw [hn]
    exact b.isLt
  have h := hr _ (List.getElem_mem hb)
  simp only [tg, vs, List.getD_eq_getElem _ _ hb]
  exact h

/-- The exit. -/
theorem exit {d : ℕ} (h : P.OK d) (x : X) (hn : (P.rows x).length = P.n) (hw : P.W x) :
    P.Rows x := by
  by_contra hno
  obtain ⟨w, hw⟩ := hw
  refine Gp.no_witness h.grp (P.G.tie_word h.grp.apart _) (P.tg x) (P.vs x) ?_ w hw
  rintro ⟨m, hm, hr⟩
  refine hno ⟨m, hm, fun r hr' => ?_⟩
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr'
  have h1 := hr ⟨i, hn ▸ hi⟩
  simp only [tg, vs, List.getD_eq_getElem _ _ hi] at h1
  exact h1

/-- The test ends the claim: from a state whose list has n rows, unless all members decode and
all rows hold, the prover has lost in the test's rounds. -/
theorem sem {d : ℕ} (h : P.OK d) (out : X → X') :
    (P.prox.step out).Sem P.Claim fun _ => True :=
  (P.prox.sem (holds h) out).conseq (fun x hw hn => exit h x hn hw) fun _ hx => hx

end GProx

end OnBytes.Slice
