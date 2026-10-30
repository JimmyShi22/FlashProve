-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineSlot.lean: what is known of a slot while the Fiat-Shamir chains of a batch
are made: definitions, and lemmas that do not depend on the programs.

For `Spec.safeProveB` (Compile/Batch/DisciplineStar.lean) (words of this library: lean/GLOSSARY.md).
The one reveal of `finishSlot` (in this sense: the `Step.reveal` in the body of `finishSlot`;
`openT`, `openE` are further ones) shows the tokens of a slot: its salt, tails and slot value, the
shared tails, the roots of its trees and of the shared trees, the request root and the tokens beside
and on its request path. `InU a0 j acc` is this set while it grows. The set is kept closed (`ClS`,
Compile/Batch/DisciplineRun.lean): for every query that is charged to a token of the set, the
query's tail and its other tokens are in the set too. Each token of the set is one of three: sealed
(`Sealed`, Compile/Batch/DisciplineTree.lean: some query to an oracle outside `Wk` holds it); or an
open end of the chains (`OpenOf`: it may still be charged); or the tail of a failed proof-of-work
attempt (`Dead`: nothing holds it, and it is never charged).

`SlotF`: what the end needs: the set is closed, its tokens are new, the slot's trees are in order,
and the slot has a token. `Cap`: what the next round needs: the open end `live ph acc` can be
charged. `SlotI`: both, and the next token to be charged is no dead tail.
-/
import Compile.Batch.DisciplineOpens
import Compile.Batch.DisciplineReq

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type}

/-- the leaf oracle of request trees: a token that only this oracle holds can still be charged -/
abbrev Wk : OracleName → Prop := fun o => o = OracleName.rleaf

/-- the tail of a failed attempt of a round with proof-of-work bits
(Compile/Batch/DisciplineRun.lean) -/
abbrev Dead (d : DSt (spec lam K L)) (u : Tok) : Prop := DeadW Wk d u

/-- the token may be charged by a run beside a slot: it is not sealed and not dead -/
def Fit (d : DSt (spec lam K L)) (u : Tok) : Prop := ¬ Sealed d u ∧ ¬ Dead d u

/-- The tokens of slot j, as far as they exist. The last two: the tails of the failed attempts, of
the slot's own rounds and of the shared rounds. -/
def InU (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Y) (u : Tok) : Prop :=
  u ∈ acc.toks ∨ u ∈ a0.toks ∨
  (∃ tr, some tr ∈ acc.trees ∧ u = tr.root) ∨
  (∃ tr, some tr ∈ a0.trees ∧ u = tr.root) ∨
  (∃ rq, a0.req = some rq ∧ (u ∈ PA rq.levels j ∨ u = rq.root)) ∨
  u ∈ acc.dead ∨ u ∈ a0.dead

/-- the open ends: the tokens of the slot that may still be charged -/
def OpenOf : PhT → SlotAcc lam K Y → Tok → Prop
  | .shr tk0, acc, u => u = acc.c ∨ u = tk0
  | _, acc, u => u = acc.tk

/-- the token of a slot that the next query of its chain is charged to -/
def live : PhT → SlotAcc lam K Y → Tok
  | .shr _, acc => acc.c
  | _, acc => acc.tk

/-- a tree that is in order (`TTOK`), all of whose tokens are sealed -/
def TTS (d : DSt (spec lam K L)) (n₀ depth : ℕ) (t : TTree) : Prop :=
  TTOK d n₀ depth t ∧
  ∀ j < 2 ^ depth, ∀ u ∈ t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j), Sealed d u

/-- the depths of the two trees of each round -/
def depthsOf : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List (ℕ × ℕ)
  | [], _, _ => []
  | _ :: s, (_, A), (w, W) => (w.depthJ, w.depth0) :: depthsOf s A W

/-- the trees of the rounds made so far are in order; done holds the depths of these rounds -/
def TreesJ (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (l : List (Option TTree)) :
    Prop :=
  List.Forall₂ (fun dp x => ∀ tr, x = some tr → TTS d n₀ dp.1 tr) done l
def Trees0 (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (l : List (Option TTree)) :
    Prop :=
  List.Forall₂ (fun dp x => ∀ tr, x = some tr → TTS d n₀ dp.2 tr) done l

/-- What the end needs of a slot. -/
structure SlotF (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (Op : Tok → Prop)
    (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Y) : Prop where
  /-- each token of the set is sealed, or an open end, or the tail of a failed attempt -/
  cl : ClS Wk d (InU a0 j acc) fun u => Op u ∨ Dead d u
  new : ∀ u, InU a0 j acc u → n₀ ≤ u
  trees : TreesJ d n₀ done acc.trees
  ne : acc.toks ≠ []

/-- What the next round needs of a slot. -/
def Cap (p : Params) (d : DSt (spec lam K L)) : PhT → Acc0 → SlotAcc lam K Y → Prop
  | .first, _, acc => Untouched d acc.tk ∧ Len d acc.tk p.sFS ∧ acc.tk ∈ acc.toks
  | .shr tk0, a0, acc =>
    acc.c < d.vals.length ∧ acc.c ∉ d.shown ∧ HeldAt d acc.c Wk ∧ Len d acc.c lam ∧
    acc.c ∈ acc.toks ∧ tk0 ∈ a0.toks ∧ acc.c ≠ tk0
  | _, _, acc => Untouched d acc.tk ∧ Len d acc.tk lam ∧ acc.tk ∈ acc.toks

structure SlotI (p : Params) (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (ph : PhT)
    (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Y) : Prop where
  fin : SlotF d n₀ done (OpenOf ph acc) a0 j acc
  cap : Cap p d ph a0 acc
  /-- the chain goes on from a tail that is not dead -/
  alive : ¬ Dead d (live ph acc)

/-- P holds of all entries of a list, numbered from j on -/
def AllFrom {σ : Type} (P : ℕ → σ → Prop) : ℕ → List σ → Prop
  | _, [] => True
  | j, a :: t => P j a ∧ AllFrom P (j + 1) t

theorem AllFrom.mono {σ : Type} {P Q : ℕ → σ → Prop} (h : ∀ j a, P j a → Q j a) :
    ∀ (j : ℕ) (l : List σ), AllFrom P j l → AllFrom Q j l
  | _, [], _ => trivial
  | j, a :: t, hl => ⟨h j a hl.1, AllFrom.mono h (j + 1) t hl.2⟩

/-! ### Lemmas -/

theorem TTS.keeps {d d' : DSt (spec lam K L)} {n₀ depth : ℕ} {t : TTree}
    {Cc Ch R : Tok → Prop} {e M : OracleName → ℕ} (h : TTS d n₀ depth t)
    (hr : Run Cc Ch R e M d d') (hc : ∀ u, Cc u → ¬ Sealed d u) : TTS d' n₀ depth t :=
  ⟨⟨fun j hj => (h.1.open_ j hj).keeps hr.charges fun u hu hcu => hc u hcu (h.2 j hj u hu),
      h.1.new⟩,
    fun j hj u hu => (h.2 j hj u hu).mono hr.keeps⟩

theorem TreesJ.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {l : List (Option TTree)} {Cc Ch R : Tok → Prop} {e M : OracleName → ℕ} (h : TreesJ d n₀ done l)
    (hr : Run Cc Ch R e M d d') (hc : ∀ u, Cc u → ¬ Sealed d u) : TreesJ d' n₀ done l :=
  List.Forall₂.imp (fun _ _ hx tr htr => (hx tr htr).keeps hr hc) h

theorem Trees0.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {l : List (Option TTree)} {Cc Ch R : Tok → Prop} {e M : OracleName → ℕ} (h : Trees0 d n₀ done l)
    (hr : Run Cc Ch R e M d d') (hc : ∀ u, Cc u → ¬ Sealed d u) : Trees0 d' n₀ done l :=
  List.Forall₂.imp (fun _ _ hx tr htr => (hx tr htr).keeps hr hc) h

/-- What the end needs survives a run that charges no sealed token, no dead tail and no open end of
the slot. -/
theorem SlotF.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {Op : Tok → Prop} {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y}
    {Cc Ch R : Tok → Prop} {e M : OracleName → ℕ} (h : SlotF d n₀ done Op a0 j acc)
    (hr : Run Cc Ch R e M d d') (hc : ∀ u, Cc u → Fit d u ∧ ¬ Op u) :
    SlotF d' n₀ done Op a0 j acc :=
  ⟨⟨(h.cl.keeps hr fun u hu => ⟨(hc u hu).1.1, fun ho => ho.elim (hc u hu).2 (hc u hu).1.2⟩).closed,
      (h.cl.keeps hr fun u hu => ⟨(hc u hu).1.1, fun ho => ho.elim (hc u hu).2 (hc u hu).1.2⟩).lt,
      fun u hu =>
        ((h.cl.keeps hr fun u hu =>
              ⟨(hc u hu).1.1, fun ho => ho.elim (hc u hu).2 (hc u hu).1.2⟩).sealed
            u hu).imp_right
          fun ho => ho.imp_right fun hdd => hdd.mono hr.keeps⟩,
    h.new,
    h.trees.keeps hr fun u hu => (hc u hu).1.1,
    h.ne⟩

/-- the trees, as opensB reads them -/
theorem TreesJ.alJ {d : DSt (spec lam K L)} {n₀ : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      TreesJ d n₀ (depthsOf s A W) l → AlJ d n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), _, h => by
      cases h with
      | cons hx ht => exact ⟨fun tr htr => (hx tr htr).1, TreesJ.alJ s A W _ ht⟩

theorem Trees0.al0 {d : DSt (spec lam K L)} {n₀ : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      Trees0 d n₀ (depthsOf s A W) l → Al0 d n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), _, h => by
      cases h with
      | cons hx ht => exact ⟨fun tr htr => (hx tr htr).1, Trees0.al0 s A W _ ht⟩

end Compile.Batch.Disc
