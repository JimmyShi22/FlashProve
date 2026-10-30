-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Slot.lean: book-keeping on one slot of a batch while the compiled prover runs, for
the lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean).
What is known of a slot while the chains of a batch are made, both ways: the records of
Compile/Batch/DisciplineSlot.lean (`TTS`, `TreesJ`, `Trees0`, `SlotF`, `SlotI`) with the way
upwards: the slot's set of tokens is closed upwards at the vertex oracles (`ClUp`); its trees stand
both ways.

Definitions and the laws that do not look at the programs. Nothing assumed beyond the hypotheses of
the statements and whatever the arguments hold as proofs. The vertex oracles are `OracleName.node`,
`OracleName.rnode` (CompileK/Defer2Tree.lean: `Jt`);
tokens, charged and further tokens: the head of Rom/Defer.lean.

Main names:
  `ClUp d V`: every evaluation at a vertex oracle that holds a token of V among its further tokens
    is charged to a token of V (the converse of `ClS`'s clause "closed", at these oracles).
  `TTS2`, `TreesJ2`, `Trees02`: `TTS`, `TreesJ`, `Trees0` and `TTUp` (CompileK/Defer2Tree.lean).
  `SlotF2`: `SlotF`; `ClUp` of the slot's set `InU a0 j acc`; the slot's trees stand upwards.
  `SlotI2`: `SlotF2`, `Cap`, alive.
  The laws `ClUp.keeps`, `TTS2.keeps`, `TreesJ2.keeps`, `Trees02.keeps`, `SlotF2.keeps`, each under
    the hypotheses of its statement: the side condition of Compile/Batch/DisciplineSlot.lean on what
    a run charges, and: what it adds at the vertex oracles (`GJ ChJ`: CompileK/Defer2Kit.lean) holds
    no sealed token and no token of the set.

Limits: This file gives no instance of `SlotF2`. It does not show `SlotF2` of a slot of a run.
CompileK/Defer2Init.lean, which imports this file, proves `SlotI2`, and with it `SlotF2`, of every
slot at the start (`safe2_initAll`), under the hypotheses of its statement.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2Opens
import Compile.Batch.DisciplineSlot

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc
  (Rules afterPlain afterFresh afterMark afterReveal length_afterFresh
    length_afterMark cnt1 mem_evs_afterMark)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {p : Params} {Y : Type}

/-- the set V is closed upwards at the vertex oracles -/
def ClUp (d : DSt (spec lam K L)) (V : Tok → Prop) : Prop :=
  ∀ e ∈ d.evs, Jt e.o = true → ∀ b ∈ e.others, V b → V e.charged

theorem ClUp.keeps {d d' : DSt (spec lam K L)} {V ChJ : Tok → Prop} (h : ClUp d V)
    (hlt : ∀ u, V u → u < d.vals.length) (hj : GJ ChJ d d') (hc : ∀ u, ChJ u → ¬ V u) :
    ClUp d' V := by
  intro e' he' hJ b hb hV
  rcases hj.evs e' he' hJ with ⟨e₀, he₀, ho, hch, hot⟩ | hnew
  · rw [← hch]
    exact h e₀ he₀ (by rw [ho]; exact hJ) b (by rw [hot]; exact hb) hV
  · rcases hnew b hb with h1 | h1
    · exact absurd hV (hc b h1)
    · exact absurd (hlt b hV) (Nat.not_lt.mpr h1)

/-- a tree that stands both ways, all of whose tokens are sealed -/
def TTS2 (d : DSt (spec lam K L)) (n₀ depth : ℕ) (t : TTree) : Prop :=
  TTS d n₀ depth t ∧ TTUp d depth t

def TreesJ2 (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (l : List (Option TTree)) :
    Prop :=
  List.Forall₂ (fun dp x => ∀ tr, x = some tr → TTS2 d n₀ dp.1 tr) done l
def Trees02 (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (l : List (Option TTree)) :
    Prop :=
  List.Forall₂ (fun dp x => ∀ tr, x = some tr → TTS2 d n₀ dp.2 tr) done l

/-- What the end needs of a slot, both ways. -/
structure SlotF2 (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (Op : Tok → Prop)
    (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Y) : Prop where
  cl : ClS Wk d (InU a0 j acc) fun u => Op u ∨ Dead d u
  up : ClUp d (InU a0 j acc)
  new : ∀ u, InU a0 j acc u → n₀ ≤ u
  trees : TreesJ2 d n₀ done acc.trees
  ne : acc.toks ≠ []

structure SlotI2 (p : Params) (d : DSt (spec lam K L)) (n₀ : ℕ) (done : List (ℕ × ℕ)) (ph : PhT)
    (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Y) : Prop where
  fin : SlotF2 d n₀ done (OpenOf ph acc) a0 j acc
  cap : Cap p d ph a0 acc
  alive : ¬ Dead d (live ph acc)

theorem TreesJ2.toJ {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {l : List (Option TTree)} (h : TreesJ2 d n₀ done l) : TreesJ d n₀ done l :=
  List.Forall₂.imp (fun _ _ hx tr htr => (hx tr htr).1) h

theorem Trees02.to0 {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {l : List (Option TTree)} (h : Trees02 d n₀ done l) : Trees0 d n₀ done l :=
  List.Forall₂.imp (fun _ _ hx tr htr => (hx tr htr).1) h

theorem SlotF2.toF {d : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {Op : Tok → Prop}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} (h : SlotF2 d n₀ done Op a0 j acc) :
    SlotF d n₀ done Op a0 j acc :=
  ⟨h.cl, h.new, h.trees.toJ, h.ne⟩

/-! ### Laws -/

theorem TTS2.keeps {d d' : DSt (spec lam K L)} {n₀ depth : ℕ} {t : TTree} {Cc Ch R ChJ : Tok → Prop}
    {e M : OracleName → ℕ} (h : TTS2 d n₀ depth t) (hr : Run Cc Ch R e M d d')
    (hc : ∀ u, Cc u → ¬ Sealed d u) (hj : GJ ChJ d d') (hcj : ∀ u, ChJ u → ¬ Sealed d u) :
    TTS2 d' n₀ depth t :=
  ⟨h.1.keeps hr hc,
    fun j hj' u hu =>
      (h.2 j hj' u hu).keepsJ ((h.1.1.open_ j hj').lt u hu) hj fun hcu =>
        hcj u hcu (h.1.2 j hj' u hu)⟩

theorem TreesJ2.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {l : List (Option TTree)} {Cc Ch R ChJ : Tok → Prop} {e M : OracleName → ℕ}
    (h : TreesJ2 d n₀ done l) (hr : Run Cc Ch R e M d d') (hc : ∀ u, Cc u → ¬ Sealed d u)
    (hj : GJ ChJ d d') (hcj : ∀ u, ChJ u → ¬ Sealed d u) : TreesJ2 d' n₀ done l :=
  List.Forall₂.imp (fun _ _ hx tr htr => (hx tr htr).keeps hr hc hj hcj) h

theorem Trees02.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)}
    {l : List (Option TTree)} {Cc Ch R ChJ : Tok → Prop} {e M : OracleName → ℕ}
    (h : Trees02 d n₀ done l) (hr : Run Cc Ch R e M d d') (hc : ∀ u, Cc u → ¬ Sealed d u)
    (hj : GJ ChJ d d') (hcj : ∀ u, ChJ u → ¬ Sealed d u) : Trees02 d' n₀ done l :=
  List.Forall₂.imp (fun _ _ hx tr htr => (hx tr htr).keeps hr hc hj hcj) h

/-- What the end needs survives a run that charges no sealed token, no dead tail and no open end of
the slot, and that adds at the vertex oracles nothing that holds a sealed token or a token of the
slot. -/
theorem SlotF2.keeps {d d' : DSt (spec lam K L)} {n₀ : ℕ} {done : List (ℕ × ℕ)} {Op : Tok → Prop}
    {a0 : Acc0} {j : ℕ} {acc : SlotAcc lam K Y} {Cc Ch R ChJ : Tok → Prop} {e M : OracleName → ℕ}
    (h : SlotF2 d n₀ done Op a0 j acc) (hr : Run Cc Ch R e M d d')
    (hc : ∀ u, Cc u → Fit d u ∧ ¬ Op u) (hj : GJ ChJ d d')
    (hcj : ∀ u, ChJ u → ¬ Sealed d u ∧ ¬ InU a0 j acc u) : SlotF2 d' n₀ done Op a0 j acc :=
  have h1 := h.toF.keeps hr hc
  ⟨h1.cl, h.up.keeps h.cl.lt hj fun u hu => (hcj u hu).2, h.new,
    h.trees.keeps hr (fun u hu => (hc u hu).1.1) hj fun u hu => (hcj u hu).1, h.ne⟩

/-- the trees, as opensB reads them -/
theorem TreesJ2.alJ {d : DSt (spec lam K L)} {n₀ : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      TreesJ2 d n₀ (depthsOf s A W) l → AlJ2 d n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), _, h => by
      cases h with
      | cons hx ht => exact ⟨fun tr htr => ⟨(hx tr htr).1.1, (hx tr htr).2⟩, TreesJ2.alJ s A W _ ht⟩

theorem Trees02.al0 {d : DSt (spec lam K L)} {n₀ : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (l : List (Option TTree)),
      Trees02 d n₀ (depthsOf s A W) l → Al02 d n₀ s A W l
  | [], _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), _, h => by
      cases h with
      | cons hx ht => exact ⟨fun tr htr => ⟨(hx tr htr).1.1, (hx tr htr).2⟩, Trees02.al0 s A W _ ht⟩

end Compile.Batch.Disc
