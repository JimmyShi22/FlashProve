-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedBlocks.lean: which blocks of an answer the algorithms of the compiled scheme may
  read. Table and hypothesis are in Compile/Batch/NeedTable.lean (words of this library:
  lean/GLOSSARY.md).

  Hypothesis `QueryLayout.NB W nb`: the challenge of round i of protocol t is a function of the blocks
  below nb t i. Under it C, P and V of Compile/Batch/Star.lean, and the programs of which they are
  made, go on in the same way after two answers that agree on the marked blocks (at a Fiat-Shamir
  query of round i of protocol t: the blocks below nb t i and the chaining value; elsewhere: all):
  equality of programs, not of distributions (`SFac`, Compile/NeedBlocks.lean; `OComp.FactorsBy`,
  Rom/OverOneN.lean). Nothing of the scheme is changed; this is a fact about it.
  Why the rounds are compared up to a relation. The prover of a batch keeps, for each slot, the
  blocks of all Fiat-Shamir answers that the slot has seen, whole (`SlotAcc.blocks`), and reads them
  at the end, through `rhoOf`, which applies the wire record's map to each. So a round of the chain,
  taken by itself, returns different states after two answers that agree on the marked blocks only.
  The rounds are therefore compared up to a relation on states (Compile/NeedRel.lean): `SlotRel`:
  all equal but the stored blocks; entry number l of these agrees below nb t l; and there are as
  many entries as rounds have passed. (Of the stored blocks of an empty slot nothing is asked: they
  are never read.)
    Part 1  trees and openings
    Part 2  queries to the Fiat-Shamir oracle and to g, up to a relation (`sfr_fbT`, `sfr_gT`); the
            search over nonces of a round with proof-of-work bits (`sfr_fbG`): it branches on the
            proof-of-work bits of the challenge, which is a function of the marked blocks
    Part 3  the relation on states
    Part 4  the rounds and the chain: `alike_chainT`, `sfr_chainT`
    Part 5  the proof strings; `sf_proveB`: one execution of the compiled prover, for any slots and
            flags
    Part 6  the verifier: `fo_chainB`, `fo_verifyBS`
    Part 7  `sf_Cp`, `sf_Pp`; `facBy_C`, `facBy_P`, `facBy_V`, for the relation on typed answers;
            `facBy_realQ`
  A scheme that is made from the programs of Parts 5 to 7 by bind, pure, `erase`, and by
  `OComp.blocks` and `OComp.derive` (Rom/OverOneNDerive.lean) has the property too, if of an answer
  of the seed's oracle nothing is left out (true of `other`: `whole_of_eq`, Top/ProgN.lean).
  Notation:
    `nb`: a map `Tag → ℕ → ℕ`; `QueryLayout.NB W nb` (Compile/Batch/NeedTable.lean): in round i of
      protocol t the challenge is a function of the blocks below nb t i;
    `tk`, `us` (`fbT`, Compile/Batch/Prover.lean): a Fiat-Shamir query is charged to tk; its other
      tokens are us and then the root, if the component has a tree;
    `nc`: an `Option ℕ`; `dd`: a list of `Tok`; `bl`: a `Blk lam K`; `tl`: a `Tok` (what the
      continuation k is given; `fbW`, `fbG`, Compile/Batch/Prover.lean): the number of the final
      attempt, if there is a proof-of-work record, the chaining values of those before it, and the
      blocks and the chaining value of the final one;
    `noted` (`hear`, Compile/Batch/Prover.lean): says whether the slot's component of this round
      has been recorded already;
    `ph`: in Parts 2 and 4 a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`,
      `shr tk0` or `aft`; in Part 6 a `Phase lam` (Compile/Batch/Verifier.lean): how far the chain
      of a slot has come;
    `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the
      trees over the external strings;
    `fl`: a map ℕ → Bool; it says for which slots a proof string is made at all (`finishAll`,
      Compile/Batch/Prover.lean);
    `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated.
  Limits: the file does not say that a marked block is read. It says nothing on numbers of queries
  (Compile/Batch/NeedCost.lean) or on distributions (Rom/OverOneN.lean has query bounds; that
  `overOneN` then has the output distribution of `overOne` is not proved in this library). Part 8,
  the same as in Part 7 in blocks, for every code m that cuts an answer as Compile/Batch/ImplOf.lean
  does: not in this library.
  Of the verifier without the strict-format check (`verifyB`, Compile/Batch/Verifier.lean) the end
  alone is treated (`fo_afterB`): Part 6's `fo_verifyBS`, and `facBy_V` at the V of
  Compile/Batch/Star.lean, are the strict verifier's (`verifyOneProtocol`).
-/
import Compile.Batch.Star
import Compile.Batch.ForestFacts
import Compile.Batch.NeedTable
import Compile.Batch.ProverG
import Compile.Batch.RealQ
import Compile.NeedRel

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.Need (SFac SFacR Alike facBy_ask_bind)

/-! ## Part 1. Trees -/

section Trees
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

local notation "Fc" => SFac (S := spec lam K L) (sp := split lam K L) (agree nb)

theorem sf_leafT (sMT : ℕ) (b : Body L) : Fc (leafT (lam := lam) (K := K) sMT b) :=
  .fresh _ fun _ =>
    .marked _ _ _ _ _ (fun v ws r r' h => by rw [show r = r' from h]; exact ⟨rfl, rfl⟩)
      fun _ _ => .pure _

theorem sf_nodeT (a b : Tok) : Fc (nodeT (lam := lam) (K := K) (L := L) a b) :=
  .marked _ _ _ _ _ (fun v ws r r' h => by rw [show r = r' from h]; exact ⟨rfl, rfl⟩)
    fun _ _ => .pure _

theorem sf_leavesT (sMT : ℕ) : ∀ l : List (Body L), Fc (leavesT (lam := lam) (K := K) sMT l)
  | [] => .pure _
  | b :: t => (sf_leafT nb sMT b).bind fun _ => (sf_leavesT sMT t).bind fun _ => .pure _

theorem sf_pairUp {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, Fc (node a b)) :
    ∀ l : List D, Fc (pairUp node l)
  | [] => .pure _
  | [_] => .pure _
  | a :: b :: t => (hn a b).bind fun _ => (sf_pairUp hn t).bind fun _ => .pure _

theorem sf_levelsM {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, Fc (node a b)) :
    ∀ (d : ℕ) (l : List D), Fc (levelsM node d l)
  | 0, _ => .pure _
  | d + 1, l => (sf_pairUp nb hn l).bind fun u => (sf_levelsM hn d u).bind fun _ => .pure _

theorem sf_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    Fc (commitT (lam := lam) (K := K) sMT d leaf) :=
  (sf_leavesT nb sMT _).bind fun x => (sf_levelsM nb (sf_nodeT nb) d x.1).bind fun _ => .pure _

theorem sf_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    Fc (openT (lam := lam) (K := K) (L := L) t j a) :=
  .reveal _ fun _ => .pure _

theorem sf_showT (t : Tok) : Fc (showT (lam := lam) (K := K) (L := L) t) :=
  .reveal _ fun _ => .pure _

theorem sf_rleafT (c : Tok) : Fc (rleafT (lam := lam) (K := K) (L := L) c) :=
  .marked _ _ _ _ _ (fun v ws r r' h => by rw [show r = r' from h]; exact ⟨rfl, rfl⟩)
    fun _ _ => .pure _

theorem sf_rnodeT (a b : Tok) : Fc (rnodeT (lam := lam) (K := K) (L := L) a b) :=
  .marked _ _ _ _ _ (fun v ws r r' h => by rw [show r = r' from h]; exact ⟨rfl, rfl⟩)
    fun _ _ => .pure _

theorem sf_rleavesT : ∀ l : List Tok, Fc (rleavesT (lam := lam) (K := K) (L := L) l)
  | [] => .pure _
  | c :: t => (sf_rleafT nb c).bind fun _ => (sf_rleavesT t).bind fun _ => .pure _

theorem sf_reqT (depthReq : ℕ) (cs : List Tok) :
    Fc (reqT (lam := lam) (K := K) (L := L) depthReq cs) :=
  (sf_rleavesT nb cs).bind fun ls =>
    (sf_levelsM nb (sf_rnodeT nb) depthReq ls).bind fun _ => .pure _

theorem sf_leafE (sMT : ℕ) (b : Body L) (bl : Bool) :
    Fc (leafE (lam := lam) (K := K) sMT b bl) := by
  unfold leafE
  cases bl
  · exact .plain _ _ (fun r r' h => by rw [show r = r' from h]) fun _ => .pure _
  · exact (sf_leafT nb sMT b).bind fun x => (sf_showT nb x.2).bind fun _ => .pure _

theorem sf_nodeE (a b : Dig lam) : Fc (nodeE (K := K) (L := L) a b) :=
  .plain _ _ (fun r r' h => by rw [show r = r' from h]) fun _ => .pure _

theorem sf_leavesE (sMT : ℕ) : ∀ l : List (Body L × Bool), Fc (leavesE (lam := lam) (K := K) sMT l)
  | [] => .pure _
  | (b, bl) :: t => (sf_leafE nb sMT b bl).bind fun _ => (sf_leavesE sMT t).bind fun _ => .pure _

theorem sf_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    Fc (commitE (lam := lam) (K := K) sMT d leaf) :=
  (sf_leavesE nb sMT _).bind fun x => (sf_levelsM nb (sf_nodeE nb) d x.1).bind fun _ => .pure _

theorem sf_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    Fc (openE (K := K) (L := L) t j a) := by
  unfold openE
  cases t.salts.getD j none with
  | none => exact .pure _
  | some s => exact .reveal _ fun _ => .pure _

theorem sf_drawT {β : Type} (e : Enum β) : Fc (drawT (lam := lam) (K := K) (L := L) e) :=
  .sample _ fun _ => .pure _

end Trees

/-! ## Part 2. Queries to the Fiat-Shamir oracle and to g -/

section Evals
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {β : Type} {R : β → β → Prop}

local notation "FR" => SFacR (S := spec lam K L) (sp := split lam K L) (agree nb)

/-- A Fiat-Shamir query of round i of protocol t: what follows may depend on the blocks below nb t i
and on the chaining value (hypotheses `he`, `h`). -/
theorem sfr_fbT (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β}
    (he : ∀ bl bl' : Blk lam K,
      (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → ∀ tl, Alike R (k bl tl) (k bl' tl))
    (h : ∀ bl tl, FR R (k bl tl)) :
    FR R (fbT t i tk us root hd hinj pl k) :=
  .marked _ _ _ _ _ (fun v ws r r' hr => by
    obtain ⟨h1, h2⟩ := hr
    exact ⟨h1, fun t' => he r.1 r'.1 h2 t'⟩) h

theorem alike_fbT (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k k' : Blk lam K → Tok → St lam K L β}
    (h : ∀ bl tl, Alike R (k bl tl) (k' bl tl)) :
    Alike R (fbT t i tk us root hd hinj pl k) (fbT t i tk us root hd hinj pl k') :=
  .marked _ _ _ _ _ h

theorem sfr_fbSlot (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok)
    (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β}
    (he : ∀ bl bl' : Blk lam K,
      (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → ∀ tl, Alike R (k bl tl) (k bl' tl))
    (h : ∀ bl tl, FR R (k bl tl)) :
    FR R (fbSlot t i cms x ph tk c root pl k) := by
  cases ph with
  | first => exact sfr_fbT nb _ _ _ _ _ _ (fun _ => f1_inj cms _) _ he h
  | shr tk0 => exact sfr_fbT nb _ _ _ _ _ _ (fun _ => f3_inj _) _ he h
  | loc => exact sfr_fbT nb _ _ _ _ _ _ (fun _ => f2_inj _) _ he h
  | aft => exact sfr_fbT nb _ _ _ _ _ _ (fun _ => f2_inj _) _ he h

theorem alike_fbSlot (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok)
    (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t)) {k k' : Blk lam K → Tok → St lam K L β}
    (h : ∀ bl tl, Alike R (k bl tl) (k' bl tl)) :
    Alike R (fbSlot t i cms x ph tk c root pl k) (fbSlot t i cms x ph tk c root pl k') := by
  cases ph with
  | first => exact alike_fbT _ _ _ _ _ _ (fun _ => f1_inj cms _) _ h
  | shr tk0 => exact alike_fbT _ _ _ _ _ _ (fun _ => f3_inj _) _ h
  | loc => exact alike_fbT _ _ _ _ _ _ (fun _ => f2_inj _) _ h
  | aft => exact alike_fbT _ _ _ _ _ _ (fun _ => f2_inj _) _ h

/-! ### The search over nonces -/

theorem sfr_fbTw (t : Tag) (j i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β}
    (he : ∀ bl bl' : Blk lam K,
      (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → ∀ tl, Alike R (k bl tl) (k bl' tl))
    (h : ∀ bl tl, FR R (k bl tl)) :
    FR R (fbTw t j i tk us root hd hinj pl k) :=
  .marked _ _ _ _ _ (fun v ws r r' hr => by
    obtain ⟨h1, h2⟩ := hr
    exact ⟨h1, fun t' => he r.1 r'.1 h2 t'⟩) h

theorem alike_fbTw (t : Tag) (j i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k k' : Blk lam K → Tok → St lam K L β}
    (h : ∀ bl tl, Alike R (k bl tl) (k' bl tl)) :
    Alike R (fbTw t j i tk us root hd hinj pl k) (fbTw t j i tk us root hd hinj pl k') :=
  .marked _ _ _ _ _ h

section Loop
variable {C P : Type} (chal : Blk lam K → C) (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
  (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (hch : ∀ bl bl' : Blk lam K, (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → chal bl = chal bl')
include hch

/-- The attempts after the first, if the challenge is a function of the marked blocks (`hch`) and
under `he`, `h`: which branch is taken depends only on the marked blocks. -/
theorem sfr_fbW (g : GrW C P) {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (he : ∀ m dd (bl bl' : Blk lam K),
      (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → ∀ tl, Alike R (k m dd bl tl) (k m dd bl' tl))
    (h : ∀ m dd bl tl, FR R (k m dd bl tl)) :
    ∀ n j dd, FR R (fbW g chal t i tk us root hd hinj emb α k n j dd)
  | 0, j, dd =>
    sfr_fbTw nb t j i tk us root hd hinj _
      (fun bl bl' e tl => he _ _ bl bl' e tl) fun bl tl => h _ _ bl tl
  | n + 1, j, dd => sfr_fbTw nb t j i tk us root hd hinj _ (fun bl bl' e tl => by
      show Alike R (if g.ok (chal bl) then _ else _) (if g.ok (chal bl') then _ else _)
      rw [hch bl bl' e]
      by_cases hok : g.ok (chal bl') = true
      · rw [if_pos hok, if_pos hok]
        exact he _ _ bl bl' e tl
      · rw [if_neg hok, if_neg hok]
        exact (sfr_fbW g he h n (j + 1) (tl :: dd)).self) fun bl tl => by
      show FR R (if g.ok (chal bl) then _ else _)
      by_cases hok : g.ok (chal bl) = true
      · rw [if_pos hok]
        exact h _ _ bl tl
      · rw [if_neg hok]
        exact sfr_fbW g he h n (j + 1) (tl :: dd)

/-- A Fiat-Shamir query with proof-of-work bits or without, under `hch`, `he`, `h`: what follows may
depend on the blocks below nb t i of the final answer, on its chaining value, on the number of the
final attempt and on the chaining values of the failed attempts. -/
theorem sfr_fbG (gr : Option (GrW C P)) {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (he : ∀ nc dd (bl bl' : Blk lam K),
      (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → ∀ tl, Alike R (k nc dd bl tl) (k nc dd bl' tl))
    (h : ∀ nc dd bl tl, FR R (k nc dd bl tl)) :
    FR R (fbG gr chal t i tk us root hd hinj emb α k) := by
  cases gr with
  | none =>
    exact sfr_fbT nb t i tk us root hd hinj _
      (fun bl bl' e tl => he _ _ bl bl' e tl) fun bl tl => h _ _ bl tl
  | some g =>
    show FR R (fbTG g chal t i tk us root hd hinj emb α fun m => k (some m))
    unfold fbTG
    cases g.more with
    | zero =>
      exact sfr_fbT nb t i tk us root hd hinj _
        (fun bl bl' e tl => he _ _ bl bl' e tl) fun bl tl => h _ _ bl tl
    | succ n =>
      have hW := sfr_fbW nb chal t i tk us root hd hinj emb α hch g (k := fun m => k (some m))
        (fun m dd bl bl' e tl => he _ _ bl bl' e tl) (fun m dd bl tl => h _ _ bl tl) n 0
      refine sfr_fbT nb t i tk us root hd hinj _ (fun bl bl' e tl => ?_) fun bl tl => ?_
      · show Alike R (if g.ok (chal bl) then _ else _) (if g.ok (chal bl') then _ else _)
        rw [hch bl bl' e]
        by_cases hok : g.ok (chal bl') = true
        · rw [if_pos hok, if_pos hok]
          exact he _ _ bl bl' e tl
        · rw [if_neg hok, if_neg hok]
          exact (hW [tl]).self
      · show FR R (if g.ok (chal bl) then _ else _)
        by_cases hok : g.ok (chal bl) = true
        · rw [if_pos hok]
          exact h _ _ bl tl
        · rw [if_neg hok]
          exact hW [tl]

omit hch in
theorem alike_fbG (gr : Option (GrW C P))
    {k k' : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h : ∀ nc dd bl tl, Alike R (k nc dd bl tl) (k' nc dd bl tl)) :
    Alike R (fbG gr chal t i tk us root hd hinj emb α k)
      (fbG gr chal t i tk us root hd hinj emb α k') :=
  fbG_two (Ψ := Alike R) gr (fun _ _ _ h => alike_fbT _ _ _ _ _ _ _ _ h)
    (fun _ _ _ _ h => alike_fbTw _ _ _ _ _ _ _ _ _ h) h

end Loop

theorem sfr_fbSlotG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (hch : ∀ bl bl' : Blk lam K, (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → chal bl = chal bl')
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (he : ∀ nc dd (bl bl' : Blk lam K),
      (∀ j : Fin K, j.val < nb t i → bl j = bl' j) → ∀ tl, Alike R (k nc dd bl tl) (k nc dd bl' tl))
    (h : ∀ nc dd bl tl, FR R (k nc dd bl tl)) :
    FR R (fbSlotG gr chal t i cms x ph tk c root emb α k) := by
  cases ph <;> exact sfr_fbG nb chal t i _ _ root _ _ emb α hch gr he h

theorem alike_fbSlotG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k k' : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h : ∀ nc dd bl tl, Alike R (k nc dd bl tl) (k' nc dd bl tl)) :
    Alike R (fbSlotG gr chal t i cms x ph tk c root emb α k)
      (fbSlotG gr chal t i cms x ph tk c root emb α k') := by
  cases ph <;> exact alike_fbG chal t i _ _ root _ _ emb α gr h

theorem sfr_gT (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Tok → St lam K L β} (h : ∀ c, FR R (k c)) : FR R (gT t i tk root pl k) :=
  .marked _ _ _ _ _
    (fun v ws r r' hr => by rw [show r = r' from hr]; exact ⟨rfl, fun t' => (h t').self⟩)
    fun _ c => h c

theorem alike_gT (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t))
    {k k' : Tok → St lam K L β} (h : ∀ c, Alike R (k c) (k' c)) :
    Alike R (gT (lam := lam) (K := K) t i tk root pl k) (gT t i tk root pl k') :=
  .marked _ _ _ _ _ fun _ c => h c

/-- the tree over a component, if it has one, and then what follows -/
theorem alike_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k k' : Option TTree → St lam K L β} (h : ∀ tr, Alike R (k tr) (k' tr)) :
    Alike R (withTree sMT has depth leaf k) (withTree sMT has depth leaf k') := by
  cases has with
  | true => exact Alike.bindSame _ fun tr => h (some tr)
  | false => exact h none

/-- the trees over a component, one after the other, and then what follows -/
theorem alike_withTrees (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k k' : List TTree → St lam K L β},
      (∀ trs, Alike R (k trs) (k' trs)) →
      Alike R (withTrees sMT ds leaf k) (withTrees sMT ds leaf k')
  | [], _, _, _, h => h []
  | _ :: ds, leaf, _, _, h =>
    Alike.bindSame _ fun tr =>
      alike_withTrees sMT ds (fun n => leaf (n + 1)) fun trs => h (tr :: trs)

theorem sfr_withTree (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} (h : ∀ tr, FR R (k tr)) :
    FR R (withTree sMT has depth leaf k) := by
  cases has with
  | true => exact SFacR.bindFac (sf_commitT nb _ _ _) fun tr => h (some tr)
  | false => exact h none

theorem sfr_withTrees (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β},
      (∀ trs, FR R (k trs)) → FR R (withTrees sMT ds leaf k)
  | [], _, _, h => h []
  | d :: ds, leaf, _, h =>
    SFacR.bindFac (sf_commitT nb sMT d (leaf 0)) fun tr =>
      sfr_withTrees sMT ds (fun n => leaf (n + 1)) fun trs => h (tr :: trs)

/-- do f in each slot: alike on lists that are alike (not all hypotheses are named here: see the
statement below) -/
theorem alike_eachM {σ τ : Type} {Q : σ → σ → Prop} {Q' : τ → τ → Prop} {f f' : σ → St lam K L τ}
    (h : ∀ a a', Q a a' → Alike Q' (f a) (f' a')) :
    ∀ {l l' : List σ}, List.Forall₂ Q l l' → Alike (List.Forall₂ Q') (eachM f l) (eachM f' l')
  | _, _, .nil => .pure .nil
  | _, _, .cons h1 h2 =>
    (h _ _ h1).bind fun _ _ hb => (alike_eachM h h2).bind fun _ _ hr => .pure (.cons hb hr)

theorem sfr_eachM {σ τ : Type} {Q : σ → σ → Prop} {Q' : τ → τ → Prop} {f : σ → St lam K L τ}
    (hs : ∀ a a', Q a a' → Alike Q' (f a) (f a')) (hf : ∀ a, Q a a → FR Q' (f a)) :
    ∀ {l : List σ}, List.Forall₂ Q l l → FR (List.Forall₂ Q') (eachM f l)
  | _, .nil => .pure .nil
  | _, .cons h1 h2 =>
    (hf _ h1).bind
      (fun _ _ hb => (alike_eachM hs h2).bind fun _ _ hr => .pure (.cons hb hr)) fun _ hb =>
        (sfr_eachM hs hf h2).bind (fun _ _ hr => .pure (.cons hb hr)) fun _ hr =>
          .pure (.cons hb hr)

theorem forall₂_map {σ τ : Type} {Q : σ → σ → Prop} {Q' : τ → τ → Prop} {f f' : σ → τ}
    (h : ∀ a a', Q a a' → Q' (f a) (f' a')) :
    ∀ {l l' : List σ}, List.Forall₂ Q l l' → List.Forall₂ Q' (l.map f) (l'.map f')
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (h _ _ h1) (forall₂_map h h2)

end Evals

/-! ## Part 3. The relation on states -/

section States
variable {lam K : ℕ} (nbf : ℕ → ℕ)

/-- two lists of stored blocks: of the same length, and entry number l of the one agrees with that
of the other below nbf (i + l) -/
def BRel : ℕ → List (Blk lam K) → List (Blk lam K) → Prop
  | _, [], [] => True
  | i, b :: t, b' :: t' => (∀ j : Fin K, j.val < nbf i → b j = b' j) ∧ BRel (i + 1) t t'
  | _, _, _ => False

theorem BRel.refl : ∀ (i : ℕ) (l : List (Blk lam K)), BRel nbf i l l
  | _, [] => trivial
  | i, _ :: t => ⟨fun _ _ => rfl, BRel.refl (i + 1) t⟩

variable {nbf}

theorem BRel.snoc {b b' : Blk lam K} :
    ∀ {i : ℕ} {l l' : List (Blk lam K)}, BRel nbf i l l' →
      (∀ j : Fin K, j.val < nbf (i + l.length) → b j = b' j) → BRel nbf i (l ++ [b]) (l' ++ [b'])
  | _, [], [], _, e => ⟨e, trivial⟩
  | i, _ :: t, _ :: t', h, e => ⟨h.1, BRel.snoc (i := i + 1) (l := t) (l' := t') h.2 (by
      have e' : i + 1 + t.length = i + (t.length + 1) := by omega
      rw [e']; exact e)⟩
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-- Under `ReadsFrom` and `BRel`: the challenges that are read off the stored blocks are the
same. -/
theorem rhoOf_congr :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (l l' : List (Blk lam K)),
      RoundsQueryLayout.ReadsFrom nbf s A W i → BRel nbf i l l' → rhoOf s A W l = rhoOf s A W l'
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: _, (_, _), (_, _), _, [], [], _, _ => rfl
  | _ :: s, (_, A), (w, W), i, b :: t, b' :: t', H, h => by
      show (w.chal b, rhoOf s A W t) = (w.chal b', rhoOf s A W t')
      rw [H.1 b b' h.1, rhoOf_congr s A W (i + 1) t t' H.2 h.2]
  | _ :: _, (_, _), (_, _), _, [], _ :: _, _, h => h.elim
  | _ :: _, (_, _), (_, _), _, _ :: _, [], _, h => h.elim

variable {Y : Type} (nbf)

/-- what two slots have gathered is alike: all is equal but the stored blocks; these are alike,
unless the slot is empty (then they are never read) -/
def AccRel (a a' : SlotAcc lam K Y) : Prop :=
  ∃ bls', a' = { a with blocks := bls' } ∧ (a.x = none ∨ BRel nbf 0 a.blocks bls')

/-- the same for a slot with what is left of its strategy, when i rounds have passed -/
def SlotRel (i : ℕ) {s : Shape} (z z' : SlotSt lam K Y s) : Prop :=
  ∃ bls',
    z' = (z.1, { z.2 with blocks := bls' }) ∧
    (z.2.x = none ∨ (z.2.blocks.length = i ∧ BRel nbf 0 z.2.blocks bls'))

variable {nbf}

theorem SlotRel.self {i : ℕ} {s : Shape} {z : SlotSt lam K Y s}
    (h : z.2.x = none ∨ z.2.blocks.length = i) : SlotRel nbf i z z :=
  ⟨z.2.blocks, rfl, h.imp id fun e => ⟨e, BRel.refl nbf 0 _⟩⟩

theorem SlotRel.lawful {i : ℕ} {s : Shape} {z z' : SlotSt lam K Y s} (h : SlotRel nbf i z z') :
    z.2.x = none ∨ z.2.blocks.length = i := by
  obtain ⟨_, _, h⟩ := h
  exact h.imp id fun e => e.1

theorem SlotRel.acc {i : ℕ} {s : Shape} {z z' : SlotSt lam K Y s} (h : SlotRel nbf i z z') :
    AccRel nbf z.2 z'.2 := by
  obtain ⟨bls', rfl, h⟩ := h
  exact ⟨bls', rfl, h.imp id fun e => e.2⟩

theorem SlotRel.c {i : ℕ} {s : Shape} {z z' : SlotSt lam K Y s} (h : SlotRel nbf i z z') :
    z.2.c = z'.2.c := by
  obtain ⟨bls', rfl, _⟩ := h
  rfl

/-- one more entry -/
theorem stepRel {x : Option Y} {i : ℕ} {l l' : List (Blk lam K)} {b b' : Blk lam K}
    (h : x = none ∨ (l.length = i ∧ BRel nbf 0 l l'))
    (e : ∀ j : Fin K, j.val < nbf i → b j = b' j) :
    x = none ∨ ((l ++ [b]).length = i + 1 ∧ BRel nbf 0 (l ++ [b]) (l' ++ [b'])) :=
  h.imp id fun h =>
    ⟨by rw [List.length_append, h.1]; rfl, h.2.snoc (by rw [Nat.zero_add, h.1]; exact e)⟩

/-- a slot receives a shared challenge: under hw, e, h the two states stay related (`SlotRel`, at
i + 1) -/
theorem rel_hear {r : Round} {s : Shape} {a : RAnn r} {w : WireRB lam K r a} {i : ℕ}
    (hw : w.ReadsBelow (nbf i)) {bl bl' : Blk lam K} (e : ∀ j : Fin K, j.val < nbf i → bl j = bl' j)
    (noted : Bool) {z z' : SlotSt lam K Y (r :: s)} (h : SlotRel nbf i z z') :
    SlotRel nbf (i + 1) (hear w bl noted z) (hear w bl' noted z') := by
  obtain ⟨bls', rfl, h⟩ := h
  obtain ⟨⟨m, k⟩, acc⟩ := z
  refine ⟨bls' ++ [bl'], ?_, stepRel h e⟩
  show (k (w.chal bl'), _) = (k (w.chal bl), _)
  rw [hw bl bl' e]
  rfl

end States

/-! ## Part 4. The rounds and the chain -/

section Rounds
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

local notation "FR" => SFacR (S := spec lam K L) (sp := split lam K L) (agree nb)

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem alike_slotLo (ph : PhT) {z z' : SlotSt lam K Y (r :: s)} (h : SlotRel (nb t) i z z') :
    Alike (SlotRel (nb t) (i + 1)) (slotLo sMT t cms xin a w emb plJ i ph z)
      (slotLo sMT t cms xin a w emb plJ i ph z') := by
  obtain ⟨bls', rfl, h⟩ := h
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact alike_withTree _ _ _ _ fun tr =>
    alike_fbSlotG _ _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
      .pure ⟨bls' ++ [bl], rfl, stepRel h fun _ _ => rfl⟩

theorem sfr_slotLo (hw : w.ReadsBelow (nb t i)) (ph : PhT) {z : SlotSt lam K Y (r :: s)}
    (h : z.2.x = none ∨ z.2.blocks.length = i) :
    FR (SlotRel (nb t) (i + 1)) (slotLo sMT t cms xin a w emb plJ i ph z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  have h' : acc.x = none ∨ (acc.blocks.length = i ∧ BRel (nb t) 0 acc.blocks acc.blocks) :=
    h.imp id fun e => ⟨e, BRel.refl _ 0 _⟩
  dsimp only [slotLo]
  refine sfr_withTree nb _ _ _ _ fun tr =>
    sfr_fbSlotG nb _ _ _ _ _ _ _ _ _ _ _ _ hw
      (fun nc dd bl bl' e tl => .pure ⟨acc.blocks ++ [bl'], ?_, stepRel h' e⟩)
      fun nc dd bl tl => .pure ⟨acc.blocks ++ [bl], rfl, stepRel h' fun _ _ => rfl⟩
  rw [hw bl bl' e]

theorem alike_slotJoin {z z' : SlotSt lam K Y (r :: s)} (h : SlotRel (nb t) i z z') :
    Alike (SlotRel (nb t) i) (slotJoin sMT t a w emb plJ i z)
      (slotJoin sMT t a w emb plJ i z') := by
  obtain ⟨bls', rfl, h⟩ := h
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact alike_withTree _ _ _ _ fun tr => alike_gT _ _ _ _ _ fun c => .pure ⟨bls', rfl, h⟩

theorem sfr_slotJoin {z : SlotSt lam K Y (r :: s)} (h : z.2.x = none ∨ z.2.blocks.length = i) :
    FR (SlotRel (nb t) i) (slotJoin sMT t a w emb plJ i z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact sfr_withTree nb _ _ _ _ fun tr => sfr_gT nb _ _ _ _ _ fun c => .pure (SlotRel.self h)

/-- what the joining round returns: the slots, and their slot values -/
def JRel (nbf : ℕ → ℕ) (i : ℕ) (o o' : List (SlotSt lam K Y (r :: s)) × List Tok) : Prop :=
  List.Forall₂ (SlotRel nbf i) o.1 o'.1 ∧ o.2 = o'.2

theorem alike_joinM :
    ∀ {zs zs' : List (SlotSt lam K Y (r :: s))}, List.Forall₂ (SlotRel (nb t) i) zs zs' →
      Alike (JRel (nb t) i) (joinM sMT t a w emb plJ i zs) (joinM sMT t a w emb plJ i zs')
  | _, _, .nil => .pure ⟨.nil, rfl⟩
  | _, _, .cons h1 h2 =>
    (alike_slotJoin nb sMT t a w emb plJ i h1).bind fun _ _ hz =>
      (alike_joinM h2).bind fun _ _ ho => .pure ⟨.cons hz ho.1, congrArg₂ List.cons hz.c ho.2⟩

theorem sfr_joinM :
    ∀ {zs : List (SlotSt lam K Y (r :: s))},
      List.Forall₂ (SlotRel (nb t) i) zs zs → FR (JRel (nb t) i) (joinM sMT t a w emb plJ i zs)
  | _, .nil => .pure ⟨.nil, rfl⟩
  | _, .cons h1 h2 =>
    (sfr_slotJoin nb sMT t a w emb plJ i h1.lawful).bind
      (fun _ _ hz =>
        (alike_joinM nb sMT t a w emb plJ i h2).bind fun _ _ ho =>
          .pure ⟨.cons hz ho.1, congrArg₂ List.cons hz.c ho.2⟩) fun _ hz =>
            (sfr_joinM h2).bind (fun _ _ ho => .pure ⟨.cons hz ho.1, congrArg₂ List.cons hz.c ho.2⟩)
              fun _ ho => .pure ⟨.cons hz ho.1, rfl⟩

end One

/-! the four kinds of rounds of chainT, written out -/

section Unfold
variable (depthReq : ℕ) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L) (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
  (m0 : a.M0) (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0)

theorem chainT_lo (hk : a.kind = .lo) (ph : PhT) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      (eachM
        (slotLo sMT t cms xin a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        zs).bind fun zs' =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl

theorem chainT_join (hk : a.kind = .sh) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0 =
      (joinM sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqT depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

theorem chainT_shr (hk : a.kind = .sh) (tk0 : Tok) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) zs a0
      = tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

/-- a shared round at the start or after the later local rounds: nothing is hashed -/
theorem chainT_none (hk : a.kind = .sh) (ph : PhT) (hph : ph = .first ∨ ph = .aft) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
        ph (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
        { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl <;> rfl

end Unfold

/-- what all chains return: what the slots have gathered, alike; what the shared part has gathered,
equal -/
def OutRel (nbf : ℕ → ℕ) (o o' : List (SlotAcc lam K Y) × Acc0) : Prop :=
  List.Forall₂ (AccRel nbf) o.1 o'.1 ∧ o.2 = o'.2

variable (depthReq : ℕ)

/-- Under `ReadsFrom`: all chains of a batch, from states that are alike (`SlotRel`), are alike
(`OutRel`). -/
theorem alike_chainT :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs zs' : List (SlotSt lam K Y s)) (a0 : Acc0),
      RoundsQueryLayout.ReadsFrom (nb t) s A W i → List.Forall₂ (SlotRel (nb t) i) zs zs' →
      Alike (OutRel (nb t)) (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
        (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs' a0)
  | [], _, _, _, _, _, _, _, _, _, _, _, hz => .pure ⟨forall₂_map (fun _ _ h => h.acc) hz, rfl⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, zs', a0, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph,
          chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk ph]
        exact (alike_eachM (fun _ _ h => alike_slotLo nb sMT t cms xin a w _ _ i ph h) hz).bind
          fun zs1 zs1' h1 => alike_chainT s A W _ _ (i + 1) _ _ zs1 zs1' _ H.2 h1
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk',
            chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk']
          refine (alike_joinM nb sMT t a w _ _ i hz).bind fun o o' ho => ?_
          obtain ⟨o1, o2⟩ := o
          obtain ⟨o1', o2'⟩ := o'
          obtain ⟨h1, h2⟩ := ho
          obtain rfl : o2 = o2' := h2
          exact Alike.bindSame _ fun rq =>
              alike_withTree _ _ _ _ fun tr0 => alike_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
            alike_chainT s A W _ _ (i + 1) _ _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) true h) h1)
        | shr tk0 =>
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0,
            chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk' tk0]
          exact alike_withTree _ _ _ _ fun tr0 => alike_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
            alike_chainT s A W _ _ (i + 1) _ _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
        | first =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl),
            chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk' _ (.inl rfl)]
          exact alike_chainT s A W _ _ (i + 1) _ _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
        | aft =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl),
            chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs' a0 hk' _ (.inr rfl)]
          exact alike_chainT s A W _ _ (i + 1) _ _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)

/-- Under `ReadsFrom`, from slots' states that are each related to themselves (`SlotRel`): all
chains of a batch go on in the same way, up to the stored blocks, after two answers that agree on
what is needed. -/
theorem sfr_chainT :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      RoundsQueryLayout.ReadsFrom (nb t) s A W i → List.Forall₂ (SlotRel (nb t) i) zs zs →
      FR (OutRel (nb t)) (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, _, _, _, hz => .pure ⟨forall₂_map (fun _ _ h => h.acc) hz, rfl⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, H, hz => by
      by_cases hk : a.kind = .lo
      · rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        exact (sfr_eachM nb (fun _ _ h => alike_slotLo nb sMT t cms xin a w _ _ i ph h)
            (fun _ h => sfr_slotLo nb sMT t cms xin a w _ _ i H.1 ph h.lawful) hz).bind
          (fun zs1 zs1' h1 =>
            alike_chainT nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ zs1 zs1' _ H.2 h1)
          fun zs1 h1 => sfr_chainT s A W _ _ (i + 1) _ _ zs1 _ H.2 h1
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine (sfr_joinM nb sMT t a w _ _ i hz).bind (fun o o' ho => ?_) fun o ho => ?_
          · obtain ⟨o1, o2⟩ := o
            obtain ⟨o1', o2'⟩ := o'
            obtain ⟨h1, h2⟩ := ho
            obtain rfl : o2 = o2' := h2
            exact Alike.bindSame _ fun rq =>
                alike_withTree _ _ _ _ fun tr0 => alike_fbG _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
              alike_chainT nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2
                (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) true h) h1)
          · refine SFacR.bindFac (sf_reqT nb _ _) fun rq =>
                sfr_withTree nb _ _ _ _ fun tr0 =>
                    sfr_fbG nb _ _ _ _ _ _ _ _ _ _ H.1 _
                        (fun nc dd bl bl' e tl => ?_) fun nc dd bl tl =>
              sfr_chainT s A W _ _ (i + 1) _ _ _ _ H.2
                (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) true h) ho.1)
            rw [H.1 bl bl' e]
            exact alike_chainT nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 e true h) ho.1)
        | shr tk0 =>
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine sfr_withTree nb _ _ _ _ fun tr0 =>
              sfr_fbG nb _ _ _ _ _ _ _ _ _ _ H.1 _ (fun nc dd bl bl' e tl => ?_) fun nc dd bl tl =>
            sfr_chainT s A W _ _ (i + 1) _ _ _ _ H.2
              (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
          rw [H.1 bl bl' e]
          exact alike_chainT nb sMT t cms xin depthReq s A W _ _ (i + 1) _ _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 e false h) hz)
        | first =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inl rfl)]
          exact sfr_chainT s A W _ _ (i + 1) _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)
        | aft =>
          rw [chainT_none sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' _ (.inr rfl)]
          exact sfr_chainT s A W _ _ (i + 1) _ _ _ _ H.2
            (forall₂_map (fun _ _ h => rel_hear H.1 (fun _ _ => rfl) false h) hz)

end Rounds

/-! ## Part 5. The proof strings; one execution -/

section Prove
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

local notation "Fc" => SFac (S := spec lam K L) (sp := split lam K L) (agree nb)
local notation "FR" => SFacR (S := spec lam K L) (sp := split lam K L) (agree nb)

theorem sf_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, Fc (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => .pure _
  | j :: js => (sf_opensComp dec posAt o tr isRead f js).bind fun f' => by
      show Fc (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => exact .pure _
      | some p =>
        show Fc (if isRead p then _ else _)
        cases isRead p
        · exact .pure _
        · exact (sf_openT nb tr j _).bind fun _ => .pure _

theorem sf_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Fc (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => exact .pure _
  | some tr => exact sf_opensComp nb dec posAt o tr isRead f _

theorem sf_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      Fc (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => .pure _
  | _, _ :: _, [], _ => .pure _
  | k, _ :: ds, tr :: trs, f =>
    (sf_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      sf_opensComp nb dec (posAt k) o tr isRead f' _

theorem sf_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      Fc (opensB (L := L) s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => .pure _
  | _ :: s, (_, A), (_, W), (_, _, τ), tjs, t0s, _ =>
      (sf_opensOpt nb _ _ _ _ _ _ _).bind fun _ =>
        (sf_opensOpt nb _ _ _ _ _ _ _).bind fun _ =>
          (sf_opensB s A W τ tjs.tail t0s.tail _).bind fun _ => .pure _

theorem sf_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos, Fc (opensExtB (K := K) (L := L) we y trees isRead ps)
  | [] => .pure _
  | p :: ps => (sf_opensExtB we y trees isRead ps).bind fun f => by
      show Fc (if isRead p then
          (openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)).bind
            fun op => Step.pure (@Function.update _ _ we.dec f p (some op)) else Step.pure f)
      cases isRead p
      · exact .pure _
      · exact (sf_openE nb _ _ _).bind fun _ => .pure _

variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

theorem sf_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    Fc (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · exact .pure _
  · exact .reveal _ fun vs =>
      (sf_opensB nb _ _ _ _ _ _ _).bind fun f => (sf_opensExtB nb _ _ _ _ _).bind fun g => .pure _

/-- The proof string of a slot is made from the challenges that are read off the stored blocks, not
from the blocks. -/
theorem finishSlot_congr (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (bls' : List (Blk lam K))
    (h : rhoOf Q.loc.shape Q.ann wq.sh acc.blocks = rhoOf Q.loc.shape Q.ann wq.sh bls') :
    finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc =
      finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj { acc with blocks := bls' } := by
  unfold finishSlot
  dsimp only
  rw [h]

theorem sf_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      Fc (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs)
  | _, [] => .pure _
  | j, acc :: zs => SFac.bind (by
      cases acc.x with
      | none => exact .pure _
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        show Fc (if fl j then _ else _)
        cases fl j
        · exact .pure _
        · exact sf_finishSlot nb Q H wq wp trees w c0 a0 j x cj acc) fun _ => (sf_finishAll fl c0 a0 (j + 1) zs).bind fun _ => .pure _

theorem finishAll_congr (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0) (fl : ℕ → Bool)
    (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) {zs zs' : List (SlotAcc lam K (Y × H.Coin))}, List.Forall₂ (AccRel (nb t)) zs zs' →
      finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs =
        finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs'
  | _, _, _, .nil => rfl
  | j, acc :: zs, _ :: zs', .cons h1 h2 => by
      obtain ⟨bls', rfl, h1⟩ := h1
      have e : (match acc.x with
          | some (x, cj) =>
            if fl j then finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc else pure none
          | none => pure none)
        = (match acc.x with
          | some (x, cj) =>
            if fl j then
              finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj { acc with blocks := bls' }
            else pure none
          | none => pure none) := by
        rcases h1 with h1 | h1
        · rw [h1]
        · have key : ∀ x cj, finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc =
              finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj { acc with blocks := bls' } :=
            fun x cj =>
              finishSlot_congr Q H wq wp trees w c0 a0 j x cj acc
                bls' (rhoOf_congr _ _ _ 0 _ _ hW h1)
          simp only [key]
      show Step.bind _ _ = Step.bind _ _
      rw [finishAll_congr hW fl c0 a0 (j + 1) h2]
      exact congrArg (fun c => Step.bind c _) e

theorem sfr_initSlot (c0 : H.Coin0) (x : Option Y) :
    FR (SlotRel (nb t) 0) (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) :=
  SFacR.bindFac (sf_drawT nb wp.coin) fun _ => .fresh _ fun _ => .pure (SlotRel.self (.inr rfl))

/-- a list and itself: equal entry by entry -/
theorem forall₂_eq_self {σ : Type} : ∀ l : List σ, List.Forall₂ Eq l l
  | [] => .nil
  | _ :: t => .cons rfl (forall₂_eq_self t)

/-- Under `ReadsFrom`: one execution of the compiled prover goes on in the same way after two
answers that agree on what is needed: whatever the slots hold, and for whichever slots proof strings
are made. -/
theorem sf_proveB (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    Fc (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) := by
  unfold proveB
  refine (sf_drawT nb wp.coin0).bind fun c0 => SFacR.toFac ?_
  refine (sfr_eachM nb (Q := Eq) (fun a _ h => h ▸ (sfr_initSlot nb sFS t Q H wp w c0 a).self)
      (fun a _ => sfr_initSlot nb sFS t Q H wp w c0 a) (forall₂_eq_self xs)).bind
    (fun zs zs' hz => ?_) fun zs hz => ?_
  · exact (alike_chainT nb sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs zs' _ hW hz).bind
        fun out out' ho => by
      obtain ⟨o1, o2⟩ := out
      obtain ⟨o1', o2'⟩ := out'
      obtain ⟨h1, h2⟩ := ho
      obtain rfl : o2 = o2' := h2
      exact Alike.of_eq (finishAll_congr nb t Q H wq wp trees w hW fl c0 o2 0 h1)
  · exact (sfr_chainT nb sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hW hz).bind (fun out out' ho => by
      obtain ⟨o1, o2⟩ := out
      obtain ⟨o1', o2'⟩ := out'
      obtain ⟨h1, h2⟩ := ho
      obtain rfl : o2 = o2' := h2
      exact Alike.of_eq (finishAll_congr nb t Q H wq wp trees w hW fl c0 o2 0 h1)) fun out _ => (sf_finishAll nb Q H wq wp trees w fl c0 out.2 0 out.1).toR

end Prove

/-! ## Part 6. The verifier's programs -/

section Verifier
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

local notation "Fo" => OComp.FactorsBy (S := spec lam K L) (agree nb)

/-- a query to an oracle at which the relation is equality -/
theorem fo_askV (o : OracleName) (q : domOf lam L o) (h : ∀ r r', agree (K := K) nb o q r r' → r = r') :
    Fo (askTypedOracle (K := K) (L := L) o q) :=
  ⟨fun r r' e => by rw [h r r' e], fun _ => trivial⟩

theorem fo_nodeV (a b : Dig lam) : Fo (hashTreeNode (K := K) (L := L) a b) :=
  fo_askV nb OracleName.node _ fun _ _ h => h
theorem fo_rnodeV (a b : Dig lam) : Fo (rnodeV (K := K) (L := L) a b) :=
  fo_askV nb OracleName.rnode _ fun _ _ h => h

theorem fo_climbM {node : Dig lam → Dig lam → TypedOracleComputation lam K L (Dig lam)} (hn : ∀ a b, Fo (node a b)) :
    ∀ (path : List (Dig lam)) (j : ℕ) (c : Dig lam), Fo (climbM node path j c)
  | [], _, _ => trivial
  | s :: ss, j, c => by
      unfold climbM
      split_ifs
      · exact OComp.FactorsBy.bind (hn c s) fun u => fo_climbM hn ss (j / 2) u
      · exact OComp.FactorsBy.bind (hn s c) fun u => fo_climbM hn ss (j / 2) u

theorem fo_runCheck (c : Check lam L) : Fo (runCheck (K := K) c) :=
  OComp.FactorsBy.bind (fo_askV nb OracleName.leaf c.inp fun _ _ h => h) fun d =>
    OComp.FactorsBy.bind (fo_climbM nb (fo_nodeV nb) c.path c.j d) fun _ => trivial

theorem fo_runChecks : ∀ cs : List (Check lam L), Fo (runChecks (K := K) cs)
  | [] => trivial
  | c :: cs =>
    OComp.FactorsBy.bind (fo_runCheck nb c) fun _ =>
      OComp.FactorsBy.bind (fo_runChecks cs) fun _ => trivial

theorem fo_reqCheck (depthReq : ℕ) (rtreq : Dig lam) (slot : ℕ)
    (path : List (Dig lam)) (c : Dig lam) :
    Fo (reqCheck (L := L) (K := K) depthReq rtreq slot path c) := by
  unfold reqCheck
  split_ifs
  · exact OComp.FactorsBy.bind (fo_askV nb OracleName.rleaf _ fun _ _ h => h) fun d =>
      OComp.FactorsBy.bind (fo_climbM nb (fo_rnodeV nb) path slot d) fun _ => trivial
  · trivial

theorem fo_afterB {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    Fo (afterB Q wq embS embE depthReq cms x π ρ rts ph) := by
  unfold afterB
  split
  · split_ifs
    · refine OComp.FactorsBy.bind (fo_runChecks nb _) fun _ => ?_
      dsimp only
      split
      · trivial
      · exact OComp.FactorsBy.bind (fo_reqCheck nb _ _ _ _ _) fun _ => trivial
    · trivial
  · trivial

/-- the last part of the strict verifier, with pruned Merkle paths -/
theorem fo_afterBO {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (ρ : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    Fo (checkPrunedOpenings Q wq embS embE depthReq cms x π ρ rts ph) :=
  Counts.afterBO (P := fun {_} c _ => OComp.FactorsBy (S := spec lam K L) (agree nb) c)
    ⟨fun _ _ => trivial, fun h hg => OComp.FactorsBy.bind h hg, fun h _ => h⟩
    (fun q => fo_askV nb OracleName.leaf q fun _ _ h => h) (fun q => fo_askV nb OracleName.node q fun _ _ h => h)
    (fun q => fo_askV nb OracleName.rleaf q fun _ _ h => h) (fun q => fo_askV nb OracleName.rnode q fun _ _ h => h)
    Q wq embS embE depthReq cms x π ρ rts ph

/-- The chain, recomputed, under `ReadsFrom`: after the Fiat-Shamir query of round i the verifier
goes on with the challenge of the round and with the chaining value. -/
theorem fo_chainB (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s),
      RoundsQueryLayout.ReadsFrom (nb t) s A W i →
      Fo (recomputeChain (L := L) t cms x salt rtreq s A W embP i ph rts pls)
  | [], _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls), H => by
      simp only [recomputeChain]
      split
      · rename_i h next e
        split
        · rename_i rt rts' _
          refine facBy_ask_bind (S := spec lam K L) (o := OracleName.fb t) (fun r r' hr => ?_) fun r =>
            OComp.FactorsBy.bind
              (fo_chainB t cms x salt rtreq s A W _ (i + 1) _ rts' pls H.2) fun _ => trivial
          obtain ⟨h1, h2⟩ := hr
          rw [h1, H.1 r.1 r'.1 h2]
        · trivial
      · rename_i h next e
        split
        · rename_i rt rts' _
          refine facBy_ask_bind (S := spec lam K L) (o := OracleName.fb t) (fun r r' hr => ?_) fun r =>
            OComp.FactorsBy.bind
              (fo_chainB t cms x salt rtreq s A W _ (i + 1) _ rts' pls H.2) fun _ => trivial
          obtain ⟨h1, h2⟩ := hr
          rw [h1, H.1 r.1 r'.1 h2]
        · trivial
      · rename_i ρ e
        split
        · rename_i rtj rts1 _
          split
          · rename_i rt0 rts' _
            refine facBy_ask_bind (S := spec lam K L) (o := OracleName.g t)
              (fun c c' hc => by rw [show c = c' from hc]) fun c => ?_
            refine facBy_ask_bind (S := spec lam K L) (o := OracleName.fb t) (fun r r' hr => ?_) fun r =>
              OComp.FactorsBy.bind
                (fo_chainB t cms x salt rtreq s A W _ (i + 1) _ rts' pls H.2) fun _ => trivial
            obtain ⟨h1, h2⟩ := hr
            rw [h1, H.1 r.1 r'.1 h2]
          · trivial
        · trivial
      · trivial

/-- Under `ReadsFrom`: the compiled verifier of one slot, with the strict-format check, goes on in
the same way after two answers that agree on what is needed. -/
theorem fo_verifyBS (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0) :
    Fo (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π) := by
  unfold verifyOneProtocol recomputeChainOfProof
  refine OComp.FactorsBy.bind (fo_chainB nb t _ _ _ _ _ _ _ _ _ _ _ _ hW) fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · trivial
  · dsimp only
    split_ifs
    · exact fo_afterBO nb Q wq embS embE depthReq cms x π ρ rts ph
    · trivial

end Verifier

/-! ## Part 7. C, P, V -/

section Star
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) {nb : Tag → ℕ → ℕ} (hW : W.NB nb)

local notation "Fc" => SFac (S := spec lam W.K L) (sp := split lam W.K L) (agree nb)
local notation "Fo" => OComp.FactorsBy (S := spec lam W.K L) (agree nb)

theorem sf_nodeP' (i : I) : Fc (nodeP' W WP p i) :=
  (sf_drawT nb WP.ri).bind fun _ => (sf_commitE nb p.sMT W.depth _).bind fun _ => .pure _

include hW

theorem fo_vTS (sMT sFS : ℕ) (cm : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)) :
    Fo (vTS W sMT sFS cm π) :=
  fo_verifyBS nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.T
theorem fo_vLS (sMT sFS : ℕ) (cm cm' : Dig lam) (π : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)) :
    Fo (vLS W sMT sFS cm cm' π) :=
  fo_verifyBS nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.Lk
theorem fo_vBS (sMT sFS : ℕ) (cm : Dig lam) (x : X) (π : OneProtocolProof lam L.onlineBatch) :
    Fo (vBS W sMT sFS cm x π) :=
  fo_verifyBS nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.B

theorem sf_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) : Fc (proveT W WP p tree i r) :=
  (sf_proveB nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.T _ _).bind fun _ => .pure _

theorem sf_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    Fc (proveLk W WP p root tree i r₀ r) :=
  (sf_proveB nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.Lk _ _).bind fun _ => .pure _

theorem sf_leavesC (i : I) (root : Node lam L) : ∀ n, Fc (leavesC W WP p i root n)
  | 0 => .pure _
  | n + 1 =>
    (sf_nodeP' W WP p i).bind fun _ =>
      (sf_proveLk W WP p hW _ _ _ _ _).bind fun _ => (sf_leavesC i root n).bind fun _ => .pure _

theorem sf_Cp (i : I) : Fc (Cp W WP p i) :=
  (sf_nodeP' W WP p i).bind fun _ =>
    (sf_proveT W WP p hW _ _ _).bind fun _ => (sf_leavesC W WP p hW i _ _).bind fun _ => .pure _

theorem sf_PpJ (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    Fc (PpJ W WP p k fr xs j σ) := by
  unfold PpJ
  cases k.leaves[j]? with
  | none => exact .pure _
  | some lf => exact (sf_proveB nb _ _ _ _ _ _ _ _ _ _ _ _ _ hW.B _ _).bind fun _ => .pure _

theorem sf_Pp (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : Fc (Pp W WP p k fr xs) :=
  .sample _ fun j => (sf_drawT nb WP.perm).bind fun σ => sf_PpJ W WP p hW k fr xs j.val σ

omit hW in
/-- The property carries over to `realQ c`, the program with every query to `fbw t k` turned into
the query to `fb t`: a ghost name `fbw t k` has the table of the oracle for which it stands. -/
theorem facBy_realQ {α : Type} (c : TypedOracleComputation lam W.K L α) (h : Fo c) : Fo (realQ c) := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r (h r)
  | query o q k ih =>
    cases o <;> exact ⟨fun r r' e => congrArg realQ (h.1 r r' e), fun r => ih r (h.2 r)⟩

/-- Under `W.NB nb`: the committer goes on in the same way after two answers that agree on what is
needed. -/
theorem facBy_C (i : I) : Fo (C W WP p i) :=
  facBy_realQ W _ (OComp.FactorsBy.bind ((sf_Cp W WP p hW i).erase []) fun _ => trivial)

/-- Under `W.NB nb`, so does the prover, on a batch. -/
theorem facBy_P (k : ISK lam L) (b : List (X × Unit)) : Fo (P W WP p k b) :=
  facBy_realQ W _ (OComp.FactorsBy.bind ((sf_Pp W WP p hW k.1 _ _).erase k.2) fun _ => trivial)

/-- Under `W.NB nb`, so does the verifier. -/
theorem facBy_V (v : IVK lam L) (x : X) (π : Prf lam L) : Fo (V W p v x π) := by
  unfold V
  split
  · split_ifs
    · exact OComp.FactorsBy.bind (fo_vTS W hW _ _ _ _) fun _ =>
        OComp.FactorsBy.bind (fo_vLS W hW _ _ _ _ _) fun _ =>
          OComp.FactorsBy.bind (fo_vBS W hW _ _ _ _ _) fun _ => trivial
    · trivial
  · trivial

end Star

end Need
end Compile.Batch
