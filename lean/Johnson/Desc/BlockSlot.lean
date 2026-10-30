-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/BlockSlot.lean: the road from a file's description (`FileDescription`,
Johnson/Desc/Block.lean) into the compiler's one slot for a file of three chains (`reductionOfWholeFile`,
OnBytes/Maker/Whole.lean), and what ties the two.

Main definitions.
  `FileDescription.data file`: the data of the file's rounds, made of `F.roundsDeclaredByBlocks` by the road
    (`writtenOf`, Johnson/G/RoundsOfPlan.lean; `WholeD.of`, `wholeAt`): no second road. It asks the
    makers' tests (`okAt`) by name and refuses where they say no: so `.ok D` is evidence. The stored
    table's depth is the description's own (`tableDepth`).
  `FileDescription.toIOR`: the file's reduction: `reductionOfWholeFile` at data D, with `F.run` in the place of the
    decision on the three views. Proved.
  `FileDescription.out_eq` (by unfolding): WHAT THE REDUCTION's VERDICT IS: NOT THE FOLD ALONE: in front of
    `F.run` the slot itself tests the proofs of work (`passT`, three times), that no draw is
    shortened (`fullOf`, three times), that every symbol read of the stored table carries its
    position (`carriesOf`), and the three rounds without a challenge (`silent`).
  `FileDescription.toIOR_local` (`wholeIOR_local`): the reduction's protocol is local: its
    decision hangs on the oracles at the positions read alone. Statements, not proved here (their
    proofs: `okViewIs`, `ofData`, Johnson/Desc/BlockSlotProofs.lean).
  `OkViewIs`: `viewWordsBelowPrime` is `okView` and, beside it, the drawn elements' words.
  `WantsAre F D`: at each chain and at all draws, what the slot reads (`wantsOf` at D) is what the
    description's declared rounds read by their own shapes (`wantsDecl`): AS WANTS: EACH TREE BY ITS
    NUMBER OVER THE FILE, so which tree is read is not forgotten. At the first chain the data have
    no sealing round: the declared rounds are taken without their last.
  `KeysAre F D`: at every opening, the key under which the slot's view shows the tree is the one by
    which `Block.step` looks for it.
  `ReadsAre F D`: the two together, as a view's columns show them (key and position): `Block.step`'s
    one matching never refuses a slot's view for its keys and positions, and `decide` sees just what
    the slot read. (The slot's `reads` and `extReads` are functions of the same three lists of
    wants.)
  `OfData`: all three under the one premise `F.data file = .ok D`.
  `GroupsAppend` (PROVED: `groupsAppend`): what rounds in a row read is what the first read, then
    what the others read: so a chain's reads are its blocks' reads at their own draws, in order.

Limits. No description of the protocol is here, so nothing is said at a real plan. (key, position)
ALONE FORGETS WHICH TREE WHERE TWO TREES SHOW UNDER ONE KEY, AND ON THE THIRD CHAIN THEY DO (a tree
that is taken over and the chain's first own tree: key 0): hence `WantsAre` beside `ReadsAre`.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Block
import Johnson.G.RoundsOfPlan
import OnBytes.Maker.OkView
import OnBytes.Maker.WholeLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc
open OnBytes OnBytes.Maker Johnson.G.OfPlan
open Iop _root_.Run _root_.Run.PQ Compile.Joined

variable {Xi : Type}

/-- The data of the file's rounds, of the description's declared rounds. -/
def FileDescription.data (F : FileDescription Xi) (file : String) : Except String WholeD := do
  let R ← writtenOf file F.roundsDeclaredByBlocks
  unless okAt F.tableDepth (some R) do
    throw (file ++ ": the makers' tests on the written rounds say no")
  pure (WholeD.of F.tableDepth (wholeAt (some R)))

section
variable (C : CK) (F : FileDescription Xi) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)
  (silent : Xi → TF → TJ → T3 → Bool)

/-- The file's reduction. -/
@[reducible] def FileDescription.toIOR : IOR Xi (oneExternalString (2 ^ D.a) SgX) Unit extNone :=
  reductionOfWholeFile C D tF tJ t3 silent F.run

/-- **What the reduction's verdict is.** -/
theorem FileDescription.out_eq (x : Xi) (y : (oneExternalString (2 ^ D.a) SgX).Str)
    (τ : Iop.Tr (F.toIOR C D tF tJ t3 silent).shape) :
    (F.toIOR C D tF tJ t3 silent).out x y τ =
      (let τ₁ := (chainsOf C D tF tJ t3).tr₁ τ
       let τ₂ := (chainsOf C D tF tJ t3).tr₂ τ
       let τ₃ := (chainsOf C D tF tJ t3).tr₃ τ
       let w₁ := wantsOf D.a D.depth D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ τ₁))
       let w₂ := wantsOf D.a D.depth D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ τ₂))
       let w₃ := wantsOf D.a D.depth D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ τ₃))
       if passT C D.ds₁ (rhoT C D.ds₁ τ₁) && passT C D.ds₂ (rhoT C D.ds₂ τ₂) &&
           passT C D.ds₃ (rhoT C D.ds₃ τ₃) &&
           fullOf D.ds₁ (drawnT C D.ds₁ (rhoT C D.ds₁ τ₁)) &&
           fullOf D.ds₂ (drawnT C D.ds₂ (rhoT C D.ds₂ τ₂)) &&
           fullOf D.ds₃ (drawnT C D.ds₃ (rhoT C D.ds₃ τ₃)) && carriesOf D y (w₁ ++ (w₂ ++ w₃)) &&
           silent x ((chainsOf C D tF tJ t3).msgF τ).2 ((chainsOf C D tF tJ t3).msgJ τ).2
             ((chainsOf C D tF tJ t3).msg3 τ).2 &&
           F.run x (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₁ τ₁) D.key₁ w₁)
             (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₂ τ₂) D.key₂ w₂)
             (viewOf C D y τ₁ τ₂ τ₃ (rvT C D.ds₃ τ₃) D.key₃ w₃) then some () else none) :=
  rfl

/-- **The reduction's protocol is local**: its decision hangs on the oracles at the positions read
alone. -/
theorem FileDescription.toIOR_local : (F.toIOR C D tF tJ t3 silent).toInteractiveOracleProof.IsLocal :=
  wholeIOR_local C D tF tJ t3 silent F.run

end

/-- The statement: `viewWordsBelowPrime` is `okView`, and the drawn elements' words. The second half
is idle under the slot's own views, whose draws are typed; it bites at a running reader's views, and
it is the premise of a law that speaks of all views. -/
def OkViewIs : Prop :=
  ∀ v : Fmt.View, viewWordsBelowPrime v =
    (okView v && v.rounds.all fun r =>
      r.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord)

/-- The number over the file of the tree that a round of the chain (from 0) opens. t₁, t₂: the
numbers of trees that the first and the second chain send. -/
def numAt (t₁ t₂ chain : ℕ) : Fmt.TreeSource → ℕ
  | .own n => (if chain = 0 then 0 else if chain = 1 then t₁ else t₁ + t₂) + n
  | .taken ch sent => (if ch = 0 then 0 else if ch = 1 then t₁ else t₁ + t₂) + sent

/-- What declared rounds read, by their own shapes, as wants. -/
def wantsDecl (num : Fmt.TreeSource → ℕ) : List Fmt.DeclaredRound → List Fmt.Drawn → List Want
  | d :: ds, R :: Rs =>
    (d.stored.flatMap fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x => Want.table s.item x) ++
    (d.opens.flatMap fun o =>
      (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x => Want.tree (num o.2) x) ++
    wantsDecl num ds Rs
  | _, _ => []

/-- The numbers of trees that the description's first and second chain send. -/
def FileDescription.t₁ (F : FileDescription Xi) : ℕ := rootsOf F.roundsDeclaredByBlocks.1
def FileDescription.t₂ (F : FileDescription Xi) : ℕ := rootsOf F.roundsDeclaredByBlocks.2.1

/-- The statement: the slot's wants at D are the declared rounds' wants, chain by chain. -/
def WantsAre (F : FileDescription Xi) (D : WholeD) : Prop :=
  (∀ Rs, wantsOf D.a D.depth D.ds₁ Rs = wantsDecl (numAt F.t₁ F.t₂ 0) F.roundsDeclaredByBlocks.1.dropLast Rs) ∧
  (∀ Rs, wantsOf D.a D.depth D.ds₂ Rs = wantsDecl (numAt F.t₁ F.t₂ 1) F.roundsDeclaredByBlocks.2.1 Rs) ∧
  (∀ Rs, wantsOf D.a D.depth D.ds₃ Rs = wantsDecl (numAt F.t₁ F.t₂ 2) F.roundsDeclaredByBlocks.2.2 Rs)

/-- The statement: at every opening the slot's key is the one by which `Block.step` looks. -/
def KeysAre (F : FileDescription Xi) (D : WholeD) : Prop :=
  (∀ r ∈ F.roundsDeclaredByBlocks.1, ∀ o ∈ r.opens, D.key₁ (numAt F.t₁ F.t₂ 0 o.2) = o.1.tree - 0) ∧
  (∀ r ∈ F.roundsDeclaredByBlocks.2.1, ∀ o ∈ r.opens, D.key₂ (numAt F.t₁ F.t₂ 1 o.2) = o.1.tree - 0) ∧
  (∀ r ∈ F.roundsDeclaredByBlocks.2.2, ∀ o ∈ r.opens, D.key₃ (numAt F.t₁ F.t₂ 2 o.2) = o.1.tree - F.lastChainFirstTreeNumber)

/-- A want as a view's column shows it: key and position. -/
def wantAt (key : ℕ → ℕ) : Want → ℕ × ℕ
  | .table item x => (Fmt.storedKey item, x)
  | .tree j x => (key j, x)

/-- What declared rounds read, as a view's columns show it. -/
def readsAt (firstTree : ℕ) (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) : List (ℕ × ℕ) :=
  ((groupsOf firstTree ds Rs).flatMap id).map fun w => (w.1, w.2.1)

/-- The statement: the slot's reads at D, as its views show them, are the blocks' rounds' reads. -/
def ReadsAre (F : FileDescription Xi) (D : WholeD) : Prop :=
  (∀ Rs, (wantsOf D.a D.depth D.ds₁ Rs).map (wantAt D.key₁) = readsAt 0 F.roundsDeclaredByBlocks.1.dropLast Rs) ∧
  (∀ Rs, (wantsOf D.a D.depth D.ds₂ Rs).map (wantAt D.key₂) = readsAt 0 F.roundsDeclaredByBlocks.2.1 Rs) ∧
  (∀ Rs, (wantsOf D.a D.depth D.ds₃ Rs).map (wantAt D.key₃) = readsAt F.lastChainFirstTreeNumber F.roundsDeclaredByBlocks.2.2 Rs)

/-- The statement: all three, under one premise. -/
def OfData : Prop :=
  ∀ (Xi : Type) (F : FileDescription Xi) (file : String) (D : WholeD), F.data file = .ok D →
    WantsAre F D ∧ KeysAre F D ∧ ReadsAre F D

/-- The statement: what rounds in a row read. -/
def GroupsAppend : Prop :=
  ∀ (firstTree : ℕ) (ds es : List Fmt.DeclaredRound) (Rs Ss : List Fmt.Drawn), ds.length = Rs.length →
    groupsOf firstTree (ds ++ es) (Rs ++ Ss) = groupsOf firstTree ds Rs ++ groupsOf firstTree es Ss

/-- What rounds in a row read is what the first read, then what the others read. -/
theorem groupsOf_append (firstTree : ℕ) :
    ∀ (ds es : List Fmt.DeclaredRound) (Rs Ss : List Fmt.Drawn), ds.length = Rs.length →
      groupsOf firstTree (ds ++ es) (Rs ++ Ss) =
        groupsOf firstTree ds Rs ++ groupsOf firstTree es Ss
  | [], _, [], _, _ => by simp [groupsOf]
  | [], _, _ :: _, _, h => by simp at h
  | _ :: _, _, [], _, h => by simp at h
  | d :: ds, es, R :: Rs, Ss, h => by
    have ih := groupsOf_append firstTree ds es Rs Ss (by simpa using h)
    simp only [List.cons_append, groupsOf, ih, List.append_assoc]

/-- `GroupsAppend` holds. -/
theorem groupsAppend : GroupsAppend := fun ft ds es Rs Ss h => groupsOf_append ft ds es Rs Ss h

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.groupsAppend
#print axioms VerifiableInference.Desc.FileDescription.data
#print axioms VerifiableInference.Desc.FileDescription.out_eq
#print axioms VerifiableInference.Desc.FileDescription.toIOR_local
