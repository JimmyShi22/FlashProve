-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Prover.lean: the compiled prover of a `BatchInteractiveOracleProof` (Iop/Batch.lean), as a token
program (`Step`, Rom/Defer.lean). (Words of this library: lean/GLOSSARY.md.)

One prover serves Test, Link and Batch, as one verifier does (Compile/Batch/Verifier.lean): a
protocol with one chain is the `BatchInteractiveOracleProof` with local rounds only and one slot.

How it is written. All slots go through the rounds together, with a phase (`first`, `loc`, `shr`,
`aft`) as on the verifier's side. Each slot holds the strategy of its transcript (shared and own
component together; for an empty slot the fixed substitutes) and an accumulator: its chain token,
its slot value, the hash blocks of Fiat-Shamir answers that it has received, its trees, the
tokens that are shown if the slot is shown. The shared component is computed once, from the shared
strategy.
* Local round: each slot: a tree over its component, then (F1), (F2) or (F3) (the formats of a
  query's head: `Head`, Compile/Batch/Oracles.lean).
* Joining round (the first shared round after the local ones): each slot: a tree over its component,
  then g, whose answer is the slot value; the request tree (the Merkle tree over the slot values);
  the tree over the shared component; (F4).
* Other shared rounds: the tree over the shared component; (F5).

A shared round at the start or after the later local rounds has no format: nothing is hashed and the
verifier message is the one of the blocks 0 (the verifier rejects).

A round with proof-of-work bits (a record `GrW` in its wire: `grJ`, `gr0`, Iop/BatchWire.lean) is
hashed by a search over nonces (`fbTG`): one Fiat-Shamir query an attempt, attempt 0 at `fb t`,
attempt j + 1 under the ghost name `fbw t j`, until the bits pass or the nonces 0 to `g.more` are
spent. If none passes, the prover goes on with the last attempt: a proof string goes out all the
same, and that the verifier rejects it is by reading: no theorem states it (the docstring of
`fbTG`).

Which token is charged (see Notation): (F1) the salt; (F2), (G), (F5) the previous chaining value;
(F3) the slot value (it also holds the last shared chaining value); (F4) the request root. A
Fiat-Shamir query also holds the root of the tree over its component, which is a token, if the
component has a tree (Iop/BatchWire.lean: `has0`, `hasJ`): a component whose flag is false is not
committed to, and its round has no root, neither in the query nor in the proof string. All trees
over prover messages are token trees (Compile/Batch/TokTree.lean), for Test and Link too; so the
compiled prover makes no ordinary query.

Empty slots. An empty slot is hashed like any other. It plays the fixed substitutes (Strat.dflt),
with no instance in (F1), a salt of its own, its trees, its chain and its slot value; no proof
string is made for it. So the hash work of a batch does not depend on which slots are empty: a batch
costs the prover the same whether it is full or not. What is gained: a simulator, which is not told
which slots beside its own are empty, can do the hash work of all slots.

Notation:
  token (`Tok`), charged, shown, released, `Step.marked`, `Step.reveal`: the rules in the head of
    Rom/Defer.lean; `St lam K L α`: `Step (spec lam K L) (split lam K L) α`
    (Compile/Batch/TokTree.lean)
  `lam`, `K`: natural numbers: K blocks of lam bits give a verifier message (`WireRB`,
    Iop/BatchWire.lean)
  `PhT`: the phase: `.first`, `.loc`, `.shr tk0`, `.aft`: before the first local round; local
    rounds; shared rounds; local rounds afterwards (`PhK`, Compile/Batch/NeedCostP.lean, is the same
    without tokens); tk0: in `chainT` the last shared chaining value; `putB` does not read it
    (`.shr 0`)
  `sMT`, `sFS`: the length of the salt of a leaf, and of the salt of a chain
    (Compile/Batch/Verifier.lean); `depthReq`: a natural number; in `QueryLayout` (Iop/BatchWire.lean):
    depth of a request tree: there are 2^depthReq slots
  `tk`, `us`, `root`, `k`: see `fbT`; `hd`, `hinj`: List Bits → Bits → Head lam X (`Head`:
    Compile/Batch/Oracles.lean), and that `hd vs` is injective for every vs; `pl`: the plain part
    (`PlainPart`, the same file)
  `embS`, `embP`: maps of the protocol's oracle symbols into `Body L`, and of its plain parts into
    those of protocol t; `xin`: Y → Option X
-/
import Compile.Batch.TokTree
import Iop.BatchWireP

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

abbrev Blk (lam K : ℕ) : Type := Fin K → Dig lam

/-- what a slot has accumulated -/
structure SlotAcc (lam K : ℕ) (Y : Type) where
  /-- what it holds; none: the slot is empty -/
  x : Option Y
  /-- the token that the next query of its chain holds (not (F3): that one holds c) -/
  tk : Tok
  /-- its slot value, once the chains have joined -/
  c : Tok
  blocks : List (Blk lam K)
  /-- the tree over its component, round by round; none where the component is not sent or has no
  tree -/
  trees : List (Option TTree)
  /-- its salt, its chaining values, its slot value -/
  toks : List Tok
  /-- the numbers of its final attempts, in the local rounds that have a proof-of-work record
  (Iop/BatchWire.lean: grJ); the newest first -/
  nons : List ℕ
  /-- the chaining values of its attempts before the final ones; they are used for nothing, and are
  shown in the slot's one reveal, which releases these attempts too (in this sense: the
  `Step.reveal` in the body of `finishSlot`; `openT`, `openE` are further ones) -/
  dead : List Tok

/-- what the shared part has accumulated -/
structure Acc0 where
  trees : List (Option TTree)
  toks : List Tok
  req : Option TTree
  /-- the numbers of the final attempts of the shared rounds that have a proof-of-work record
  (Iop/BatchWire.lean: gr0); the newest first -/
  nons : List ℕ
  /-- the chaining values of the shared attempts before the final ones -/
  dead : List Tok

inductive PhT
  | first
  | loc
  | shr (tk0 : Tok)
  | aft

/-- the phase after a local round -/
def PhT.afterLo : PhT → PhT
  | .first => .loc
  | .loc => .loc
  | .shr _ => .aft
  | .aft => .aft

/-- do f in each slot, in order -/
def eachM {σ τ : Type} (f : σ → St lam K L τ) : List σ → St lam K L (List τ)
  | [] => pure []
  | a :: t => do
      let b ← f a
      let r ← eachM f t
      pure (b :: r)

/-- the leaves of the tree over one component of a prover message: posAt says which position is at a
leaf -/
def bodyAt {r : Round} (posAt : ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) : ℕ → Body L :=
  fun l => match posAt l with
    | some p => emb p (r.rd o p)
    | none => none

theorem f1_inj (cms : List (Dig lam)) (x : Option X) : Function.Injective (Head.f1 cms x) :=
  fun _ _ h => by cases h; rfl
theorem f2_inj (xl : Option X) : Function.Injective (Head.f2 xl : Bits → Head lam X) :=
  fun _ _ h => by cases h; rfl
theorem f3_inj (ρ0 : Bits) : Function.Injective (Head.f3 ρ0 : Bits → Head lam X) :=
  fun _ _ h => by cases h; rfl
theorem f4_inj (cms : List (Dig lam)) : Function.Injective (Head.f4 cms : Bits → Head lam X) :=
  fun _ _ h => by cases h; rfl
theorem f5_inj : Function.Injective (Head.f5 : Bits → Head lam X) :=
  fun _ _ h => by cases h; rfl

/-- a Fiat-Shamir query: charged to tk; its other tokens are us and then the root, if the component
has a tree -/
def fbT {β : Type} (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β) : St lam K L β :=
  Step.marked (S := spec lam K L) (OracleName.fb t) tk (us ++ root.toList)
    (fun v vs =>
      (⟨i, hd vs v, root.map fun _ => digD lam (vs.getD us.length []), pl⟩ : FbIn lam L t))
    (fun vs _ _ h => hinj vs (congrArg FbIn.head h)) k

/-! ### A Fiat-Shamir query with proof-of-work bits: the search over nonces -/

/-- fbT under the ghost name fbw t j (Compile/Batch/Oracles.lean): the same input, the same
charge -/
def fbTw {β : Type} (t : Tag) (j : ℕ) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β) : St lam K L β :=
  Step.marked (S := spec lam K L) (OracleName.fbw t j) tk (us ++ root.toList)
    (fun v vs =>
      (⟨i, hd vs v, root.map fun _ => digD lam (vs.getD us.length []), pl⟩ : FbIn lam L t))
    (fun vs _ _ h => hinj vs (congrArg FbIn.head h)) k

/-- The attempts after the first: attempt number j + 1, and at most n more. The plain part of
attempt number m holds the nonce for m. dd: the chaining values of the attempts that have failed so
far, the newest first. k is given the number of the final attempt, the chaining values of those
before it, and the blocks and the chaining value of the final one. -/
def fbW {β C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (i : ℕ) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : ℕ → List Tok → Blk lam K → Tok → St lam K L β) : ℕ → ℕ → List Tok → St lam K L β
  | 0, j, dd =>
    fbTw t j i tk us root hd hinj (emb (g.put (j + 1) α)) fun bl tl => k (j + 1) dd bl tl
  | n + 1, j, dd => fbTw t j i tk us root hd hinj (emb (g.put (j + 1) α)) fun bl tl =>
      if g.ok (chal bl) then k (j + 1) dd bl tl
      else fbW g chal t i tk us root hd hinj emb α k n (j + 1) (tl :: dd)

/-- The search: the nonces 0, 1, .., g.more in this order, one Fiat-Shamir query each (an attempt),
until all proof-of-work bits of the verifier message that the answer gives are 0. The search depends
on these bits only, and it takes no sample.

All attempts are charged to the token tk to which the query without proof-of-work bits is charged,
and they hold the same other tokens; they differ in the nonce alone. A token program may charge a
token once at each oracle: so attempt 0 is written as a query to fb t and attempt j + 1 as one to
the ghost name fbw t j. If no attempt passes, the prover goes on with the last one; the proof string
is not `none` for that (that the verifier of a protocol built by `InteractiveOracleProof.grind`, Iop/Grind.lean,
rejects the proof string that then goes out is by reading: no theorem states it). -/
def fbTG {β C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (i : ℕ) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : ℕ → List Tok → Blk lam K → Tok → St lam K L β) : St lam K L β :=
  match g.more with
  | 0 => fbT t i tk us root hd hinj (emb (g.put 0 α)) fun bl tl => k 0 [] bl tl
  | n + 1 => fbT t i tk us root hd hinj (emb (g.put 0 α)) fun bl tl =>
      if g.ok (chal bl) then k 0 [] bl tl else fbW g chal t i tk us root hd hinj emb α k n 0 [tl]

/-- A Fiat-Shamir query, with a proof-of-work record or without. Without (none): fbT, by definition
(fbG_none). k is also given the number of the final attempt, if there is a record, and the chaining
values of the attempts before it. -/
def fbG {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) : St lam K L β :=
  match gr with
  | none => fbT t i tk us root hd hinj (emb α) (k none [])
  | some g => fbTG g chal t i tk us root hd hinj emb α fun m => k (some m)

theorem fbG_none {β C P : Type} (chal : Blk lam K → C) (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) :
    fbG (none : Option (GrW C P)) chal t i tk us root hd hinj emb α k =
      fbT t i tk us root hd hinj (emb α) (k none []) := rfl

/-- the Fiat-Shamir query of a slot in a local round; x is the whole request of the slot: (F1) holds
L.early x, and (F2) holds x in the round L.late (as on the verifier's side) -/
def fbSlot {β : Type} (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X)
    (ph : PhT) (tk c : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β) : St lam K L β :=
  match ph with
  | .first => fbT t i tk [] root (fun _ => Head.f1 cms (x.map L.early)) (fun _ => f1_inj cms _) pl k
  | .shr tk0 => fbT t i c [tk0] root (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _) pl k
  | _ => fbT t i tk [] root (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) pl k

/-- the same, with a proof-of-work record or without -/
def fbSlotG {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) : St lam K L β :=
  match ph with
  | .first =>
    fbG gr chal t i tk [] root (fun _ => Head.f1 cms (x.map L.early))
      (fun _ => f1_inj cms _) emb α k
  | .shr tk0 =>
    fbG gr chal t i c [tk0] root (fun vs => Head.f3 (vs.headD [])) (fun _ => f3_inj _) emb α k
  | _ => fbG gr chal t i tk [] root (fun _ => Head.f2 (lateInstancePart L i x)) (fun _ => f2_inj _) emb α k

theorem fbSlotG_none {β C P : Type} (chal : Blk lam K → C) (t : Tag) (i : ℕ) (cms : List (Dig lam))
    (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) :
    fbSlotG (none : Option (GrW C P)) chal t i cms x ph tk c root emb α k =
      fbSlot t i cms x ph tk c root (emb α) (k none []) := by
  cases ph <;> rfl

/-- the query to g in the joining round: its answer is the slot value -/
def gT {β : Type} (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Tok → St lam K L β) :
    St lam K L β :=
  Step.marked (S := spec lam K L) (OracleName.g t) tk root.toList
    (fun v vs => (⟨i, v, root.map fun _ => digD lam (vs.headD []), pl⟩ : JoiningRoundQuery lam L t))
    (fun _ _ _ h => congrArg JoiningRoundQuery.ρ h) fun _ c => k c

/-- The tree over a component, if it has one, and then k. A component without a tree costs nothing:
no salt, no query. -/
def withTree {β : Type} (sMT : ℕ) (has : Bool) (depth : ℕ)
    (leaf : ℕ → Body L) (k : Option TTree → St lam K L β) : St lam K L β :=
  match has with
  | true => (commitT sMT depth leaf).bind fun tr => k (some tr)
  | false => k none

/-- The trees over a component with a list of trees, one after the other, and then k on the list of
them. The first argument after sMT: the depths, in the order in which the roots are sent; `leaf n`:
the leaves of tree number n. No tree: no salt, no query. The form of `withTree` for a list of trees
(`withTrees_ite`). -/
def withTrees {β : Type} (sMT : ℕ) :
    List ℕ → (ℕ → ℕ → Body L) → (List TTree → St lam K L β) → St lam K L β
  | [], _, k => k []
  | d :: ds, leaf, k =>
    (commitT sMT d (leaf 0)).bind fun tr =>
      withTrees sMT ds (fun n => leaf (n + 1)) fun trs => k (tr :: trs)

theorem withTrees_one {β : Type} (sMT d : ℕ) (leaf : ℕ → ℕ → Body L)
    (k : List TTree → St lam K L β) :
    withTrees sMT [d] leaf k = withTree sMT true d (leaf 0) fun o => k o.toList := rfl

/-- a component that has its one tree, or none: `withTree` -/
theorem withTrees_ite {β : Type} (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → ℕ → Body L)
    (k : List TTree → St lam K L β) :
    withTrees sMT (if has then [d] else []) leaf k =
      withTree sMT has d (leaf 0) fun o => k o.toList := by
  cases has <;> rfl

/-! ## The rounds -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- a slot with the rest of its strategy -/
abbrev SlotSt (lam K : ℕ) (Y : Type) (s : Shape) : Type := Strat s Unit × SlotAcc lam K Y

/-- the blocks 0 -/
def blk0 (lam K : ℕ) : Blk lam K := fun _ _ => false

/-- a local round, in one slot -/
def slotLo {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) :
    SlotSt lam K Y (r :: s) → St lam K L (SlotSt lam K Y s)
  | ((m, k), acc) =>
      withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
      fbSlotG w.grJ w.chal t i cms (acc.x.bind xin) ph acc.tk acc.c (tr.map TTree.root) plJ
          (a.plain m.2).2 fun nc dd bl tl =>
      Step.pure (k (w.chal bl),
        { acc with
          tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [tr],
          toks := acc.toks ++ [tl], nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead })

/-- the joining round, in one slot: the tree over its component and its slot value -/
def slotJoin {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    SlotSt lam K Y (r :: s) → St lam K L (SlotSt lam K Y (r :: s))
  | ((m, k), acc) =>
      withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
      gT t i acc.tk (tr.map TTree.root) (plJ (a.plain m.2).2) fun c =>
      Step.pure ((m, k), { acc with c := c, trees := acc.trees ++ [tr], toks := acc.toks ++ [c] })

/-- the joining round in all slots; the slot values of all slots -/
def joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    List (SlotSt lam K Y (r :: s)) → St lam K L (List (SlotSt lam K Y (r :: s)) × List Tok)
  | [] => pure ([], [])
  | z :: zs => (slotJoin sMT t a w emb plJ i z).bind fun z' =>
      (joinM a w emb plJ i zs).bind fun o => Step.pure (z' :: o.1, z'.2.c :: o.2)

/-- a slot receives a shared verifier message; `noted` says whether its component of this round has
been recorded already -/
def hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a)
    (bl : Blk lam K) (noted : Bool) :
    SlotSt lam K Y (r :: s) → SlotSt lam K Y s
  | ((_, k), acc) =>
    (k (w.chal bl),
      { acc with
        blocks := acc.blocks ++ [bl], trees := if noted then acc.trees else acc.trees ++ [none] })

/-- the tree over the shared component, if it has one, and then k -/
def tree0 {β : Type} {r : Round} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0) (k : Option TTree → St lam K L β) :
    St lam K L β :=
  withTree sMT w.has0 w.depth0 (bodyAt w.posAt0 emb (a.join m0 (a.split (r.dOrc, r.dPlain)).2).1) k

/-- All chains of a batch. -/
def chainT (depthReq : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → PhT → SStrat s A → List (SlotSt lam K Y s) →
    Acc0 → St lam K L (List (SlotAcc lam K Y) × Acc0)
  | [], _, _, _, _, _, _, _, zs, a0 => pure (zs.map Prod.snd, a0)
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0 =>
      match a.kind, ph with
      | .lo, ph =>
          (eachM (slotLo sMT t cms xin a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i ph)
              zs).bind fun zs' =>
          chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph.afterLo
            (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs' { a0 with trees := a0.trees ++ [none] }
      | .sh, .loc =>
          (joinM sMT t a w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqT depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr tl)
            (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
            { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      | .sh, .shr tk0 =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr tl)
            (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      | .sh, ph =>
          chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph
            (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
            { a0 with trees := a0.trees ++ [none] }

end Rounds

/-! ## From the chains to the proof strings -/

/-- the verifier messages of a slot's transcript, from the blocks that the slot has received -/
def rhoOf : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → List (Blk lam K) → Rho s
  | [], _, _, _ => ()
  | _ :: s, (_, A), (w, W), bls => (w.chal (bls.headD (blk0 lam K)), rhoOf s A W bls.tail)

/-- The plain parts with the nonces of the final attempts written in. nJ: the numbers of the final
attempts of the slot, n0: those of the shared rounds, both in the order of the rounds. The recursion
is that of chainT: a local round with a proof-of-work record takes the next number of nJ; a shared
round in format (F4) or (F5) with a record takes the next number of n0. A round without a record
keeps its plain part. -/
def putB :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PhT → List ℕ → List ℕ → Plains s → Plains s
  | [], _, _, _, _, _, _ => ()
  | _ :: s, (a, A), (w, W), ph, nJ, n0, (pl, pls) =>
      match a.kind, ph with
      | .lo, ph =>
          match w.grJ with
          | none => (pl, putB s A W ph.afterLo nJ n0 pls)
          | some g =>
            (a.plain.symm ((a.plain pl).1, g.put (nJ.headD 0) (a.plain pl).2),
              putB s A W ph.afterLo nJ.tail n0 pls)
      | .sh, .first => (pl, putB s A W .first nJ n0 pls)
      | .sh, .aft => (pl, putB s A W .aft nJ n0 pls)
      | .sh, _ =>
          match w.gr0 with
          | none => (pl, putB s A W (.shr 0) nJ n0 pls)
          | some g =>
            (a.plain.symm (g.put (n0.headD 0) (a.plain pl).1, (a.plain pl).2),
              putB s A W (.shr 0) nJ n0.tail pls)

/-- the root tokens of a slot's proof string, in the order in which the verifier needs them: in each
round the slot's, then the shared one -/
def rootToks : List (Option TTree) → List (Option TTree) → List Tok
  | tj :: tjs, t0 :: t0s =>
    (tj.map TTree.root).toList ++ (t0.map TTree.root).toList ++ rootToks tjs t0s
  | _, _ => []

/-- open the positions read in one component of one round, leaf by leaf; f holds the openings made
so far -/
def opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    List ℕ → St lam K L ((p : r.Pos) → Option (Opening lam (r.Sym p)))
  | [] => pure f
  | j :: js => do
      let f' ← opensComp dec posAt o tr isRead f js
      match posAt j with
      | some p =>
          if isRead p then do
            let op ← openT tr j (r.rd o p)
            pure (@Function.update _ _ dec f' p (some op))
          else pure f'
      | none => pure f'

/-- the same for a component that may not have been sent, or has no tree -/
def opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    St lam K L ((p : r.Pos) → Option (Opening lam (r.Sym p))) :=
  match tr with
  | none => pure f
  | some tr => opensComp dec posAt o tr isRead f (List.range (2 ^ depth))

/-- Open the positions read in the trees of one component, from tree number k on, in each tree that
has a depth and a tree; f holds the openings made so far. `posAt k j`: the position at leaf j of
tree number k. As in `opensComp`, what comes later in the list is opened first; if no position
stands in two trees, what is returned does not depend on that order. Where the depths or the trees
end, nothing more is opened. The form of `opensOpt` for a list of trees (`opensTrees_one`). -/
def opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ℕ → List ℕ → List TTree → ((p : r.Pos) → Option (Opening lam (r.Sym p))) →
    St lam K L ((p : r.Pos) → Option (Opening lam (r.Sym p)))
  | k, d :: ds, tr :: trs, f =>
      (opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
        opensComp dec (posAt k) o tr isRead f' (List.range (2 ^ d))
  | _, _, _, f => pure f

theorem opensTrees_one {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) (k d : ℕ) (tr : Option TTree)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    opensTrees (K := K) (L := L) dec posAt o isRead k [d] tr.toList f =
      opensOpt dec (posAt k) d o tr isRead f := by
  cases tr <;> rfl

theorem opensTrees_nil {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) (k : ℕ) (trs : List TTree)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    opensTrees (K := K) (L := L) dec posAt o isRead k [] trs f = pure f := by
  cases trs <;> rfl

/-- A component that has its one tree, or none: `opensOpt`, if there is no tree where the component
has none. (`opensOpt` takes no flag: it opens whatever tree it is handed.) -/
theorem opensTrees_ite {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) (k : ℕ) (has : Bool) (d : ℕ) (tr : Option TTree)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) (h : has = false → tr = none) :
    opensTrees (K := K) (L := L) dec posAt o isRead k (if has then [d] else []) tr.toList f =
      opensOpt dec (posAt k) d o tr isRead f := by
  cases has with
  | true => exact opensTrees_one dec posAt o isRead k d tr f
  | false => rw [h rfl]; rfl

def opensB :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Tr s → List (Option TTree) →
    List (Option TTree) → (OPos s → Bool) →
    St lam K L ((p : OPos s) → Option (Opening lam (OSym s p)))
  | [], _, _, _, _, _, _ => pure fun p => nomatch p
  | _ :: s, (_, A), (w, W), (m, _, τ), tjs, t0s, isRead => do
      let f0 ← opensOpt w.pt.decPos w.posAt0 w.depth0 m.1 (t0s.headD none)
        (fun p => isRead (.inl p)) (fun _ => none)
      let f ← opensOpt w.pt.decPos w.posAtJ w.depthJ m.1 (tjs.headD none)
        (fun p => isRead (.inl p)) f0
      let g ← opensB s A W τ tjs.tail t0s.tail (fun p => isRead (.inr p))
      pure fun p => match p with
        | .inl q => f q
        | .inr q => g q

/-- open positions of the external strings -/
def opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    List E.Pos → St lam K L (E.Pos → Option (Opening lam E.Sym))
  | [] => pure fun _ => none
  | p :: ps => do
      let f ← opensExtB we y trees isRead ps
      if isRead p then do
        let op ← openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)
        pure (@Function.update _ _ we.dec f p (some op))
      else pure f

/-- a sample from an enumerated type (uniform if its `Enum` has `Enum.OK`, Iop/Wire.lean) -/
def drawT {β : Type} (e : Enum β) : St lam K L β := Step.sample e.n fun r => Step.pure (e.e r)

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- The proof string of slot j, or none, if its verifier randomness is in the withheld set; then
nothing is shown.

One reveal shows the salt, the roots, the digests beside and on the request path, all chaining
values and the slot value of the slot, and the shared chaining values, those of the attempts before
the final ones included; it releases the Fiat-Shamir queries of the slot and of the shared part (in
a round with proof-of-work bits: all attempts), g, and the request path. The nonces of the final
attempts are written into the plain parts (putB). Then the positions read are opened.

A failed search gives no `none`: if in some round no attempt passed, the proof string is made all
the same, with the last attempt; the verifier of a protocol built by `InteractiveOracleProof.grind` rejects it (by
reading: see fbTG). -/
def finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    St lam K L (Option (OneProtocolProof lam Q)) :=
  let ρ := rhoOf Q.loc.shape Q.ann wq.sh acc.blocks
  let τ := ((H.one.strat w x (c0, cj)).run ρ).1
  let roots := rootToks acc.trees a0.trees
  let path := (a0.req.map fun rq => pathOf rq.levels j).getD []
  let anc := (a0.req.map fun rq => ancOf rq.levels j).getD []
  let pls := putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse τ.plains
  haveI := wp.decW w x ρ
  if ρ ∈ H.one.withheld w x then pure none
  else
    Step.reveal (acc.toks.headD 0 ::
        (roots ++ path ++ (a0.req.map TTree.root).toList ++ anc ++ acc.toks ++
          a0.toks ++ (acc.dead ++ a0.dead))) fun vs =>
    haveI := wq.decO
    haveI := wq.ext.dec
    (opensB Q.loc.shape Q.ann wq.sh τ acc.trees a0.trees
        (fun p => decide (p ∈ Q.loc.reads x ρ pls))).bind fun f =>
    (opensExtB wq.ext (H.ext w) trees
        (fun p => decide (p ∈ Q.loc.extReads x ρ)) wq.ext.all).bind fun g =>
    pure (some ⟨vs.headD [], ((vs.drop 1).take roots.length).map (digD lam), pls, f, g,
      digD lam (vs.getD (1 + roots.length + path.length) []), j,
      ((vs.drop (1 + roots.length)).take path.length).map (digD lam)⟩)

/-- the proof strings of all slots from number j on; fl says for which slots one is made at all -/
def finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ℕ → List (SlotAcc lam K (Y × H.Coin)) → St lam K L (List (Option (OneProtocolProof lam Q)))
  | _, [] => pure []
  | j, acc :: zs =>
      (match acc.x with
        | some (x, cj) => if fl j then finishSlot Q H wq wp trees w c0 a0 j x cj acc else pure none
        | none => pure none).bind fun π =>
      (finishAll fl c0 a0 (j + 1) zs).bind fun r => pure (π :: r)

/-- a slot at the start: its coins (sampled for an empty slot too, and not used) and the salt of its
chain -/
def initSlot (c0 : H.Coin0) (x : Option Y) : St lam K L (SlotSt lam K (Y × H.Coin) Q.loc.shape) :=
  (drawT wp.coin).bind fun cj =>
  Step.fresh sFS fun salt =>
  Step.pure (match x with
      | some x => H.one.strat w x (c0, cj)
      | none => Strat.dflt Q.loc.shape (),
    ⟨x.map fun x => (x, cj), salt, 0, [], [], [salt], [], []⟩)

/-- The compiled prover: one execution of the `BatchInteractiveOracleProof` on the slots xs (none: an empty slot).
For each slot its proof string, or none (the slot is empty, or withheld, or fl says that none is
made). The scheme has fl = true everywhere; the analysis also uses the program that makes proof
strings, and so reveals, only for some slots. -/
def proveB (fl : ℕ → Bool) (xs : List (Option Y)) : St lam K L (List (Option (OneProtocolProof lam Q))) :=
  (drawT wp.coin0).bind fun c0 =>
  (eachM (initSlot sFS Q H wp w c0) xs).bind fun zs =>
  (chainT sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape Q.ann
      wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩).bind fun out =>
  finishAll Q H wq wp trees w fl c0 out.2 0 out.1

end Prove

end Compile.Batch
