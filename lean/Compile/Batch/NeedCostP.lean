-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedCostP.lean: what the honest prover and the honest committer of the compiled
  scheme cost over one hash function, if only the marked blocks are queried: one upper bound for
  each term below the chains (words of this library: lean/GLOSSARY.md).
  Sums of the terms at the weight "marked blocks" (for a slot, the shared part, one execution, the
  prover, the committer) and theorems at that weight on the chains, on one execution and on the
  whole prover and committer are not in this library.

  The weight of a typed query is the number of its marked blocks (`needOf nb m`,
  Compile/Batch/NeedTable.lean): at most nb t i + 1 at a Fiat-Shamir query of round i of protocol t,
  for `Std m` at most one everywhere else. nb is a parameter. The bounds are stated with `SWA`
  (Compile/CostAt.lean); the trees are those of Compile/Batch/NeedCostTree.lean.
  Bounds on the whole prover `PU` (no query for an empty slot) and on the whole committer are in
  Compile/Batch/OneCallCostS.lean (`costV_PU`, `costV_C`), under `W.OKG` and `NbPos`, for the
  weights that meet `TryW` (Compile/Batch/OneCallCostW.lean), which may depend on the answer; their
  proof takes the pieces without a search over nonces from here.
  Rounds with proof-of-work bits. Where the wire record of a round holds a proof-of-work record, its
  Fiat-Shamir query is a search over nonces, and the lemmas on the search (`swa_fbG`, `swa_fbSlotG`)
  count all more + 1 attempts, each with nb t i + 1 marked blocks: triesOf gr · (nb t i + 1). This
  is the worst case over the oracle, under the static reading rule (every attempt reads all marked
  blocks of its answer, not the block with the proof-of-work bits first): it is no estimate of the
  prover's usual work, which is about 2^b attempts a search (b: the number of proof-of-work bits,
  `GrW.b`). In a round without a record `triesOf` is 1.
  For `Std m` a bound on an oracle algorithm carries over to `realQ` of it, the same algorithm with
  `fb t` written back for the ghost names (`costBoundAt_realQ`: a ghost name has as many marked
  blocks as `fb t`: `num_fbw_eq`).
    Part 1  The bounds: `costJ`, `cost0`. `PhK`: where the chains are (before the first local
            round; local rounds; shared rounds; local rounds afterwards), without tokens.
    Part 2  queries to the Fiat-Shamir oracles and to g; the search (by `fbG_cost` of
            Compile/Batch/ProverG.lean); doing something in each slot
    Part 3  the rounds, also for the prover `PU`, for `Std m`
    Part 5  the proof strings cost nothing; the start of a slot
    Part 6  the slots of a batch; for `Std m`: `num_fbw_eq`, `costBoundAt_realQ`, the tree of a
            node
    Part 7  explicit forms, with nb apart from the trees: `trJ`, `tr0`: the trees over a slot's
            components, and over the shared components, of all rounds
  Not in this library (the file has no Part 4):
    Part 1  The sums at this weight for a slot and for the shared part are not in this library.
            Their counterparts `cSlotW`, `cSharedW` of Compile/Batch/OneCallCostR.lean have the same
            terms but for what a Fiat-Shamir query costs. One slot with a request, from round i on:
            in a local round its tree and its Fiat-Shamir query, with all attempts; in the joining
            round its tree, its query to g, its leaf of the request tree; in the other shared rounds
            nothing. The shared part, for Ns slots: in the joining round the Ns − 1 inner nodes of
            the request tree; in each shared round the shared tree and the shared Fiat-Shamir query,
            with all attempts; in local rounds nothing. (In `cSharedW` that is the joining round and
            the shared rounds after it up to the next local round: a shared round before the first
            local round, or after a later local round, is counted as nothing.)
            The sums at this weight for one execution with one slot, for the prover on a batch with
            n requests and for the committer are not in this library; their counterparts
            `cProve1W`, `cPUW`, `cCBW` are in Compile/Batch/OneCallCostR.lean.
    Part 4  all chains of a batch, at the weight "marked blocks"
    Part 5  one execution, at that weight
    Part 6  the theorems at that weight on the prover and on the committer
    Part 7  sums of the attempts of all rounds and explicit bounds for them (but for the sums of
            attempts that are in this library: `cFb`, Compile/Batch/Counts.lean; `sMoreJ`,
            `sMore0`, Compile/Batch/CountsGr.lean; explicit bounds for the sums `cSlotW`,
            `cSharedW`: Compile/Batch/OneCallCostClosed.lean)
  Notation:
    `SWo c n P`: `SWA` (Compile/CostAt.lean) at the weight `Rom.Need.num (needOf nb m)`: on every
      path the weights of the queries of the program c add up to at most n, and its result has the
      property P (the last argument); `T1`: the property fun _ => True
    token (`Tok`), marked query, charged: the head of Rom/Defer.lean; ghost name `fbw t j`: `OracleName`,
      Compile/Batch/Oracles.lean
    at a Fiat-Shamir query (`fbT`, `fbW`, `fbG`, Compile/Batch/Prover.lean): `tk`: the token to
      which it is charged; `us`, `root`: its other tokens are us and then the root, if the component
      has a tree; `hd`, `hinj`: List Bits → Bits → Head lam X (`Head`: Compile/Batch/Oracles.lean),
      and that `hd vs` is injective for every vs; `pl`: the plain part; `k`: what follows; it is
      given `bl`, `tl`: the blocks and the chaining value of the final attempt, `nc`: its number, if
      there is a record, `dd`: the chaining values of the attempts before it
    `gr`: Option (GrW C P) (Iop/BatchWire.lean); its field `more`: at most more + 1 tries;
      `triesOf gr`: at most this many attempts for one Fiat-Shamir query (Compile/Batch/Counts.lean)
    `hear`, `noted`: a slot receives a shared verifier message; `noted` says whether its component
      of this round has been recorded already (Compile/Batch/Prover.lean)
    `sMT`, `sFS`: natural numbers: sMT is the length of the salt of a leaf, sFS that of the salt of
      a chain (Compile/Batch/Verifier.lean)
  Limits: nothing on what the programs return, but for what the last argument of `SWA` says (among
  it: lengths of lists, which slots hold a request). The bounds hold on every path, whatever index,
  key and requests: they are upper bounds on numbers of marked blocks, that is, of queries to the
  one hash function if only these are queried, each counted as one however long its string; nothing
  on time, memory or work in the fields. A slot whose request is withheld (the prover outputs no
  proof for it) does all its work and is counted. `trJ` and `tr0` of Part 7 count for each slot and
  for the shared part a tree in every round; the explicit bounds that rest on them (`cSlotW_leG`,
  `cSharedW_leG` of Compile/Batch/OneCallCostClosed.lean) count also a Fiat-Shamir query in every
  round.
-/
import Compile.Batch.NeedCostTree
import Compile.Batch.NeedBlocksU
import Compile.Batch.ProverG

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.CostP (SWA)
open Compile.Need (sumNb)

/-! ## Part 1. The bounds -/

/-- where the chains are, without tokens -/
inductive PhK
  | first
  | loc
  | shr
  | aft

def PhK.afterLo : PhK → PhK
  | .first => .loc
  | .loc => .loc
  | .shr => .aft
  | .aft => .aft

def phK : PhT → PhK
  | .first => .first
  | .loc => .loc
  | .shr _ => .shr
  | .aft => .aft

theorem phK_afterLo (ph : PhT) : phK ph.afterLo = (phK ph).afterLo := by cases ph <;> rfl

section Bounds
variable {lam K : ℕ}

/-- what the tree over a slot's component of the round costs; it is counted whether or not the
component has a tree (Iop/BatchWire.lean: hasJ): as a tree of the depth that the wire record gives
(one leaf at depth 0) -/
def costJ {r : Round} {a : RAnn r} (w : WireRB lam K r a) : ℕ := tr w.depthJ
/-- what the tree over the shared component of the round costs; it is counted whether or not the
component has a tree (has0): as a tree of the depth that the wire record gives (one leaf at depth
0) -/
def cost0 {r : Round} {a : RAnn r} (w : WireRB lam K r a) : ℕ := tr w.depth0

end Bounds

/-! ## Part 2. Queries; doing something in each slot -/

section Evals
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam}

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam K L) (sp := split lam K L) (Rom.Need.num (needOf nb m))

theorem swa_fbT {β : Type} (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} {n : ℕ}
    {P : β → Prop} (hk : ∀ bl tl, SWo (k bl tl) n P) :
    SWo (fbT t i tk us root hd hinj pl k) ((nb t i + 1) + n) P :=
  ⟨nb t i + 1, n, fun _ _ => num_fb_le nb m t _, rfl, hk⟩

theorem swa_fbSlot {β : Type} (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT)
    (tk c : Tok) (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} {n : ℕ} {P : β → Prop} (hk : ∀ bl tl, SWo (k bl tl) n P) :
    SWo (fbSlot t i cms x ph tk c root pl k) ((nb t i + 1) + n) P := by
  cases ph with
  | first => exact swa_fbT nb t i _ _ _ _ (fun _ => f1_inj cms _) pl hk
  | shr tk0 => exact swa_fbT nb t i _ _ _ _ (fun _ => f3_inj _) pl hk
  | loc => exact swa_fbT nb t i _ _ _ _ (fun _ => f2_inj _) pl hk
  | aft => exact swa_fbT nb t i _ _ _ _ (fun _ => f2_inj _) pl hk

/-- a query of round i under a ghost name `fbw t j` has at most nb t i + 1 marked blocks, as one to
`fb t` (`num_fb_le`) -/
theorem num_fbw_le (t : Tag) (j : ℕ) (q : FbIn lam L t) :
    (needOf nb m).num (.fbw t j) q ≤ nb t q.round + 1 :=
  Compile.Need.cnt_le_of _ K _

theorem swa_fbTw {β : Type} (t : Tag) (j i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} {n : ℕ}
    {P : β → Prop} (hk : ∀ bl tl, SWo (k bl tl) n P) :
    SWo (fbTw t j i tk us root hd hinj pl k) ((nb t i + 1) + n) P :=
  ⟨nb t i + 1, n, fun _ _ => num_fbw_le nb t j _, rfl, hk⟩

/-- A Fiat-Shamir query with proof-of-work bits or without: at the worst every attempt is made, and
each attempt costs nb t i + 1; then the bound n on what follows (`hk`). -/
theorem swa_fbG {β C P' : Type} (gr : Option (GrW C P')) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (tk : Tok) (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P' → PlainPart (shapeOf L t) (annOf L t)) (α : P')
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {n : ℕ} {P : β → Prop}
    (hk : ∀ nc dd bl tl, SWo (k nc dd bl tl) n P) :
    SWo (fbG gr chal t i tk us root hd hinj emb α k) (triesOf gr * (nb t i + 1) + n) P :=
  fbG_cost (Φ := fun n c => SWo c n P) gr (fun _ _ _ hab h => h.mono (fun _ h => h) hab)
    (fun _ pl _ h => swa_fbT nb t i tk us root hd hinj pl h)
    (fun _ j pl _ h => swa_fbTw nb t j i tk us root hd hinj pl h) hk

theorem swa_fbSlotG {β C P' : Type} (gr : Option (GrW C P')) (chal : Blk lam K → C) (t : Tag)
    (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P' → PlainPart (shapeOf L t) (annOf L t)) (α : P')
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {n : ℕ} {P : β → Prop}
    (hk : ∀ nc dd bl tl, SWo (k nc dd bl tl) n P) :
    SWo (fbSlotG gr chal t i cms x ph tk c root emb α k) (triesOf gr * (nb t i + 1) + n) P := by
  cases ph <;> exact swa_fbG nb gr chal t i _ _ root _ _ emb α hk

theorem swa_gT (hm : Std m) {β : Type} (t : Tag) (i : ℕ) (tk : Tok)
    (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Tok → St lam K L β}
    {n : ℕ} {P : β → Prop} (hk : ∀ c, SWo (k c) n P) :
    SWo (gT t i tk root pl k) (1 + n) P :=
  ⟨1, n, fun _ _ => num_le_blk nb hm (OracleName.g t) _, rfl, fun _ c => hk c⟩

/-- something that costs c where a flag is set and nothing elsewhere, and keeps the flag, done in
each slot -/
theorem swa_eachM {σ τ : Type} {f : σ → St lam K L τ} (g : σ → Bool) (g' : τ → Bool) (c : ℕ)
    (hf : ∀ a, SWo (f a) (if g a then c else 0) fun b => g' b = g a) :
    ∀ l : List σ, SWo (eachM f l) ((l.map g).count true * c) fun l' => l'.map g' = l.map g
  | [] => rfl
  | a :: t =>
      SWA.bind' (hf a) (m' := (t.map g).count true * c) (fun b hb => SWA.bind' (swa_eachM g g' c hf t) (m' := 0) (fun r hr => by
        show (b :: r).map g' = (a :: t).map g
        rw [List.map_cons, List.map_cons, hb, hr]) (Nat.le_refl _)) (by
        rw [List.map_cons, List.count_cons]
        cases g a
        · simp
        · simp [Nat.add_mul, Nat.add_comm])

/-- something that costs c, done in each slot -/
theorem swa_eachM_all {σ τ : Type} {f : σ → St lam K L τ} (c : ℕ) (hf : ∀ a, SWo (f a) c T1) :
    ∀ l : List σ, SWo (eachM f l) (l.length * c) fun l' => l'.length = l.length
  | [] => rfl
  | a :: t =>
      SWA.bind' (hf a) (m' := t.length * c) (fun b _ => SWA.bind' (swa_eachM_all c hf t) (m' := 0) (fun r hr => by
        show (b :: r).length = (a :: t).length
        rw [List.length_cons, List.length_cons, hr]) (Nat.le_refl _)) (by rw [List.length_cons, Nat.succ_mul]; omega)

end Evals

/-! ## Part 3. The rounds -/

/-- does the slot hold a request -/
def full {lam K : ℕ} {Y : Type} {s : Shape} (z : SlotSt lam K Y s) : Bool := z.2.x.isSome

section Rounds
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam} (hm : Std m) {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam K L) (sp := split lam K L) (Rom.Need.num (needOf nb m))

theorem full_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (z : SlotSt lam K Y (r :: s)) :
    full (hear w bl noted z) = full z := by
  obtain ⟨⟨_, _⟩, _⟩ := z
  rfl

theorem map_full_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (zs : List (SlotSt lam K Y (r :: s))) :
    (zs.map (hear w bl noted)).map full = zs.map full := by
  rw [List.map_map]
  exact List.map_congr_left fun z _ => full_hear w bl noted z

include hm

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- the tree over a component, if it has one, and then what follows. The bound counts the tree in
both cases: a component without a tree costs nothing -/
theorem swa_withTree {β : Type} (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} {n : ℕ} {P : β → Prop} (hk : ∀ tr, SWo (k tr) n P) :
    SWo (withTree sMT has depth leaf k) (tr depth + n) P := by
  cases has with
  | true =>
    exact SWA.bind' (swa_commitT nb hm sMT depth leaf) (fun tr _ => hk (some tr)) (Nat.le_refl _)
  | false => exact (hk none).mono (fun _ h => h) (Nat.le_add_left _ _)

/-- the trees over a component, one after the other, and then what follows. The bound counts `tr d`
for each depth d of the list: so nothing for a component without a tree -/
theorem swa_withTrees {β : Type} {n : ℕ} {P : β → Prop} :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β},
      (∀ trs, SWo (k trs) n P) → SWo (withTrees sMT ds leaf k) ((ds.map tr).sum + n) P
  | [], _, _, hk => (hk []).mono (fun _ h => h) (Nat.le_add_left _ _)
  | d :: ds, leaf, _, hk =>
    SWA.bind' (swa_commitT nb hm sMT d (leaf 0)) (m' := (ds.map tr).sum + n)
      (fun x _ => swa_withTrees ds (fun j => leaf (j + 1)) fun trs => hk (x :: trs))
      (le_of_eq (by rw [List.map_cons, List.sum_cons, Nat.add_assoc]))

/-- the tree over the shared component, and then what follows -/
theorem swa_tree0 {β : Type} (m0 : a.M0) {k : Option TTree → St lam K L β} {n : ℕ}
    {P : β → Prop} (hk : ∀ tr, SWo (k tr) n P) :
    SWo (tree0 sMT a w emb m0 k) (cost0 w + n) P :=
  swa_withTree nb hm sMT _ _ _ hk

/-- a local round in one slot: its tree, its Fiat-Shamir query -/
theorem swa_slotLo (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    SWo (slotLo sMT t cms xin a w emb plJ i ph z)
      (costJ w + triesOf w.grJ * (nb t i + 1)) fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact swa_withTree nb hm sMT _ _ _ (n := triesOf w.grJ * (nb t i + 1) + 0) fun _ =>
    swa_fbSlotG nb _ _ t i cms _ ph _ _ _ _ _ fun _ _ _ _ => rfl

/-- the joining round in one slot: its tree, its query to g -/
theorem swa_slotJoin (z : SlotSt lam K Y (r :: s)) :
    SWo (slotJoin sMT t a w emb plJ i z) (costJ w + 1) fun z' => full z' = full z := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact swa_withTree nb hm sMT _ _ _ (n := 1 + 0) fun _ => swa_gT nb hm t i _ _ _ fun _ => rfl

/-- For `Std m`: an empty slot does nothing in a local round -/
theorem swa_slotLoU (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    SWo (slotLoU sMT t cms xin a w emb plJ i ph z)
      (if full z then costJ w + triesOf w.grJ * (nb t i + 1) else 0)
      fun z' => full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [slotLoU_none sMT t cms xin a w emb plJ i ph hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [slotLoU_some sMT t cms xin a w emb plJ i ph hx, hf, if_pos rfl]
    exact (swa_slotLo nb hm sMT t cms xin a w emb plJ i ph z).mono
      (fun _ h => h.trans hf) (Nat.le_refl _)

theorem swa_slotJoinU (z : SlotSt lam K Y (r :: s)) :
    SWo (slotJoinU sMT t a w emb plJ i z) (if full z then costJ w + 1 else 0) fun z' =>
      full z' = full z := by
  cases hx : z.2.x with
  | none =>
    rw [slotJoinU_none sMT t a w emb plJ i hx]
    exact rfl
  | some y =>
    have hf : full z = true := by unfold full; rw [hx]; rfl
    rw [slotJoinU_some sMT t a w emb plJ i hx, hf, if_pos rfl]
    exact (swa_slotJoin nb hm sMT t a w emb plJ i z).mono (fun _ h => h.trans hf) (Nat.le_refl _)

/-- the joining round in all slots -/
theorem swa_joinM :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      SWo (joinM sMT t a w emb plJ i zs) (zs.length * (costJ w + 1)) fun o =>
        o.1.length = zs.length ∧ o.2.length = zs.length
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWA.bind' (swa_slotJoin nb hm sMT t a w emb plJ i z) (m' := zs.length * (costJ w + 1)) (fun z' _ => SWA.bind' (swa_joinM zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).length = (z :: zs).length ∧ (z'.2.c :: o.2).length = (z :: zs).length
        rw [List.length_cons, List.length_cons, List.length_cons, ho.1, ho.2]
        exact ⟨rfl, rfl⟩) (Nat.le_refl _)) (by rw [List.length_cons, Nat.succ_mul]; omega)

/-- For `Std m`: the joining round in all slots, with no query for an empty slot: there is a slot
value exactly for the slots with a request -/
theorem swa_joinMU :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      SWo (joinMU sMT t a w emb plJ i zs) ((zs.map full).count true * (costJ w + 1))
        fun o => o.1.map full = zs.map full ∧ o.2.map Option.isSome = zs.map full
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWA.bind' (swa_slotJoinU nb hm sMT t a w emb plJ i z) (m' := (zs.map full).count true * (costJ w + 1)) (fun z' hz' => SWA.bind' (swa_joinMU zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).map full = (z :: zs).map full ∧
          ((z'.2.x.map fun _ => z'.2.c) :: o.2).map Option.isSome = (z :: zs).map full
        rw [List.map_cons, List.map_cons, List.map_cons, ho.1, ho.2, hz', Option.isSome_map]
        exact ⟨rfl, by rw [← hz']; rfl⟩) (Nat.le_refl _)) (by
        rw [List.map_cons, List.count_cons]
        cases full z
        · simp
        · simp [Nat.add_mul, Nat.add_comm])

end One

variable (depthReq : ℕ)


end Rounds

/-! ## Part 5. The proof strings cost nothing; the start of a slot -/

section Prove
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam K L) lam}

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam K L) (sp := split lam K L) (Rom.Need.num (needOf nb m))

theorem swa_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, SWo (opensComp (K := K) (L := L) dec posAt o tr isRead f js) 0 T1
  | [] => trivial
  | j :: js => SWA.bind' (swa_opensComp dec posAt o tr isRead f js) (m' := 0) (fun f' _ => by
      show SWo (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f') 0 T1
      cases posAt j with
      | none => trivial
      | some p =>
        show SWo (if isRead p then _ else _) 0 T1
        cases isRead p
        · trivial
        · exact SWA.bind' (swa_openT nb tr j _) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _)

theorem swa_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    SWo (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) 0 T1 := by
  cases tr with
  | none => trivial
  | some tr => exact swa_opensComp nb dec posAt o tr isRead f _

theorem swa_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      SWo (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) 0 T1
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, x :: trs, f =>
    SWA.bind' (swa_opensTrees dec posAt o isRead (k + 1) ds trs f) (m' := 0)
      (fun f' _ => swa_opensComp nb dec (posAt k) o x isRead f' _) (Nat.le_refl _)

theorem swa_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      SWo (opensB (L := L) s A W τ tjs t0s isRead) 0 T1
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, _, τ), tjs, t0s, _ =>
      SWA.bind' (swa_opensOpt nb _ _ _ _ _ _ _) (m' := 0)
        (fun _ _ =>
          SWA.bind' (swa_opensOpt nb _ _ _ _ _ _ _) (m' := 0)
            (fun _ _ =>
              SWA.bind' (swa_opensB s A W τ tjs.tail t0s.tail _) (m' := 0)
                (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _)) (Nat.le_refl _)

theorem swa_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos, SWo (opensExtB (K := K) (L := L) we y trees isRead ps) 0 T1
  | [] => trivial
  | p :: ps => SWA.bind' (swa_opensExtB we y trees isRead ps) (m' := 0) (fun f _ => by
      show SWo (if isRead p then
          (openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)).bind
            fun op => Step.pure (@Function.update _ _ we.dec f p (some op)) else Step.pure f)
        0 T1
      cases isRead p
      · trivial
      · exact SWA.bind' (swa_openE nb _ _ _) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _)

variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

theorem swa_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    SWo (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) 0 T1 := by
  unfold finishSlot
  dsimp only
  split_ifs
  · trivial
  · exact fun vs =>
      SWA.bind' (swa_opensB nb _ _ _ _ _ _ _) (m' := 0)
        (fun f _ =>
          SWA.bind' (swa_opensExtB nb _ _ _ _ _) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
        (Nat.le_refl _)

theorem swa_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      SWo (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs) 0 T1
  | _, [] => trivial
  | j, acc :: zs => SWA.bind' (P := T1) (m := 0) (by
      cases acc.x with
      | none => trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        show SWo (if fl j then _ else _) 0 T1
        cases fl j
        · trivial
        · exact swa_finishSlot nb Q H wq wp trees w c0 a0 j x cj acc) (m' := 0) (fun _ _ => SWA.bind' (swa_finishAll fl c0 a0 (j + 1) zs) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _)

theorem swa_initSlot (c0 : H.Coin0) (x : Option Y) :
    SWo (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) 0 fun z => full z = x.isSome :=
  fun _ _ => by cases x <;> rfl

theorem swa_initSlotU (c0 : H.Coin0) :
    ∀ x : Option Y,
      SWo (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) 0 fun z => full z = x.isSome
  | some x => swa_initSlot nb sFS Q H wp w c0 (some x)
  | none => rfl

variable (hm : Std m)
include hm


end Prove

/-! ## Part 6. The slots of a batch; `realQ`; the tree of a node -/

section Slots
variable {X : Type}

theorem length_slotsOfReq {N : ℕ} (σ : Equiv.Perm (Fin N)) (xs : List X) :
    (slotsOfReq σ xs).length = N := by
  unfold slotsOfReq
  rw [List.length_map, List.length_finRange]

/-- of the slots at most as many hold a request as there are requests -/
theorem count_slotsOfReq {N : ℕ} (σ : Equiv.Perm (Fin N)) (xs : List X) :
    ((slotsOfReq σ xs).map Option.isSome).count true ≤ xs.length := by
  unfold slotsOfReq
  rw [List.map_map, List.count_eq_countP, List.countP_map, List.countP_eq_length_filter]
  have hnd : ((List.finRange N).filter
      ((fun b : Bool => b == true) ∘
        (Option.isSome ∘ fun j : Fin N => xs[(σ.symm j).val]?))).Nodup :=
    (List.nodup_finRange N).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  refine le_trans
    (Finset.card_le_card_of_injOn (t := Finset.range xs.length) (fun j => (σ.symm j).val)
      (fun j hj => ?_) (fun a _ b _ h => σ.symm.injective (Fin.val_injective h)))
    (le_of_eq (Finset.card_range _))
  have hj' := (List.mem_filter.1 (List.mem_toFinset.1 hj)).2
  have hs : (xs[(σ.symm j).val]?).isSome = true := by simpa using hj'
  refine Finset.mem_coe.2 (Finset.mem_range.2 ?_)
  by_contra hlt
  rw [List.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hs
  exact Bool.noConfusion hs

end Slots

section Star
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam W.K L) lam} (hm : Std m)

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam W.K L) (sp := split lam W.K L) (Rom.Need.num (needOf nb m))

include hm


omit hm in
theorem cnt_val {n n' : ℕ} (e : n = n') (f : ℕ → Bool) :
    Rom.cnt n (fun j => f j.val) = Rom.cnt n' (fun j => f j.val) := by
  subst e
  rfl

omit WP p in
/-- For `Std m`: a ghost name `fbw t j` has as many marked blocks as the oracle for which it
stands. -/
theorem num_fbw_eq (t : Tag) (j : ℕ) (q : FbIn lam L t) :
    (needOf nb m).num (.fbw t j) q = (needOf nb m).num (.fb t) q :=
  cnt_val ((hm.blocks (.fbw t j)).trans (hm.blocks (.fb t)).symm) fun v =>
    decide (v = W.K ∨ v < nb t q.round)

omit WP p in
/-- For `Std m`: the bound carries over to `realQ c`, the algorithm with every query to `fbw t k`
turned into the query to `fb t`. -/
theorem costBoundAt_realQ {α : Type} (c : TypedOracleComputation lam W.K L α) :
    ∀ t, c.CostBoundAt (needOf nb m).num t → (realQ c).CostBoundAt (needOf nb m).num t := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    rintro t ⟨t', e, h⟩
    cases o with
    | fbw t₀ j =>
      exact ⟨t', e.trans (congrArg (· + t') (num_fbw_eq W nb hm t₀ j q)), fun r => ih r t' (h r)⟩
    | _ => exact ⟨t', e, fun r => ih r t' (h r)⟩

theorem swa_nodeP' (i : I) : SWo (nodeP' W WP p i) (tr W.depth) T1 :=
  SWA.bind' (swa_drawT nb WP.ri)
    (fun _ _ =>
      SWA.bind' (swa_commitE nb hm p.sMT W.depth _) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
    (le_of_eq (Nat.zero_add _))



end Star

/-! ## Part 7. Explicit forms, with nb apart from the trees -/

section Closed
variable {lam K : ℕ} (nbf : ℕ → ℕ)

/-- the trees over a slot's components of all rounds -/
def trJ : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => costJ w + trJ s A W
/-- the trees over the shared components of all rounds -/
def tr0 : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => cost0 w + tr0 s A W

/-- q, as long as the chains can still join -/
def PhK.jn (q : ℕ) : PhK → ℕ
  | .first => q
  | .loc => q
  | _ => 0

theorem PhK.jn_afterLo (q : ℕ) (ph : PhK) : ph.afterLo.jn q ≤ ph.jn q := by
  cases ph <;> exact Nat.le_refl _

theorem triesOf_pos {C P : Type} (gr : Option (GrW C P)) : 1 ≤ triesOf gr := by
  cases gr <;> simp [triesOf]

end Closed

end Need
end Compile.Batch
