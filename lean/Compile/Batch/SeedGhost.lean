-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedGhost.lean: in the forms of the compiled scheme with one seed, with a cache and
with the lazy prover, the provers and the verifier query no ghost name. Sanity lemmas. (Words of
this library: lean/GLOSSARY.md.)

This file does not state it for a whole scheme (C, P and V together).

In a round with proof-of-work bits the token programs make attempt k + 1 as a query to the ghost
name `fbw t k` (Compile/Batch/Oracles.lean); the verifier queries `fb t`. An algorithm of a scheme
must therefore query no ghost name, or an honest proof is rejected. `NoGhost`
(Compile/Batch/GhostGuards.lean) says that of an algorithm. Here, for every wire record, it is
proved of:

  `NoGhost.of_eq`, `NoGhost.blocks`, `NoGhost.derive`
      an algorithm that `realQ` does not change; an algorithm with `NoGhost` whose samples are made
      from small ones, or derived under a seed through an oracle that is no ghost name
  `ng_eraseR`, `ng_erase`   what a scheme runs of a token program (`eraseR`); what `erase` makes of
                            a program without a query to a ghost name (`NoGT`)
  `ng_PS`, `ng_PC`, `ng_PL`   the provers with isk = (i, seed), with the stored level, and the lazy
                              prover of Compile/Batch/SeedLazyDefs.lean
  `ng_VK`   the verifier of the schemes with the entries in the key
  `ng_PSL`, `ng_CL`   the prover and the committer written with labels
                      (Compile/Batch/SeedLabel.lean)

Hypothesis on the seed oracle: σ.o (τ.o) is no ghost name (it holds if σ.o = `OracleName.other`:
`ne_of_other`).

Notation: `realQ`: an algorithm with the analysis's oracles written back: a query to fbw t k becomes
the query to fb t at the same input (Compile/Batch/Oracles.lean); `bk`: a `CoinPlan`: how a uniform
sample is made from small ones (Rom/Blocks.lean); `σ`: a `SeedOracle`: an auxiliary oracle, used as
a source of coins; `pt s j` is the query for the seed s and the counter j (Rom/SpecDerive.lean);
`τ`: a `LabelOracle`: an auxiliary oracle, used as a source of coins under labels: pt s q j is the
query for the seed s, the purpose q and the counter j; `.anchor`, `.test`, `.leaf k`, `.link k`: the
values of `Purpose`: the `Node` of the first encoding; the compiled Test on the first encoding; the
`Node` of copy k; the compiled Link between the first encoding and copy k (both:
Compile/Batch/SeedLabel.lean); `no`: a function of the copy's number and the batch: "no proof";
`own`: a `Bool`: with the comparison (own = true) or without it (own = false); `ℓ`: a natural
number, a level of the tree (level 0: the digests of the leaves) (these three: the head of
Compile/Batch/SeedCache.lean); `kc`: an element of `(I × Fin (σ.sd + 1)) × Ca lam`: (i, seed) with
the cache; `Ca`: for each copy the root of its tree and the digests of one level
(Compile/Batch/SeedCache.lean).

Limits: nothing about probabilities. These are properties of the terms; they do not say that an
honest proof is accepted.
-/
import Compile.Batch.SeedLazy
import Compile.Batch.SeedLabel
import Compile.Batch.GhostGuards

noncomputable section

open Rom Iop ZKCP

namespace Compile.Batch

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

section Kit
variable {K : ℕ} {α : Type}

/-- an algorithm that `realQ` does not change queries no ghost name -/
theorem NoGhost.of_eq {c : TypedOracleComputation lam K L α} (h : realQ c = c) : NoGhost c := by
  rw [← h]
  exact noGhost_realQ c

theorem NoGhost.blocks (bk : CoinPlan) {c : TypedOracleComputation lam K L α} (h : NoGhost c) : NoGhost (c.blocks bk) :=
  .of_eq (by rw [realQ_blocks, realQ_of_noGhost c h])

theorem NoGhost.derive (σ : SeedOracle (spec lam K L)) (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j)
    (s : Fin (σ.sd + 1)) {c : TypedOracleComputation lam K L α} (h : NoGhost c) (j : ℕ) : NoGhost (c.derive σ s j) :=
  .of_eq (by rw [realQ_derive σ hσ, realQ_of_noGhost c h])

theorem ng_eraseR (c : St lam K L α) (vs : List Bits) : NoGhost (eraseR c vs) := noGhost_realQ _

theorem ng_erase {c : St lam K L α} (hc : NoGT c) (vs : List Bits) : NoGhost (erase c vs) :=
  .of_eq (realQ_erase hc vs)

/-- the auxiliary oracle is no ghost name -/
theorem ne_of_other {o : OracleName} (h : o = OracleName.other) : ∀ t j, o ≠ OracleName.fbw t j :=
  fun _ _ e => by rw [h] at e; cases e

theorem ng_pairUpV : ∀ l : List (Dig lam), NoGhost (pairUp (hashTreeNode (K := K) (L := L)) l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t =>
    NoGhost.bind (c := hashTreeNode a b) (fun _ => trivial) fun _ =>
      NoGhost.bind (ng_pairUpV t) fun _ => trivial

theorem ng_levelsV : ∀ (d : ℕ) (l : List (Dig lam)), NoGhost (levelsM (hashTreeNode (K := K) (L := L)) d l)
  | 0, _ => trivial
  | d + 1, l => NoGhost.bind (ng_pairUpV l) fun u => NoGhost.bind (ng_levelsV d u) fun _ => trivial

end Kit

namespace Seed

variable {W : QueryLayout lam L} (WP : WireBP L) (p : Params) {IVK' Pf' : Type} (F : Face W IVK' Pf')
  (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-! ## The prover with the proving key (i, seed) -/

variable (W) in
theorem ng_nodeD (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    NoGhost (nodeD W WP p bk σ k j) :=
  ((ng_erase (nog_nodeP' W WP p k.1) []).blocks bk).derive σ hσ k.2 _

theorem ng_PS (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) :
    NoGhost (PS WP p F bk σ k b) :=
  fun j =>
    NoGhost.bind (ng_nodeD W WP p bk σ hσ k j.val) fun _ =>
      NoGhost.bind (ng_eraseR _ _) fun _ => trivial

/-! ## With the stored level -/

variable (W) in
theorem nog_frontP (i : I) : NoGT (frontP W WP p i) := by
  unfold frontP
  exact (nog_drawT WP.ri).bind fun _ => (nog_leavesE p.sMT _).bind fun _ => trivial

variable (W) in
theorem ng_frontD (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    NoGhost (frontD W WP p bk σ k j) :=
  ((ng_erase (nog_frontP W WP p k.1) []).blocks bk).derive σ hσ k.2 _

variable (W) in
theorem ng_cacheFrom (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) :
    ∀ js, NoGhost (cacheFrom W WP p bk σ ℓ k js)
  | [] => trivial
  | j :: js =>
    NoGhost.bind (ng_nodeD W WP p bk σ hσ k j) fun _ =>
      NoGhost.bind (ng_cacheFrom hσ ℓ k js) fun _ => trivial

theorem ng_lowV {K : ℕ} (own : Bool) :
    ∀ (ℓ : ℕ) (l lv : List (Dig lam)), NoGhost (lowV (K := K) (L := L) own ℓ l lv)
  | 0, _, _ => trivial
  | ℓ + 1, l, lv => NoGhost.bind (ng_levelsV ℓ l) fun lo => by
      cases own
      · exact trivial
      · exact NoGhost.bind (ng_pairUpV _) fun _ => trivial

variable (W) in
theorem ng_nodeC (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (own : Bool) (ℓ : ℕ) (k : I × Fin (σ.sd + 1))
    (j : ℕ) (st : Dig lam × List (Dig lam)) :
    NoGhost (nodeC W WP p bk σ own ℓ k j st) :=
  NoGhost.bind (ng_levelsV _ _) fun hi => by
    split_ifs
    · exact NoGhost.bind (ng_frontD W WP p bk σ hσ k j) fun a =>
        NoGhost.bind (ng_lowV own ℓ _ _) fun _ => trivial
    · exact trivial

theorem ng_PC (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (own : Bool) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) :
    NoGhost (PC WP p bk σ F own ℓ no kc b) :=
  fun j => NoGhost.bind (ng_nodeC W WP p bk σ hσ own ℓ kc.1 j.val _) fun oa => by
    cases oa with
    | none => exact trivial
    | some a => exact NoGhost.bind (ng_eraseR _ _) fun _ => trivial

/-! ## Written with labels -/

section Label
variable (τ : LabelOracle (spec lam W.K L))

theorem ng_PSL (hτ : ∀ t j, τ.o ≠ OracleName.fbw t j) (k : I × Fin (τ.sd + 1)) (b : List (X × Unit)) :
    NoGhost (PSL WP p F bk τ k b) :=
  fun j =>
    NoGhost.bind
      (((ng_erase (nog_nodeP' W WP p k.1) []).blocks bk).derive (τ.at (.leaf j.val)) hτ k.2 0)
      fun _ => NoGhost.bind (ng_eraseR _ _) fun _ => trivial

theorem ng_leavesL (hτ : ∀ t j, τ.o ≠ OracleName.fbw t j) (i : I) (s : Fin (τ.sd + 1)) (root : Node lam L) :
    ∀ (n k : ℕ) (vs : List Bits), NoGhost (leavesL WP p bk τ i s root n k vs)
  | 0, _, _ => trivial
  | n + 1, k, vs =>
      NoGhost.bind (((ng_erase (nog_nodeP' W WP p i) vs).blocks bk).derive
          (τ.at (.leaf k)) hτ s 0) fun a =>
      NoGhost.bind (((ng_eraseR _ a.2).blocks bk).derive (τ.at (.link k)) hτ s 0) fun c =>
      NoGhost.bind (ng_leavesL hτ i s root n (k + 1) c.2) fun _ => trivial

theorem ng_CL (hτ : ∀ t j, τ.o ≠ OracleName.fbw t j) (i : I) : NoGhost (CL WP p F bk τ i) :=
  fun s =>
      NoGhost.bind (((ng_erase (nog_nodeP' W WP p i) []).blocks bk).derive (τ.at .anchor) hτ s 0)
          fun a =>
    NoGhost.bind (((ng_eraseR _ a.2).blocks bk).derive (τ.at .test) hτ s 0) fun b =>
    NoGhost.bind (ng_leavesL WP p bk τ hτ i s a.1 (p.M + 1) 0 b.2) fun _ => trivial

end Label

/-! ## The lazy prover -/

section Fin
variable {K : ℕ} {E : ExtSpec} {Y : Type} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
  (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
  (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam))))

theorem ng_opensExtL (hn : ∀ q, NoGhost (opL q)) (we : WireE E)
    (y : E.Str) (isRead : E.Pos → Bool) :
    ∀ ps, NoGhost (opensExtL we y opL isRead ps)
  | [] => trivial
  | p :: ps => NoGhost.bind (ng_opensExtL hn we y isRead ps) fun of => by
      cases of with
      | none => exact trivial
      | some f =>
        show NoGhost (if isRead p then _ else _ : TypedOracleComputation lam K L _)
        split_ifs
        · exact NoGhost.bind (hn _) fun _ => trivial
        · exact trivial

theorem ng_finishSlotL (hn : ∀ q, NoGhost (opL q)) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    NoGhost (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc vs) := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · exact trivial
  · refine NoGhost.bind (ng_opensExtL opL hn _ _ _ _) fun og => ?_
    cases og with
    | none => exact trivial
    | some gx =>
      exact NoGhost.bind (ng_erase (nog_finishSlotG Q H wq wp w _ c0 a0 j x cj acc) vs)
        fun _ => trivial

theorem ng_finishAllL (hn : ∀ q, NoGhost (opL q)) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits),
      NoGhost (finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs vs)
  | _, [], _ => trivial
  | j, acc :: zs, vs => by
    unfold finishAllL slotL
    refine NoGhost.bind ?_ fun o1 => ?_
    · cases acc.x with
      | none => exact trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · exact ng_finishSlotL Q H wq wp w opL hn c0 a0 j x cj acc vs
        · exact trivial
    · cases o1 with
      | none => exact trivial
      | some o => exact NoGhost.bind (ng_finishAllL hn fl c0 a0 (j + 1) zs o.2) fun _ => trivial

end Fin

variable (W)

theorem ng_opL (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness)
    (lvl : List (Dig lam)) (hi : List (List (Dig lam))) (q : ℕ) :
    NoGhost (opL W WP p bk σ ℓ k j r lvl hi q) :=
  NoGhost.bind (((ng_erase (nog_leavesE p.sMT _) []).blocks bk).derive σ hσ k.2 _)
    fun a => NoGhost.bind (ng_levelsV ℓ a.1.1) fun _ => trivial

theorem ng_PLrun (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b)
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : ℕ) (st : Dig lam × List (Dig lam))
    (hi : List (List (Dig lam))) (r : L.EncodingRandomness) :
    NoGhost (PLrun W WP p bk σ ℓ no k b j st hi r) :=
  fun z =>
      NoGhost.bind (ng_eraseR _ _) fun o =>
          NoGhost.bind
              (ng_finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) _
                (ng_opL W WP p bk σ hσ ℓ k j r st.2 hi) _ _ _ 0 _ _) fun oπ => by
    cases oπ with
    | none => exact trivial
    | some πs => exact trivial

theorem ng_PL (hσ : ∀ t j, σ.o ≠ OracleName.fbw t j) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) :
    NoGhost (PL W WP p bk σ ℓ no kc b) := by
  intro j
  show NoGhost (PLat W WP p bk σ ℓ no kc b j.val)
  unfold PLat
  cases kc.2[j.val]? with
  | none => exact trivial
  | some st =>
    refine NoGhost.bind (ng_levelsV _ _) fun hi => ?_
    split_ifs
    · exact NoGhost.bind (((ng_erase (nog_drawT WP.ri) []).blocks bk).derive σ hσ kc.1.2 _)
        fun ra => ng_PLrun W WP p bk σ hσ ℓ no kc.1 b j.val st hi ra.1
    · exact trivial

/-- the verifier of the schemes with the entries in the key -/
theorem ng_VK (v : IVKK lam L) (x : X) (π : PrfK lam L) : NoGhost ((faceKE W WP p).V v x π) :=
  noGhost_V W p v.1 x _

end Seed

variable (W : QueryLayout lam L)
  (WP : WireBP L) (p : Params) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))


end Compile.Batch
