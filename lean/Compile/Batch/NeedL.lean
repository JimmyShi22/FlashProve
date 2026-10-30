-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NeedL.lean: under the two hypotheses below the three algorithms of the scheme
  `argPL` (isk = (i, seed, for each copy its root and one level of its tree); the lazy prover) go on
  in the same way after two answers that agree on the marked blocks. Beside
  Compile/Batch/NeedP.lean. (Words of this library: lean/GLOSSARY.md.)

  Compile/Batch/SeedLazyDefs.lean: argPL = withCache argP cacheOf PL. Its committer is that of
  `argP` followed by the computation of the cache; its verifier is that of `argP`; its prover `PL`
  makes again, of the `Node` of the sampled copy, the randomness of the encoding and the blocks of
  2^ℓ leaves that hold a position that it shows.
  What is new against `argP`. `PLrun` (steps 4 to 6 of `PL`) has two halves. The first, eraseR
  (chainsU ..) [] (a token program, erased: Compile/Batch/RealQ.lean), runs all chains of the batch
  and returns what the slots have gathered, the blocks of Fiat-Shamir answers among them, whole; the
  second, `finishAllL`, a plain oracle algorithm, reads them through `rhoOf`. So the relation on
  states of Compile/Batch/NeedBlocks.lean has to pass through `erase`: Compile/NeedRelErase.lean,
  Rom/OverOneNRel.lean.
  Hypotheses: `QueryLayout.NB W nb` and hσ (of an answer of the derivation oracle nothing is left out), as
  in Compile/Batch/NeedP.lean.
    Part 1  `fo_levelsV`: levels of a tree, hashed by the verifier's node function;
            `sf_finishSlotG`, `finishSlotG_congr`; `fo_opensExtL`, `fo_finishSlotL`,
            `finishSlotL_congr`, `fo_slotL`, `slotL_congr`, `fo_finishAllL`, `finishAllL_congr`
    Part 2  `CRel`, `sfr_chainsU`: all chains, up to the stored blocks
    Part 3  `fo_rD`, `fo_blockD`, `fo_opL`, `fo_nodeD`, `fo_cacheOf`; `fo_PLrun`, `fo_PLat`,
            `facBy_PL`
    Part 4  `facOK_argPL`. Not in this library: the step from it to what the second exit
            (Rom/OverOneN.lean) asks, and a bound on V's queries over that exit. V's marked blocks:
            `costBoundAt_V_argP`, Compile/Batch/NeedP.lean; from marked blocks to queries, for one
            algorithm: `queryBound_overOneN`, Rom/OverOneN.lean.
  Notation:
    `Fo c`: `OComp.FactorsBy (agree nb) c` (Rom/OverOneN.lean), c an oracle algorithm: the program
      reads an answer only up to a relation ag on answers: at every query node, answers in the
      relation have the same continuation program; and so on in every continuation. Lemmas fo_..
    `Fc c`: `SFac (agree nb) c` (Compile/NeedBlocks.lean): `FactorsBy` for a token program. Lemmas
      sf_..; sfr_..: `SFacR` (Compile/NeedRel.lean): the same up to a relation at its ends
    `agree nb`: two typed answers agree on what is needed (Compile/Batch/NeedTable.lean); `nb`: Tag
      → ℕ → ℕ, a parameter; nb t i: the number of blocks that round i of protocol t needs (the head
      of Compile/Batch/NeedTable.lean)
    lemmas .._congr: under the hypotheses of their statements, an equality of two programs: the same
      definition at two values of what the slots have gathered
    `bk`: a `CoinPlan`: how a uniform sample is made from small ones (Rom/Blocks.lean)
    `σ`: a `SeedOracle`: an auxiliary oracle, used as a source of coins; seeds are the elements of
      Fin (sd + 1) (Rom/SpecDerive.lean)
    `ℓ`: the number of the stored level (`keep`, Compile/Batch/SeedCache.lean); `no`: the value
      `no j b`, "without a proof" (the head of Compile/Batch/SeedLazyDefs.lean)
  Limits: this file says nothing on numbers of queries, and nothing on a bound of any theorem. No
  probability and no error bound is stated here.
-/
import Compile.Batch.SeedLazyDefs
import Compile.Batch.NeedP
import Compile.NeedRelErase

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.Need (SFac SFacR Alike ERel)
open Compile.Batch.Seed

/-! ## Part 1. The second half of the prover -/

section Fin
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)

local notation "Fc" => SFac (S := spec lam K L) (sp := split lam K L) (agree nb)
local notation "Fo" => OComp.FactorsBy (S := spec lam K L) (agree nb)

theorem fo_pairUpV : ∀ l : List (Dig lam), Fo (pairUp (hashTreeNode (K := K) (L := L)) l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t =>
    OComp.FactorsBy.bind (fo_nodeV nb a b) fun _ =>
      OComp.FactorsBy.bind (fo_pairUpV t) fun _ => trivial

theorem fo_levelsV : ∀ (d : ℕ) (l : List (Dig lam)), Fo (levelsM (hashTreeNode (K := K) (L := L)) d l)
  | 0, _ => trivial
  | d + 1, l =>
    OComp.FactorsBy.bind (fo_pairUpV nb l) fun u =>
      OComp.FactorsBy.bind (fo_levelsV d u) fun _ => trivial

variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)

theorem sf_finishSlotG (ext : (E.Pos → Bool) → ExtF lam E) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    Fc (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · exact .pure _
  · exact .reveal _ fun vs => (sf_opensB nb _ _ _ _ _ _ _).bind fun f => .pure _

theorem finishSlotG_congr (ext : (E.Pos → Bool) → ExtF lam E) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (bls' : List (Blk lam K))
    (h : rhoOf Q.loc.shape Q.ann wq.sh acc.blocks = rhoOf Q.loc.shape Q.ann wq.sh bls') :
    finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc =
      finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj { acc with blocks := bls' } := by
  unfold finishSlotG
  dsimp only
  rw [h]

variable {opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam)))}

theorem fo_opensExtL (hop : ∀ q, Fo (opL q)) (we : WireE E) (y : E.Str) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos, Fo (opensExtL we y opL isRead ps)
  | [] => trivial
  | p :: ps => OComp.FactorsBy.bind (fo_opensExtL hop we y isRead ps) fun of => by
      cases of with
      | none => trivial
      | some f =>
        show Fo (if isRead p then _ else _)
        cases isRead p
        · trivial
        · exact OComp.FactorsBy.bind (hop _) fun _ => trivial

theorem fo_finishSlotL (hop : ∀ q, Fo (opL q)) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    Fo (finishSlotL Q H wq wp w opL c0 a0 j x cj acc vs) := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · trivial
  · refine OComp.FactorsBy.bind (fo_opensExtL nb hop _ _ _ _) fun og => ?_
    cases og with
    | none => trivial
    | some gx =>
      exact OComp.FactorsBy.bind
        ((sf_finishSlotG nb Q H wq wp w _ c0 a0 j x cj acc).erase vs) fun _ => trivial

theorem fo_slotL (hop : ∀ q, Fo (opL q)) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    Fo (slotL Q H wq wp w opL fl c0 a0 j acc vs) := by
  unfold slotL
  cases acc.x with
  | none => trivial
  | some xc =>
    obtain ⟨x, cj⟩ := xc
    show Fo (if fl j then _ else _)
    cases fl j
    · trivial
    · exact fo_finishSlotL nb Q H wq wp w hop c0 a0 j x cj acc vs

theorem fo_finishAllL (hop : ∀ q, Fo (opL q)) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits),
      Fo (Seed.finishAllL Q H wq wp w opL fl c0 a0 j zs vs)
  | _, [], _ => trivial
  | j, acc :: zs, vs => OComp.FactorsBy.bind (fo_slotL nb Q H wq wp w hop fl c0 a0 j acc vs) fun o1 => by
      cases o1 with
      | none => trivial
      | some o =>
        exact OComp.FactorsBy.bind (fo_finishAllL hop fl c0 a0 (j + 1) zs o.2) fun _ => trivial

theorem finishSlotL_congr (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (bls' : List (Blk lam K)) (vs : List Bits)
    (h : rhoOf Q.loc.shape Q.ann wq.sh acc.blocks = rhoOf Q.loc.shape Q.ann wq.sh bls') :
    finishSlotL Q H wq wp w opL c0 a0 j x cj acc vs =
      finishSlotL Q H wq wp w opL c0 a0 j x cj { acc with blocks := bls' } vs := by
  have key : ∀ ext, finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc =
      finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj { acc with blocks := bls' } :=
    fun ext => finishSlotG_congr Q H wq wp w ext c0 a0 j x cj acc bls' h
  unfold finishSlotL
  dsimp only
  simp only [key]
  rw [h]

theorem slotL_congr (t : Tag) (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0)
    (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) {acc acc' : SlotAcc lam K (Y × H.Coin)}
    (h : AccRel (nb t) acc acc') (vs : List Bits) :
    slotL Q H wq wp w opL fl c0 a0 j acc vs = slotL Q H wq wp w opL fl c0 a0 j acc' vs := by
  obtain ⟨bls', rfl, h⟩ := h
  unfold slotL
  dsimp only
  rcases h with h | h
  · rw [h]
  · have key : ∀ x cj, finishSlotL Q H wq wp w opL c0 a0 j x cj acc vs =
        finishSlotL Q H wq wp w opL c0 a0 j x cj { acc with blocks := bls' } vs :=
      fun x cj =>
        finishSlotL_congr Q H wq wp w c0 a0 j x cj acc bls' vs (rhoOf_congr _ _ _ 0 _ _ hW h)
    simp only [key]

theorem finishAllL_congr (t : Tag) (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0)
    (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) {zs zs' : List (SlotAcc lam K (Y × H.Coin))}, List.Forall₂ (AccRel (nb t)) zs zs' →
      ∀ vs, Seed.finishAllL Q H wq wp w opL fl c0 a0 j zs vs =
        Seed.finishAllL Q H wq wp w opL fl c0 a0 j zs' vs
  | _, _, _, .nil, _ => rfl
  | j, acc :: zs, acc' :: zs', .cons h1 h2, vs => by
      have ih := finishAllL_congr t hW fl c0 a0 (j + 1) h2
      simp only [Seed.finishAllL, slotL_congr nb Q H wq wp w t hW fl c0 a0 j h1 vs, ih]

end Fin

/-! ## Part 2. All chains, up to the stored blocks -/

section Chains
variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (nb : Tag → ℕ → ℕ)
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (cms : List (Dig lam)) (w : Wt)

/-- what the first half of the prover returns: the shared coins, equal; what the chains return,
alike -/
def CRel (nbf : ℕ → ℕ) (o o' : H.Coin0 × (List (SlotAcc lam K (Y × H.Coin)) × Acc0)) : Prop :=
  o.1 = o'.1 ∧ OutRel nbf o.2 o'.2

theorem sfr_chainsU (hW : RoundsQueryLayout.ReadsFrom (nb t) Q.loc.shape Q.ann wq.sh 0)
    (xs : List (Option Y)) :
    SFacR (S := spec lam K L) (sp := split lam K L) (agree nb) (CRel Q H (nb t))
      (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs) := by
  unfold chainsU
  refine SFacR.bindFac (sf_drawT nb wp.coin0) fun c0 => ?_
  refine (sfr_eachM nb (Q := Eq) (fun a _ h => h ▸ (sfr_initSlotU nb sFS t Q H wp w c0 a).self)
      (fun a _ => sfr_initSlotU nb sFS t Q H wp w c0 a) (forall₂_eq_self xs)).bind
    (fun zs zs' hz => ?_) fun zs hz => ?_
  · exact (alike_chainTU nb sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs zs' _ hW hz).bind
      fun _ _ ho => .pure ⟨rfl, ho⟩
  · exact (sfr_chainTU nb sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hW hz).bind
      (fun _ _ ho => .pure ⟨rfl, ho⟩) fun _ ho => .pure ⟨rfl, ho⟩

end Chains

/-! ## Part 3. The lazy prover -/

section Lazy
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) {nb : Tag → ℕ → ℕ}
  (hσ : ∀ q r r', agree (lam := lam) (K := W.K) (L := L) nb σ.o q r r' → r = r')

local notation "Fo" => OComp.FactorsBy (S := spec lam W.K L) (agree nb)

include hσ

theorem fo_rD (k : I × Fin (σ.sd + 1)) (j : ℕ) : Fo (rD W WP p bk σ k j) :=
  (((sf_drawT nb WP.ri).erase []).blocks bk).derive σ k.2 hσ _

theorem fo_blockD (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (u : ℕ) :
    Fo (blockD W WP p bk σ ℓ k j r u) :=
  (((sf_leavesE nb p.sMT _).erase []).blocks bk).derive σ k.2 hσ _

theorem fo_opL (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (lvl : List (Dig lam))
    (hi : List (List (Dig lam))) (q : ℕ) :
    Fo (Seed.opL W WP p bk σ ℓ k j r lvl hi q) :=
  OComp.FactorsBy.bind (fo_blockD W WP p bk σ hσ ℓ k j r _) fun a =>
    OComp.FactorsBy.bind (fo_levelsV nb ℓ a.1.1) fun _ => trivial

theorem fo_nodeD (k : I × Fin (σ.sd + 1)) (j : ℕ) : Fo (nodeD W WP p bk σ k j) :=
  (((sf_nodeP' (nb := nb) W WP p k.1).erase []).blocks bk).derive σ k.2 hσ _

theorem fo_cacheFrom (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) : ∀ js, Fo (cacheFrom W WP p bk σ ℓ k js)
  | [] => trivial
  | j :: js =>
    OComp.FactorsBy.bind (fo_nodeD W WP p bk σ hσ k j) fun _ =>
      OComp.FactorsBy.bind (fo_cacheFrom ℓ k js) fun _ => trivial

theorem fo_cacheOf (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) : Fo (cacheOf W WP p bk σ ℓ k) :=
  fo_cacheFrom W WP p bk σ hσ ℓ k _

omit hσ in
/-- Two algorithms that are alike (`OComp.AlikeO`) stay alike after `realQ`
(Compile/Batch/Oracles.lean). -/
theorem alikeO_realQ {α : Type} {Rr : α → α → Prop}
    {c c' : TypedOracleComputation lam W.K L α} (h : OComp.AlikeO Rr c c') :
    OComp.AlikeO Rr (realQ c) (realQ c') := by
  induction h with
  | pure h => exact .pure h
  | sample n _ ih => exact .sample n ih
  | query o q _ ih =>
    cases o with
    | fbw t j => exact .query (S := spec lam W.K L) (.fb t) q ih
    | _ => exact .query _ q ih

omit hσ in
/-- `OComp.FactorsByR` (goes on in the same way, up to a relation) passes to `realQ` of the
algorithm (`fb t` written back for each ghost name: Compile/Batch/Oracles.lean): a ghost name has
the table of the oracle for which it stands. -/
theorem facByR_realQ {α : Type} {Rr : α → α → Prop} {c : TypedOracleComputation lam W.K L α}
    (h : OComp.FactorsByR (agree nb) Rr c) :
    OComp.FactorsByR (agree nb) Rr (realQ c) := by
  induction h with
  | pure h => exact .pure h
  | sample n _ ih => exact .sample n ih
  | query o q he _ ih =>
    cases o with
    | fbw t j =>
      exact .query (S := spec lam W.K L) (.fb t) q (fun r r' e => alikeO_realQ W (he r r' e)) ih
    | _ => exact .query _ q (fun r r' e => alikeO_realQ W (he r r' e)) ih

variable (hW : W.NB nb)
include hW

/-- Steps 4 to 6 of the lazy prover (numbered in the header of Compile/Batch/SeedLazyDefs.lean): the
chains hand whole answers to the second half, which reads of them what the wire record reads. -/
theorem fo_PLrun (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : ℕ) (st : Dig lam × List (Dig lam))
    (hi : List (List (Dig lam))) (r : L.EncodingRandomness) :
    Fo (PLrun W WP p bk σ ℓ no k b j st hi r) := by
  unfold PLrun
  refine fun z => OComp.FactorsByR.toFactorsBy ?_
  refine (facByR_realQ W
      ((sfr_chainsU nb p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq [st.1]
        (k.1, r) hW.B _).erase [])).bind
    (fun o o' ho => ?_) fun o _ => ?_
  · obtain ⟨⟨c0, out1, out2⟩, vs⟩ := o
    obtain ⟨⟨c0', out1', out2'⟩, vs'⟩ := o'
    obtain ⟨⟨h1, h2, h3⟩, h4⟩ := ho
    obtain rfl : c0 = c0' := h1
    obtain rfl : out2 = out2' := h3
    obtain rfl : vs = vs' := h4
    refine OComp.AlikeO.of_eq ?_
    show OComp.bind (Seed.finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) _ _ c0 out2 0 out1 vs) _ =
      OComp.bind (Seed.finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) _ _ c0 out2 0 out1' vs) _
    rw [finishAllL_congr nb L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) Tag.onl hW.B _ c0 out2 0 h2 vs]
  · refine OComp.FactorsBy.toR
      (OComp.FactorsBy.bind
        (fo_finishAllL nb L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r)
          (fo_opL W WP p bk σ hσ ℓ k j r st.2 hi) _ _ _ _ _ _) fun oπ => ?_)
    cases oπ <;> trivial

theorem fo_PLat (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) (j : ℕ) :
    Fo (PLat W WP p bk σ ℓ no kc b j) := by
  unfold PLat
  cases kc.2[j]? with
  | none => trivial
  | some st =>
    refine OComp.FactorsBy.bind (fo_levelsV nb _ _) fun hi => ?_
    split_ifs
    · exact OComp.FactorsBy.bind (fo_rD W WP p bk σ hσ kc.1 j) fun ra =>
        fo_PLrun W WP p bk σ hσ hW ℓ no kc.1 b j st hi ra.1
    · trivial

/-- Under `W.NB nb` and hσ: the lazy prover goes on in the same way after two answers that agree on
what is needed. -/
theorem facBy_PL (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) : Fo (PL W WP p bk σ ℓ no kc b) :=
  fun j => fo_PLat W WP p bk σ hσ hW ℓ no kc b j.val

/-! ## Part 4. The scheme -/

theorem facOK_argPL (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b) :
    FacOK (agree nb) (argPL W WP p bk σ ℓ no) where
  C := fun i =>
    OComp.FactorsBy.bind ((facOK_argP W WP p bk σ hW hσ).C i) fun o =>
      OComp.FactorsBy.bind (fo_cacheOf W WP p bk σ hσ ℓ o.2) fun _ => trivial
  P := fun kc b => facBy_PL W WP p bk σ hσ hW ℓ no kc b
  V := fun v x π => (facOK_argP W WP p bk σ hW hσ).V v x π

omit hσ hW

end Lazy

end Need
end Compile.Batch
