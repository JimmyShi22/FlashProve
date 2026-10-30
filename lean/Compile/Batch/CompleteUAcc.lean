-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUAcc.lean: for fixed oracle functions, V accepts the proofs of the honest
prover with free empty slots (no query for an empty slot: `proveBU`, Compile/Batch/ProverU.lean),
unless a part is bad (not all hypotheses are named here: see `Spec.acceptsHonestBUG`).

`acceptsHonestBUG` proves `Spec.acceptsHonestBUG` (Compile/Batch/SpecCompleteUG.lean): under
`W.OKG`, `GrFitB`, `L.PropsNoAcc`, `Fmt`, and if every request of the batch is in `Ryes i`: on every
output of the instrumented honest run `runAllBUX` (Compile/Batch/StarUX.lean), V accepts the proof
of every request that has a slot, unless Test, the Link of the sampled copy or the slot is bad
(`none`, or a search that has failed). The method: Compile/Batch/CompleteAcc.lean (words of this
library: lean/GLOSSARY.md).

  Part 1  One slot: `finishSlot` and `finishAll` against `verifyOneProtocol`. The programs are those of
          Compile/Batch/Prover.lean. The lemmas of Compile/Batch/CompleteAcc.lean assume that the
          request tree is the tree over the slot values of all slots; here they are proved from what
          they use of it: the check of this slot's leaf accepts (`ReqAt`).
  Part 2  One execution: `proveBUX`; `proveBU` without proof-of-work bits.
  Part 3  The scheme: `PpUX`, `PUX`, V. The committer is that of Compile/Batch/Star.lean, and its
          lemma (`tri_CpX`) is used unchanged.

Notation: `runAllBUX` (Compile/Batch/StarUX.lean): the committer, then the prover `PUX` on one
batch: the verification key and the proofs; and `RunX`; bad (`RunX.badT`, `RunX.badL`, `RunX.badB`,
Compile/Batch/StarX.lean): Test's proof string is `none`, or one of its searches over nonces has
failed; Link's proof string for the sampled copy is `none`, or one of its searches has failed (true
also without such a copy); the proof string of the slot of request number a, which is x, is `none`,
or a search of its transcript has failed (true also without such a copy); a copy: C encodes the
index once (the first encoding) and `p.M` + 1 more times (the copies) (the head of
Compile/Batch/Star.lean); `RoundsQueryLayout.pass` (Iop/BatchWire.lean): a `Bool`: all tests of a local
transcript are passed; `fl`: `ℕ → Bool`: for which slots a proof string is made (`proveB`,
Compile/Batch/Prover.lean); `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has
accumulated; `acc`: a `SlotAcc` (Compile/Batch/Prover.lean): what a slot has accumulated; `tjs`,
`t0s`, `rts` (`RoundsOK`, Compile/Batch/CompleteChain.lean): tjs are the trees over the slot's
components, t0s those over the shared components, rts the roots as the verifier has them; `embS`,
`embP`, `embE` say how symbols and plain parts are written into queries (`verifyB`,
Compile/Batch/Verifier.lean); `xin`: `Y → Option X`: `xin x` is the x of `recomputeChain`
(Compile/Batch/Verifier.lean): the whole instance (none: Test, Link); `W.OKG` (`QueryLayout.OKG`,
Iop/BatchWire.lean): the laws of a wire whose rounds may have tests; `GrFitB W Ryes`
(Compile/Batch/SpecFit.lean): `GrFit` for the three protocols of a record of protocols;
`L.PropsNoAcc Ryes Rno M` (Iop/BatchGrind.lean): all properties of a record of protocols but
completeness, (Acc); `Fmt` (`RoundSplits.Fmt`, Iop/BatchFmt.lean): a proposition: every round has a format,
and an unsent component is empty.

Limits: nothing on how often a part is bad (`none`, or a search that has failed)
(Compile/Batch/CompleteURef.lean and the files after it).
-/
import Compile.Batch.CompleteAcc
import Compile.Batch.CompleteUChain
import Compile.Batch.SpecCompleteUG

noncomputable section

namespace Compile.Batch.CmplU
open Iop Rom
open Compile.Batch.Cmpl

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-- what the verifier of slot number j, with the slot value c, needs of the request tree: there is
none before the chains have joined; afterwards the check of the leaf of c at leaf number j accepts
-/
def ReqAt (depthReq : ℕ) (vs : List Bits) (phE : PhT) (req : Option TTree) (j : ℕ) (c : Tok) :
    Prop :=
  (¬ Cmpl.chainsHaveJoined phE → req = none) ∧
  (Cmpl.chainsHaveJoined phE →
    ∃ rq,
      req = some rq ∧
      EvalsTo f (reqCheck (L := L) (K := K) depthReq (dv lam vs rq.root) j
          ((pathOf rq.levels j).map (dv lam vs)) (dv lam vs c)) true)

/-! ## Part 1. One slot -/

section Slot
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- Under the hypotheses below, the verifier of one slot accepts a proof string with the honest
fields. -/
theorem evalsTo_verifyB_ofU (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (x : Y)
    (y : E.Str) (τ : Tr Q.loc.shape) (hτ : Q.loc.accept x y τ = true)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees y) (req : Option TTree) (j : ℕ)
    (acc : SlotAcc lam K (Y × H.Coin)) (t0s : List (Option TTree)) (phE : PhT)
    (h : ∀ rtreq : Dig lam, (∀ rq, req = some rq → rtreq = dv lam vs rq.root) →
      ∃ rts,
        RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS τ acc.trees t0s rts ∧
        EvalsTo f (recomputeChain t (trees.map TreeH.root) (xin x) (vs.getD (acc.toks.headD 0) [])
            rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
            ((rootToks acc.trees t0s).map (dv lam vs)) τ.plains)
          (some (τ.rho, rts, phV vs phE acc)))
    (hreq : ReqAt f depthReq vs phE req j acc.c) (isR1 : OPos Q.loc.shape → Bool)
    (hR1 : ∀ p, isR1 p = true ↔ p ∈ Q.loc.reads x τ.rho τ.plains) (isR2 : E.Pos → Bool)
    (hR2 : ∀ p, isR2 p = true ↔ p ∈ Q.loc.extReads x τ.rho) (π : OneProtocolProof lam Q)
    (hg1 : OpensOK vs Q.loc.shape Q.ann wq.sh τ acc.trees t0s isR1 π.opens)
    (hg2 : ∀ p, isR2 p = true → π.ext p = some (honestExt wq.ext vs trees y p))
    (hsalt : π.salt = vs.getD (acc.toks.headD 0) [])
    (hroots : π.roots = (rootToks acc.trees t0s).map (dv lam vs)) (hpl : π.plains = τ.plains)
    (hrt : ∀ rq, req = some rq → π.rtreq = dv lam vs rq.root) (hslot : π.slot = j)
    (hpath : ∀ rq, req = some rq → π.path = (pathOf rq.levels j).map (dv lam vs)) :
    EvalsTo f (verifyB t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π) true := by
  obtain ⟨rts, hR, hE⟩ := h π.rtreq hrt
  have hokr : EvalsTo f ((fun ok ac : Bool => match (phV vs phE acc).slotVal with
      | none => (pure true : TypedOracleComputation lam K L Bool) >>= fun y => pure (ok && y && ac)
      | some c => reqCheck (L := L) (K := K) depthReq π.rtreq π.slot π.path c >>= fun y => pure (ok && y && ac)) true true) true := by
    have hjoin : Cmpl.chainsHaveJoined phE →
        EvalsTo f (reqCheck (L := L) (K := K) depthReq π.rtreq π.slot π.path (dv lam vs acc.c))
          true := fun hh => by
      obtain ⟨rq, h1, h4⟩ := hreq.2 hh
      rw [hrt rq h1, hslot, hpath rq h1]
      exact h4
    cases phE with
    | first => exact (evaluates_eager f).bind ((evaluates_eager f).pure true) ((evaluates_eager f).pure _)
    | loc => exact (evaluates_eager f).bind ((evaluates_eager f).pure true) ((evaluates_eager f).pure _)
    | shr tk0 => exact (evaluates_eager f).bind (hjoin trivial) ((evaluates_eager f).pure _)
    | aft => exact (evaluates_eager f).bind (hjoin trivial) ((evaluates_eager f).pure _)
  have key := evalsTo_afterChain f Q wq hwq hloc hC embS embE trees y x hDe vs hext τ hτ acc.trees
    t0s rts hR π.opens isR1 hR1 hg1 π.ext isR2 hR2
    hg2 (fun ok ac : Bool => match (phV vs phE acc).slotVal with
      | none => (pure true : TypedOracleComputation lam K L Bool) >>= fun y => pure (ok && y && ac)
      | some c => reqCheck (L := L) (K := K) depthReq π.rtreq π.slot π.path c >>= fun y => pure (ok && y && ac)) hokr
  unfold verifyB recomputeChainOfProof afterB
  refine (evaluates_eager f).bind
    (a := some (τ.rho, rts, phV vs phE acc)) (by rw [hsalt, hroots, hpl]; exact hE) ?_
  dsimp only
  rw [hpl, effPlains_eq f _ _ _ embS τ acc.trees t0s rts hC hR]
  have e1 : (fun p =>
        @decide (p ∈ Q.loc.reads x τ.rho τ.plains) (@Finset.decidableMem _ wq.decO _ _)) = isR1 :=
    funext fun p => by rw [Bool.eq_iff_iff, hR1]; simp
  have e2 : (fun p =>
        @decide (p ∈ Q.loc.extReads x τ.rho) (@Finset.decidableMem _ wq.ext.dec _ _)) = isR2 :=
    funext fun p => by rw [Bool.eq_iff_iff, hR2]; simp
  rw [e1, e2]
  exact key

/-- Under the hypotheses below, the verifier of one slot with the strict format accepts a proof
string with the honest fields and nothing else. -/
theorem evalsTo_verifyBS_ofU (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (x : Y)
    (y : E.Str) (τ : Tr Q.loc.shape) (hτ : Q.loc.accept x y τ = true)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees y) (req : Option TTree) (j : ℕ)
    (acc : SlotAcc lam K (Y × H.Coin)) (t0s : List (Option TTree)) (phE : PhT)
    (h : ∀ rtreq : Dig lam, (∀ rq, req = some rq → rtreq = dv lam vs rq.root) →
      ∃ rts,
        RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS τ acc.trees t0s rts ∧
        EvalsTo f (recomputeChain t (trees.map TreeH.root) (xin x) (vs.getD (acc.toks.headD 0) [])
            rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
            ((rootToks acc.trees t0s).map (dv lam vs)) τ.plains)
          (some (τ.rho, rts, phV vs phE acc)))
    (hreq : ReqAt f depthReq vs phE req j acc.c) (isR1 : OPos Q.loc.shape → Bool)
    (hR1 : ∀ p, isR1 p = true ↔ p ∈ Q.loc.reads x τ.rho τ.plains) (isR2 : E.Pos → Bool)
    (hR2 : ∀ p, isR2 p = true ↔ p ∈ Q.loc.extReads x τ.rho) (π : OneProtocolProof lam Q)
    (hg1 : OpensOK vs Q.loc.shape Q.ann wq.sh τ acc.trees t0s isR1 π.opens)
    (hg2 : ∀ p, isR2 p = true → π.ext p = some (honestExt wq.ext vs trees y p))
    (hsalt : π.salt = vs.getD (acc.toks.headD 0) [])
    (hroots : π.roots = (rootToks acc.trees t0s).map (dv lam vs)) (hpl : π.plains = τ.plains)
    (hrt : ∀ rq, req = some rq → π.rtreq = dv lam vs rq.root) (hslot : π.slot = j)
    (hpath : ∀ rq, req = some rq → π.path = (pathOf rq.levels j).map (dv lam vs))
    (hsl : (vs.getD (acc.toks.headD 0) []).length = sFS) (hextS : ExtSalt wq.ext vs sMT trees)
    (ho1 : OpensOnly vs Q.loc.shape Q.ann wq.sh τ acc.trees t0s isR1 π.opens)
    (ho2 : ∀ p op, π.ext p = some op → isR2 p = true ∧ op = honestExt wq.ext vs trees y p)
    (hjN : j < 2 ^ depthReq) (hpath0 : req = none → π.path = []) :
    EvalsTo f (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π)
      true := by
  obtain ⟨rts, hR, hE⟩ := h π.rtreq hrt
  have hq : EvalsTo f (reqPart (K := K) (L := L) depthReq π (phV vs phE acc)) true := by
    have hjoin : Cmpl.chainsHaveJoined phE →
        EvalsTo f (reqCheck (L := L) (K := K) depthReq π.rtreq π.slot π.path (dv lam vs acc.c))
          true := fun hh => by
      obtain ⟨rq, h1, h4⟩ := hreq.2 hh
      rw [hrt rq h1, hslot, hpath rq h1]
      exact h4
    unfold reqPart
    cases phE with
    | first => exact (evaluates_eager f).pure true
    | loc => exact (evaluates_eager f).pure true
    | shr tk0 => exact hjoin trivial
    | aft => exact hjoin trivial
  have hafter := evalsTo_afterBO f Q wq hwq hloc hC embS embE depthReq trees y x hDe vs hext τ hτ
    acc.trees t0s rts hR π hpl isR1 hR1 hg1 isR2 hR2 hg2 (phV vs phE acc) hq
  refine evalsTo_verifyBS hafter (ρ := τ.rho) (rts := rts) (ph := phV vs phE acc)
    (by unfold recomputeChainOfProof; rw [hsalt, hroots, hpl]; exact hE) ?_
  have e1 : (fun p =>
        @decide (p ∈ Q.loc.reads x τ.rho τ.plains) (@Finset.decidableMem _ wq.decO _ _)) = isR1 :=
    funext fun p => by rw [Bool.eq_iff_iff, hR1]; simp
  have e2 : (fun p =>
        @decide (p ∈ Q.loc.extReads x τ.rho) (@Finset.decidableMem _ wq.ext.dec _ _)) = isR2 :=
    funext fun p => by rw [Bool.eq_iff_iff, hR2]; simp
  have s1 : π.salt.length = sFS := by rw [hsalt]; exact hsl
  have s2 : π.roots.length ≤ RootsOfChain.count Q.loc.shape rts := by
    rw [hroots, List.length_map, length_rootToks f _ _ _ embS τ acc.trees t0s rts hR]
  have s3 :=
    strictSB_of f Q.loc.shape Q.ann wq.sh hwq.sh embS τ acc.trees t0s rts hR isR1 π.opens ho1
  have s4 : strictExt sMT wq.ext isR2 π.ext = true := strictExt_of wq.ext fun p op hop => by
    obtain ⟨h1, rfl⟩ := ho2 p op hop
    exact ⟨h1, hextS p⟩
  have s5 : π.slot < 2 ^ depthReq := by rw [hslot]; exact hjN
  have s6 : ((phV vs phE acc).slotVal.isSome || π.path.isEmpty) = true := by
    by_cases hjo : Cmpl.chainsHaveJoined phE
    · rw [isSome_slotVal_phV vs phE acc hjo]; rfl
    · rw [isEmpty_of_eq_nil (hpath0 (hreq.1 hjo)), Bool.or_true]
  unfold proofHasStrictFormat
  rw [hpl, effPlains_eq f _ _ _ embS τ acc.trees t0s rts hC hR, e1, e2]
  simp only [s1, s2, s3, s4, s5, s6, decide_true, Bool.and_self]

/-- Under the hypotheses below, the proof string of a slot all of whose proof-of-work checks are
passed is accepted. What the chain has ensured for the slot (h), the check in the request tree
(hreq), the external trees (hext), and (Acc) (BatchHonestProver.Acc, Iop/Batch.lean) where all proof-of-work
checks are passed (hacc: the clause acc of GrFit, Compile/Batch/SpecFit.lean) give: a slot whose
verifier randomness is not withheld gets a proof string; and if finishSlot returns a proof string
and all proof-of-work bits of the slot's verifier messages are 0, the compiled verifier of one slot
with the strict format (verifyOneProtocol) accepts it. For the format also: the chain's salt has sFS bits
(hsl), the salts in the external trees have sMT bits (hextS), and j is the number of a slot (hjN).
Further hypotheses are below. -/
theorem tri_finishSlotU (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (x : Y)
    (hacc : ∀ c ρ, ρ ∉ H.one.withheld w x → RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh ρ = true →
      ∀ (nJ n0 : List ℕ) (τ : Tr Q.loc.shape), τ.rho = ρ →
        τ.plains = putB Q.loc.shape Q.ann wq.sh .first nJ n0 ((H.one.strat w x c).run ρ).1.plains →
        (∀ p, τ.read p = ((H.one.strat w x c).run ρ).1.read p) → Q.loc.accept x (H.ext w) τ = true)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w)) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (phE : PhT)
    (h : ∀ rtreq : Dig lam, (∀ rq, a0.req = some rq → rtreq = dv lam vs rq.root) →
      ∃ rts,
        RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS
          ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1
          acc.trees a0.trees rts ∧
        EvalsTo f (recomputeChain t (trees.map TreeH.root) (xin x) (vs.getD (acc.toks.headD 0) []) rtreq
            Q.loc.shape Q.ann wq.sh embP 0 .first ((rootToks acc.trees a0.trees).map (dv lam vs))
            (putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse
              ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains))
          (some (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks, rts, phV vs phE acc)))
    (hreq : ReqAt f depthReq vs phE a0.req j acc.c)
    (hsl : (vs.getD (acc.toks.headD 0) []).length = sFS)
    (hextS : ExtSalt wq.ext vs sMT trees) (hjN : j < 2 ^ depthReq) :
    Tri f (finishSlot Q H wq wp trees w c0 a0 j x cj acc) vs fun o vs' =>
      vs' = vs ∧ (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∉ H.one.withheld w x → o.isSome = true) ∧
      ∀ π, o = some π →
          RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks) = true →
          EvalsTo f (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π)
            true := by
  unfold finishSlot
  dsimp only
  by_cases hw : rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x
  · rw [if_pos hw]
    exact tri_pure_iff.2 ⟨rfl, fun h => absurd hw h, fun π hπ => by cases hπ⟩
  · rw [if_neg hw]
    refine tri_reveal_iff.2 ?_
    refine Tri.bind
      ((tri_opensB f Q.loc.shape Q.ann wq.sh hwq.sh _ acc.trees a0.trees _ vs).and
        (tri_opensB_only f Q.loc.shape Q.ann wq.sh hwq.sh _ acc.trees a0.trees _ vs))
      fun g1 vs2 hg1 => ?_
    obtain ⟨⟨rfl, hg1⟩, -, ho1⟩ := hg1
    refine Tri.bind
      ((tri_opensExtB f wq.ext (H.ext w) trees _ wq.ext.all vs2).and
        (tri_opensExtB_only f wq.ext (H.ext w) trees _ wq.ext.all vs2))
      fun g2 vs3 hg2 => tri_pure_iff.2 ?_
    obtain ⟨⟨rfl, hg2⟩, -, ho2⟩ := hg2
    refine ⟨rfl, fun _ => rfl, fun π hπ hps => ?_⟩
    obtain rfl := Option.some.inj hπ
    have hρ := Strat.rho_run (H.one.strat w x (c0, cj)) (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)
    have hassoc : ∀ (R P a b c d e : List Tok), R ++ P ++ a ++ b ++ c ++ d ++ e =
        R ++ P ++ (a ++ b ++ c ++ d ++ e) := fun R P a b c d e => by
      simp only [List.append_assoc]
    refine evalsTo_verifyBS_ofU
      f sMT sFS t Q H wq embS embP xin embE depthReq trees hwq hloc hC x (H.ext w)
      (setPl ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1
        (putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse
          ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains))
      (hacc (c0, cj) _ hw hps acc.nons.reverse a0.nons.reverse _ (by rw [rho_setPl, hρ])
        (plains_setPl _ _) (read_setPl _ _))
      hDe vs3 hext a0.req j
      acc a0.trees phE (fun rtreq hrt => by
        obtain ⟨rts, hR, hE⟩ := h rtreq hrt
        exact ⟨rts, hR.setPl _, by rw [plains_setPl, rho_setPl, hρ]; exact hE⟩) hreq _ (fun p => by rw [rho_setPl, plains_setPl, hρ]; simp) _
      (fun p => by rw [rho_setPl, hρ]; simp) _ (hg1.setPl _)
      (fun p hp => hg2 p hp (hwq.ext.complete p))
      rfl ?_ (plains_setPl _ _).symm ?_ rfl ?_ hsl hextS (ho1.setPl _) ho2 hjN ?_
    · show ((((_ :: _).map _).drop 1).take _).map (digD lam) = _
      rw [hassoc, take_drop_one, List.map_map]
      rfl
    · intro rq hrq
      show digD lam (((_ :: _).map _).getD _ []) = _
      rw [hassoc, getD_three, hrq]
      rfl
    · intro rq hrq
      show ((((_ :: _).map _).drop _).take _).map (digD lam) = _
      rw [hassoc, take_drop_two, List.map_map, hrq]
      rfl
    · intro hrq
      show ((((_ :: _).map _).drop _).take _).map (digD lam) = _
      rw [hrq]
      rfl

/-- what finishSlot needs of slot number j, relative to the store after the chain (that the chain's
salt has sFS bits among it) -/
def ReadyU (vs : List Bits) (c0 : H.Coin0) (a0 : Acc0) (phE : PhT)
    (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) : Prop :=
  ∀ x cj, acc.x = some (x, cj) →
    (∀ c ρ, ρ ∉ H.one.withheld w x → RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh ρ = true →
      ∀ (nJ n0 : List ℕ) (τ : Tr Q.loc.shape), τ.rho = ρ →
        τ.plains = putB Q.loc.shape Q.ann wq.sh .first nJ n0 ((H.one.strat w x c).run ρ).1.plains →
        (∀ p, τ.read p = ((H.one.strat w x c).run ρ).1.read p) →
        Q.loc.accept x (H.ext w) τ = true) ∧
    ReqAt f depthReq vs phE a0.req j acc.c ∧
    (vs.getD (acc.toks.headD 0) []).length = sFS ∧
    ∀ rtreq : Dig lam, (∀ rq, a0.req = some rq → rtreq = dv lam vs rq.root) →
      ∃ rts,
        RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS
          ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1
          acc.trees a0.trees rts ∧
        EvalsTo f (recomputeChain t (trees.map TreeH.root) (xin x) (vs.getD (acc.toks.headD 0) []) rtreq
            Q.loc.shape Q.ann wq.sh embP 0 .first ((rootToks acc.trees a0.trees).map (dv lam vs))
            (putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse
              ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains))
          (some (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks, rts, phV vs phE acc))

/-- the proof strings of all slots -/
theorem tri_finishAllU (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w))
    (hextS : ExtSalt wq.ext vs sMT trees) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (phE : PhT) :
    ∀ (j0 : ℕ) (accs : List (SlotAcc lam K (Y × H.Coin))), j0 + accs.length ≤ 2 ^ depthReq →
    (∀ (k : ℕ) (acc : SlotAcc lam K (Y × H.Coin)), accs[k]? = some acc →
      ReadyU f sMT sFS t Q H wq embS embP xin depthReq trees w vs c0 a0 phE (j0 + k) acc) →
    Tri f (finishAll Q H wq wp trees w fl c0 a0 j0 accs) vs fun πs vs' =>
      vs' = vs ∧ πs.length = accs.length ∧
      (∀ (k : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) (x : Y) (cj : H.Coin), accs[k]? = some acc →
        acc.x = some (x, cj) → fl (j0 + k) = true →
        rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∉ H.one.withheld w x →
        ∃ π, πs[k]? = some (some π)) ∧
      ∀ (k : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) (π : OneProtocolProof lam Q), accs[k]? = some acc →
        πs[k]? = some (some π) →
        RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks) = true →
        ∃ x cj,
          acc.x = some (x, cj) ∧
          EvalsTo f
            (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π) true
  | _, [], _, _ =>
    tri_pure_iff.2 ⟨rfl, rfl, (fun _ _ _ _ h => by simp at h), fun _ _ _ h => by simp at h⟩
  | j0, acc :: accs, hlen, h => by
      have hlen' : j0 + (accs.length + 1) ≤ 2 ^ depthReq := hlen
      have h0 : Tri f (match acc.x with
          | some (x, cj) =>
            if fl j0 then finishSlot Q H wq wp trees w c0 a0 j0 x cj acc else pure none
          | none => pure none) vs fun o vs' => vs' = vs ∧
            (∀ x cj, acc.x = some (x, cj) → fl j0 = true →
              rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∉ H.one.withheld w x → o.isSome = true) ∧
            ∀ π, o = some π →
              RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks) =
                true →
            ∃ x cj,
              acc.x = some (x, cj) ∧
              EvalsTo f
                (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π)
                true := by
        cases hx : acc.x with
        | none => exact tri_pure_iff.2 ⟨rfl, (fun x cj h => by cases h), fun π hπ => by cases hπ⟩
        | some xc =>
          obtain ⟨x, cj⟩ := xc
          obtain ⟨hacc, hj, hsl, hh⟩ := h 0 acc rfl x cj hx
          by_cases hfl : fl j0 = true
          · simp only [hfl, if_true]
            refine (tri_finishSlotU f sMT sFS t Q H wq wp embS embP xin embE depthReq trees w hwq
              hloc hC x hacc hDe vs hext c0 a0 j0 cj acc phE hh
              (by simpa using hj) hsl hextS (by omega)).mono fun o vs' ho => ⟨ho.1, fun x' cj' e _ hw => by
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
                exact ho.2.1 hw, fun π hπ hps => ⟨x, cj, rfl, ho.2.2 π hπ hps⟩⟩
          · simp only [hfl, Bool.false_eq_true, if_false]
            exact tri_pure_iff.2 ⟨rfl, fun _ _ _ h' => absurd h' (by simp), fun π hπ => by cases hπ⟩
      refine Tri.bind h0 fun π0 vs1 hπ0 => ?_
      obtain ⟨rfl, hπ0s, hπ0⟩ := hπ0
      refine Tri.bind (tri_finishAllU hwq hloc hC hDe vs1 hext hextS fl c0 a0 phE (j0 + 1) accs (by omega) fun k acc' hk => by
        have := h (k + 1) acc' (by simpa using hk)
        rwa [show j0 + (k + 1) = j0 + 1 + k by omega] at this) fun r vs2 hr => tri_pure_iff.2 ?_
      obtain ⟨rfl, hr1, hr3, hr2⟩ := hr
      refine ⟨rfl, by simp [hr1], fun k acc' x cj hk hx hfl hw => ?_, fun k acc' π hk hπ => ?_⟩
      · cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          obtain ⟨π, hπ⟩ := Option.isSome_iff_exists.1 (hπ0s x cj hx hfl hw)
          exact ⟨π, by simp [hπ]⟩
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk ⊢
          exact hr3 k acc' x cj hk hx (by rwa [show j0 + 1 + k = j0 + (k + 1) by omega]) hw
      · cases k with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk hπ
          subst hk
          exact hπ0 π hπ
        | succ k =>
          simp only [List.getElem?_cons_succ] at hk hπ
          exact hr2 k acc' π hk hπ

end Slot


/-! ## Part 2. One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- a slot at the start: empty; or as in Compile/Batch/CompleteAcc.lean -/
def InitPostU (c0 : H.Coin0) (x : Option Y)
    (z : SlotSt lam K (Y × H.Coin) Q.loc.shape) (vs' : List Bits) : Prop :=
  (x = none ∧ z.2.x = none) ∨ (x ≠ none ∧ InitPost sFS Q H w c0 x z vs')

/-- Every proof string of the honest compiled prover with free empty slots, all of whose
proof-of-work checks are passed, is accepted, for fixed oracle functions with `RealFam` (the ghost
names `fbw t j` are answered as `fb t`): whatever the coins, one execution of the protocol (proveBUX
of Compile/Batch/StarUX.lean) returns one entry for each slot; a slot that holds an instance, is
flagged, and whose verifier randomness is not withheld gets a proof string; and a proof string whose
slot has proof-of-work bits 0 throughout belongs to a slot that holds an instance and is accepted by
the compiled verifier with the strict format (verifyOneProtocol) for that instance. Further hypotheses are
below. -/
theorem tri_proveBUX (hf : RealFam f) (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hF : Q.ann.Fmt) (hDe : wq.ext.depth ≤ wq.maxDepth) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (hN' : xs.length ≤ 2 ^ depthReq)
    (hacc : ∀ x, some x ∈ xs →
      ∀ c ρ, ρ ∉ H.one.withheld w x → RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh ρ = true →
        ∀ (nJ n0 : List ℕ) (τ : Tr Q.loc.shape), τ.rho = ρ →
          τ.plains =
            putB Q.loc.shape Q.ann wq.sh .first nJ n0 ((H.one.strat w x c).run ρ).1.plains →
          (∀ p, τ.read p = ((H.one.strat w x c).run ρ).1.read p) →
          Q.loc.accept x (H.ext w) τ = true)
    (vs : List Bits) (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w))
    (hextS : ExtSalt wq.ext vs sMT trees) :
    Tri f (proveBUX sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs fun o _ =>
      o.1.length = xs.length ∧
      (∀ (j : ℕ) (x : Y), xs[j]? = some (some x) → fl j = true →
        rhoOf Q.loc.shape Q.ann wq.sh (o.2.getD j []) ∉ H.one.withheld w x →
        ∃ π, o.1[j]? = some (some π)) ∧
      ∀ (j : ℕ) (π : OneProtocolProof lam Q), o.1[j]? = some (some π) →
          RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (o.2.getD j [])) =
            true →
          ∃ x,
            xs[j]? = some (some x) ∧
            EvalsTo f
              (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π)
              true := by
  unfold proveBUX
  refine Tri.bind (tri_drawT f wp.coin0 vs) fun c0 vs0 h0 => ?_
  subst h0
  refine Tri.bind
    ((tri_eachM (f := f) (initSlotU sFS Q H wp w c0) (fun _ _ => True)
      (InitPostU sFS Q H w c0) (fun _ _ _ _ _ => trivial)
    (fun x z v v' hp h => h.imp id fun h => ⟨h.1, by
      obtain ⟨cj, salt, hs, hz⟩ := h.2
      exact ⟨cj, salt, ⟨lt_of_lt_of_le hs.1 hp.length_le, by rw [getD_of_prefix hp hs.1]; exact hs.2⟩, hz⟩⟩) (fun x v _ => ?_) xs vs0 fun _ _ => trivial).with_prefix) fun zs vs1 hzs => ?_
  · cases x with
    | none => exact tri_pure_iff.2 (Or.inl ⟨rfl, rfl⟩)
    | some x =>
      refine Tri.bind (tri_drawT f wp.coin v) fun cj v0 hv0 => ?_
      subst hv0
      exact tri_fresh_iff.2 fun r =>
        tri_pure_iff.2
          (Or.inr
            ⟨by simp, cj, v0.length, ⟨by simp, by rw [getD_concat_length, List.length_ofFn]⟩, rfl⟩)
  obtain ⟨hzs, hp1⟩ := hzs
  refine Tri.bind
    ((tri_chainTU f sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1)
      depthReq hf Q.loc.shape Q.ann wq.sh embS embP 0 .first
    (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hwq.sh hC hF
    (hN.imp (fun h => by rw [← hzs.length_eq]; exact h) id) (fun z hz hx => by
      obtain ⟨x, -, hx0⟩ := forall₂_mem_right hzs z hz
      rcases hx0 with ⟨-, h0⟩ | ⟨-, cj, salt, hs, rfl⟩
      · exact absurd h0 hx
      · exact hs.1) trivial ⟨fun _ => rfl, fun h => h.elim⟩).with_prefix) fun out vs2 hout => ?_
  obtain ⟨⟨phE, t0s, n0s, e1, e0, e2, -, e4⟩, hp2⟩ := hout
  have e1' : out.2.trees = t0s := by simpa using e1
  have e0' : out.2.nons.reverse = n0s := by rw [e0]; simp
  have hbl : ∀ j, (out.1.map fun a => a.blocks).getD j [] =
      (out.1[j]?.map fun a => a.blocks).getD [] := fun j => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  refine Tri.bind
    (tri_finishAllU f sMT sFS t Q H wq wp embS embP xin embE depthReq trees w hwq hloc hC hDe vs2
      (hext.mono (hp1.trans hp2)) (hextS.mono (hp1.trans hp2) hext) fl c0 out.2 phE 0 out.1
      (by rw [Nat.zero_add, ← e4.length_eq, ← hzs.length_eq]; exact hN') ?_)
    fun πs vs3 hπs => tri_pure_iff.2 ?_
  · intro k acc hk x cj hx
    rw [Nat.zero_add]
    obtain ⟨z, hz, hdx, hd⟩ := forall₂_getElem?_right e4 k acc hk
    have hzx : z.2.x ≠ none := by rw [← hdx, hx]; simp
    obtain ⟨xo, hxo, hi⟩ := forall₂_getElem?_right hzs k z hz
    rcases hi with ⟨-, h0⟩ | ⟨-, cj', salt, hs, rfl⟩
    · exact absurd h0 hzx
    obtain ⟨d1, ⟨more, d2⟩, -, -, bls, tjs, nJ, d5, d6, d8, d7⟩ := hd hzx
    have hx' : xo.map (fun x => (x, cj')) = some (x, cj) := d1.symm.trans hx
    obtain ⟨x', rfl, hx''⟩ := Option.map_eq_some_iff.1 hx'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx''
    have d2' : acc.toks.headD 0 = salt := by rw [d2]; rfl
    refine ⟨hacc x' (List.mem_of_getElem? hxo),
      ⟨e2.1, fun hj => ?_⟩,
      by rw [d2', getD_of_prefix hp2 hs.1]; exact hs.2,
      fun rtreq hrt => ?_⟩
    · obtain ⟨rq, lv, h1, h2, h3, h4⟩ := e2.2 hj
      have hkl : k < 2 ^ depthReq := by
        rw [← h4, List.length_map]
        exact (List.getElem?_eq_some_iff.1 hk).1
      exact ⟨rq, h1,
        reqCheck_honestU f h2 (h3.1.trans h4) hkl
          (h3.2 k acc.c (by rw [List.getElem?_map, hk]; simp [csOf, hx]))⟩
    have d5' : acc.blocks = bls := by simpa using d5
    have d6' : acc.trees = tjs := by simpa using d6
    have d8' : acc.nons.reverse = nJ := by rw [d8]; simp
    obtain ⟨rts, hR, hE⟩ := d7 (H.strat w c0 x' cj') rfl (vs1.getD salt []) rtreq (fun _ => rfl) hrt
    rw [d5', d6', d8', e0', d2', e1', getD_of_prefix hp2 hs.1]
    exact ⟨rts, hR, hE⟩
  · obtain ⟨-, hl, hs, hh⟩ := hπs
    have hlen : out.1.length = xs.length := by rw [← e4.length_eq, ← hzs.length_eq]
    refine ⟨by rw [hl, hlen], fun j x hxj hfl hw => ?_, fun j π hπ hps => ?_⟩
    · have hjl : j < out.1.length := by
        rw [hlen]
        exact (List.getElem?_eq_some_iff.1 hxj).1
      obtain ⟨z, hz, hdx, -⟩ := forall₂_getElem?_right e4 j _ (List.getElem?_eq_getElem hjl)
      obtain ⟨xo, hxo, hi⟩ := forall₂_getElem?_right hzs j z hz
      obtain rfl : xo = some x := Option.some.inj (hxo.symm.trans hxj)
      rcases hi with ⟨h0, -⟩ | ⟨-, cj', salt, hs', rfl⟩
      · cases h0
      rw [show (out.1.map fun a => a.blocks).getD j [] =
          out.1[j].blocks by rw [hbl, List.getElem?_eq_getElem hjl]; rfl] at hw
      exact hs j out.1[j] x cj' (List.getElem?_eq_getElem hjl) hdx (by rwa [Nat.zero_add]) hw
    · have hjl : j < out.1.length := by
        rw [← hl]
        exact (List.getElem?_eq_some_iff.1 hπ).1
      rw [show (out.1.map fun a => a.blocks).getD j [] =
          out.1[j].blocks by rw [hbl, List.getElem?_eq_getElem hjl]; rfl] at hps
      obtain ⟨x, cj, hx, hE⟩ := hh j out.1[j] π (List.getElem?_eq_getElem hjl) hπ hps
      obtain ⟨z, hz, hdx, -⟩ := forall₂_getElem?_right e4 j _ (List.getElem?_eq_getElem hjl)
      have hzx : z.2.x ≠ none := by rw [← hdx, hx]; simp
      obtain ⟨xo, hxo, hi⟩ := forall₂_getElem?_right hzs j z hz
      rcases hi with ⟨-, h0⟩ | ⟨-, cj', salt, hs', rfl⟩
      · exact absurd h0 hzx
      have hx' : xo.map (fun x => (x, cj')) = some (x, cj) := hdx.symm.trans hx
      obtain ⟨x', rfl, hx''⟩ := Option.map_eq_some_iff.1 hx'
      obtain ⟨rfl, -⟩ := Prod.mk.inj hx''
      exact ⟨x', hxo, hE⟩

/-- Without proof-of-work bits (`ProtocolQueryLayout.OK`), under the hypotheses below: every proof string of the
honest compiled prover with free empty slots is accepted. -/
theorem tri_proveBU (hf : RealFam f) (hwq : wq.OK) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hF : Q.ann.Fmt) (hDe : wq.ext.depth ≤ wq.maxDepth) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (hN' : xs.length ≤ 2 ^ depthReq)
    (hacc : ∀ x, some x ∈ xs →
      ∀ c ρ, ρ ∉ H.one.withheld w x → Q.loc.accept x (H.ext w) ((H.one.strat w x c).run ρ).1 = true)
    (vs : List Bits) (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w))
    (hextS : ExtSalt wq.ext vs sMT trees) :
    Tri f (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs fun πs _ =>
      πs.length = xs.length ∧
      ∀ (j : ℕ) (π : OneProtocolProof lam Q), πs[j]? = some (some π) →
        ∃ x,
          xs[j]? = some (some x) ∧
          EvalsTo f (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π)
            true := by
  rw [proveBU_eq]
  refine Tri.bind (tri_proveBUX f sMT sFS t Q H wq wp embS embP xin embE depthReq trees w hf hwq.toG hloc hC hF hDe fl xs hN hN' (fun x hx c ρ hρ _ nJ n0 τ h1 h2 h3 => by
    rw [putB_ok _ _ _ hwq.sh] at h2
    rw [← hacc x hx c ρ hρ]
    exact hloc x _ _ τ _ (h1.trans (Strat.rho_run _ _).symm) h2 (fun _ _ => rfl) fun p _ => h3 p) vs hext hextS) fun o vs1 ho => tri_pure_iff.2 ?_
  exact ⟨ho.1, fun j π hπ => ho.2.2 j π hπ (pass_ok _ _ _ hwq.sh _)⟩

end Prove

/-! ## Part 3. The scheme: honest batches on honest keys -/

section Scheme
variable {W : QueryLayout lam L} (WP : WireBP L) (p : Params) (fW : Fam (spec lam W.K L))
variable {Ryes Rno : I → X → Prop} {M : LH.Nums}

/-- An honest batch of the prover with free empty slots on an honest key, for wire records that may
have proof-of-work bits, under the hypotheses below: one proof for each request; the copy's number
is at most p.M; the proof of a request with a slot has the sampled copy's number, root and Link,
and, unless its slot is bad, a proof string that vBS accepts. -/
theorem tri_PpUX (hf : RealFam fW) (hL : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitB W Ryes)
    (hF : L.onlineBatch.ann.Fmt) {i : I} (xs : List X) (hx : ∀ x ∈ xs, Ryes i x) {v : IVK lam L}
    {k : IskH lam L} {xc : XC lam W.K} {vs : List Bits} (hk : KeyOKX WP p fW vs i v k xc) :
    Tri fW (PpUX W WP p k (fun _ => true) xs) vs fun o _ =>
      o.1.length = xs.length ∧
      o.2.1 ≤ p.M ∧
      ∀ lf, k.leaves[o.2.1]? = some lf →
        ∀ (a : Fin L.maxBatchSize) (x : X) (π : Prf lam L), xs[a.val]? = some x → o.1[a.val]? = some π →
          π.leaf = o.2.1 ∧
          π.cm = lf.node.tree.root ∧
          π.piL = lf.piL ∧
          (Ref.badAt L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.i, lf.node.r) x (o.2.2.1 a).val o.2.2.2 = false →
            ∃ πB, π.piB = some πB ∧ EvalsTo fW (vBS W p.sMT p.sFS π.cm x πB) true) := by
  refine tri_sample_iff.2 fun j => ?_
  refine Tri.bind (tri_drawT fW WP.perm vs) fun σ vs0 h0 => ?_
  subst h0
  unfold PpJUX
  split
  · rename_i hnone
    refine (show Tri fW
      (Step.pure
        (xs.map (fun _ => (⟨j.val, default, none, none⟩ : Prf lam L)),
          (j.val, σ, ([] : List (List (Blk lam W.K))))))
      vs0 _ from tri_pure_iff.2 ?_)
    exact ⟨by simp, Nat.le_of_lt_succ j.isLt, fun lf hlf => by rw [hnone] at hlf; cases hlf⟩
  · rename_i lf hlf
    obtain ⟨h1, -⟩ := hk.leaves _ lf hlf
    rw [Step.bind_assoc']
    refine Tri.bind
      (tri_proveBUX fW p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some (fun s => some (.inl s))
        W.depthReq [lf.node.tree]
      (k.i, lf.node.r) hf hW.B hL.localB hL.cohB hF (by rw [hW.extDepth.2.2]; exact hW.depthB)
      (slotFlags σ fun _ => true) (slotsOfReq σ xs)
      (Or.inl (by rw [← hW.slots]; simp [slotsOfReq]))
      (by rw [← hW.slots]; simp [slotsOfReq]) (fun x hxm c ρ hρ hps => hG.B.acc _ x c ρ (by
        rw [hk.idx]
        obtain ⟨s, -, hs⟩ := List.mem_map.1 hxm
        exact hx x (List.mem_of_getElem? hs)) hρ hps) vs0 (by rw [hk.idx]; exact extOK_B hW hL.wired h1) (extSalt_B p fW hW h1)) fun πs vs1 hπs => tri_pure_iff.2 ?_
    refine ⟨by simp, Nat.le_of_lt_succ j.isLt, fun lf' hlf' a x π hxa hπ => ?_⟩
    obtain rfl : lf = lf' := Option.some.inj (hlf.symm.trans hlf')
    have hπ' : ((List.range xs.length).map fun a =>
          (⟨j.val, lf.node.tree.root, lf.piL,
            if h : a < L.maxBatchSize then πs.1.getD (σ ⟨a, h⟩).val none else none⟩ : Prf lam L))[a.val]? =
        some π := hπ
    rw [List.getElem?_map] at hπ'
    obtain ⟨a', ha', rfl⟩ := Option.map_eq_some_iff.1 hπ'
    have haa : a' = a.val := by
      have := (List.getElem?_eq_some_iff.1 ha').2
      simpa using this.symm
    subst haa
    refine ⟨rfl, rfl, rfl, fun hb => ?_⟩
    obtain ⟨hnw, hps⟩ := (badAt_false_iff _ _ _ _ _ _ _ _).1 hb
    obtain ⟨πB, hπB⟩ :=
      hπs.2.1 (σ a).val x (by rw [getElem?_slotsOfReq σ xs a, hxa]) (slotFlags_true σ (σ a)) hnw
    obtain ⟨x', hx', hE⟩ := hπs.2.2 _ πB hπB hps
    rw [getElem?_slotsOfReq σ xs a, hxa] at hx'
    obtain rfl := Option.some.inj (Option.some.inj hx')
    refine ⟨πB, ?_, hE⟩
    show (if h : a.val < L.maxBatchSize then πs.1.getD (σ ⟨a.val, h⟩).val none else none) = some πB
    rw [dif_pos a.isLt, List.getD_eq_getElem?_getD, hπB]
    rfl

end Scheme

/-- Wire records that may have proof-of-work bits, under the hypotheses of `Spec.acceptsHonestBUG`.
For fixed oracle functions, V accepts the proof of every request of an honest batch of the prover
with free empty slots, on an honest key, that has a slot, unless Test, the Link of the sampled copy
or the slot is bad. -/
theorem acceptsHonestBUG : Spec.acceptsHonestBUG := by
  intro I X lam L W WP p Ryes Rno M hL hW hG hF f i b hb z hz a x π hx hπ hbT hbL hbB
  unfold runAllBUX at hz
  obtain ⟨key, hkey, hz1⟩ := mem_outs_bind.1 (show z ∈ Outs f _ from hz)
  obtain ⟨πs, hπs, hz2⟩ := mem_outs_bind.1 hz1
  obtain rfl := mem_outs_pure.1 hz2
  unfold CX at hkey
  have hkey1 := outs_realQ hkey
  unfold CtokX at hkey1
  obtain ⟨o, ho, hkey'⟩ := mem_outs_bind.1 hkey1
  obtain rfl := mem_outs_pure.1 hkey'
  unfold PUX at hπs
  have hπs1 := outs_realQ hπs
  unfold PtokUX at hπs1
  obtain ⟨o', ho', hπ'⟩ := mem_outs_bind.1 hπs1
  obtain rfl := mem_outs_pure.1 hπ'
  have hk := tri_CpX WP p (realF f) (realFam_realF f) hL hW hG i [] o ho
  have hp := tri_PpUX WP p (realF f) (realFam_realF f) hL hW hG hF (b.map Prod.fst) (fun x hx => by
    obtain ⟨xw, hxw, rfl⟩ := List.mem_map.1 hx
    exact hb xw hxw) hk o' ho'
  have hπ1 : (fitLen (⟨0, default, none, none⟩ : Prf lam L) b.length o'.1.1).val[a.val]? = some π :=
    hπ
  rw [fitLen_val _ _ _ (by rw [hp.1, List.length_map])] at hπ1
  have hlt : o'.1.2.1 < o.1.1.2.leaves.length := by
    rw [hk.len]
    exact Nat.lt_succ_of_le hp.2.1
  have hlf : o.1.1.2.leaves[o'.1.2.1]? = some o.1.1.2.leaves[o'.1.2.1] :=
    List.getElem?_eq_getElem hlt
  generalize o.1.1.2.leaves[o'.1.2.1] = lf at hlf
  have hbT' : Ref.badAt (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
        (o.1.1.2.i, o.1.1.2.root.r) () 0 o.1.2.1 = false := hbT
  have hbL' : Ref.badAt (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
        (o.1.1.2.i, o.1.1.2.root.r, lf.node.r) () 0 (o.1.2.2.getD o'.1.2.1 []) = false := by
    have h := hbL
    unfold RunX.badL at h
    dsimp only at h
    rw [hlf] at h
    exact h
  have hbB' : Ref.badAt L.onlineBatch L.honestOnlineBatchProver W.B WP.B (o.1.1.2.i, lf.node.r) x (o'.1.2.2.1 a).val o'.1.2.2.2 =
      false := by
    have h := hbB
    unfold RunX.badB at h
    dsimp only at h
    rw [hlf] at h
    exact h
  rw [hk.idx] at hbT' hbL'
  obtain ⟨πT, hπT, hET⟩ := hk.test hbT'
  obtain ⟨πL, hπL, hEL⟩ := (hk.leaves _ lf hlf).2 hbL'
  obtain ⟨e1, e2, e3, h4⟩ := hp.2.2 lf hlf a x π hx hπ1
  obtain ⟨πB, hπB, hEB⟩ := h4 hbB'
  rw [← runEager_V_real]
  exact evalsTo_V p (realF f) hπT (e3.trans hπL) hπB (by rw [e1]; exact hp.2.1) hET
    (by rw [e2]; exact hEL) hEB

end Compile.Batch.CmplU

/-- `CmplU.acceptsHonestBUG` under a shorter name: under the hypotheses of `Spec.acceptsHonestBUG`,
V accepts unless a part is `none` or a search has failed. -/
theorem Compile.Batch.acceptsHonestBUG : Compile.Batch.Spec.acceptsHonestBUG :=
  Compile.Batch.CmplU.acceptsHonestBUG
