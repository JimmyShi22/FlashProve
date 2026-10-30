-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteAcc.lean: for fixed oracle functions with `RealFam`, and under further
hypotheses, every proof string of the honest compiled prover all of whose proof-of-work checks are
passed is accepted by the compiled verifier of its slot (words of this library: lean/GLOSSARY.md).

  Parts 1 to 3  the fields of the proof string; one slot (`finishSlot` against `verifyB`,
                `verifyOneProtocol`); one execution (`proveBX`, Compile/Batch/StarX.lean: `proveB` with a
                further output: the hash blocks that each slot has seen)
  Part 4  the scheme: Test and Link without proof-of-work bits (`tri_proveT`, `tri_proveLk`) and
          with them (`tri_proveTX`, `tri_proveLkX`); the committer (`tri_CpX`; the copies:
          Compile/Batch/Star.lean); when V accepts (`evalsTo_V`)

`W.OK` includes that no round has proof-of-work bits. With them (`W.OKG`, `GrFitB`, `L.PropsNoAcc`;
not all hypotheses are named here: see `tri_proveTX`, `tri_proveLkX`) Test or a Link is accepted
unless it is bad (`Ref.badAt`; for a slot: `tri_proveBX`, under hacc): its verifier randomness is
withheld, or some proof-of-work bit of it is 1: a search has failed.

The store is the list of strings for which the tokens stand (vs). The scheme's C and P are `realQ`
of what `erase` makes of programs with tokens: under f they output what these output under `realF f`
(`outs_realQ`), and `realF f` answers the ghost names `fbw` as `fb`, which is `RealFam`
(Compile/Batch/CompleteChain.lean). V never queries a ghost name (`noGhost_V`,
Compile/Batch/GhostGuards.lean; hence `runEager_V_real`). The transcript that V judges is the honest
one with the numbers of the final attempts written into its plain parts (`setPl`, `putB`); trees,
roots and openings depend on the oracle parts only. That V's local verifier accepts it where all
proof-of-work bits are 0 is the clause `acc` of `GrFit` (Compile/Batch/SpecFit.lean), a hypothesis
here. Under the hypotheses of its statement, a slot whose verifier randomness is not withheld gets a
proof string (`tri_finishSlot`, second clause).

Notation: `Tri f c vs Q` (Compile/EraseKit.lean): a proposition: under the oracle functions f,
whatever the coins, the erased program c, started with the store vs, returns a value a and a store
vs' with Q a vs'; `EvalsTo f x a` (Compile/MerkleRom.lean): a proposition: under the oracle
functions f the algorithm x returns a, whatever its coins; `t`: a `Tag` (Compile/Oracles.lean):
test, link or onl; `embS`, `embP`, `embE` say how symbols and plain parts are written into queries
(`verifyB`, Compile/Batch/Verifier.lean); `xin`: `Y → Option X`: `xin x` is the x of `recomputeChain`
(Compile/Batch/Verifier.lean): the whole instance (none: Test, Link); `depthReq`: a natural number;
in `QueryLayout` (Iop/BatchWire.lean): depth of a request tree: there are 2^depthReq slots; `fl`:
`ℕ → Bool`: for which slots a proof string is made (`proveB`, Compile/Batch/Prover.lean); `a0`: an
`Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated; `tjs`, `t0s`, `rts`
(`RoundsOK`, Compile/Batch/CompleteChain.lean): tjs are the trees over the slot's components, t0s
those over the shared components, rts the roots as the verifier has them; `nJ`, `n0` (`putB`,
Compile/Batch/Prover.lean): nJ: the numbers of the final attempts of the slot, n0: those of the
shared rounds, both in the order of the rounds; `AllLo s A` (Compile/Batch/CompleteChain.lean): a
proposition: there is no shared round; the phases `first`, `loc`, `shr`, `aft` (`PhT`,
Compile/Batch/Prover.lean): all slots go through the rounds together, with a phase, as on the
verifier's side.

Limits: this file does not prove that V accepts every proof of an honest batch on an honest key (for
the prover with free empty slots: `acceptsHonestBUG`, Compile/Batch/CompleteUAcc.lean, unless a part
is bad, under its hypotheses); nothing on how likely a bad event is (the distributions:
Compile/Batch/CompleteRef.lean and the files after it, Compile/Batch/CompleteUnif.lean).
-/
import Compile.Batch.CompleteStrict
import Compile.Batch.CompleteForest
import Compile.Batch.Star
import Compile.Batch.SpecCompleteG
import Compile.Batch.LoopEager
import Compile.Batch.GhostGuards
import Compile.Batch.GrOK
import Iop.ShapeKit

noncomputable section

namespace Compile.Batch.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. The fields -/

section Fields
variable {A B : Type} (g : A → B) (d : B) (s : A) (R P Rest : List A)

theorem take_drop_one : (((s :: (R ++ P ++ Rest)).map g).drop 1).take R.length = R.map g := by
  simp only [List.map_cons, List.drop_succ_cons, List.drop_zero, List.map_append, List.append_assoc]
  exact List.take_left' (by simp)

theorem take_drop_two :
    (((s :: (R ++ P ++ Rest)).map g).drop (1 + R.length)).take P.length = P.map g := by
  rw [Nat.add_comm]
  simp only [List.map_cons, List.drop_succ_cons, List.map_append, List.append_assoc]
  rw [List.drop_left' (by simp)]
  exact List.take_left' (by simp)

theorem getD_three :
    ((s :: (R ++ P ++ Rest)).map g).getD (1 + R.length + P.length) d = (Rest.map g).getD 0 d := by
  have e : 1 + R.length + P.length = (R ++ P).length + 0 + 1 := by simp; omega
  rw [e]
  simp only [List.getD_eq_getElem?_getD, List.map_cons, List.getElem?_cons_succ, List.map_append]
  rw [← List.map_append, List.getElem?_append_right (by simp)]
  simp

end Fields

/-! ## Part 2. One slot -/

section SetPl

/-- the transcript with other plain parts: the same oracles, the same verifier messages -/
def setPl : {s : Shape} → Tr s → Plains s → Tr s
  | [], _, _ => ()
  | _ :: _, (m, c, τ), (pl, pls) => ((m.1, pl), c, setPl τ pls)

theorem plains_setPl : ∀ {s : Shape} (τ : Tr s) (P : Plains s), (setPl τ P).plains = P
  | [], _, () => rfl
  | _ :: _, (_, _, τ), (pl, pls) => congrArg (Prod.mk pl) (plains_setPl τ pls)

theorem rho_setPl : ∀ {s : Shape} (τ : Tr s) (P : Plains s), (setPl τ P).rho = τ.rho
  | [], _, _ => rfl
  | _ :: _, (_, c, τ), (_, pls) => congrArg (Prod.mk c) (rho_setPl τ pls)

theorem read_setPl :
    ∀ {s : Shape} (τ : Tr s) (P : Plains s) (p : OPos s), (setPl τ P).read p = τ.read p
  | _ :: _, (_, _, _), (_, _), .inl _ => rfl
  | _ :: _, (_, _, τ), (_, pls), .inr p => read_setPl τ pls p

variable {f}

/-- trees, roots and openings depend on the oracle parts only -/
theorem RoundsOK.setPl {sMT : ℕ} {vs : List Bits} :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {embS : (p : OPos s) → OSym s p → Body L}
        {τ : Tr s} {tjs t0s : List (Option TTree)} {rts : RootsOfChain lam s},
      RoundsOK f sMT vs s A W embS τ tjs t0s rts →
      ∀ P : Plains s, RoundsOK f sMT vs s A W embS (Cmpl.setPl τ P) tjs t0s rts
  | [], _, _, _, _, _, _, _, h, _ => h
  | _ :: _, (_, _), (_, _), _, (_, _, _), _, _, (_, _), h, (_, pls) => by
      obtain ⟨tj, t0, tjs', t0s', e1, e2, h1, h2, h3, h4, h5, h6, hr⟩ := h
      exact ⟨tj, t0, tjs', t0s', e1, e2, h1, h2, h3, h4, h5, h6, hr.setPl pls⟩

theorem OpensOK.setPl {vs : List Bits} :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {τ : Tr s} {tjs t0s : List (Option TTree)}
        {isRead : OPos s → Bool} {g : (p : OPos s) → Option (Opening lam (OSym s p))},
      OpensOK vs s A W τ tjs t0s isRead g →
      ∀ P : Plains s, OpensOK vs s A W (Cmpl.setPl τ P) tjs t0s isRead g
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _, _), _, _, _, _, h, (_, pls) => ⟨h.1, h.2.1, h.2.2.setPl pls⟩

theorem OpensOnly.setPl {vs : List Bits} :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {τ : Tr s} {tjs t0s : List (Option TTree)}
        {isRead : OPos s → Bool} {g : (p : OPos s) → Option (Opening lam (OSym s p))},
      OpensOnly vs s A W τ tjs t0s isRead g →
      ∀ P : Plains s, OpensOnly vs s A W (Cmpl.setPl τ P) tjs t0s isRead g
  | [], _, _, _, _, _, _, _, _, _ => trivial
  | _ :: _, (_, _), (_, _), (_, _, _), _, _, _, _, h, (_, pls) => ⟨h.1, h.2.setPl pls⟩

end SetPl

section Slot
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- Under the hypotheses below, the verifier of one slot accepts a proof string with the honest
fields. -/
theorem evalsTo_verifyB_of (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (x : Y)
    (y : E.Str) (τ : Tr Q.loc.shape) (hτ : Q.loc.accept x y τ = true)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits) (hext : ExtOK f sMT wq.ext embE vs trees y)
    (req : Option TTree) (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) (t0s : List (Option TTree))
    (phE : PhT) (cs : List Tok)
    (h : ∀ rtreq : Dig lam, (∀ rq, req = some rq → rtreq = dv lam vs rq.root) →
      ∃ rts,
        RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS τ acc.trees t0s rts ∧
        EvalsTo f (recomputeChain t (trees.map TreeH.root) (xin x) (vs.getD (acc.toks.headD 0) [])
            rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
            ((rootToks acc.trees t0s).map (dv lam vs)) τ.plains)
          (some (τ.rho, rts, phV vs phE acc)))
    (hreq : ReqInv f depthReq vs phE req cs) (hj : cs[j]? = some acc.c)
    (isR1 : OPos Q.loc.shape → Bool) (hR1 : ∀ p, isR1 p = true ↔ p ∈ Q.loc.reads x τ.rho τ.plains)
    (isR2 : E.Pos → Bool) (hR2 : ∀ p, isR2 p = true ↔ p ∈ Q.loc.extReads x τ.rho) (π : OneProtocolProof lam Q)
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
    have hjoin : chainsHaveJoined phE →
        EvalsTo f (reqCheck (L := L) (K := K) depthReq π.rtreq π.slot π.path (dv lam vs acc.c))
          true := fun hh => by
      obtain ⟨rq, h1, h2, h3⟩ := hreq.2 hh
      have hjl : j < 2 ^ depthReq := by
        rw [← h3]
        exact (List.getElem?_eq_some_iff.1 hj).1
      have h4 := reqCheck_honest f h2 (by simpa using h3) hjl
      have h5 : (cs.map (dv lam vs)).getD j default = dv lam vs acc.c := by
        simp [List.getD_eq_getElem?_getD, hj]
      rw [h5] at h4
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

omit sFS in
theorem isEmpty_of_eq_nil {β : Type} {l : List β} (h : l = []) : l.isEmpty = true := by rw [h]; rfl

/-- Under the hypotheses below, the verifier of one slot with the strict format accepts a proof
string with the honest fields and nothing else. -/
theorem evalsTo_verifyBS_of (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (x : Y)
    (y : E.Str) (τ : Tr Q.loc.shape) (hτ : Q.loc.accept x y τ = true)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits) (hext : ExtOK f sMT wq.ext embE vs trees y)
    (req : Option TTree) (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) (t0s : List (Option TTree))
    (phE : PhT) (cs : List Tok)
    (h : ∀ rtreq : Dig lam, (∀ rq, req = some rq → rtreq = dv lam vs rq.root) →
      ∃ rts,
        RoundsOK f sMT vs Q.loc.shape Q.ann wq.sh embS τ acc.trees t0s rts ∧
        EvalsTo f (recomputeChain t (trees.map TreeH.root) (xin x) (vs.getD (acc.toks.headD 0) [])
            rtreq Q.loc.shape Q.ann wq.sh embP 0 .first
            ((rootToks acc.trees t0s).map (dv lam vs)) τ.plains)
          (some (τ.rho, rts, phV vs phE acc)))
    (hreq : ReqInv f depthReq vs phE req cs) (hj : cs[j]? = some acc.c)
    (isR1 : OPos Q.loc.shape → Bool) (hR1 : ∀ p, isR1 p = true ↔ p ∈ Q.loc.reads x τ.rho τ.plains)
    (isR2 : E.Pos → Bool) (hR2 : ∀ p, isR2 p = true ↔ p ∈ Q.loc.extReads x τ.rho) (π : OneProtocolProof lam Q)
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
    have hjoin : chainsHaveJoined phE →
        EvalsTo f (reqCheck (L := L) (K := K) depthReq π.rtreq π.slot π.path (dv lam vs acc.c))
          true := fun hh => by
      obtain ⟨rq, h1, h2, h3⟩ := hreq.2 hh
      have hjl : j < 2 ^ depthReq := by
        rw [← h3]
        exact (List.getElem?_eq_some_iff.1 hj).1
      have h4 := reqCheck_honest f h2 (by simpa using h3) hjl
      have h5 : (cs.map (dv lam vs)).getD j default = dv lam vs acc.c := by
        simp [List.getD_eq_getElem?_getD, hj]
      rw [h5] at h4
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
    by_cases hjo : chainsHaveJoined phE
    · rw [isSome_slotVal_phV vs phE acc hjo]; rfl
    · rw [isEmpty_of_eq_nil (hpath0 (hreq.1 hjo)), Bool.or_true]
  unfold proofHasStrictFormat
  rw [hpl, effPlains_eq f _ _ _ embS τ acc.trees t0s rts hC hR, e1, e2]
  simp only [s1, s2, s3, s4, s5, s6, decide_true, Bool.and_self]

/-- Under the hypotheses below, the proof string of a slot all of whose proof-of-work checks are
passed is accepted. What the chain has ensured for the slot (h), the request tree (hreq; cs are the
slot values of all slots, and number j is the slot's), the external trees (hext), and (Acc)
(BatchHonestProver.Acc, Iop/Batch.lean) where all proof-of-work checks are passed (hacc: the clause acc of
GrFit, Compile/Batch/SpecFit.lean) give: if finishSlot returns a proof string and all proof-of-work
bits of the slot's verifier messages are 0, the compiled verifier of one slot with the strict format
(verifyOneProtocol) accepts it. The transcript that V judges is the honest one with the numbers of the final
attempts written into its plain parts (setPl, putB). For the format also: the chain's salt has sFS
bits (hsl), the salts in the external trees have sMT bits (hextS), and j is the number of a slot
(hjN). Further hypotheses are below. -/
theorem tri_finishSlot (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent) (x : Y)
    (hacc : ∀ c ρ, ρ ∉ H.one.withheld w x → RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh ρ = true →
      ∀ (nJ n0 : List ℕ) (τ : Tr Q.loc.shape), τ.rho = ρ →
        τ.plains = putB Q.loc.shape Q.ann wq.sh .first nJ n0 ((H.one.strat w x c).run ρ).1.plains →
        (∀ p, τ.read p = ((H.one.strat w x c).run ρ).1.read p) → Q.loc.accept x (H.ext w) τ = true)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w)) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (phE : PhT) (cs : List Tok)
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
    (hreq : ReqInv f depthReq vs phE a0.req cs) (hj : cs[j]? = some acc.c)
    (hsl : (vs.getD (acc.toks.headD 0) []).length = sFS)
    (hextS : ExtSalt wq.ext vs sMT trees) (hjN : j < 2 ^ depthReq) :
    Tri f (finishSlot Q H wq wp trees w c0 a0 j x cj acc) vs fun o vs' =>
      vs' = vs ∧
      (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∉ H.one.withheld w x → o.isSome = true) ∧
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
    refine evalsTo_verifyBS_of
      f sMT sFS t Q H wq embS embP xin embE depthReq trees hwq hloc hC x (H.ext w)
      (setPl ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1
        (putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse
          ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1.plains))
      (hacc (c0, cj) _ hw hps acc.nons.reverse a0.nons.reverse _ (by rw [rho_setPl, hρ])
        (plains_setPl _ _) (read_setPl _ _))
      hDe vs3 hext a0.req j
      acc a0.trees phE cs (fun rtreq hrt => by
        obtain ⟨rts, hR, hE⟩ := h rtreq hrt
        exact ⟨rts, hR.setPl _, by rw [plains_setPl, rho_setPl, hρ]; exact hE⟩) hreq hj _ (fun p => by rw [rho_setPl, plains_setPl, hρ]; simp) _
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

/-- what finishSlot needs of slot number j, relative to the store after the chain (among other
things, that the chain's salt has sFS bits) -/
def Ready (vs : List Bits) (c0 : H.Coin0) (a0 : Acc0) (phE : PhT) (cs : List Tok)
    (j : ℕ) (acc : SlotAcc lam K (Y × H.Coin)) : Prop :=
  ∀ x cj, acc.x = some (x, cj) →
    (∀ c ρ, ρ ∉ H.one.withheld w x → RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh ρ = true →
      ∀ (nJ n0 : List ℕ) (τ : Tr Q.loc.shape), τ.rho = ρ →
        τ.plains = putB Q.loc.shape Q.ann wq.sh .first nJ n0 ((H.one.strat w x c).run ρ).1.plains →
        (∀ p, τ.read p = ((H.one.strat w x c).run ρ).1.read p) →
        Q.loc.accept x (H.ext w) τ = true) ∧
    cs[j]? = some acc.c ∧
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
theorem tri_finishAll (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hDe : wq.ext.depth ≤ wq.maxDepth) (vs : List Bits)
    (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w))
    (hextS : ExtSalt wq.ext vs sMT trees) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (phE : PhT)
    (cs : List Tok) (hreq : ReqInv f depthReq vs phE a0.req cs) :
    ∀ (j0 : ℕ) (accs : List (SlotAcc lam K (Y × H.Coin))), j0 + accs.length ≤ 2 ^ depthReq →
    (∀ (k : ℕ) (acc : SlotAcc lam K (Y × H.Coin)), accs[k]? = some acc →
      Ready f sMT sFS t Q H wq embS embP xin trees w vs c0 a0 phE cs (j0 + k) acc) →
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
            refine (tri_finishSlot f sMT sFS t Q H wq wp embS embP xin embE depthReq trees w hwq
              hloc hC x hacc hDe vs hext c0 a0 j0 cj acc phE cs hh
              hreq hj hsl hextS (by omega)).mono fun o vs' ho => ⟨ho.1, fun x' cj' e _ hw => by
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
                exact ho.2.1 hw, fun π hπ hps => ⟨x, cj, rfl, ho.2.2 π hπ hps⟩⟩
          · simp only [hfl, Bool.false_eq_true, if_false]
            exact tri_pure_iff.2 ⟨rfl, fun _ _ _ h' => absurd h' (by simp), fun π hπ => by cases hπ⟩
      refine Tri.bind h0 fun π0 vs1 hπ0 => ?_
      obtain ⟨rfl, hπ0s, hπ0⟩ := hπ0
      refine Tri.bind (tri_finishAll hwq hloc hC hDe vs1 hext hextS fl c0 a0 phE cs hreq (j0 + 1) accs (by omega) fun k acc' hk => by
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

/-! ## Part 3. One execution -/

theorem forall₂_getElem?_right {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ P l₁ l₂ → ∀ (k : ℕ) (b : β), l₂[k]? = some b → ∃ a, l₁[k]? = some a ∧ P a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons h1 t1, 0, b, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      exact ⟨_, rfl, h1⟩
  | _, _, .cons _ t1, k + 1, b, h => by
      simp only [List.getElem?_cons_succ] at h ⊢
      exact forall₂_getElem?_right t1 k b h

theorem tri_drawT {β : Type} (e : Enum β) (vs : List Bits) :
    Tri f (drawT (lam := lam) (K := K) (L := L) e) vs fun _ vs' => vs' = vs :=
  tri_sample_iff.2 fun _ => tri_pure_iff.2 rfl

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

/-- a slot at the start; its chain's salt has sFS bits -/
def InitPost (c0 : H.Coin0) (x : Option Y)
    (z : SlotSt lam K (Y × H.Coin) Q.loc.shape) (vs' : List Bits) : Prop :=
  ∃ (cj : H.Coin) (salt : Tok), (salt < vs'.length ∧ (vs'.getD salt []).length = sFS) ∧
    z = (match x with
      | some x => H.one.strat w x (c0, cj)
      | none =>
        Strat.dflt Q.loc.shape (), ⟨x.map fun x => (x, cj), salt, 0, [], [], [salt], [], []⟩)

/-- Every proof string of the honest compiled prover all of whose proof-of-work checks are passed is
accepted, for fixed oracle functions with `RealFam` (the ghost names are answered as `fb t`):
whatever the coins, one execution of the compiled prover of a protocol with slots Q (proveBX of
Compile/Batch/StarX.lean: proveB with a further output: the hash blocks that each slot has seen)
returns one entry for each slot; a slot that holds an instance, is flagged, and whose verifier
randomness is not withheld gets a proof string; and a proof string whose slot has proof-of-work bits
0 throughout belongs to a slot that holds an instance and is accepted by the compiled verifier with
the strict format (verifyOneProtocol) for that instance. For the format: there are at most 2^depthReq slots
(hN'), and the salts in the external trees have sMT bits (hextS). Further hypotheses are below. -/
theorem tri_proveBX (hf : RealFam f) (hwq : wq.OKG) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
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
    Tri f (proveBX sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs fun o _ =>
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
  unfold proveBX
  refine Tri.bind (tri_drawT f wp.coin0 vs) fun c0 vs0 h0 => ?_
  subst h0
  refine Tri.bind
    ((tri_eachM (f := f) (initSlot sFS Q H wp w c0) (fun _ _ => True)
      (InitPost sFS Q H w c0) (fun _ _ _ _ _ => trivial)
    (fun x z v v' hp h => by
      obtain ⟨cj, salt, hs, hz⟩ := h
      exact ⟨cj, salt, ⟨lt_of_lt_of_le hs.1 hp.length_le, by rw [getD_of_prefix hp hs.1]; exact hs.2⟩, hz⟩) (fun x v _ => ?_) xs vs0 fun _ _ => trivial).with_prefix) fun zs vs1 hzs => ?_
  · refine Tri.bind (tri_drawT f wp.coin v) fun cj v0 hv0 => ?_
    subst hv0
    exact tri_fresh_iff.2 fun r =>
      tri_pure_iff.2 ⟨cj, v0.length, ⟨by simp, by rw [getD_concat_length, List.length_ofFn]⟩, rfl⟩
  obtain ⟨hzs, hp1⟩ := hzs
  refine Tri.bind
    ((tri_chainT f sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1)
      depthReq hf Q.loc.shape Q.ann wq.sh embS embP 0 .first
    (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hwq.sh hC hF
    (hN.imp (fun h => by rw [← hzs.length_eq]; exact h) id) (fun z hz => by
      obtain ⟨x, -, cj, salt, hs, rfl⟩ := forall₂_mem_right hzs z hz
      exact hs.1) ⟨fun _ => rfl, fun h => h.elim⟩).with_prefix) fun out vs2 hout => ?_
  obtain ⟨⟨phE, t0s, n0s, e1, e0, e2, -, e4⟩, hp2⟩ := hout
  have e1' : out.2.trees = t0s := by simpa using e1
  have e0' : out.2.nons.reverse = n0s := by rw [e0]; simp
  have hbl : ∀ j, (out.1.map fun a => a.blocks).getD j [] =
      (out.1[j]?.map fun a => a.blocks).getD [] := fun j => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  refine Tri.bind
    (tri_finishAll f sMT sFS t Q H wq wp embS embP xin embE depthReq trees w hwq hloc hC hDe vs2
      (hext.mono (hp1.trans hp2)) (hextS.mono (hp1.trans hp2) hext) fl c0 out.2 phE
      (out.1.map fun acc => acc.c) e2 0 out.1
      (by rw [Nat.zero_add, ← e4.length_eq, ← hzs.length_eq]; exact hN') ?_)
    fun πs vs3 hπs => tri_pure_iff.2 ?_
  · intro k acc hk x cj hx
    obtain ⟨z, hz, hd⟩ := forall₂_getElem?_right e4 k acc hk
    obtain ⟨xo, hxo, cj', salt, hs, rfl⟩ := forall₂_getElem?_right hzs k z hz
    obtain ⟨d1, ⟨more, d2⟩, -, -, bls, tjs, nJ, d5, d6, d8, d7⟩ := hd
    have hx' : xo.map (fun x => (x, cj')) = some (x, cj) := d1.symm.trans hx
    obtain ⟨x', rfl, hx''⟩ := Option.map_eq_some_iff.1 hx'
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx''
    have d2' : acc.toks.headD 0 = salt := by rw [d2]; rfl
    refine ⟨hacc x' (List.mem_of_getElem? hxo),
      by simp [hk],
      by rw [d2', getD_of_prefix hp2 hs.1]; exact hs.2,
      fun rtreq hrt => ?_⟩
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
      obtain ⟨z, hz, hd⟩ := forall₂_getElem?_right e4 j _ (List.getElem?_eq_getElem hjl)
      obtain ⟨xo, hxo, cj', salt, hs', rfl⟩ := forall₂_getElem?_right hzs j z hz
      obtain rfl : xo = some x := Option.some.inj (hxo.symm.trans hxj)
      rw [show (out.1.map fun a => a.blocks).getD j [] =
          out.1[j].blocks by rw [hbl, List.getElem?_eq_getElem hjl]; rfl] at hw
      exact hs j out.1[j] x cj' (List.getElem?_eq_getElem hjl) hd.1 (by rwa [Nat.zero_add]) hw
    · have hjl : j < out.1.length := by
        rw [← hl]
        exact (List.getElem?_eq_some_iff.1 hπ).1
      rw [show (out.1.map fun a => a.blocks).getD j [] =
          out.1[j].blocks by rw [hbl, List.getElem?_eq_getElem hjl]; rfl] at hps
      obtain ⟨x, cj, hx, hE⟩ := hh j out.1[j] π (List.getElem?_eq_getElem hjl) hπ hps
      obtain ⟨z, hz, hd⟩ := forall₂_getElem?_right e4 j _ (List.getElem?_eq_getElem hjl)
      obtain ⟨xo, hxo, cj', salt, hs', rfl⟩ := forall₂_getElem?_right hzs j z hz
      have hx' : xo.map (fun x => (x, cj')) = some (x, cj) := hd.1.symm.trans hx
      obtain ⟨x', rfl, hx''⟩ := Option.map_eq_some_iff.1 hx'
      obtain ⟨rfl, -⟩ := Prod.mk.inj hx''
      exact ⟨x', hxo, hE⟩

/-- Without proof-of-work bits (`ProtocolQueryLayout.OK`), under the hypotheses below: every proof string of the
honest compiled prover is accepted. -/
theorem tri_proveB (hf : RealFam f) (hwq : wq.OK) (hloc : Q.loc.IsLocal) (hC : Q.ann.Coherent)
    (hF : Q.ann.Fmt) (hDe : wq.ext.depth ≤ wq.maxDepth) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (hN' : xs.length ≤ 2 ^ depthReq)
    (hacc : ∀ x, some x ∈ xs →
      ∀ c ρ, ρ ∉ H.one.withheld w x → Q.loc.accept x (H.ext w) ((H.one.strat w x c).run ρ).1 = true)
    (vs : List Bits) (hext : ExtOK f sMT wq.ext embE vs trees (H.ext w))
    (hextS : ExtSalt wq.ext vs sMT trees) :
    Tri f (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs fun πs _ =>
      πs.length = xs.length ∧
      ∀ (j : ℕ) (π : OneProtocolProof lam Q), πs[j]? = some (some π) →
        ∃ x,
          xs[j]? = some (some x) ∧
          EvalsTo f (verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq (trees.map TreeH.root) x π)
            true := by
  rw [proveB_eq]
  refine Tri.bind (tri_proveBX f sMT sFS t Q H wq wp embS embP xin embE depthReq trees w hf hwq.toG hloc hC hF hDe fl xs hN hN' (fun x hx c ρ hρ _ nJ n0 τ h1 h2 h3 => by
    rw [putB_ok _ _ _ hwq.sh] at h2
    rw [← hacc x hx c ρ hρ]
    exact hloc x _ _ τ _ (h1.trans (Strat.rho_run _ _).symm) h2 (fun _ _ => rfl) fun p _ => h3 p) vs hext hextS) fun o vs1 ho => tri_pure_iff.2 ?_
  exact ⟨ho.1, fun j π hπ => ho.2.2 j π hπ (pass_ok _ _ _ hwq.sh _)⟩

end Prove

/-! ## Part 4. The scheme: honest keys -/

theorem allLo_allLocal : ∀ s : Shape, AllLo s (RoundSplits.allLocal s)
  | [] => trivial
  | _ :: s => ⟨rfl, allLo_allLocal s⟩

section Scheme
variable {W : QueryLayout lam L} (WP : WireBP L) (p : Params) (fW : Fam (spec lam W.K L))

/-- the leaves of the tree over an encoding of the index i with the randomness r -/
def encLeaf (i : I) (r : L.EncodingRandomness) : ℕ → Body L × Bool :=
  fun j => if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true) else (none, false)

/-- The prover keeps the tree of a node correctly. -/
def NodeOK (vs : List Bits) (i : I) (nd : Node lam L) : Prop :=
  TreeOK fW p.sMT vs nd.tree W.depth (encLeaf i nd.r)

theorem tri_nodeP' (i : I) (vs : List Bits) :
    Tri fW (nodeP' W WP p i) vs fun nd vs' => NodeOK p fW vs' i nd := by
  refine Tri.bind (tri_drawT fW WP.ri vs) fun r vs0 _ => ?_
  exact Tri.bind (tri_commitE fW p.sMT W.depth (encLeaf i r) vs0) fun t vs1 ht => tri_pure_iff.2 ht

theorem encLeaf_val (i : I) (r : L.EncodingRandomness) (q : Fin L.wordLength) :
    (encLeaf i r q.val).1 = some (.inl (L.encodeIndex i r q)) := by
  simp [encLeaf, q.isLt]

variable {p fW}

theorem extOK_T (hW : W.OKG) (hwd : L.Wired) {vs : List Bits} {i : I}
    {nd : Node lam L} (h : NodeOK p fW vs i nd) :
    ExtOK fW p.sMT W.T.ext (fun s => some (.inl s)) vs [nd.tree] (L.honestOfflineProver.ext (i, nd.r)) := fun q => by
  obtain ⟨h1, h2⟩ := hW.extT q
  refine ⟨by rw [h1]; exact Nat.one_pos,
    by rw [h2, hW.extDepth.1]; exact lt_of_lt_of_le q.isLt hW.fits, encLeaf i nd.r, ?_, ?_⟩
  · rw [h1, hW.extDepth.1]; exact h
  · rw [h2, hwd.extT, encLeaf_val]

theorem extOK_B (hW : W.OKG) (hwd : L.Wired) {vs : List Bits} {i : I}
    {nd : Node lam L} (h : NodeOK p fW vs i nd) :
    ExtOK fW p.sMT W.B.ext (fun s => some (.inl s)) vs [nd.tree] (L.honestOnlineBatchProver.ext (i, nd.r)) := fun q => by
  obtain ⟨h1, h2⟩ := hW.extB q
  refine ⟨by rw [h1]; exact Nat.one_pos,
    by rw [h2, hW.extDepth.2.2]; exact lt_of_lt_of_le q.isLt hW.fits, encLeaf i nd.r, ?_, ?_⟩
  · rw [h1, hW.extDepth.2.2]; exact h
  · rw [h2, hwd.extB, encLeaf_val]

theorem extOK_L (hW : W.OKG) (hwd : L.Wired) {vs : List Bits} {i : I} {root nd : Node lam L}
    (h0 : NodeOK p fW vs i root) (h : NodeOK p fW vs i nd) :
    ExtOK fW p.sMT W.Lk.ext (fun s => some (.inl s)) vs [root.tree, nd.tree]
      (L.honestLinkProver.ext (i, root.r, nd.r)) := fun q => by
  cases q with
  | inl q =>
    obtain ⟨h1, h2⟩ := hW.extL.1 q
    refine ⟨by rw [h1]; exact Nat.succ_pos _,
      by rw [h2, hW.extDepth.2.1]; exact lt_of_lt_of_le q.isLt hW.fits, encLeaf i root.r, ?_, ?_⟩
    · rw [h1, hW.extDepth.2.1]; exact h0
    · rw [h2, hwd.extL, encLeaf_val]; rfl
  | inr q =>
    obtain ⟨h1, h2⟩ := hW.extL.2 q
    refine ⟨by rw [h1]; exact Nat.lt_succ_self _,
      by rw [h2, hW.extDepth.2.1]; exact lt_of_lt_of_le q.isLt hW.fits, encLeaf i nd.r, ?_, ?_⟩
    · rw [h1, hW.extDepth.2.1]; exact h
    · rw [h2, hwd.extL, encLeaf_val]; rfl

variable (p fW)
variable {Ryes Rno : I → X → Prop} {M : LH.Nums}

theorem encLeaf_salted (i : I) (r : L.EncodingRandomness) (q : Fin L.wordLength) : (encLeaf i r q.val).2 = true := by
  simp [encLeaf, q.isLt]

theorem NodeOK.salt_at (hW : W.OKG) {vs : List Bits} {i : I} {nd : Node lam L}
    (h : NodeOK p fW vs i nd) (q : Fin L.wordLength) :
    (saltVal vs (nd.tree.salts.getD q.val none)).length = p.sMT :=
  h.2.2.1 q.val (lt_of_lt_of_le q.isLt hW.fits) (encLeaf_salted i nd.r q)

theorem extSalt_T (hW : W.OKG) {vs : List Bits} {i : I}
    {nd : Node lam L} (h : NodeOK p fW vs i nd) :
    ExtSalt W.T.ext vs p.sMT [nd.tree] := fun q => by
  obtain ⟨h1, h2⟩ := hW.extT q
  rw [h1, h2]
  exact NodeOK.salt_at p fW hW h q

theorem extSalt_B (hW : W.OKG) {vs : List Bits} {i : I}
    {nd : Node lam L} (h : NodeOK p fW vs i nd) :
    ExtSalt W.B.ext vs p.sMT [nd.tree] := fun q => by
  obtain ⟨h1, h2⟩ := hW.extB q
  rw [h1, h2]
  exact NodeOK.salt_at p fW hW h q

theorem extSalt_L (hW : W.OKG) {vs : List Bits} {i : I} {root nd : Node lam L}
    (h0 : NodeOK p fW vs i root) (h : NodeOK p fW vs i nd) :
    ExtSalt W.Lk.ext vs p.sMT [root.tree, nd.tree] := fun q => by
  cases q with
  | inl q =>
    obtain ⟨h1, h2⟩ := hW.extL.1 q
    rw [h1, h2]
    exact NodeOK.salt_at p fW hW h0 q
  | inr q =>
    obtain ⟨h1, h2⟩ := hW.extL.2 q
    rw [h1, h2]
    exact NodeOK.salt_at p fW hW h q

theorem headD_eq_some {β : Type} {l : List (Option β)} {b : β} (h : l.headD none = some b) :
    l[0]? = some (some b) := by
  cases l with
  | nil => cases h
  | cons a t => exact congrArg some h

/-- Under the hypotheses below: Test's proof string, unless it is `none`, is accepted. -/
theorem tri_proveT (hf : RealFam fW) (hL : L.Props Ryes Rno M) (hW : W.OK) {i : I} {vs : List Bits}
    {root : Node lam L} (hr : NodeOK p fW vs i root) :
    Tri fW (proveT W WP p root.tree i root.r) vs fun o _ =>
      ∀ π, o = some π → EvalsTo fW (vTS W p.sMT p.sFS root.tree.root π) true := by
  refine Tri.bind
    (tri_proveB fW p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver)
      W.T WP.T _ id (fun _ => none) (fun s => some (.inl s)) W.depthReq [root.tree]
      (i, root.r) hf hW.T hL.localT (BatchOne.BAnn.allLocal_coherent _) (RoundSplits.fmt_allLocal _)
      (by rw [hW.extDepth.1]; exact hW.depthT) (fun _ => true) [some ()]
      (Or.inr (allLo_allLocal _)) (Nat.one_le_two_pow)
      (fun x _ c ρ hρ => (BatchOne.acc_one_iff L.honestOfflineProver _).2 hL.complete.accT _ x c ρ trivial hρ)
      vs (extOK_T hW.toG hL.wired hr) (extSalt_T p fW hW.toG hr))
    fun l vs1 hl => tri_pure_iff.2 ?_
  intro π hπ
  obtain ⟨x, -, hE⟩ := hl.2 0 π (headD_eq_some hπ)
  exact hE

/-- Under the hypotheses below: Link's proof string, unless it is `none`, is accepted. -/
theorem tri_proveLk (hf : RealFam fW) (hL : L.Props Ryes Rno M) (hW : W.OK) {i : I} {vs : List Bits}
    {root nd : Node lam L} (hr : NodeOK p fW vs i root) (hn : NodeOK p fW vs i nd) :
    Tri fW (proveLk W WP p root.tree nd.tree i root.r nd.r) vs fun o _ =>
      ∀ π, o = some π → EvalsTo fW (vLS W p.sMT p.sFS root.tree.root nd.tree.root π) true := by
  refine Tri.bind
    (tri_proveB fW p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver)
      W.Lk WP.Lk _ id (fun _ => none) (fun s => some (.inl s)) W.depthReq [root.tree, nd.tree]
      (i, root.r, nd.r) hf hW.Lk hL.localL (BatchOne.BAnn.allLocal_coherent _)
      (RoundSplits.fmt_allLocal _) (by rw [hW.extDepth.2.1]; exact hW.depthL) (fun _ => true)
      [some ()] (Or.inr (allLo_allLocal _)) (Nat.one_le_two_pow)
      (fun x _ c ρ hρ => (BatchOne.acc_one_iff L.honestLinkProver _).2 hL.complete.accL _ x c ρ trivial hρ)
      vs (extOK_L hW.toG hL.wired hr hn) (extSalt_L p fW hW.toG hr hn))
    fun l vs1 hl => tri_pure_iff.2 ?_
  intro π hπ
  obtain ⟨x, -, hE⟩ := hl.2 0 π (headD_eq_some hπ)
  exact hE



theorem getElem?_slotsOfReq {N : ℕ} (σ : Equiv.Perm (Fin N)) (xs : List X) (a : Fin N) :
    (slotsOfReq σ xs)[(σ a).val]? = some xs[a.val]? := by
  unfold slotsOfReq
  rw [List.getElem?_map, List.getElem?_eq_getElem (by simp), List.getElem_finRange]
  simp

/-- Under the hypotheses below: V accepts if the field leaf is the number of a copy and its three
verifiers accept. -/
theorem evalsTo_V {v : IVK lam L} {x : X} {π : Prf lam L}
    {πT : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline)} {πL : OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)}
    {πB : OneProtocolProof lam L.onlineBatch} (hT : v.piT = some πT) (hLk : π.piL = some πL) (hB : π.piB = some πB)
    (hleaf : π.leaf ≤ p.M) (h1 : EvalsTo fW (vTS W p.sMT p.sFS v.cm πT) true)
    (h2 : EvalsTo fW (vLS W p.sMT p.sFS v.cm π.cm πL) true)
    (h3 : EvalsTo fW (vBS W p.sMT p.sFS π.cm x πB) true) :
    EvalsTo fW (V W p v x π) true := by
  unfold V
  simp only [hT, hLk, hB, if_pos hleaf]
  refine (evaluates_eager fW).bind h1 ?_
  refine (evaluates_eager fW).bind h2 ?_
  refine (evaluates_eager fW).bind h3 ?_
  exact (evaluates_eager fW).pure _

/-! ### The same for wire records that may have proof-of-work bits, on the programs that also output
the hash blocks (Compile/Batch/StarX.lean) -/

omit fW in
/-- not bad: the verifier randomness is not withheld, and all its proof-of-work bits are 0 -/
theorem badAt_false_iff {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (w : Wt)
    (x : Y) (n : ℕ) (bss : List (List (Blk lam K))) :
    Ref.badAt Q H wq wp w x n bss = false ↔
    rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n []) ∉ H.one.withheld w x ∧
    RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n [])) = true := by
  unfold Ref.badAt Ref.noneAt
  rw [Bool.or_eq_false_iff, Bool.not_eq_false', decide_eq_false_iff_not]

omit fW in
theorem headD_of_getElem? {β : Type} {l : List (Option β)} {b : β} (h : l[0]? = some (some b)) :
    l.headD none = some b := by
  cases l with
  | nil => simp at h
  | cons a _ => simpa using h

/-- Under the hypotheses below: Test has a proof string, which is accepted, unless it is bad. -/
theorem tri_proveTX (hf : RealFam fW) (hL : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitB W Ryes) {i : I} {vs : List Bits} {root : Node lam L} (hr : NodeOK p fW vs i root) :
    Tri fW (proveTX W WP p root.tree i root.r) vs fun o _ =>
      Ref.badAt (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T (i, root.r) () 0 o.2 =
        false →
      ∃ π, o.1 = some π ∧ EvalsTo fW (vTS W p.sMT p.sFS root.tree.root π) true := by
  refine Tri.bind
    (tri_proveBX fW p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T
      WP.T _ id (fun _ => none) (fun s => some (.inl s)) W.depthReq [root.tree] (i, root.r) hf hW.T
      hL.localT (BatchOne.BAnn.allLocal_coherent _) (RoundSplits.fmt_allLocal _)
      (by rw [hW.extDepth.1]; exact hW.depthT) (fun _ => true) [some ()] (Or.inr (allLo_allLocal _))
      (Nat.one_le_two_pow) (fun x _ c ρ hρ hps => hG.T.acc _ x c ρ trivial hρ hps) vs
      (extOK_T hW hL.wired hr) (extSalt_T p fW hW hr))
    fun l vs1 hl => tri_pure_iff.2 ?_
  intro hb
  obtain ⟨hnw, hps⟩ := (badAt_false_iff _ _ _ _ _ _ _ _).1 hb
  obtain ⟨π, hπ⟩ := hl.2.1 0 () rfl rfl hnw
  obtain ⟨x, -, hE⟩ := hl.2.2 0 π hπ hps
  exact ⟨π, headD_of_getElem? hπ, hE⟩

/-- Under the hypotheses below: Link has a proof string, which is accepted, unless it is bad. -/
theorem tri_proveLkX (hf : RealFam fW) (hL : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitB W Ryes) {i : I} {vs : List Bits} {root nd : Node lam L}
    (hr : NodeOK p fW vs i root) (hn : NodeOK p fW vs i nd) :
    Tri fW (proveLkX W WP p root.tree nd.tree i root.r nd.r) vs fun o _ =>
      Ref.badAt (BatchInteractiveOracleProof.ofProto L.link)
          (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk (i, root.r, nd.r) () 0 o.2 = false →
      ∃ π, o.1 = some π ∧ EvalsTo fW (vLS W p.sMT p.sFS root.tree.root nd.tree.root π) true := by
  refine Tri.bind
    (tri_proveBX fW p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver)
      W.Lk WP.Lk _ id (fun _ => none) (fun s => some (.inl s)) W.depthReq [root.tree, nd.tree]
      (i, root.r, nd.r) hf hW.Lk hL.localL (BatchOne.BAnn.allLocal_coherent _)
      (RoundSplits.fmt_allLocal _) (by rw [hW.extDepth.2.1]; exact hW.depthL) (fun _ => true) [some ()]
      (Or.inr (allLo_allLocal _)) (Nat.one_le_two_pow)
      (fun x _ c ρ hρ hps => hG.Lk.acc _ x c ρ trivial hρ hps) vs (extOK_L hW hL.wired hr hn)
      (extSalt_L p fW hW hr hn))
    fun l vs1 hl => tri_pure_iff.2 ?_
  intro hb
  obtain ⟨hnw, hps⟩ := (badAt_false_iff _ _ _ _ _ _ _ _).1 hb
  obtain ⟨π, hπ⟩ := hl.2.1 0 () rfl rfl hnw
  obtain ⟨x, -, hE⟩ := hl.2.2 0 π hπ hps
  exact ⟨π, headD_of_getElem? hπ, hE⟩

/-- the record of a copy is correct: its node satisfies `NodeOK`, and its Link has a proof string,
which is accepted, unless it is bad; bss: the hash blocks of its Link -/
def LeafOKX (vs : List Bits) (i : I) (r₀ : L.EncodingRandomness) (cm : Dig lam)
    (lf : LeafRec lam L) (bss : List (List (Blk lam W.K))) : Prop :=
  NodeOK p fW vs i lf.node ∧
  (Ref.badAt (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
        (i, r₀, lf.node.r) () 0 bss = false →
    ∃ π, lf.piL = some π ∧ EvalsTo fW (vLS W p.sMT p.sFS cm lf.node.tree.root π) true)

/-- An honest key, relative to a store, with the hash blocks that the committer has seen. -/
structure KeyOKX (vs : List Bits) (i : I) (v : IVK lam L) (k : IskH lam L) (xc : XC lam W.K) :
    Prop where
  idx : k.i = i
  test : Ref.badAt (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
        (i, k.root.r) () 0 xc.1 = false →
    ∃ π, v.piT = some π ∧ EvalsTo fW (vTS W p.sMT p.sFS v.cm π) true
  leaves : ∀ j lf, k.leaves[j]? = some lf → LeafOKX WP p fW vs i k.root.r v.cm lf (xc.2.getD j [])
  len : k.leaves.length = p.M + 1

theorem tri_leavesCX (hf : RealFam fW) (hL : L.PropsNoAcc Ryes Rno M) (hW : W.OKG)
    (hG : GrFitB W Ryes) (i : I) (root : Node lam L) : ∀ (n : ℕ) (vs : List Bits),
    NodeOK p fW vs i root → Tri fW (leavesCX W WP p i root n) vs fun ls vs' =>
      ls.1.length = n ∧
      ∀ j lf, ls.1[j]? = some lf → LeafOKX WP p fW vs' i root.r root.tree.root lf (ls.2.getD j [])
  | 0, _, _ => tri_pure_iff.2 ⟨rfl, fun _ _ h => by simp at h⟩
  | n + 1, vs, h0 => by
      refine Tri.bind (tri_nodeP' WP p fW i vs).with_prefix fun nd vs1 hnd => ?_
      refine Tri.bind (tri_proveLkX WP p fW hf hL hW hG (h0.mono hnd.2) hnd.1).with_prefix
        fun π vs2 hπ => ?_
      refine Tri.bind
        (tri_leavesCX hf hL hW hG i root n vs2 (h0.mono (hnd.2.trans hπ.2))).with_prefix
        fun rest vs3 hrest => tri_pure_iff.2 ⟨by simp [hrest.1.1], fun j lf hlf => ?_⟩
      cases j with
      | zero =>
        obtain rfl : (⟨nd, π.1⟩ : LeafRec lam L) = lf := by simpa using hlf
        exact ⟨hnd.1.mono (hπ.2.trans hrest.2), hπ.1⟩
      | succ j => exact hrest.1.2 j lf (by simpa using hlf)

theorem tri_CpX (hf : RealFam fW) (hL : L.PropsNoAcc Ryes Rno M) (hW : W.OKG) (hG : GrFitB W Ryes)
    (i : I) (vs : List Bits) :
    Tri fW (CpX W WP p i) vs fun o vs' => KeyOKX WP p fW vs' i o.1.1 o.1.2 o.2 := by
  refine Tri.bind (tri_nodeP' WP p fW i vs) fun root vs1 hroot => ?_
  refine Tri.bind (tri_proveTX WP p fW hf hL hW hG hroot).with_prefix fun πT vs2 hπ => ?_
  refine Tri.bind (tri_leavesCX WP p fW hf hL hW hG i root (p.M + 1) vs2 (hroot.mono hπ.2))
    fun ls vs3 hls => tri_pure_iff.2 ?_
  exact ⟨rfl, hπ.1, hls.2, hls.1⟩

omit fW in
theorem slotFlags_true {N : ℕ} (σ : Equiv.Perm (Fin N)) (s : Fin N) :
    slotFlags σ (fun _ => true) s.val = true := by
  unfold slotFlags
  rw [dif_pos s.isLt]

end Scheme

theorem fitLen_val {β : Type} (d : β) (n : ℕ) (l : List β) (h : l.length = n) :
    (fitLen d n l).val = l := by
  show (l ++ List.replicate n d).take n = l
  exact List.take_left' h

theorem realFam_realF {K : ℕ} (f : Fam (spec lam K L)) : RealFam (realF f) := fun _ _ _ => rfl

/-- V never queries a ghost name (`noGhost_V`, Compile/Batch/GhostGuards.lean): so it does not see
how the ghost names are answered. Its run under `realF f` is its run under f. -/
theorem runEager_V_real {W : QueryLayout lam L} (p : Params) (f : Fam (spec lam W.K L)) (v : IVK lam L)
    (x : X) (π : Prf lam L) :
    (V W p v x π).runEager (realF f) = (V W p v x π).runEager f := by
  rw [← realQ_eager, realQ_of_noGhost _ (noGhost_V ..)]

/-- what `realQ c`, c with the ghost names written back, outputs under f, the algorithm c itself
outputs under realF f -/
theorem outs_realQ {K : ℕ} {α : Type} {f : Fam (spec lam K L)} {c : TypedOracleComputation lam K L α}
    {a : α} (h : a ∈ Outs f (realQ c)) : a ∈ Outs (realF f) c := by
  unfold Outs at h ⊢
  rwa [realQ_eager] at h


end Compile.Batch.Cmpl

