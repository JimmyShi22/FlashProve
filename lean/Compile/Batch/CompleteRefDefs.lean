-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteRefDefs.lean: the hash work of the honest compiled prover, without tokens.
Definitions (words of this library: lean/GLOSSARY.md). Towards completeness of the compiled scheme
whose rounds may have proof-of-work bits.

The programs of Compile/Batch/TokTree.lean, Compile/Batch/Prover.lean and Compile/Batch/Star.lean
are programs with tokens, and a token is a position in a store; so what a program does depends, as a
term, on the store's length. Here the same hash work is written as ordinary oracle algorithms on
strings: no store, no openings, no proof strings; the result is, for each slot, the list of the hash
blocks of the Fiat-Shamir answers that it has seen (in a shared round without a format: the zero
block `blk0`), from which its verifier randomness is made (`rhoOf`). (F1) to (F5) are the query
formats, the constructors of `Head` (Compile/Batch/Oracles.lean).

  `freshO`, `leafO`, `rootO`  a salted leaf, the root of a tree over a prover message (`commitT`)
  `rootOO`  the same for a component that may have no tree (`withTree`)
  `rootEO`  the root of a tree over an encoded index (`commitE`)
  `VSlot`, `PhO`  a slot and the phase, with strings in the place of tokens
  `slotLoO`, `slotJoinO`, `reqRootO`, `hearO`, `chainO`  the rounds (`slotLo`, `slotJoin`, `reqT`,
                                                         `hear`, `chainT`), in the same order
  `initO`, `proveO`  one execution (`initSlot`, `proveB`)
  `noneAt`, `badAt`  is the proof string of a slot `none`; is it `none`, or has a search failed
                     ("bad")
  `nodeO`, `RT`, `RL`  two small experiments: a fresh node and its Test; two fresh nodes and their
                       Link

What they are for (the statements are not in this file): for every fixed family of oracle functions,
the honest run shows "bad" in a given place with the distribution of the small experiment
(`Spec.lawTUG`, `Spec.lawLUG`, Compile/Batch/SpecCompleteUG.lean, for the run `runAllBUX`; for the
committer of `argB` alone, at families with `RealFam`: `law_CpX_test`, `law_CpX_link`,
Compile/Batch/CompleteRefStarG.lean); under lazily sampled oracles, under `RoundsQueryLayout.OKG` and further
hypotheses, the verifier randomness of any one slot is exactly uniform, except for the proof-of-work
bits (`blocks_proveOG`, `zero_ublkG`, Compile/Batch/CompleteUnif.lean).
-/
import Compile.Batch.Star
import Rom.Bridge

noncomputable section

namespace Compile.Batch.Ref
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Trees -/

/-- the string of l bits that stands for a number below 2^l, as `erase` (Compile/Star.lean) makes it
-/
def bitsOf (l : ℕ) (r : Fin (2 ^ l - 1 + 1)) : Bits := List.ofFn fun i : Fin l => r.val.testBit i

/-- a fresh string of l bits -/
def freshO (l : ℕ) : TypedOracleComputation lam K L Bits := OComp.sample (2 ^ l - 1) fun r => OComp.pure (bitsOf l r)

/-- uniform choice from an enumerated type, if its `Enum` has `Enum.OK` (Iop/Wire.lean) -/
def drawO {β : Type} (e : Enum β) : TypedOracleComputation lam K L β := OComp.sample e.n fun r => OComp.pure (e.e r)

/-- do g on each entry, in order -/
def eachO {σ τ : Type} (g : σ → TypedOracleComputation lam K L τ) : List σ → TypedOracleComputation lam K L (List τ)
  | [] => OComp.pure []
  | a :: t => (g a).bind fun b => (eachO g t).bind fun r => OComp.pure (b :: r)

/-- the digest of a salted leaf -/
def leafO (sMT : ℕ) (b : Body L) : TypedOracleComputation lam K L (Dig lam) :=
  (freshO sMT).bind fun s => askTypedOracle (L := L) (K := K) OracleName.leaf (⟨b, s⟩ : LeafIn L)

/-- the root of the tree over 2^d salted leaves -/
def rootO (sMT d : ℕ) (leaf : ℕ → Body L) : TypedOracleComputation lam K L (Dig lam) :=
  (eachO (leafO sMT) ((List.range (2 ^ d)).map leaf)).bind fun ds =>
  (levelsM (hashTreeNode (L := L) (K := K)) d ds).bind fun lv => OComp.pure (rootOf lv)

/-- the root of the tree over a component, if it has a tree -/
def rootOO (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → Body L) : TypedOracleComputation lam K L (Option (Dig lam)) :=
  match has with
  | true => (rootO sMT d leaf).bind fun rt => OComp.pure (some rt)
  | false => OComp.pure none

/-- The roots of the trees over a component with a list of trees, one after the other, in the order
of `withTrees` (Compile/Batch/Prover.lean). The form of `rootOO` for a list of trees
(`rootsOO_ite`). -/
def rootsOO (sMT : ℕ) : List ℕ → (ℕ → ℕ → Body L) → TypedOracleComputation lam K L (List (Dig lam))
  | [], _ => OComp.pure []
  | d :: ds, leaf =>
    (rootO sMT d (leaf 0)).bind fun rt =>
      (rootsOO sMT ds fun n => leaf (n + 1)).bind fun rts => OComp.pure (rt :: rts)

theorem rootsOO_nil (sMT : ℕ) (leaf : ℕ → ℕ → Body L) :
    rootsOO (lam := lam) (K := K) sMT [] leaf = OComp.pure [] := rfl

/-- one tree: its root (`rootO`), in a list -/
theorem rootsOO_one (sMT d : ℕ) (leaf : ℕ → ℕ → Body L) :
    rootsOO (lam := lam) (K := K) sMT [d] leaf =
      (rootO sMT d (leaf 0)).bind fun rt => OComp.pure [rt] := rfl

/-- a component that has its one tree, or none: the root that `rootOO` gives, as a list -/
theorem rootsOO_ite (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → ℕ → Body L) :
    rootsOO (lam := lam) (K := K) sMT (if has then [d] else []) leaf =
      (rootOO sMT has d (leaf 0)).bind fun o => OComp.pure o.toList := by
  cases has with
  | false => rfl
  | true =>
    exact (OComp.bind_assoc (rootO sMT d (leaf 0)) (fun rt => OComp.pure (some rt))
      fun o => OComp.pure o.toList).symm

/-- the digest of a leaf of a tree over an encoded index: salted, or padding -/
def leafEO (sMT : ℕ) (x : Body L × Bool) : TypedOracleComputation lam K L (Dig lam) :=
  if x.2 then leafO sMT x.1 else askTypedOracle (L := L) (K := K) OracleName.leaf (⟨x.1, []⟩ : LeafIn L)

/-- the root of a tree over an encoded index -/
def rootEO (sMT d : ℕ) (leaf : ℕ → Body L × Bool) : TypedOracleComputation lam K L (Dig lam) :=
  (eachO (leafEO sMT) ((List.range (2 ^ d)).map leaf)).bind fun ds =>
  (levelsM (hashTreeNode (L := L) (K := K)) d ds).bind fun lv => OComp.pure (rootOf lv)

/-- the root of the request tree over the slot values cs -/
def reqRootO (depthReq : ℕ) (cs : List Bits) : TypedOracleComputation lam K L (Dig lam) :=
  (eachO (fun c => askTypedOracle (L := L) (K := K) OracleName.rleaf c) cs).bind fun ls =>
  (levelsM (rnodeV (L := L) (K := K)) depthReq ls).bind fun lv => OComp.pure (rootOf lv)

/-! ## Slots and phases -/

/-- a slot: what is left of its strategy; its whole instance, if it has one; the string that the
next query of its chain holds; its slot value (the empty string before the chains have joined); the
hash blocks that it has seen -/
structure VSlot (lam K : ℕ) (X : Type) (s : Shape) where
  st : Strat s Unit
  x : Option X
  tk : Bits
  c : Bits
  blocks : List (Blk lam K)

inductive PhO
  | first
  | loc
  | shr (ρ0 : Bits)
  | aft

def PhO.afterLo : PhO → PhO
  | .first => .loc
  | .loc => .loc
  | .shr _ => .aft
  | .aft => .aft

/-- the header of the Fiat-Shamir query of a slot in the local round i: as in the prover, (F1) holds
L.early x and (F2) holds x in the round L.late -/
def headO (L : BatchProtocol I X) {s : Shape} (cms : List (Dig lam)) (i : ℕ) :
    PhO → VSlot lam K X s → Head lam X
  | .first, v => .f1 cms (v.x.map L.early) v.tk
  | .loc, v => .f2 (lateInstancePart L i v.x) v.tk
  | .shr ρ0, v => .f3 ρ0 v.c
  | .aft, v => .f2 (lateInstancePart L i v.x) v.tk

/-- The search over nonces (Compile/Batch/Prover.lean: fbW, fbTG), on strings and with the oracle fb
t itself: the queries q j, q (j + 1), .. to fb t, at most n + 1 of them, until the proof-of-work
check is passed; the answer of the final attempt -/
def askW {C P : Type} (g : GrW C P) (chal : Blk lam K → C) (t : Tag) (q : ℕ → FbIn lam L t) :
    ℕ → ℕ → TypedOracleComputation lam K L ((Fin K → Dig lam) × Dig lam)
  | 0, j => askTypedOracle (L := L) (K := K) (OracleName.fb t) (q j)
  | n + 1, j =>
    (askTypedOracle (L := L) (K := K) (OracleName.fb t) (q j)).bind fun ans =>
      if g.ok (chal ans.1) then OComp.pure ans else askW g chal t q n (j + 1)

/-- a Fiat-Shamir query, with proof-of-work bits or without (Compile/Batch/Prover.lean: fbG); q α is
the query with the plain part α -/
def askG {C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag)
    (q : P → FbIn lam L t) (α : P) :
    TypedOracleComputation lam K L ((Fin K → Dig lam) × Dig lam) :=
  match gr with
  | none => askTypedOracle (L := L) (K := K) (OracleName.fb t) (q α)
  | some g => askW g chal t (fun j => q (g.put j α)) g.more 0

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam))

/-- a local round, in one slot -/
def slotLoO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhO) (v : VSlot lam K X (r :: s)) : TypedOracleComputation lam K L (VSlot lam K X s) :=
  (rootOO sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb v.st.1.1)).bind fun rt =>
  (askG w.grJ w.chal t (fun α => (⟨i, headO L cms i ph v, rt, plJ α⟩ : FbIn lam L t))
      (a.plain v.st.1.2).2).bind fun ans =>
  OComp.pure ⟨v.st.2 (w.chal ans.1), v.x, List.ofFn ans.2, v.c, v.blocks ++ [ans.1]⟩

/-- the joining round, in one slot -/
def slotJoinO {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (v : VSlot lam K X (r :: s)) :
    TypedOracleComputation lam K L (VSlot lam K X (r :: s)) :=
  (rootOO sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb v.st.1.1)).bind fun rt =>
  (askTypedOracle (L := L) (K := K) (OracleName.g t)
      (⟨i, v.tk, rt, plJ (a.plain v.st.1.2).2⟩ : JoiningRoundQuery lam L t)).bind fun c =>
  OComp.pure ⟨v.st, v.x, v.tk, List.ofFn c, v.blocks⟩

/-- a slot receives a shared verifier message -/
def hearO {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a)
    (bl : Blk lam K) (v : VSlot lam K X (r :: s)) : VSlot lam K X s :=
  ⟨v.st.2 (w.chal bl), v.x, v.tk, v.c, v.blocks ++ [bl]⟩

/-- the root of the tree over the shared component, if it has a tree -/
def root0O {r : Round} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0) : TypedOracleComputation lam K L (Option (Dig lam)) :=
  rootOO sMT w.has0 w.depth0 (bodyAt w.posAt0 emb (a.join m0 (a.split (r.dOrc, r.dPlain)).2).1)

/-- All chains of a batch: for each slot the hash blocks that it has seen. -/
def chainO (depthReq : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → PhO → SStrat s A →
    List (VSlot lam K X s) → TypedOracleComputation lam K L (List (List (Blk lam K)))
  | [], _, _, _, _, _, _, _, vs => OComp.pure (vs.map fun v => v.blocks)
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), vs =>
      match a.kind, ph with
      | .lo, ph =>
          (eachO
              (slotLoO sMT t cms a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
              vs).bind fun vs' =>
          chainO depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph.afterLo
            (k0 (a.kind.shOf (w.chal (blk0 lam K)))) vs'
      | .sh, .loc =>
          (eachO (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i)
              vs).bind fun vs1 =>
          (reqRootO depthReq (vs1.map fun v => v.c)).bind fun rq =>
          (root0O sMT a w (fun p => embS (.inl p)) m0).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f4 cms (List.ofFn rq), rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 m0)).bind fun ans =>
          chainO depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            (.shr (List.ofFn ans.2)) (k0 (a.kind.shOf (w.chal ans.1))) (vs1.map (hearO w ans.1))
      | .sh, .shr ρ0 =>
          (root0O sMT a w (fun p => embS (.inl p)) m0).bind fun rt0 =>
          (askG w.gr0 w.chal t
              (fun α => (⟨i, .f5 ρ0, rt0, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.pl0 m0)).bind fun ans =>
          chainO depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            (.shr (List.ofFn ans.2)) (k0 (a.kind.shOf (w.chal ans.1))) (vs.map (hearO w ans.1))
      | .sh, ph =>
          chainO depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph
            (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (vs.map (hearO w (blk0 lam K)))

end Rounds

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (cms : List (Dig lam)) (w : Wt)

/-- a slot at the start -/
def initO (c0 : H.Coin0) (x : Option Y) : TypedOracleComputation lam K L (VSlot lam K X Q.loc.shape) :=
  (drawO wp.coin).bind fun cj => (freshO sFS).bind fun salt =>
  OComp.pure ⟨match x with
    | some x => H.one.strat w x (c0, cj)
    | none => Strat.dflt Q.loc.shape (), x.bind xin, salt, [], []⟩

/-- One execution of the protocol: for each slot the hash blocks that it has seen. cms are the roots
of the external trees. -/
def proveO (xs : List (Option Y)) : TypedOracleComputation lam K L (List (List (Blk lam K))) :=
  (drawO wp.coin0).bind fun c0 =>
  (eachO (initO sFS Q H wp xin w c0) xs).bind fun vs =>
  chainO sMT t cms depthReq Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) vs

/-- Is the proof string of slot number n, which holds x, `none`: is its verifier randomness in the
withheld set. -/
def noneAt (x : Y) (n : ℕ) (bss : List (List (Blk lam K))) : Bool :=
  @decide (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n []) ∈ H.one.withheld w x) (wp.decW w x _)

/-- Is the proof string of slot number n `none`, or has a search over nonces of its transcript
failed, in this sense: some proof-of-work bit of its verifier randomness is 1. Without proof-of-work
bits: noneAt. -/
def badAt (x : Y) (n : ℕ) (bss : List (List (Blk lam K))) : Bool :=
  noneAt Q H wq wp w x n bss ||
    !RoundsQueryLayout.pass Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh (bss.getD n []))

end Prove

/-! ## The two small experiments -/

section Scheme
variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I)

/-- the leaves of the tree over an encoding of the index i with the randomness r -/
def encLeaf (i : I) (r : L.EncodingRandomness) : ℕ → Body L × Bool :=
  fun j => if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true) else (none, false)

/-- a fresh encoding of i and the root of its tree -/
def nodeO : TypedOracleComputation lam W.K L (L.EncodingRandomness × Dig lam) :=
  (drawO WP.ri).bind fun r => (rootEO p.sMT W.depth (encLeaf i r)).bind fun cm => OComp.pure (r, cm)

/-- is Test's proof string on a node `none`, or has one of its searches failed -/
def testO (nd : L.EncodingRandomness × Dig lam) : TypedOracleComputation lam W.K L Bool :=
  (proveO p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
      (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [nd.2]
      (i, nd.1) [some ()]).bind fun bss =>
  OComp.pure (badAt (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T (i, nd.1) () 0 bss)

/-- is the proof string of the Link from a node to another `none`, or has one of its searches failed
-/
def linkO (nd0 nd : L.EncodingRandomness × Dig lam) : TypedOracleComputation lam W.K L Bool :=
  (proveO p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
      (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [nd0.2, nd.2]
      (i, nd0.1, nd.1) [some ()]).bind fun bss =>
  OComp.pure (badAt (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
    (i, nd0.1, nd.1) () 0 bss)

/-- a fresh node and its Test -/
def RT : TypedOracleComputation lam W.K L Bool := (nodeO W WP p i).bind (testO W WP p i)
/-- two fresh nodes and the Link from the first to the second -/
def RL : TypedOracleComputation lam W.K L Bool :=
  (nodeO W WP p i).bind fun nd0 => (nodeO W WP p i).bind (linkO W WP p i nd0)

end Scheme

end Compile.Batch.Ref
