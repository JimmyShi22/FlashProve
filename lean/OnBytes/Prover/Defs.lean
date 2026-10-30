-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Prover/Defs.lean: the compiled PROVER of one slot of a batch protocol, for the compiler's
verifier side in OnBytes/TypedOracleCompiler/. Definitions only.

The verifier there (`verifyOneProtocol`, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) is given a proof
string (`OneProtocolProof`). Here is a program that makes one. It plays an interactive strategy σ against
verifier messages that it draws from the oracles as the verifier will: round by round it takes σ's
message, builds the hash trees over what is sent, and asks the verifier's own Fiat-Shamir queries;
in a round with a test (proof of work) it tries nonces until all test bits are 0; at the joining
round it makes the request root from its own slot value and given sibling digests; at the end it
opens what is read.

ARGUMENTS, not drawn or chosen here: the strategy σ; all coins (`Coins`); the number of nonces that
the search of round number i may try (cap i + 1: the wire record's own number `GrW.more` is not
read); the external strings y with the trees xt that their committer has kept.

Main names:
  `TreeK`, `treeO`, `treesO`   a tree as the prover keeps it; its builder; a component's trees
  `Coins`                      all that is drawn
  `Res`   an outcome: a value; "a round has no format"; "the search of round i ran out"
  `searchO`, `fsO`, `onFs`     the search for a nonce; a Fiat-Shamir query with a test or without;
                    what follows it
  `Kept`, `OutP`, `chainO`     what is kept of the rounds; what the chain yields; the chain
  `rootsK`, `trK`, `opensK`, `extK`, `finish`   from what is kept to the fields of the proof string
  `proveX`, `prove`            the prover, with the transcript as it was hashed beside the string,
                    and without

Limits: definitions only: nothing is proved here. ONE slot: the other leaves of the request tree are
not made; the slot's sibling digests are coins. That is not what the programs do at a batch of more
than one request. No committer. Tied to no program. The file bears no "noncomputable": Lean makes
code for every definition in it. The definitions leavesO, treeO, treesO, searchO, fsO follow
committerLeafHashes, committerTreeRoot (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) and rootO, rootsOO, askW, askG
(Compile/Batch/CompleteRefDefs.lean) step for step, and chainO has the plan of chainO there, for one
slot. Here trees are kept, salts are handed in, and a search that runs out says so.
Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Rooted
import Compile.MerkleM
import Iop.BatchWire

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-! ## Trees -/

/-- a tree as the prover keeps it: the inputs of its leaves, and all levels of digests -/
structure TreeK (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  inp : ℕ → LeafIn L
  lv : List (List (Dig lam))

def TreeK.root (T : TreeK lam L) : Dig lam := rootOf T.lv

/-- the opening of leaf j, which holds the symbol a -/
def TreeK.opening {σ : Type} (T : TreeK lam L) (j : ℕ) (a : σ) : Opening lam σ :=
  ⟨a, (T.inp j).salt, pathOf T.lv j⟩

def leavesO : List (LeafIn L) → TypedOracleComputation lam K L (List (Dig lam))
  | [] => .pure []
  | x :: xs => (askTypedOracle (L := L) (K := K) OracleName.leaf x).bind fun u =>
      (leavesO xs).bind fun us => .pure (u :: us)

/-- build the tree of depth d over the leaves inp 0, .., inp (2 ^ d - 1) -/
def treeO (d : ℕ) (inp : ℕ → LeafIn L) : TypedOracleComputation lam K L (TreeK lam L) :=
  (leavesO ((List.range (2 ^ d)).map inp)).bind fun l =>
    (levelsM (hashTreeNode (K := K) (L := L)) d l).bind fun lv => .pure ⟨inp, lv⟩

/-- the trees of one component of one round, from tree number k on -/
def treesO {r : Round} (pad : Body L) (sl : ℕ → ℕ → Bits) (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (o : r.Orc) :
    ℕ → List ℕ → TypedOracleComputation lam K L (List (TreeK lam L))
  | _, [] => .pure []
  | k, d :: ds =>
    (treeO d fun j => ⟨match posAt k j with
        | some p => emb p (r.rd o p)
        | none => pad, sl k j⟩).bind fun T =>
      (treesO pad sl posAt emb o (k + 1) ds).bind fun Ts => .pure (T :: Ts)

/-! ## Coins -/

/-- All that the compiled prover draws, as one argument. -/
structure Coins (lam : ℕ) (L : BatchProtocolWithLeafBody I X) where
  /-- the salt of the first query (F1) -/
  salt : Bits
  /-- the salt of a leaf: round, own component?, tree, leaf -/
  leaf : ℕ → Bool → ℕ → ℕ → Bits
  /-- the body of a leaf at which no position stands -/
  pad : Body L
  /-- the slot, the sibling digests of its leaf in the request tree, the string behind its value -/
  slot : ℕ
  path : List (Dig lam)
  rsalt : Bits

/-! ## Outcomes -/

/-- An outcome of the prover: a value; or a round has no format (its kind does not fit the phase);
or the search for a nonce in round number i has run out. -/
inductive Res (α : Type)
  | ok (a : α)
  | noFormat
  | ranOut (i : ℕ)

def Res.map {α β : Type} (f : α → β) : Res α → Res β
  | .ok a => .ok (f a)
  | .noFormat => .noFormat
  | .ranOut i => .ranOut i

def Res.toOption {α : Type} : Res α → Option α
  | .ok a => some a
  | _ => none

/-! ## The search for a nonce -/

/-- try the nonces n, n + 1, ..: at most fuel of them; the first whose test bits are all 0 -/
def searchO {C P : Type} (gr : GrW C P) (chal : (Fin K → Dig lam) → C)
    (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (α : P) : ℕ → ℕ → TypedOracleComputation lam K L (Option (P × FsAns lam K))
  | 0, _ => .pure none
  | fuel + 1, n => (ask (gr.put n α)).bind fun a =>
      if gr.ok (chal a.1) then .pure (some (gr.put n α, a)) else searchO gr chal ask α fuel (n + 1)

/-- a Fiat-Shamir query, with a test or without: the plain part that was hashed, and the answer -/
def fsO {C P : Type} (gr : Option (GrW C P)) (cap : ℕ) (chal : (Fin K → Dig lam) → C)
    (ask : P → TypedOracleComputation lam K L (FsAns lam K)) (α : P) : TypedOracleComputation lam K L (Option (P × FsAns lam K)) :=
  match gr with
  | none => (ask α).bind fun a => .pure (some (α, a))
  | some g => searchO g chal ask α (cap + 1) 0

/-- go on with what a Fiat-Shamir query has returned; or stop: the search of round i has run out -/
def onFs {P β : Type} (i : ℕ) (k : P × FsAns lam K → TypedOracleComputation lam K L (Res β)) :
    Option (P × FsAns lam K) → TypedOracleComputation lam K L (Res β)
  | none => .pure (.ranOut i)
  | some p => k p

/-! ## The chain -/

/-- what the prover keeps of the rounds s: the message as it was hashed (the nonce written in), the
trees over the shared component, the trees over the slot's -/
def Kept (lam : ℕ) (L : BatchProtocolWithLeafBody I X) : Shape → Type
  | [] => Unit
  | r :: s => (r.Msg × List (TreeK lam L) × List (TreeK lam L)) × Kept lam L s

/-- what the chain yields: the verifier messages, what is kept, the last phase, and the request root
if the joining round lies in these rounds -/
abbrev OutP (lam : ℕ) (L : BatchProtocolWithLeafBody I X) (s : Shape) : Type :=
  Rho s × Kept lam L s × Phase lam × Option (Dig lam)

def consP {r : Round} {s : Shape} (c : r.Chal)
    (kp : r.Msg × List (TreeK lam L) × List (TreeK lam L)) (rq : Option (Dig lam))
    (z : OutP lam L s) : OutP lam L (r :: s) :=
  ((c, z.1), (kp, z.2.1), z.2.2.1, rq.orElse fun _ => z.2.2.2)

/-- The prover's chain: round by round the strategy's message, the trees over what is sent, and the
verifier's own queries (recomputeChain, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), in a round with a test by
a search over the nonces 0, .., cap i in round number i. -/
def chainO (t : Tag) (cms : List (Dig lam)) (x : Option X) (co : Coins lam L) (cap : ℕ → ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → Phase lam → Strat s Unit →
    TypedOracleComputation lam K L (Res (OutP lam L s))
  | [], _, _, _, _, _, ph, _ => .pure (.ok ((), (), ph, none))
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m, k) =>
      match actOf cms (x.map L.early) co.salt a.kind ph with
      | some (.one h true next) =>
          (treesO co.pad (co.leaf i true) w.posAtJ (fun p => embS (.inl p)) m.1 0 w.depthJ).bind
            fun TJ =>
          (fsO w.grJ (cap i) w.chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
              (⟨i, h.withLate (lateInstancePart L i x), TJ.map TreeK.root, embP (.inl (.inr α))⟩ :
                FbIn lam L t)) (a.plain m.2).2).bind <| onFs i fun q =>
            (chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              (next (List.ofFn q.2.2)) (k (w.chal q.2.1))).bind fun r =>
            .pure (r.map (consP (w.chal q.2.1)
              ((m.1, a.plain.symm ((a.plain m.2).1, q.1)), [], TJ) none))
      | some (.one h false next) =>
          (treesO co.pad (co.leaf i false) w.posAt0 (fun p => embS (.inl p)) m.1 0 w.depth0).bind
            fun T0 =>
          (fsO w.gr0 (cap i) w.chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
              (⟨i, h, T0.map TreeK.root, embP (.inl (.inl α))⟩ : FbIn lam L t))
              (a.plain m.2).1).bind <| onFs i fun q =>
            (chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              (next (List.ofFn q.2.2)) (k (w.chal q.2.1))).bind fun r =>
            .pure (r.map (consP (w.chal q.2.1)
              ((m.1, a.plain.symm (q.1, (a.plain m.2).2)), T0, []) none))
      | some (.join ρ) =>
          (treesO co.pad (co.leaf i true) w.posAtJ (fun p => embS (.inl p)) m.1 0 w.depthJ).bind
            fun TJ =>
          (treesO co.pad (co.leaf i false) w.posAt0 (fun p => embS (.inl p)) m.1 0 w.depth0).bind
            fun T0 =>
          (askTypedOracle (L := L) (K := K) (OracleName.g t)
            (⟨i, ρ, TJ.map TreeK.root, embP (.inl (.inr (a.plain m.2).2))⟩ : JoiningRoundQuery lam L t)).bind
            fun c =>
          (askTypedOracle (L := L) (K := K) OracleName.rleaf (List.ofFn c ++ co.rsalt)).bind fun d =>
          (climbM (rnodeV (K := K) (L := L)) co.path co.slot d).bind fun rq =>
          (fsO w.gr0 (cap i) w.chal (fun α => askTypedOracle (L := L) (K := K) (OracleName.fb t)
              (⟨i, .f4 cms (List.ofFn rq), T0.map TreeK.root, embP (.inl (.inl α))⟩ :
                FbIn lam L t)) (a.plain m.2).1).bind <| onFs i fun q =>
            (chainO t cms x co cap s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              (.shr (List.ofFn q.2.2) c) (k (w.chal q.2.1))).bind fun r =>
            .pure (r.map (consP (w.chal q.2.1)
              ((m.1, a.plain.symm (q.1, (a.plain m.2).2)), T0, TJ) (some rq)))
      | none => .pure .noFormat

/-! ## From what is kept to the proof string -/

/-- the roots, in the order in which recomputeChain takes them: in each round the slot's, then the shared -/
def rootsK : (s : Shape) → Kept lam L s → List (Dig lam)
  | [], _ => []
  | _ :: s, (kp, ks) => kp.2.2.map TreeK.root ++ (kp.2.1.map TreeK.root ++ rootsK s ks)

/-- the transcript as it was hashed -/
def trK : (s : Shape) → Kept lam L s → Rho s → Tr s
  | [], _, _ => ()
  | _ :: s, (kp, ks), (c, ρ) => (kp.1, c, trK s ks ρ)

/-- the openings at the positions that are read -/
def opensK : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Kept lam L s → (OPos s → Bool) →
    (p : OPos s) → Option (Opening lam (OSym s p))
  | [], _, _, _, _, p => nomatch p
  | r :: _, (a, _), (w, _), (kp, _), rd, .inl p =>
      if rd (.inl p) then
        ((if a.own p then kp.2.2 else kp.2.1)[w.tree p]?).map fun T =>
          T.opening (w.place p) (r.rd kp.1.1 p)
      else none
  | _ :: s, (_, A), (_, W), (_, ks), rd, .inr q => opensK s A W ks (fun p => rd (.inr p)) q

/-- the openings of the external strings, out of the trees xt that their committer has kept -/
def extK {E : ExtSpec} (we : WireE E) (y : E.Str) (xt : ℕ → TreeK lam L) (rd : E.Pos → Bool) :
    E.Pos → Option (Opening lam E.Sym) := fun p =>
  if rd p then some ((xt (we.which p)).opening (we.leaf p) (E.rd y p)) else none

section Prove
variable (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (cms : List (Dig lam)) (x : Y) (y : E.Str) (xt : ℕ → TreeK lam L)
  (σ : Strat Q.loc.shape Unit) (co : Coins lam L) (cap : ℕ → ℕ)

/-- the proof string from what the chain has yielded -/
def finish (z : OutP lam L Q.loc.shape) : OneProtocolProof lam Q :=
  haveI := wq.decO
  haveI := wq.ext.dec
  let τ := trK Q.loc.shape z.2.1 z.1
  { salt := co.salt
    roots := rootsK Q.loc.shape z.2.1
    plains := τ.plains
    opens := opensK Q.loc.shape Q.ann wq.sh z.2.1 fun p => decide (p ∈ Q.loc.reads x z.1 τ.plains)
    ext := extK wq.ext y xt fun p => decide (p ∈ Q.loc.extReads x z.1)
    rtreq := z.2.2.2.getD (fun _ => false)
    slot := co.slot
    path := if z.2.2.1.slotVal.isSome then co.path else []
    rsalt := if z.2.2.1.slotVal.isSome then co.rsalt else [] }

/-- **The compiled prover of one slot**, with the transcript as it was hashed beside the string. -/
def proveX : TypedOracleComputation lam K L (Res (OneProtocolProof lam Q × Tr Q.loc.shape)) :=
  (chainO t cms (xin x) co cap Q.loc.shape Q.ann wq.sh embS embP 0 .first σ).bind fun r =>
    .pure (r.map fun z => (finish Q wq x y xt co z, trK Q.loc.shape z.2.1 z.1))

def prove : TypedOracleComputation lam K L (Option (OneProtocolProof lam Q)) :=
  (proveX t Q wq embS embP xin cms x y xt σ co cap).bind fun r => .pure (r.toOption.map Prod.fst)

end Prove

end OnBytes.Prover
