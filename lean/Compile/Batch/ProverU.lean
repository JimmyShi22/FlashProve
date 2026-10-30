-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/ProverU.lean: the compiled prover of a `BatchInteractiveOracleProof` with no query for an empty slot.
Definitions only. (Words of this library: lean/GLOSSARY.md.)

`proveBU`: the compiled prover `proveB` of Compile/Batch/Prover.lean with one change. For a slot
that holds no request it samples no coins and no salt, builds no tree and queries no oracle; the
leaf of the request tree (`reqTU`) that belongs to the slot is a fresh uniform string of lam bits.
Everything that a slot with a request does, the shared part, the inner nodes of the request tree and
the proof strings are the terms of Compile/Batch/Prover.lean and Compile/Batch/TokTree.lean,
unchanged.

What changes. In `proveB` an empty slot is hashed like any other. With `proveBU` the hash work of a
batch is that of its requests, of the shared part and of the 2^depthReq - 1 inner nodes of the
request tree (for a batch of 2^depthReq slots). What is uniform is the leaf digest of the request
tree, not a slot value that is then hashed by h'_lf (the leaf oracle of request trees: `rleafT`,
Compile/Batch/TokTree.lean): the implementation does it so, and an empty slot queries no oracle at
all.

Notation:
  the letters of `proveB` (`sMT`, `sFS`, `depthReq`, `embS`, `embP`, `xin`, `PhT`, token): the
    legend in the head of Compile/Batch/Prover.lean; `fl`: ℕ → Bool; fl says for a slot whether a
    proof string is made (`proveB`)
  `blk0`: the blocks 0; `hear w bl noted`: a slot receives a shared verifier message; `noted` says
    whether its component of this round has been recorded already (Compile/Batch/Prover.lean)
  `Head.f4`, `Head.f5`: (F4): the joining round; (F5): a later shared round
    (Compile/Batch/Oracles.lean)
  ⟨none, 0, 0, [], [], [], [], []⟩: a `SlotAcc`: its fields x, tk, c, blocks, trees, toks, nons,
    dead; ⟨[], [], none, [], []⟩: an `Acc0`: trees, toks, req, nons, dead
    (Compile/Batch/Prover.lean)

Limits. Nothing is proved here. A slot whose request is withheld (its proof string is `none`) is not
an empty slot: it does all its work and keeps its real leaf, as in `proveB`. The implementation
differs there: a request that has failed by the time the request tree is made gets a uniform leaf
like an empty slot; one that fails later keeps its real leaf.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.Prover

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## The request tree -/

/-- the leaves of the request tree: h'_lf (`rleafT`) of a slot value; for an empty slot (none) a
fresh uniform string of lam bits -/
def rleavesTU : List (Option Tok) → St lam K L (List Tok)
  | [] => pure []
  | some c :: t => (rleafT c).bind fun d => (rleavesTU t).bind fun r => Step.pure (d :: r)
  | none :: t => Step.fresh lam fun d => (rleavesTU t).bind fun r => Step.pure (d :: r)

/-- the request tree over the slot values cs; none: an empty slot -/
def reqTU (depthReq : ℕ) (cs : List (Option Tok)) : St lam K L TTree :=
  (rleavesTU cs).bind fun ls => (levelsM rnodeT depthReq ls).bind fun lv => Step.pure ⟨lv, []⟩

/-! ## The rounds -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- a local round, in one slot; an empty slot does nothing -/
def slotLoU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (z : SlotSt lam K Y (r :: s)) : St lam K L (SlotSt lam K Y s) :=
  match z.2.x with
  | some _ => slotLo sMT t cms xin a w emb plJ i ph z
  | none => Step.pure (z.1.2 (w.chal (blk0 lam K)), z.2)

/-- the joining round, in one slot; an empty slot does nothing -/
def slotJoinU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (z : SlotSt lam K Y (r :: s)) :
    St lam K L (SlotSt lam K Y (r :: s)) :=
  match z.2.x with
  | some _ => slotJoin sMT t a w emb plJ i z
  | none => Step.pure z

/-- the joining round in all slots; for each slot its slot value, or none if it is empty -/
def joinMU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    List (SlotSt lam K Y (r :: s)) → St lam K L (List (SlotSt lam K Y (r :: s)) × List (Option Tok))
  | [] => pure ([], [])
  | z :: zs => (slotJoinU sMT t a w emb plJ i z).bind fun z' =>
      (joinMU a w emb plJ i zs).bind fun o =>
        Step.pure (z' :: o.1, (z'.2.x.map fun _ => z'.2.c) :: o.2)

/-- All chains of a batch; only slots with a request have one. The definition of chainT, with
slotLoU, joinMU and reqTU. -/
def chainTU (depthReq : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) → ℕ → PhT → SStrat s A → List (SlotSt lam K Y s) →
    Acc0 → St lam K L (List (SlotAcc lam K Y) × Acc0)
  | [], _, _, _, _, _, _, _, zs, a0 => pure (zs.map Prod.snd, a0)
  | _ :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0 =>
      match a.kind, ph with
      | .lo, ph =>
          (eachM (slotLoU sMT t cms xin a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i ph)
              zs).bind fun zs' =>
          chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs'
            { a0 with trees := a0.trees ++ [none] }
      | .sh, .loc =>
          (joinMU sMT t a w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqTU depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr tl)
            (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
            { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      | .sh, .shr tk0 =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) (.shr tl)
            (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      | .sh, ph =>
          chainTU depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph
            (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
            { a0 with trees := a0.trees ++ [none] }

end Rounds

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- a slot at the start: with a request as in initSlot; an empty slot gets neither coins nor a
salt -/
def initSlotU (c0 : H.Coin0) : Option Y → St lam K L (SlotSt lam K (Y × H.Coin) Q.loc.shape)
  | some x => initSlot sFS Q H wp w c0 (some x)
  | none => Step.pure (Strat.dflt Q.loc.shape (), ⟨none, 0, 0, [], [], [], [], []⟩)

/-- The compiled prover with no query for an empty slot: one execution of the `BatchInteractiveOracleProof` on the
slots xs (none: an empty slot). The arguments and the result are those of proveB. -/
def proveBU (fl : ℕ → Bool) (xs : List (Option Y)) : St lam K L (List (Option (OneProtocolProof lam Q))) :=
  (drawT wp.coin0).bind fun c0 =>
  (eachM (initSlotU sFS Q H wp w c0) xs).bind fun zs =>
  (chainTU sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape Q.ann
      wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩).bind fun out =>
  finishAll Q H wq wp trees w fl c0 out.2 0 out.1

end Prove

end Compile.Batch
