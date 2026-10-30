-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Mirror.lean: the compiled prover in the language that names the input of a marked
query (`Step.marked`, Rom/Defer.lean) only at its release: `LStep` (Rom/DeferLate.lean: as `Step`,
but for `marked` and `reveal`; `marked` has no closure pt). Definitions (words of this library:
lean/GLOSSARY.md).

Each program of the honest parties (`leafL`, .., `PpL`) follows, constructor by constructor, a
definition of Compile/Batch/TokTree.lean, Compile/Batch/Prover.lean or Compile/Batch/Star.lean. What
is gained:
 * the hashing of a batch (`skB`) reads no message of the prover and no request: trees of the right
   shape over fresh tokens (`Tok`, `Step`: Rom/Defer.lean; only where the wire record says that the
   component has a tree, as in the prover), Fiat-Shamir queries, g, the request tree;
 * the closures (`Clo`) of the node oracle and of the two oracles of request trees hold no data, so
   every reveal supplies them for all tokens at once (`baseC`); only the closures of leaves (the
   body), of Fiat-Shamir queries and of g (formats (F1) to (F5): `Head`, Compile/Batch/Oracles.lean;
   plain parts) are supplied token by token, from the disclosed view (`ctxB`, `finishBL`);
 * with verifier randomness given, in a round without proof-of-work bits a Fiat-Shamir answer is
   sampled from the answers that yield the given challenge (all, if none does: `ansB`); in a round
   with such bits: `tryL`.
`proveBL` is the honest prover in this form, `proveBW` the subroutine of the reduction (`theWrapBP`,
Compile/Batch/PubWr.lean), which is given, for the slots that it owns, the request, the verifier
randomness and the output of the session.

Notation:
  `tk`, `us` (`fbL`): a Fiat-Shamir query is charged to tk; its other tokens are us;
  `nc`, `dd`, `bl`, `tl` (what the continuation k is given; `fbW`, `fbG`,
    Compile/Batch/Prover.lean): the number of the final attempt, if there is a proof-of-work record,
    the chaining values of those before it, and the blocks and the chaining value of the final one;
  `ph`: a `PhT` (Compile/Batch/Prover.lean), the phase: `first`, `loc`, `shr tk0` or `aft`;
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated;
  `acc.tk`, `acc.c` (fields of `SlotAcc`, Compile/Batch/Prover.lean: what a slot has accumulated):
    the token that the next query of its chain holds (not in the phase `shr tk0`: see `live`,
    Compile/Batch/DisciplineSlot.lean); its slot value, once the chains have joined;
  g (in the comments): the oracle `OracleName.g t` (Compile/Batch/Oracles.lean); `gL` (after `gT`,
    Compile/Batch/Prover.lean): the query to g in the joining round: its answer is the slot value;
  local, shared (of a round; the head of Compile/Batch/Verifier.lean): shared if its challenge is
    one for all slots, local if each slot has its own;
  `sMT`, `sFS`: natural numbers; sMT is the length of the salt of a leaf, sFS that of the salt of
    a chain (Compile/Batch/Verifier.lean);
  `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the trees
    over the external strings;
  `depthReq`: a natural number; depth of a request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `fl`: a map ℕ → Bool; it says for which slots a proof string is made at all (`finishAll`,
    Compile/Batch/Prover.lean);
  `fr`: a map ℕ → Bool; for which requests a proof string is made at all (the head of
    Compile/Batch/Star.lean).
-/
import Compile.Batch.Star
import Compile.Batch.SpecLifeStar
import Rom.DeferLate

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

abbrev Lp (lam K : ℕ) (L : BatchProtocol I X) (α : Type) : Type := LStep (spec lam K L) (split lam K L) α
abbrev Cx (lam K : ℕ) (L : BatchProtocol I X) : Type := Ctx (spec lam K L)

/-! ## Closures -/

def cloLeaf (K : ℕ) (b : Body L) : Clo (spec lam K L) OracleName.leaf := fun v _ => (⟨b, v⟩ : LeafIn L)
def cloNode : Clo (spec lam K L) OracleName.node := fun v vs => ((v, vs.headD []) : Bits × Bits)
def cloRleaf : Clo (spec lam K L) OracleName.rleaf := fun v _ => (v : Bits)
def cloRnode : Clo (spec lam K L) OracleName.rnode := fun v vs => ((v, vs.headD []) : Bits × Bits)
/-- the root in a query: the digest d if the component has a tree, none otherwise -/
def rtIf (has : Bool) (d : Dig lam) : Option (Dig lam) :=
  match has with
  | true => some d
  | false => none
/-- has: the component of the round has a tree; then its root is the token at index rtAt among the
other tokens of the query -/
def cloFb (K : ℕ) (t : Tag) (i : ℕ) (hd : List Bits → Bits → Head lam X) (has : Bool)
    (rtAt : ℕ) (pl : PlainPart (shapeOf L t) (annOf L t)) : Clo (spec lam K L) (OracleName.fb t) :=
  fun v vs => (⟨i, hd vs v, rtIf has (digD lam (vs.getD rtAt [])), pl⟩ : FbIn lam L t)
/-- the same closure under the ghost name `fbw t j` (Compile/Batch/Oracles.lean) -/
def cloFbw (K : ℕ) (t : Tag) (j : ℕ) (i : ℕ) (hd : List Bits → Bits → Head lam X) (has : Bool)
    (rtAt : ℕ) (pl : PlainPart (shapeOf L t) (annOf L t)) :
    Clo (spec lam K L) (OracleName.fbw t j) :=
  fun v vs => (⟨i, hd vs v, rtIf has (digD lam (vs.getD rtAt [])), pl⟩ : FbIn lam L t)
def cloG (K : ℕ) (t : Tag) (i : ℕ) (has : Bool) (pl : PlainPart (shapeOf L t) (annOf L t)) :
    Clo (spec lam K L) (OracleName.g t) :=
  fun v vs => (⟨i, v, rtIf has (digD lam (vs.headD [])), pl⟩ : JoiningRoundQuery lam L t)

/-- the closures that hold no data, for every token -/
def baseC : Cx lam K L := fun _ o => match o with
  | .node => some cloNode
  | .rleaf => some cloRleaf
  | .rnode => some cloRnode
  | _ => none

/-! ## Token trees -/

def leafL (sMT : ℕ) : Lp lam K L (Tok × Tok) :=
  LStep.fresh sMT fun s =>
  LStep.marked (S := spec lam K L) OracleName.leaf s [] Finset.univ
    Finset.univ_nonempty fun _ d => LStep.pure (s, d)

def nodeL (a b : Tok) : Lp lam K L Tok :=
  LStep.marked (S := spec lam K L) OracleName.node a [b] Finset.univ
    Finset.univ_nonempty fun _ d => LStep.pure d

def leavesL (sMT : ℕ) : ℕ → Lp lam K L (List Tok × List Tok)
  | 0 => pure ([], [])
  | n + 1 => do
      let x ← leafL sMT
      let r ← leavesL sMT n
      pure (x.2 :: r.1, x.1 :: r.2)

def commitL (sMT depth : ℕ) : Lp lam K L TTree := do
  let x ← leavesL sMT (2 ^ depth)
  let lv ← levelsM nodeL depth x.1
  pure ⟨lv, x.2⟩

/-- open leaf j, whose body b is named now -/
def openL {σ : Type} (t : TTree) (j : ℕ) (b : Body L) (a : σ) : Lp lam K L (Opening lam σ) :=
  LStep.reveal (t.salts.getD j 0 :: (pathOf t.levels j ++ ancOf t.levels j))
      (baseC.set (t.salts.getD j 0) OracleName.leaf (cloLeaf K b)) fun vs =>
    LStep.pure ⟨a, vs.headD [], (vs.tail.take (pathOf t.levels j).length).map (digD lam)⟩

def showL (t : Tok) : Lp lam K L (Dig lam) :=
  LStep.reveal [t] baseC fun vs => LStep.pure (digD lam (vs.headD []))

def rleafL (c : Tok) : Lp lam K L Tok :=
  LStep.marked (S := spec lam K L) OracleName.rleaf c [] Finset.univ
    Finset.univ_nonempty fun _ d => LStep.pure d

def rnodeL (a b : Tok) : Lp lam K L Tok :=
  LStep.marked (S := spec lam K L) OracleName.rnode a [b]
    Finset.univ Finset.univ_nonempty fun _ d => LStep.pure d

def rleavesL : List Tok → Lp lam K L (List Tok)
  | [] => pure []
  | c :: t => do
      let d ← rleafL c
      let r ← rleavesL t
      pure (d :: r)

def reqL (depthReq : ℕ) (cs : List Tok) : Lp lam K L TTree := do
  let ls ← rleavesL cs
  let lv ← levelsM rnodeL depthReq ls
  pure ⟨lv, []⟩

/-! ## Trees over encoded indices -/

/-- true: a salted leaf, whose body is not named; false: padding -/
def leafEL (sMT : ℕ) (blind : Bool) : Lp lam K L (Dig lam × Option (Tok × Tok)) :=
  if blind then
    (leafL sMT).bind fun x => (showL x.2).bind fun d => LStep.pure (d, some x)
  else LStep.plain (S := spec lam K L) OracleName.leaf (⟨none, []⟩ : LeafIn L) fun d => LStep.pure (d, none)

def nodeEL (a b : Dig lam) : Lp lam K L (Dig lam) :=
  LStep.plain (S := spec lam K L) OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits) LStep.pure

def leavesEL (sMT : ℕ) : List Bool → Lp lam K L (List (Dig lam) × List (Option (Tok × Tok)))
  | [] => pure ([], [])
  | bl :: t => do
      let x ← leafEL sMT bl
      let r ← leavesEL sMT t
      pure (x.1 :: r.1, x.2 :: r.2)

def commitEL (sMT depth : ℕ) (mask : ℕ → Bool) : Lp lam K L (TreeH lam) := do
  let x ← leavesEL sMT ((List.range (2 ^ depth)).map mask)
  let lv ← levelsM nodeEL depth x.1
  pure ⟨lv, x.2⟩

def openEL {σ : Type} (t : TreeH lam) (j : ℕ) (b : Body L) (a : σ) : Lp lam K L (Opening lam σ) :=
  match t.salts.getD j none with
  | some (s, d) =>
    LStep.reveal [s, d] (baseC.set s OracleName.leaf (cloLeaf K b)) fun vs =>
      LStep.pure ⟨a, vs.headD [], pathOf t.levels j⟩
  | none => LStep.pure ⟨a, [], pathOf t.levels j⟩

/-! ## The hashing of a batch -/

/-- a non-empty set of Fiat-Shamir answers -/
abbrev ASet (lam K : ℕ) : Type := { A : Finset ((Fin K → Dig lam) × Dig lam) // A.Nonempty }

open Classical in
/-- the answers from which the answer of a round is sampled: all, or those that yield the given
challenge (all, if none does) -/
def ansB {r : Round} {a : RAnn r} (w : WireRB lam K r a) : Option r.Chal → ASet lam K
  | none => ⟨Finset.univ, Finset.univ_nonempty⟩
  | some c =>
      if h : (Finset.univ.filter fun x : (Fin K → Dig lam) × Dig lam =>
          w.chal x.1 = c).Nonempty then ⟨_, h⟩
      else ⟨Finset.univ, Finset.univ_nonempty⟩

def fbL {β : Type} (t : Tag) (tk : Tok) (us : List Tok)
    (A : ASet lam K) (k : Blk lam K → Tok → Lp lam K L β) : Lp lam K L β :=
  LStep.marked (S := spec lam K L) (OracleName.fb t) tk us A.1 A.2 k

/-! ### A Fiat-Shamir query with proof-of-work bits (Compile/Batch/Prover.lean: fbTw, fbW, fbTG,
fbG) -/

def fbLw {β : Type} (t : Tag) (j : ℕ) (tk : Tok) (us : List Tok)
    (A : ASet lam K) (k : Blk lam K → Tok → Lp lam K L β) : Lp lam K L β :=
  LStep.marked (S := spec lam K L) (OracleName.fbw t j) tk us A.1 A.2 k

/-- the answers whose challenge has the proof-of-work bits z (all, if none has). (Nothing is decided
classically here: proof-of-work bits are strings of bits.) -/
def ansT {r : Round} {a : RAnn r} {P : Type} (w : WireRB lam K r a)
    (g : GrW r.Chal P) (z : Fin g.b → Bool) : ASet lam K :=
  if h : (Finset.univ.filter fun x : (Fin K → Dig lam) × Dig lam =>
      g.tst (w.chal x.1) = z).Nonempty then ⟨_, h⟩
  else ⟨Finset.univ, Finset.univ_nonempty⟩

/-- b bits from a number below 2^b -/
def zBits (b : ℕ) (r : Fin (2 ^ b - 1 + 1)) : Fin b → Bool := fun i => r.val.testBit i.val

/-- From which answers the answer of one attempt is sampled. h = none (the honest prover; a slot
that is not the reduction's own): from all. h = some c: the challenge c is given, and its
proof-of-work bits are not used: the reduction samples the bits z of this attempt itself; if they
are all 0, or if this is the last attempt, it will be the final attempt, and its answer is sampled
from those that yield c with the bits z; else from all answers with the bits z. ab: the answers that
yield a given challenge (ansB w). -/
def tryL {β : Type} {r : Round} {a : RAnn r} {P : Type} (w : WireRB lam K r a)
    (g : GrW r.Chal P) (ab : Option r.Chal → ASet lam K) (h : Option r.Chal)
    (last : Bool) (mk : ASet lam K → Lp lam K L β) :
    Lp lam K L β :=
  match h with
  | none => mk ⟨Finset.univ, Finset.univ_nonempty⟩
  | some c => LStep.sample (2 ^ g.b - 1) fun x =>
      mk (if last || decide (zBits g.b x = fun _ => false) then ab (some (g.set (zBits g.b x) c))
        else ansT w g (zBits g.b x))

def fbWL {β : Type} {r : Round} {a : RAnn r} {P : Type} (w : WireRB lam K r a) (g : GrW r.Chal P)
    (ab : Option r.Chal → ASet lam K) (t : Tag) (tk : Tok) (us : List Tok) (h : Option r.Chal)
    (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) : ℕ → ℕ → List Tok → Lp lam K L β
  | 0, j, dd => tryL w g ab h true fun A => fbLw t j tk us A fun bl tl => k (j + 1) dd bl tl
  | n + 1, j, dd => tryL w g ab h false fun A => fbLw t j tk us A fun bl tl =>
      if g.ok (w.chal bl) then k (j + 1) dd bl tl else fbWL w g ab t tk us h k n (j + 1) (tl :: dd)

def fbTGL {β : Type} {r : Round} {a : RAnn r} {P : Type} (w : WireRB lam K r a) (g : GrW r.Chal P)
    (ab : Option r.Chal → ASet lam K) (t : Tag) (tk : Tok) (us : List Tok) (h : Option r.Chal)
    (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) : Lp lam K L β :=
  match g.more with
  | 0 => tryL w g ab h true fun A => fbL t tk us A fun bl tl => k 0 [] bl tl
  | n + 1 => tryL w g ab h false fun A => fbL t tk us A fun bl tl =>
      if g.ok (w.chal bl) then k 0 [] bl tl else fbWL w g ab t tk us h k n 0 [tl]

/-- with proof-of-work bits or without; h: the challenge, if it is given -/
def fbGL {β : Type} {r : Round} {a : RAnn r} {P : Type} (w : WireRB lam K r a)
    (gr : Option (GrW r.Chal P)) (ab : Option r.Chal → ASet lam K) (t : Tag) (tk : Tok)
    (us : List Tok) (h : Option r.Chal) (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) :
    Lp lam K L β :=
  match gr with
  | none => fbL t tk us (ab h) (k none [])
  | some g => fbTGL w g ab t tk us h fun m => k (some m)

def fbSlotGL {β : Type} {r : Round} {a : RAnn r} {P : Type} (w : WireRB lam K r a)
    (gr : Option (GrW r.Chal P)) (ab : Option r.Chal → ASet lam K) (t : Tag) (ph : PhT) (tk c : Tok)
    (root : Option Tok) (h : Option r.Chal)
    (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) : Lp lam K L β :=
  match ph with
  | .first => fbGL w gr ab t tk root.toList h k
  | .shr tk0 => fbGL w gr ab t c (tk0 :: root.toList) h k
  | _ => fbGL w gr ab t tk root.toList h k

def gL {β : Type} (t : Tag) (tk : Tok) (root : Option Tok) (k : Tok → Lp lam K L β) :
    Lp lam K L β :=
  LStep.marked (S := spec lam K L) (OracleName.g t) tk root.toList Finset.univ
    Finset.univ_nonempty fun _ c => k c

/-- the tree over a component, if it has one, and then k (Compile/Batch/Prover.lean: withTree) -/
def withTreeL {β : Type} (sMT : ℕ) (has : Bool) (depth : ℕ) (k : Option TTree → Lp lam K L β) :
    Lp lam K L β :=
  match has with
  | true => (commitL sMT depth).bind fun tr => k (some tr)
  | false => k none

/-- the trees over a component with a list of trees, one after the other, and then k
(Compile/Batch/Prover.lean: `withTrees`) -/
def withTreesL {β : Type} (sMT : ℕ) : List ℕ → (List TTree → Lp lam K L β) → Lp lam K L β
  | [], k => k []
  | d :: ds, k => (commitL sMT d).bind fun tr => withTreesL sMT ds fun trs => k (tr :: trs)

theorem withTreesL_one {β : Type} (sMT d : ℕ) (k : List TTree → Lp lam K L β) :
    withTreesL sMT [d] k = withTreeL sMT true d fun o => k o.toList := rfl

theorem withTreesL_ite {β : Type} (sMT : ℕ) (has : Bool) (d : ℕ)
    (k : List TTree → Lp lam K L β) :
    withTreesL sMT (if has then [d] else []) k = withTreeL sMT has d fun o => k o.toList := by
  cases has <;> rfl

section Skeleton
variable {Y : Type} (sMT : ℕ) (t : Tag)

/-- a slot during the hashing: the challenges that are still to come, if they are given; and its
accumulator -/
abbrev SlotSk (lam K : ℕ) (Y : Type) (s : Shape) : Type := Option (Rho s) × SlotAcc lam K Y

def skSlotLo {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (ph : PhT) :
    SlotSk lam K Y (r :: s) → Lp lam K L (SlotSk lam K Y s)
  | (fo, acc) =>
      withTreeL sMT w.hasJ w.depthJ fun tr =>
      fbSlotGL w w.grJ (ansB w) t ph acc.tk acc.c (tr.map TTree.root)
          (fo.map Prod.fst) fun nc dd bl tl =>
      LStep.pure (fo.map Prod.snd,
        { acc with
          tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [tr],
          toks := acc.toks ++ [tl], nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead })

def skSlotJoin {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) :
    SlotSk lam K Y (r :: s) → Lp lam K L (SlotSk lam K Y (r :: s))
  | (fo, acc) =>
      withTreeL sMT w.hasJ w.depthJ fun tr =>
      gL t acc.tk (tr.map TTree.root) fun c =>
      LStep.pure (fo, { acc with c := c, trees := acc.trees ++ [tr], toks := acc.toks ++ [c] })

def skJoinM {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) :
    List (SlotSk lam K Y (r :: s)) → Lp lam K L (List (SlotSk lam K Y (r :: s)) × List Tok)
  | [] => pure ([], [])
  | z :: zs => (skSlotJoin sMT t w z).bind fun z' =>
      (skJoinM w zs).bind fun o => LStep.pure (z' :: o.1, z'.2.c :: o.2)

def hearL {r : Round} {s : Shape} (bl : Blk lam K) (noted : Bool) :
    SlotSk lam K Y (r :: s) → SlotSk lam K Y s
  | (fo, acc) =>
    (fo.map Prod.snd,
      { acc with
        blocks := acc.blocks ++ [bl], trees := if noted then acc.trees else acc.trees ++ [none] })

def eachL {σ τ : Type} (f : σ → Lp lam K L τ) : List σ → Lp lam K L (List τ)
  | [] => pure []
  | a :: t => do
      let b ← f a
      let r ← eachL f t
      pure (b :: r)

/-- The hashing of all chains of a batch (Compile/Batch/Prover.lean: chainT). f0: the challenges of
a slot's transcript from which the shared ones are taken, if they are given. -/
def skB (depthReq : ℕ) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → PhT → Option (Rho s) → List (SlotSk lam K Y s) →
    Acc0 → Lp lam K L (List (SlotAcc lam K Y) × Acc0)
  | [], _, _, _, _, zs, a0 => pure (zs.map Prod.snd, a0)
  | _ :: s, (a, A), (w, W), ph, f0, zs, a0 =>
      match a.kind, ph with
      | .lo, ph =>
          (eachL (skSlotLo sMT t w ph) zs).bind fun zs' =>
          skB depthReq s A W ph.afterLo (f0.map Prod.snd)
            zs' { a0 with trees := a0.trees ++ [none] }
      | .sh, .loc =>
          (skJoinM sMT t w zs).bind fun o =>
          (reqL depthReq o.2).bind fun rq =>
          withTreeL sMT w.has0 w.depth0 fun tr0 =>
          fbGL w w.gr0 (ansB w) t rq.root (tr0.map TTree.root).toList
              (f0.map Prod.fst) fun nc dd bl tl =>
          skB depthReq s A W (.shr tl) (f0.map Prod.snd) (o.1.map (hearL bl true))
            { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      | .sh, .shr tk0 =>
          withTreeL sMT w.has0 w.depth0 fun tr0 =>
          fbGL w w.gr0 (ansB w) t tk0 (tr0.map TTree.root).toList
              (f0.map Prod.fst) fun nc dd bl tl =>
          skB depthReq s A W (.shr tl) (f0.map Prod.snd) (zs.map (hearL bl false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
      | .sh, ph =>
          skB depthReq s A W ph (f0.map Prod.snd) (zs.map (hearL (blk0 lam K) false))
            { a0 with trees := a0.trees ++ [none] }

end Skeleton

/-! ## The closures of the chains of one slot and of the shared chain -/

/-- record a closure for the first token of a list, if there is one -/
def setHd (Pc : Cx lam K L) (l : List Tok) (o : OracleName) (c : Clo (spec lam K L) o) : Cx lam K L :=
  match l with
  | [] => Pc
  | u :: _ => Pc.set u o c

/-- the closures of the attempts 1, .., m of a round with proof-of-work bits, all associated with u:
attempt j + 1 under the ghost name `fbw t j`, with the plain part pl (j + 1) -/
def setW (t : Tag) (u : Tok) (i : ℕ) (hd : List Bits → Bits → Head lam X) (has : Bool) (rtAt : ℕ)
    (pl : ℕ → PlainPart (shapeOf L t) (annOf L t)) (Pc : Cx lam K L) : ℕ → Cx lam K L
  | 0 => Pc
  | m + 1 =>
    (setW t u i hd has rtAt pl Pc m).set u (OracleName.fbw t m) (cloFbw K t m i hd has rtAt (pl (m + 1)))

/-- The closures of the Fiat-Shamir queries of one round, associated with the first token of l.
Without proof-of-work bits: one closure, with the plain part emb α. With them, m the number of the
final attempt: the closures of the attempts 0, .., m, whose plain parts hold the nonces for 0, ..,
m. -/
def setFb {P : Type} {C : Type} (gr : Option (GrW C P)) (t : Tag) (l : List Tok) (i : ℕ)
    (hd : List Bits → Bits → Head lam X) (has : Bool) (rtAt : ℕ)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P) (m : ℕ) (Pc : Cx lam K L) : Cx lam K L :=
  match l with
  | [] => Pc
  | u :: _ =>
      match gr with
      | none => Pc.set u (OracleName.fb t) (cloFb K t i hd has rtAt (emb α))
      | some g =>
        setW t u i hd has rtAt (fun j => emb (g.put j α))
          (Pc.set u (OracleName.fb t) (cloFb K t i hd has rtAt (emb (g.put 0 α)))) m

/-- the rest of a list of numbers of final attempts after a round: a round with proof-of-work bits
has taken the first -/
def restN {C P : Type} (gr : Option (GrW C P)) (n : List ℕ) : List ℕ :=
  match gr with
  | none => n
  | some _ => n.tail

/-- The closures of a slot's chain and of the shared chain, from what is public at the end: the
formats, the plain parts of the slot's transcript as the interactive prover sends them (pl, pls;
this function writes the nonces), the chain tokens of the slot (tj: its salt, chaining values and
slot value, in order: each query of the slot, and in a round with proof-of-work bits each of its
attempts, is associated with the next of them) and those of the shared chain (t0: the request root,
then the shared chaining values), and the numbers of the final attempts of the slot (nJ) and of the
shared rounds (n0), in the order of the rounds. The wire record says which components have a tree,
and so which queries hold a root. x is the whole request of the slot: as in the prover, (F1) holds
L.early x and (F2) holds x in the round L.late. -/
def ctxB (t : Tag) (cms : List (Dig lam)) (x : Option X) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) →
    ℕ → PhT → List Tok → List Tok → List ℕ → List ℕ → Plains s → Cx lam K L → Cx lam K L
  | [], _, _, _, _, _, _, _, _, _, _, Pc => Pc
  | _ :: s, (a, A), (w, W), embP, i, ph, tj, t0, nJ, n0, (pl, pls), Pc =>
      match a.kind, ph with
      | .lo, ph =>
          ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1)
            ph.afterLo tj.tail t0 (restN w.grJ nJ) n0 pls
            (match ph with
              | .first =>
                setFb w.grJ t tj i (fun _ => Head.f1 cms (x.map L.early)) w.hasJ 0
                  (fun α => embP (.inl (.inr α))) (a.plain pl).2 (nJ.headD 0) Pc
              | .shr _ =>
                setFb w.grJ t tj i (fun vs => Head.f3 (vs.headD [])) w.hasJ 1
                  (fun α => embP (.inl (.inr α))) (a.plain pl).2 (nJ.headD 0) Pc
              | _ =>
                setFb w.grJ t tj i (fun _ => Head.f2 (lateInstancePart L i x)) w.hasJ 0
                  (fun α => embP (.inl (.inr α))) (a.plain pl).2 (nJ.headD 0) Pc)
      | .sh, .loc =>
          ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) (.shr 0)
            tj.tail t0.tail nJ (restN w.gr0 n0) pls
            (setFb w.gr0 t t0 i (fun _ => Head.f4 cms) w.has0 0 (fun α => embP (.inl (.inl α)))
              (a.plain pl).1 (n0.headD 0)
              (setHd Pc tj (OracleName.g t) (cloG K t i w.hasJ (embP (.inl (.inr (a.plain pl).2))))))
      | .sh, .shr _ =>
          ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) (.shr 0)
            tj t0.tail nJ (restN w.gr0 n0) pls
            (setFb w.gr0 t t0 i (fun _ => Head.f5) w.has0 0 (fun α => embP (.inl (.inl α)))
              (a.plain pl).1 (n0.headD 0) Pc)
      | .sh, ph => ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) ph tj t0 nJ n0 pls Pc

/-! ## Openings -/

def opensCompL {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (tr : TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    List ℕ → Lp lam K L ((p : r.Pos) → Option (Opening lam (r.Sym p)))
  | [] => pure f
  | j :: js => do
      let f' ← opensCompL dec posAt sym zero emb tr isRead f js
      match posAt j with
      | some p =>
          if isRead p then do
            let op ← openL tr j (emb p ((sym p).getD (zero p))) ((sym p).getD (zero p))
            pure (@Function.update _ _ dec f' p (some op))
          else pure f'
      | none => pure f'

def opensOptL {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Lp lam K L ((p : r.Pos) → Option (Opening lam (r.Sym p))) :=
  match tr with
  | none => pure f
  | some tr => opensCompL dec posAt sym zero emb tr isRead f (List.range (2 ^ depth))

/-- open the positions read in the trees of one component, from tree number k on, what comes later
in the list first (Compile/Batch/Prover.lean: `opensTrees`) -/
def opensTreesL {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool) :
    ℕ → List ℕ → List TTree → ((p : r.Pos) → Option (Opening lam (r.Sym p))) →
    Lp lam K L ((p : r.Pos) → Option (Opening lam (r.Sym p)))
  | k, d :: ds, tr :: trs, f =>
      (opensTreesL dec posAt sym zero emb isRead (k + 1) ds trs f).bind fun f' =>
        opensCompL dec (posAt k) sym zero emb tr isRead f' (List.range (2 ^ d))
  | _, _, _, f => pure f

theorem opensTreesL_one {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool) (k d : ℕ) (tr : Option TTree)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    opensTreesL (K := K) dec posAt sym zero emb isRead k [d] tr.toList f =
      opensOptL dec (posAt k) d sym zero emb tr isRead f := by
  cases tr <;> rfl

theorem opensTreesL_nil {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool) (k : ℕ) (trs : List TTree)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    opensTreesL (K := K) dec posAt sym zero emb isRead k [] trs f = pure f := by
  cases trs <;> rfl

theorem opensTreesL_ite {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (sym : (p : r.Pos) → Option (r.Sym p)) (zero : (p : r.Pos) → r.Sym p)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool) (k : ℕ) (has : Bool) (d : ℕ)
    (tr : Option TTree) (f : (p : r.Pos) → Option (Opening lam (r.Sym p)))
    (h : has = false → tr = none) :
    opensTreesL (K := K) dec posAt sym zero emb isRead k (if has then [d] else []) tr.toList f =
      opensOptL dec (posAt k) d sym zero emb tr isRead f := by
  cases has with
  | true => exact opensTreesL_one dec posAt sym zero emb isRead k d tr f
  | false => rw [h rfl]; rfl

def opensBL :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → Option (OSym s p)) →
    ((p : OPos s) → OSym s p → Body L) → List (Option TTree) → List (Option TTree) →
    (OPos s → Bool) → Lp lam K L ((p : OPos s) → Option (Opening lam (OSym s p)))
  | [], _, _, _, _, _, _, _ => pure fun p => nomatch p
  | _ :: s, (_, A), (w, W), orc, emb, tjs, t0s, isRead => do
      let f0 ← opensOptL w.pt.decPos w.posAt0 w.depth0 (fun p => orc (.inl p)) w.pt.zero
        (fun p => emb (.inl p)) (t0s.headD none) (fun p => isRead (.inl p)) (fun _ => none)
      let f ← opensOptL w.pt.decPos w.posAtJ w.depthJ (fun p => orc (.inl p)) w.pt.zero
        (fun p => emb (.inl p)) (tjs.headD none) (fun p => isRead (.inl p)) f0
      let g ← opensBL s A W (fun p => orc (.inr p)) (fun p => emb (.inr p))
        tjs.tail t0s.tail (fun p => isRead (.inr p))
      pure fun p => match p with
        | .inl q => f q
        | .inr q => g q

def opensExtBL {E : ExtSpec} (we : WireE E) (ans : E.Pos → Option E.Sym) (embE : E.Sym → Body L)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    List E.Pos → Lp lam K L (E.Pos → Option (Opening lam E.Sym))
  | [] => pure fun _ => none
  | p :: ps => do
      let f ← opensExtBL we ans embE trees isRead ps
      if isRead p then
        match ans p with
        | some a => do
            let op ← openEL (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (embE a) a
            pure (@Function.update _ _ we.dec f p (some op))
        | none => pure f
      else pure f

def drawL {β : Type} (e : Enum β) : Lp lam K L β := LStep.sample e.n fun r => LStep.pure (e.e r)

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam))

/-- From the disclosed view of a slot to its proof string (Compile/Batch/Prover.lean: finishSlot,
after the check of the withheld set). -/
def finishBL {Z : Type} (x : Y) (ρ : Rho Q.loc.shape) (dv : DView Q.loc) (a0 : Acc0)
    (j : ℕ) (acc : SlotAcc lam K Z) :
    Lp lam K L (Option (OneProtocolProof lam Q)) :=
  let roots := rootToks acc.trees a0.trees
  let path := (a0.req.map fun rq => pathOf rq.levels j).getD []
  let anc := (a0.req.map fun rq => ancOf rq.levels j).getD []
  let pls := putB Q.loc.shape Q.ann wq.sh .first acc.nons.reverse a0.nons.reverse dv.plains
  LStep.reveal (acc.toks.headD 0 ::
        (roots ++ path ++ (a0.req.map TTree.root).toList ++
          anc ++ acc.toks ++ a0.toks ++ (acc.dead ++ a0.dead)))
      (ctxB t (trees.map TreeH.root) (xin x) Q.loc.shape Q.ann wq.sh embP 0
        .first acc.toks ((a0.req.map TTree.root).toList ++ a0.toks)
        acc.nons.reverse a0.nons.reverse dv.plains baseC) fun vs =>
  haveI := wq.decO
  haveI := wq.ext.dec
  (opensBL Q.loc.shape Q.ann wq.sh dv.orc embS acc.trees a0.trees
      (fun p => decide (p ∈ Q.loc.reads x ρ pls))).bind fun f =>
  (opensExtBL wq.ext dv.ext embE trees
      (fun p => decide (p ∈ Q.loc.extReads x ρ)) wq.ext.all).bind fun g =>
  pure (some ⟨vs.headD [], ((vs.drop 1).take roots.length).map (digD lam), pls, f, g,
    digD lam (vs.getD (1 + roots.length + path.length) []), j,
    ((vs.drop (1 + roots.length)).take path.length).map (digD lam)⟩)

/-! ### The honest prover -/

def finishAllL (w : Wt) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ℕ → List (SlotAcc lam K (Y × H.Coin)) → Lp lam K L (List (Option (OneProtocolProof lam Q)))
  | _, [] => pure []
  | j, acc :: zs =>
      (match acc.x with
        | some (x, cj) =>
            if fl j then
              haveI := wp.decW w x (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)
              if rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x then pure none
              else
                finishBL t Q wq embS embP xin embE trees x
                  (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)
                  (Q.loc.dview x (H.ext w)
                    ((H.one.strat w x (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks)).1)
                  a0 j acc
            else pure none
        | none => pure none).bind fun π =>
      (finishAllL w fl c0 a0 (j + 1) zs).bind fun r => pure (π :: r)

def initL (x : Option Y) : Lp lam K L (SlotSk lam K (Y × H.Coin) Q.loc.shape) :=
  (drawL wp.coin).bind fun cj =>
  LStep.fresh sFS fun salt =>
  LStep.pure (none, ⟨x.map fun x => (x, cj), salt, 0, [], [], [salt], [], []⟩)

/-- The honest prover: coins, hashing, and only then the messages (Compile/Batch/Prover.lean:
proveB). -/
def proveBL (w : Wt) (fl : ℕ → Bool) (xs : List (Option Y)) :
    Lp lam K L (List (Option (OneProtocolProof lam Q))) :=
  (drawL wp.coin0).bind fun c0 =>
  (eachL (initL sFS Q H wp) xs).bind fun zs =>
  (skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first none zs ⟨[], [], none, [], []⟩).bind fun out =>
  finishAllL t Q H wq wp embS embP xin embE trees w fl c0 out.2 0 out.1

/-! ### The reduction's subroutine -/

/-- what the reduction knows of a slot that it owns: the request, the challenges of the slot's
transcript, and the disclosed view or `none` -/
abbrev Own {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) : Type :=
  Y × Rho Q.loc.shape × Option (DView Q.loc)

def finishAllW (a0 : Acc0) :
    ℕ → List (SlotAcc lam K (Own Q)) → Lp lam K L (List (Option (OneProtocolProof lam Q)))
  | _, [] => pure []
  | j, acc :: zs =>
      (match acc.x with
        | some (x, ρ, some dv) => finishBL t Q wq embS embP xin embE trees x ρ dv a0 j acc
        | _ => pure none).bind fun π =>
      (finishAllW a0 (j + 1) zs).bind fun r => pure (π :: r)

def initW (o : Option (Own Q)) : Lp lam K L (SlotSk lam K (Own Q) Q.loc.shape) :=
  LStep.fresh sFS fun salt =>
    LStep.pure (o.map fun z => z.2.1, ⟨o, salt, 0, [], [], [salt], [], []⟩)

/-- The reduction's subroutine for one execution: for each slot what it knows of it (none: the slot
is not its own). It does the hashing of all slots. -/
def proveBW (os : List (Option (Own Q))) : Lp lam K L (List (Option (OneProtocolProof lam Q))) :=
  (eachL (initW sFS Q) os).bind fun zs =>
  (skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first (os.findSome? fun o => o.map fun z => z.2.1)
      zs ⟨[], [], none, [], []⟩).bind fun out =>
  finishAllW t Q wq embS embP xin embE trees out.2 0 out.1

end Prove

/-! ## Committer and prover (Compile/Batch/Star.lean: nodeP', proveT, proveLk, leavesC, Cp, PpJ,
Pp) -/

section StarL
open Compile.Lifetime (Sess)
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- the body of a leaf over a symbol of an encoded index -/
def embSg (s : L.Symbol) : Body L := some (.inl s)

/-- the tree over an encoded index: L.wordLength salted leaves, whose bodies are not named, and padding -/
def treeEL : Lp lam W.K L (TreeH lam) := commitEL p.sMT W.depth fun j => decide (j < L.wordLength)

def nodeLL : Lp lam W.K L (Node lam L) :=
  (drawL WP.ri).bind fun r => (treeEL W p).bind fun t => pure ⟨r, t⟩

def proveTL (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    Lp lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))) :=
  (proveBL p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T
      (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) embSg W.depthReq [tree] (i, r)
      (fun _ => true) [some ()]).bind fun l =>
  pure (l.headD none)

def proveLkL (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    Lp lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))) :=
  (proveBL p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
      (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) embSg W.depthReq [root, tree]
      (i, r₀, r) (fun _ => true) [some ()]).bind fun l =>
  pure (l.headD none)

def leavesCL (i : I) (root : Node lam L) : ℕ → Lp lam W.K L (List (LeafRec lam L))
  | 0 => pure []
  | n + 1 =>
      (nodeLL W WP p).bind fun nd =>
      (proveLkL W WP p root.tree nd.tree i root.r nd.r).bind fun π =>
      (leavesCL i root n).bind fun rest => pure (⟨nd, π⟩ :: rest)

def CpL (i : I) : Lp lam W.K L (IVK lam L × IskH lam L) :=
  (nodeLL W WP p).bind fun root =>
  (proveTL W WP p root.tree i root.r).bind fun πT =>
  (leavesCL W WP p i root (p.M + 1)).bind fun ls =>
  pure (⟨root.tree.root, πT⟩, ⟨i, root, ls⟩)

def PpJL (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    Lp lam W.K L (List (Prf lam L)) :=
  match k.leaves[j]? with
  | none => pure (xs.map fun _ => ⟨j, default, none, none⟩)
  | some lf =>
      (proveBL p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
          (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some embSg W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun πs =>
      pure ((List.range xs.length).map fun a =>
        ⟨j, lf.node.tree.root, lf.piL, if h : a < L.maxBatchSize then πs.getD (σ ⟨a, h⟩).val none else none⟩)

def PpL (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : Lp lam W.K L (List (Prf lam L)) :=
  LStep.sample p.M fun j => (drawL WP.perm).bind fun σ => PpJL W WP p k fr xs j.val σ

/-! ### The reduction's programs -/

/-- what the reduction keeps of the setup: for each copy its tree and Link's proof string -/
abbrev WKey (lam : ℕ) (L : BatchProtocol I X) : Type :=
  List (TreeH lam × Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))

def keyOf (k : IskH lam L) : WKey lam L := k.leaves.map fun lf => (lf.node.tree, lf.piL)

def proveTW (tree : TreeH lam) (s : Sess L.offline) :
    Lp lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.offline))) :=
  (proveBW p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) W.T
      (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) embSg W.depthReq
      [tree] [some ((), s.1, s.2)]).bind
    fun l => pure (l.headD none)

def proveLkW (root tree : TreeH lam) (s : Sess L.link) :
    Lp lam W.K L (Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link))) :=
  (proveBW p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) W.Lk
      (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) embSg W.depthReq
      [root, tree] [some ((), s.1, s.2)]).bind
    fun l => pure (l.headD none)

def leavesW (root : TreeH lam) : List (Sess L.link) → Lp lam W.K L (WKey lam L)
  | [] => pure []
  | s :: rest => (treeEL W p).bind fun tr => (proveLkW W p root tr s).bind fun π =>
      (leavesW root rest).bind fun k => pure ((tr, π) :: k)

/-- the reduction's setup, from what the experiment's setup returns -/
def CpW (sT : Sess L.offline) (ls : List (Sess L.link)) : Lp lam W.K L (IVK lam L × WKey lam L) :=
  (treeEL W p).bind fun root => (proveTW W p root sT).bind fun πT =>
  (leavesW W p root ls).bind fun key => pure (⟨root.root, πT⟩, key)

open Classical in
/-- what the reduction knows of the slots, from what the experiment's batch returns: sl are the slot
numbers of its requests xs, in their order -/
def ownsOf (xs : List X) (sl : List (Fin L.maxBatchSize))
    (J : Finset (Fin L.maxBatchSize)) (a : Compile.BatchLife.BSess L.onlineBatch J) : List (Option (Own L.onlineBatch)) :=
  (List.finRange L.maxBatchSize).map fun s =>
    if h : s ∈ J then (xs[sl.idxOf s]?).map fun x => (x, a.1 ⟨s, h⟩, a.2 ⟨s, h⟩) else none

/-- the reduction's batch on the copy j, from what the experiment's batch returns -/
def PpW (key : WKey lam L) (xs : List X) (j : ℕ) (ret : Compile.BatchLife.BRet L) :
    Lp lam W.K L (List (Prf lam L)) :=
  match key[j]? with
  | none => pure (xs.map fun _ => ⟨j, default, none, none⟩)
  | some (tr, piL) =>
      (proveBW p.sMT p.sFS Tag.onl L.onlineBatch W.B (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩))
          id some embSg W.depthReq [tr] (ownsOf xs ret.1 ret.2.1 ret.2.2)).bind fun πs =>
      pure ((List.range xs.length).map fun a =>
        ⟨j, tr.root, piL, (ret.1[a]?).bind fun s => πs.getD s.val none⟩)

end StarL

end Compile.Batch
