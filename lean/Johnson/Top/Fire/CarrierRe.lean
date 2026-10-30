-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/CarrierRe.lean: a law for exchanging the interface record at which the compiled
verifier's oracle queries are typed.

The compiled verifier of one proof string, `verifyOneProtocol` (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean), is
a tree of queries to typed oracles. The types of these queries have a whole interface record
`L : BatchProtocolWithLeafBody I X` as a parameter, though a query's type uses of that record only the type of a leaf's
body (`L.Bd`) and the types of the plain parts of the provers' messages (given by each protocol's
shape and annotation: `shapeOf`, `annOf`). The record has many more fields (an encoder, a decoder,
three protocols, honest provers), which may have no executable code. So that the verifier can be run
at a record that has executable code, the record is exchanged here for any other record L' over the
same type X of instances. (The library calls this record the carrier of the typed oracles; names
ending in `Re` or `_re` are about carrying over from L' to L.)

Variables: `bd` maps a leaf's body at L' to one at L; `pm` maps a plain part at L' to one at L, for
each of the three protocols. Nothing is asked of the two maps.

"Returns" is `OComp.det` (Rom/Cache.lean): the run in which every coin toss gives 0. `verifyOneProtocol`
tosses no coin (`detBound_verifyBS`, OnBytes/TypedOracleCompiler/Compile/Batch/GlueTools.lean); that is not used
here.

Main names.
  `pullF bd pm g`: oracle functions for L' made of oracle functions g for L: a query is carried over
    to L through `bd` and `pm` (`domRe`), then answered by g.
  `verifyBS_det_re`: the verifier at L, run at g, returns what the verifier at L' returns at
    `pullF bd pm g`, where the verifier at L is handed the three maps of the verifier at L' (into
    leaf bodies and plain parts) followed by `bd` and `pm`; all other arguments are the same. One
    premise, `SameOn`: both records write the same part of the instance into the queries (their
    fields `early` and `late`).
  `verifyBS_det_re_none`, `verifyBS_det_re_same`: two cases in which `SameOn` holds: the verifier is
    handed no instance; the two fields are equal.
  `verifyF_re`: the same for `verifyF` (OnBytes/TypedOracleCompiler/Run/VerifyDet.lean), the verifier as a plain
    function of the oracle functions.

Not shown here: anything about `verifyB`, the verifier without the strict check of the format and
with whole Merkle paths; anything about oracle queries that a larger verifier makes outside
`verifyOneProtocol`; that the oracle functions of a given run at L' are `pullF bd pm g` for some g; that any
term here has executable code; that the verifier accepts anything. Nothing on soundness; no
probability.

Remains: the protocol and its wire record are the same on both sides, so whoever runs the verifier
at L' has to evaluate them too. The executable `verify-on-bytes` does not import this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.VerifyDetProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Run
open TypedOracleCompiler.Iop Rom _root_.Compile TypedOracleCompiler.Compile.Batch
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

section
variable {I I' X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {L' : BatchProtocolWithLeafBody I' X}
  (bd : Body L' → Body L)
  (pm : (t : Tag) → PlainPart (shapeOf L' t) (annOf L' t) → PlainPart (shapeOf L t) (annOf L t))

/-! ## Queries, checks and forests carried over from L' to L -/

/-- A leaf query at L' carried over to L. -/
def leafRe (q : LeafIn L') : LeafIn L := ⟨bd q.body, q.salt⟩

/-- A query at L' carried over to L. -/
def domRe : (o : TypedOracleCompiler.Compile.Batch.OracleName) → domOf lam L' o → domOf lam L o
  | .leaf, q => leafRe bd q
  | .node, q => q
  | .rleaf, q => q
  | .rnode, q => q
  | .fb t, q => (⟨q.round, q.head, q.rt, pm t q.plain⟩ : FbIn lam L t)
  | .fbw t _, q => (⟨q.round, q.head, q.rt, pm t q.plain⟩ : FbIn lam L t)
  | .g t, q => (⟨q.round, q.ρ, q.rt, pm t q.plain⟩ : JoiningRoundQuery lam L t)
  | .ann, q => q
  | .other, q => q

/-- Oracle functions for L': a query is carried over to L, then answered by g. -/
def pullF (g : Fam (typedOracleFamily lam K L)) : Fam (typedOracleFamily lam K L') :=
  fun o q => g o (domRe bd pm o q)

/-- One check of an opening at L' carried over to L. -/
def checkRe (c : Check lam L') : Check lam L := ⟨leafRe bd c.inp, c.j, c.path, c.root, c.depth⟩

/-- A forest (the checks in some trees of one depth) at L' carried over to L. -/
def forestRe (F : Forest lam L') : Forest lam L :=
  ⟨F.depth, F.treeRoot, F.cs.map fun e => (e.1, checkRe bd e.2)⟩

/-! ## The chain -/

omit bd pm in
/-- Without an instance, the round that would hold the whole instance holds none. -/
theorem lateF_none (L : BatchProtocolWithLeafBody I X) (i : ℕ) : lateInstancePart L i (none : Option X) = none := by
  unfold lateInstancePart
  split <;> rfl

/-- Both records write the same part of the instance x into the chain's queries: into the first
query, and into the round that holds the whole instance. -/
def SameOn (L : BatchProtocolWithLeafBody I X) (L' : BatchProtocolWithLeafBody I' X) (x : Option X) : Prop :=
  x.map L'.early = x.map L.early ∧ ∀ i, lateInstancePart L' i x = lateInstancePart L i x

omit bd pm in
/-- `SameOn` holds where there is no instance. -/
theorem sameOn_none : SameOn L L' none :=
  ⟨rfl, fun i => (lateF_none L' i).trans (lateF_none L i).symm⟩

omit bd pm in
/-- `SameOn` holds at every instance, if the records' fields `early` and `late` are equal. -/
theorem sameOn_of_eq (he : L'.early = L.early) (hl : L'.late = L.late) (x : Option X) :
    SameOn L L' x :=
  ⟨by rw [he], fun i => by unfold lateInstancePart; rw [hl]⟩

/-- The hash chain that gives the verifier's messages: at L' under `pullF bd pm g` it returns what
it returns at L under g with `pm` after its map, if `SameOn` holds. -/
theorem chainF_re (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (hx : SameOn L L' x) (salt : Bits) (rtreq : Dig lam) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L' t) (annOf L' t)) (i : ℕ) (ph : Phase lam)
        (rts : List (Dig lam)) (pls : Plains s),
      chainF (pullF bd pm g) t cms x salt rtreq s A W embP i ph rts pls =
        chainF g t cms x salt rtreq s A W (fun z => pm t (embP z)) i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      simp only [chainF, hx.1, hx.2]
      generalize actOf cms (x.map L.early) salt a.kind ph = act
      cases act with
      | none => rfl
      | some ac =>
        cases ac with
        | one h own next =>
          cases own with
          | true =>
            dsimp only
            generalize takeRt w.depthJ.length rts = tr
            cases tr with
            | none => rfl
            | some p =>
              dsimp only
              rw [chainF_re g t cms x hx salt rtreq s A W]
              rfl
          | false =>
            dsimp only
            generalize takeRt w.depth0.length rts = tr
            cases tr with
            | none => rfl
            | some p =>
              dsimp only
              rw [chainF_re g t cms x hx salt rtreq s A W]
              rfl
        | join r =>
          dsimp only
          generalize takeRt w.depthJ.length rts = tr
          cases tr with
          | none => rfl
          | some p =>
            dsimp only
            generalize takeRt w.depth0.length p.2 = tr2
            cases tr2 with
            | none => rfl
            | some p2 =>
              dsimp only
              rw [chainF_re g t cms x hx salt rtreq s A W]
              rfl

/-! ## The lists of checks -/

/-- The checks of one tree at L are those at L' carried over. -/
theorem checksComp_re {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L') (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ,
      checksComp (L := L) posAt depth (fun p a => bd (emb p a)) rt isRead f js =
        (checksComp (L := L') posAt depth emb rt isRead f js).map (List.map (checkRe bd))
  | [] => rfl
  | j :: js => by
      have ih := checksComp_re posAt depth emb rt isRead f js
      simp only [checksComp]
      cases posAt j with
      | none => exact ih
      | some p =>
        dsimp only
        cases isRead p with
        | false => exact ih
        | true =>
          simp only [if_true]
          rw [ih]
          cases f p with
          | none => rfl
          | some op =>
            cases checksComp (L := L') posAt depth emb rt isRead f js with
            | none => rfl
            | some cs => rfl

/-- One tree's depth, root and checks at L' carried over to L. -/
def treeRe (z : ℕ × Dig lam × List (Check lam L')) : ℕ × Dig lam × List (Check lam L) :=
  (z.1, z.2.1, z.2.2.map (checkRe bd))

/-- The same for all trees of one component. -/
theorem checksTrees_re {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L') (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ) (cs : List (Dig lam)),
      checksTrees (L := L) posAt (fun p a => bd (emb p a)) isRead f k ds cs =
        (checksTrees (L := L') posAt emb isRead f k ds cs).map (List.map (treeRe bd))
  | _, [], _ => by simp only [checksTrees]; rfl
  | _, _ :: _, [] => by simp only [checksTrees]; rfl
  | k, d :: ds, c :: cs => by
      simp only [checksTrees]
      rw [checksComp_re bd (posAt k) d emb c isRead f,
        checksTrees_re posAt emb isRead f (k + 1) ds cs]
      cases checksComp (L := L') (posAt k) d emb c isRead f (List.range (2 ^ d)) with
      | none => rfl
      | some a =>
        cases checksTrees (L := L') posAt emb isRead f (k + 1) ds cs with
        | none => rfl
        | some b => rfl

/-- Splitting a forest commutes with carrying it over. -/
theorem split_re (pr : Bool) (F : Forest lam L') :
    Forest.split pr (forestRe bd F) = (Forest.split pr F).map (forestRe bd) := by
  unfold Forest.split
  cases pr with
  | true => rfl
  | false =>
    simp only [Bool.false_eq_true, if_false, forestRe, List.map_map]
    rfl

/-- The forests of one component's trees at L are those at L' carried over. -/
theorem forestsT_re (pr : Bool) (l : List (ℕ × Dig lam × List (Check lam L'))) :
    forestsT pr (l.map (treeRe bd)) = (forestsT pr l).map (forestRe bd) := by
  unfold forestsT
  induction l with
  | nil => rfl
  | cons z l ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, ih]
    congr 1
    rw [← split_re]
    simp only [forestRe, treeRe, List.map_map]
    rfl

/-- The same for the forests over all of the prover's messages. -/
theorem forestsB_re :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (emb : (p : OPos s) → OSym s p → Body L')
        (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))),
      forestsB (L := L) s A W (fun p a => bd (emb p a)) rts isRead f =
        (forestsB (L := L') s A W emb rts isRead f).map (List.map (forestRe bd))
  | [], _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f => by
      have h1 := checksTrees_re bd w.posAt0 (fun p => emb (.inl p)) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD [])
      have h2 := checksTrees_re bd w.posAtJ (fun p => emb (.inl p)) (fun p => isRead (.inl p))
        (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD [])
      have h3 := forestsB_re s A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p))
        (fun p => f (.inr p))
      simp only [forestsB]
      -- `erw`, not `rw`: the goal's functions are typed at `OSym (r :: s) (.inl p)`, those of h1,
      -- h2, h3 at `r.Sym p`; the two types are equal only after unfolding `OSym`.
      erw [h1, h2, h3]
      cases checksTrees (L := L') w.posAt0 (fun p => emb (.inl p)) (fun p => isRead (.inl p))
          (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []) with
      | none => rfl
      | some a =>
        cases checksTrees (L := L') w.posAtJ (fun p => emb (.inl p)) (fun p => isRead (.inl p))
            (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []) with
        | none => rfl
        | some b =>
          cases forestsB (L := L') s A W (fun p => emb (.inr p)) rts (fun p => isRead (.inr p))
              (fun p => f (.inr p)) with
          | none => rfl
          | some c =>
            simp only [Option.map_some, forestsT_re, List.map_append]

/-- The same for the checks over the external oracles. -/
theorem checksExtW_re {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L') (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    ∀ ps : List E.Pos,
      checksExtW (L := L) we (fun a => bd (emb a)) cms isRead f ps =
        (checksExtW (L := L') we emb cms isRead f ps).map
          (List.map fun e => (e.1, checkRe bd e.2))
  | [] => rfl
  | p :: ps => by
      have ih := checksExtW_re we emb cms isRead f ps
      simp only [checksExtW]
      cases isRead p with
      | false => exact ih
      | true =>
        simp only [if_true]
        rw [ih]
        cases f p with
        | none => rfl
        | some op =>
          cases checksExtW (L := L') we emb cms isRead f ps with
          | none => rfl
          | some cs => rfl

/-- The same for the forest over the external oracles. -/
theorem forestExt_re {E : ExtSpec} (we : WireE E) (emb : E.Sym → Body L') (cms : List (Dig lam))
    (isRead : E.Pos → Bool) (f : E.Pos → Option (Opening lam E.Sym)) :
    forestExt (L := L) we (fun a => bd (emb a)) cms isRead f =
      (forestExt (L := L') we emb cms isRead f).map (List.map (forestRe bd)) := by
  unfold forestExt
  rw [checksExtW_re]
  cases checksExtW (L := L') we emb cms isRead f we.all with
  | none => rfl
  | some cs =>
    simp only [Option.map_some]
    rw [← split_re]
    rfl

variable {Y : Type} {E : ExtSpec}

/-- All forests of a proof string at L are those at L' carried over. -/
theorem forestsOf_re (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L') (embE : E.Sym → Body L')
    (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (r : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) :
    forestsOf (L := L) Q wq (fun p a => bd (embS p a)) (fun a => bd (embE a)) cms x π r rts =
      (forestsOf (L := L') Q wq embS embE cms x π r rts).map (List.map (forestRe bd)) := by
  unfold forestsOf
  rw [forestsB_re, forestExt_re]
  cases forestsB (L := L') Q.loc.shape Q.ann wq.sh embS rts _ π.opens with
  | none => rfl
  | some a =>
    cases forestExt (L := L') wq.ext embE cms _ π.ext with
    | none => rfl
    | some b => simp only [Option.map_some, List.map_append]

/-! ## What is read off the forests -/

omit pm in
theorem idx_re (F : Forest lam L') : (forestRe bd F).idx = F.idx := by
  simp only [Forest.idx, forestRe, List.map_map]
  rfl

omit pm in
theorem need_re (F : Forest lam L') : (forestRe bd F).need = F.need := by
  unfold Forest.need
  rw [idx_re]
  rfl

omit pm in
theorem reads_re (F : Forest lam L') : (forestRe bd F).reads = F.reads := by
  simp only [Forest.reads, forestRe, List.map_map]
  rfl

omit pm in
theorem flatF_re (Fs : List (Forest lam L')) :
    flatF (Fs.map (forestRe bd)) = (flatF Fs).map (checkRe bd) := by
  unfold flatF
  induction Fs with
  | nil => rfl
  | cons F Fs ih =>
    simp only [List.map_cons, List.flatMap_cons, List.map_append, ih, forestRe, List.map_map]
    rfl

omit pm in
theorem readsF_re (Fs : List (Forest lam L')) : readsF (Fs.map (forestRe bd)) = readsF Fs := by
  unfold readsF
  induction Fs with
  | nil => rfl
  | cons F Fs ih => simp only [List.map_cons, List.flatMap_cons, ih, reads_re]

/-! ## Checking the forests -/

/-- Checking a forest carried over, at g, is checking it at `pullF bd pm g`. -/
theorem runForestF_re (g : Fam (typedOracleFamily lam K L)) (F : Forest lam L') (s : List (Dig lam)) :
    runForestF g (forestRe bd F) s = runForestF (pullF bd pm g) F s := by
  unfold runForestF
  rw [idx_re]
  simp only [forestRe, List.map_map]
  rfl

/-- The same for a list of forests. -/
theorem runForestsF_re (g : Fam (typedOracleFamily lam K L)) :
    ∀ (Fs : List (Forest lam L')) (s : List (Dig lam)),
      runForestsF g (Fs.map (forestRe bd)) s = runForestsF (pullF bd pm g) Fs s
  | [], _ => rfl
  | F :: Fs, s => by
    simp only [List.map_cons, runForestsF, runForestF_re bd pm, need_re, runForestsF_re g Fs]

/-- The check in the request tree asks no query whose type depends on the record. -/
theorem reqPartF_re (g : Fam (typedOracleFamily lam K L)) {Q : BatchInteractiveOracleProof Y E} (depthReq : ℕ)
    (π : OneProtocolProof lam Q) (ph : Phase lam) :
    reqPartF (pullF bd pm g) depthReq π ph = reqPartF g depthReq π ph := rfl

/-! ## The verifier -/

/-- The verifier's part after the chain, likewise. -/
theorem afterBOF_re (g : Fam (typedOracleFamily lam K L)) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L') (embE : E.Sym → Body L')
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (r : Rho Q.loc.shape)
    (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    afterBOF (pullF bd pm g) Q wq embS embE depthReq cms x π r rts ph =
      afterBOF g Q wq (fun p a => bd (embS p a)) (fun a => bd (embE a)) depthReq cms x π r rts
        ph := by
  unfold afterBOF
  rw [forestsOf_re]
  cases forestsOf (L := L') Q wq embS embE cms x π r rts with
  | none => rfl
  | some Fs =>
    simp only [Option.map_some, flatF_re, readsF_re, List.length_map, List.all_map,
      runForestsF_re bd pm, reqPartF_re]
    rfl

/-- **`verifyF` at L, handed the maps of L' followed by `bd` and `pm`, returns at g what `verifyF`
at L' returns at `pullF bd pm g`**, if `SameOn` holds at the instance. -/
theorem verifyF_re (g : Fam (typedOracleFamily lam K L)) (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X)
    (embE : E.Sym → Body L') (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (hx : SameOn L L' (xin x)) :
    verifyF (pullF bd pm g) sMT sFS t Q wq embS embP xin embE depthReq cms x π =
      verifyF g sMT sFS t Q wq (fun p a => bd (embS p a)) (fun z => pm t (embP z)) xin
        (fun a => bd (embE a)) depthReq cms x π := by
  unfold verifyF
  rw [chainF_re bd pm g t cms (xin x) hx]
  cases chainF g t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh (fun z => pm t (embP z)) 0
      .first π.roots π.plains with
  | none => rfl
  | some r =>
    dsimp only
    rw [afterBOF_re]

/-- **`verifyOneProtocol` at L, handed the maps of L' followed by `bd` and `pm`, returns at g what `verifyOneProtocol`
at L' returns at `pullF bd pm g`**, if `SameOn` holds at the instance. -/
theorem verifyBS_det_re (g : Fam (typedOracleFamily lam K L)) (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X)
    (embE : E.Sym → Body L') (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (hx : SameOn L L' (xin x)) :
    (verifyOneProtocol (L := L) (K := K) sMT sFS t Q wq (fun p a => bd (embS p a))
        (fun z => pm t (embP z)) xin (fun a => bd (embE a)) depthReq cms x π).det g =
      (verifyOneProtocol (L := L') (K := K) sMT sFS t Q wq embS embP xin embE depthReq cms x π).det
        (pullF bd pm g) := by
  rw [verifyBS_det, verifyBS_det, verifyF_re bd pm g sMT sFS t Q wq embS embP xin embE depthReq cms
    x π hx]

/-- Where the verifier is handed no instance: no premise. -/
theorem verifyBS_det_re_none (g : Fam (typedOracleFamily lam K L)) (sMT sFS : ℕ) (t : Tag)
    (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (embE : E.Sym → Body L')
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    (verifyOneProtocol (L := L) (K := K) sMT sFS t Q wq (fun p a => bd (embS p a))
        (fun z => pm t (embP z)) (fun _ => none) (fun a => bd (embE a)) depthReq cms x π).det g =
      (verifyOneProtocol (L := L') (K := K) sMT sFS t Q wq embS embP (fun _ => none) embE depthReq cms x
        π).det (pullF bd pm g) :=
  verifyBS_det_re bd pm g sMT sFS t Q wq embS embP (fun _ => none) embE depthReq cms x π
    sameOn_none

/-- Where the two records have equal fields `early` and `late`: at every instance. -/
theorem verifyBS_det_re_same (he : L'.early = L.early) (hl : L'.late = L.late)
    (g : Fam (typedOracleFamily lam K L)) (sMT sFS : ℕ) (t : Tag) (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L')
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L' t) (annOf L' t)) (xin : Y → Option X)
    (embE : E.Sym → Body L') (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) :
    (verifyOneProtocol (L := L) (K := K) sMT sFS t Q wq (fun p a => bd (embS p a))
        (fun z => pm t (embP z)) xin (fun a => bd (embE a)) depthReq cms x π).det g =
      (verifyOneProtocol (L := L') (K := K) sMT sFS t Q wq embS embP xin embE depthReq cms x π).det
        (pullF bd pm g) :=
  verifyBS_det_re bd pm g sMT sFS t Q wq embS embP xin embE depthReq cms x π
    (sameOn_of_eq he hl _)

end

end TypedOracleCompiler.Run

#print axioms TypedOracleCompiler.Run.chainF_re
#print axioms TypedOracleCompiler.Run.forestsOf_re
#print axioms TypedOracleCompiler.Run.afterBOF_re
#print axioms TypedOracleCompiler.Run.verifyF_re
#print axioms TypedOracleCompiler.Run.verifyBS_det_re
#print axioms TypedOracleCompiler.Run.verifyBS_det_re_none
#print axioms TypedOracleCompiler.Run.verifyBS_det_re_same
