-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SizeO.lean: size bounds for keys and proofs with pruned Merkle paths.

The file treats the schemes of Compile/Batch/StarO.lean (words of this library: lean/GLOSSARY.md).
For full paths, Compile/Batch/Size.lean and Compile/Batch/SizeAccepted.lean have what is serialized
and the conditions on the format, but no size bound for keys and proofs. A proof string (`BPrfO`)
holds one list `sibs` of sibling digests (Hash/Octopus.lean) in place of a Merkle path for each
opened position. In Lean names an entry of a key is a `Pair`, the number of a copy a `leaf`. From
serializers `D` of symbols and plain parts the file builds serializations of keys and of the proofs
of `VKO`, injective if the wire record `W` is well-formed (`putIVKO_injective`,
`putIVKKO_injective`, `putPrfKO_injective`). It proves three things.

  1. If `VO` or `VKO` accepts under some oracle functions, whoever made key and proof, then the part
     (cm, Test's proof string) of the key, the proof of `VKO`, and the entry that `VKO` reads are
     each within an explicit bound, a sum over the rounds with a few further terms
     (`sizeIVKO_le_of_accepted`, `sizePrfKO_le_of_accepted`, `sizePairO_le_of_accepted`). The
     proof's bound grows with the number of entries in the key.
  2. `sibsAccepted`: under the hypotheses of its statement (beside those below: `ExtInj`), an
     accepted proof string has exactly as many sibling digests as the verification consumes, and at
     most `sibBound`. The equality rests on the verifier's check `usedUp`; without that check
     surplus digests would be accepted and no bound on the length would hold.
  3. `VO` uses no coins and makes at most `tVB W` queries to the typed oracles, one oracle for each
     kind of query (`detBound_VO`). The queries of `VO` and `VKO`, each weighed by the hash blocks
     of its answer (`blk`), add up to at most `cVB W` (`costBound_VO`, `costBound_VKO`); for one
     hash function: Rom/Cost.lean. Both are the bounds of the verifier for full paths.

Hypotheses: a well-formed wire record `W` (Iop/BatchWire.lean): the theorems of point 1 take `W.OK`;
their forms with the suffix Gr, and the lemmas, take `W.OKG`, which allows proof-of-work bits.
Numbers `Z` that bound the positions that the three verifiers read and the widths of the serializers
(`OpensOK`, `SizeNums.Within`). And, where the trees over encodings of the index (the external
strings) are pruned, that `W` lists their positions in ascending order of the leaf numbers, which
are in range (`ExtAscOK`). The trees over prover messages need no such hypothesis: they are verified
in the order of their leaves by construction.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Notation: `VO`: "The verifier for pruned keys and proofs"; `VKO`: "The verifier for pruned keys that
list the entries, and pruned proofs" (both: Compile/Batch/StarO.lean); `verifyBO`: "The compiled
verifier of one slot for proof strings with pruned Merkle paths"; `verifyBC`: "the chain; the
strict-format check; then afterBC"; `Plan`: "a forest as the proof string shows it: its depth; the
numbers of the leaves at which the proof string holds an opening, each with its path"; `planOf`:
"all forests of a proof string"; `Plan.need`, `needAll`: natural numbers (`Octopus.need`,
Hash/Octopus.lean); `fillO`: a `OneProtocolProof` made from a `BPrfO` (all these: Compile/Batch/Pruned.lean);
`reP`: Compile/Batch/Verifier.lean; `gam n`: "The number of bits of the self-delimiting binary
encoding of n" (Iop/Ser.lean); `octMax`: Hash/OctopusFacts.lean; `eN.x`: a field of `ExtNums`
(Compile/Size.lean): "the bits of (position, symbol)"; `blk`: "the number of hash blocks of lam bits
in an answer" (Compile/Batch/ImplOf.lean); `tVB`: Compile/Batch/SpecBinding.lean; `cVB`:
Compile/Batch/VCost.lean.

Limits: there is no bound on the whole list of entries of a key, and none on a proof of `VO`. The
bounds are not tight. The two trees of a round (over the shared and the slot's component of the
prover message) are counted together with all n openings of the round, at the larger of the two
depths (if only one of the two is pruned, each with all n). As in Compile/Batch/Size.lean, the
request path (the path of a slot in the request tree, the tree over the slots of a batch) is counted
for Test and Link too. Nothing is stated about honest outputs as such.
-/
import Compile.Batch.MainO
import Iop.SizesO
import Iop.BatchWirePr
import Compile.Batch.SizeAccepted
import Compile.Batch.VCost

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom Octopus Compile.GenLe Compile.Batch.SizeA
open Ser (gam)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 0. The queries of the verifiers for pruned proof strings -/

section Cost
variable {P : {α : Type} → TypedOracleComputation lam K L α → ℕ → Prop} (hP : Counts (spec lam K L) P)
  (hleaf : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.leaf q) 1)
  (hnode : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.node q) 1)
  (hrleaf : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.rleaf q) 1)
  (hrnode : ∀ q, P (askTypedOracle (L := L) (K := K) OracleName.rnode q) 1)
include hP hleaf hnode hrleaf hrnode

theorem Counts.afterBC {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L) (embE : E.Sym → Body L)
    (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q) (s : List (Dig lam))
    (ρ : Rho Q.loc.shape) (rts : RootsOfChain lam Q.loc.shape) (ph : Phase lam) :
    P (afterBC Q wq embS embE depthReq cms x π s ρ rts ph)
      (wq.nOpen * (wq.maxDepth + 1) + reqCost depthReq ph) := by
  unfold Compile.Batch.afterBC
  split
  · rename_i Fs hFs
    split_ifs with hc
    · refine Counts.afterF hP hleaf hnode hrleaf hrnode Q wq depthReq x π ρ rts ph Fs _ hc.1.1
        (fun c hmem => ?_) (forestsOf_spec hFs).1
      have := List.all_eq_true.1 hc.1.2 c hmem
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.2
    · exact hP.pure _ _
  · exact hP.pure _ _

end Cost

theorem detBound_verifyBC (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y) (π : OneProtocolProof lam Q)
    (s : List (Dig lam)) :
    DetBound (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s)
      (tVQB wq depthReq) := by
  unfold verifyBC recomputeChainOfProof tVQB
  refine (detBound_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains).bind fun r => ?_
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact detBound_pure _ _
  · dsimp only
    split_ifs
    · exact (Counts.afterBC (counts_detBound (spec lam K L)) (detBound_askV _) (detBound_askV _)
          (detBound_askV _) (detBound_askV _) Q wq embS embE depthReq cms x π s ρ rts ph).mono
        (Nat.add_le_add_left (reqCost_le _ _) _)
    · exact detBound_pure _ _

theorem cb_verifyBC (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
    (π : OneProtocolProof lam Q) (s : List (Dig lam)) :
    VCost.CB (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s)
      (cVQB wq depthReq) := by
  unfold verifyBC recomputeChainOfProof cVQB
  refine OComp.CostBound.bind (fun r => ?_)
    (VCost.cb_chainB t cms (xin x) π.salt π.rtreq Q.loc.shape Q.ann wq.sh embP 0
      .first π.roots π.plains)
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact OComp.CostBound.pure _ _
  · dsimp only
    split_ifs
    · exact (Counts.afterBC VCost.counts_cb (VCost.cb_askV OracleName.leaf)
          (VCost.cb_askV OracleName.node) (VCost.cb_askV OracleName.rleaf) (VCost.cb_askV OracleName.rnode)
          Q wq embS embE depthReq cms x π s ρ rts ph).mono
        (Nat.add_le_add_left (reqCost_le _ _) _)
    · exact OComp.CostBound.pure _ _

/-- `VO` uses no coins and makes at most `tVB W` queries: the bound of `V`. -/
theorem detBound_VO {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (v : IVKO lam L)
    (x : X) (π : PrfO lam L) :
    DetBound (VO W p v x π) (tVB W) := by
  unfold VO tVB
  split
  · split_ifs
    · simp only [bind_eq]
      refine ((detBound_verifyBC _ _ _ _ W.T _ _ _ _ _ _ _ _ _).bind
        (t := tVQB W.Lk W.depthReq + (tVQB W.B W.depthReq + 0)) fun a =>
          (detBound_verifyBC _ _ _ _ W.Lk _ _ _ _ _ _ _ _ _).bind
            (t := tVQB W.B W.depthReq + 0) fun b =>
              (detBound_verifyBC _ _ _ _ W.B _ _ _ _ _ _ _ _ _).bind (t := 0) fun c =>
                detBound_pure _ _).mono ?_
      omega
    · exact detBound_pure _ _
  · exact detBound_pure _ _

/-- On every execution path the queries of `VO`, each weighed by the hash blocks of its answer
(`blk`), add up to at most `cVB W`, as for `V`. -/
theorem costBound_VO {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (v : IVKO lam L)
    (x : X) (π : PrfO lam L) :
    OComp.CostBound (S := spec lam W.K L) (blk W.K) (VO W p v x π) (cVB W) := by
  unfold VO cVB
  split
  · split_ifs
    · simp only [bind_eq]
      refine (OComp.CostBound.bind (t := cVQB W.Lk W.depthReq + (cVQB W.B W.depthReq + 0)) (fun a =>
        OComp.CostBound.bind (t := cVQB W.B W.depthReq + 0) (fun b =>
          OComp.CostBound.bind (t := 0) (fun c => OComp.CostBound.pure _ _)
            (cb_verifyBC _ _ _ _ W.B _ _ _ _ _ _ _ _ _))
          (cb_verifyBC _ _ _ _ W.Lk _ _ _ _ _ _ _ _ _)) (cb_verifyBC _ _ _ _ W.T _ _ _ _ _ _ _ _ _)).mono ?_
      omega
    · exact OComp.CostBound.pure _ _
  · exact OComp.CostBound.pure _ _

theorem costBound_VKO {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (v : IVKKO lam L)
    (x : X) (π : PrfKO lam L) :
    OComp.CostBound (S := spec lam W.K L) (blk W.K) (VKO W p v x π) (cVB W) :=
  costBound_VO W p v.1 x (reKO v.2 π)

/-! ## Part 1. The serialization -/

/-- an opened position of a round, with symbol and salt -/
abbrev EntRO (r : Round) : Type := Σ p : r.Pos, OpenO (r.Sym p)

def serEntRO {r : Round} (a : Ser (Σ p : r.Pos, r.Sym p)) : Ser (EntRO r) :=
  Ser.ofEquiv (β := (Σ p : r.Pos, r.Sym p) × Bits)
    ⟨fun e => (⟨e.1, e.2.sym⟩, e.2.salt), fun y => ⟨y.1.1, ⟨y.1.2, y.2⟩⟩,
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod a serBits)

/-- for each round the list of its opened positions -/
def EntSO : Shape → Type
  | [] => Unit
  | r :: s => List (EntRO r) × EntSO s

def serEntSO : (s : Shape) → SerS s → Ser (EntSO s)
  | [], _ => Ser.unit
  | _ :: s, ((a, _), e) => Ser.prod (Ser.lenList (serEntRO a)) (serEntSO s e)

/-- the opened positions of one component of one round, in the order of the leaves of its tree -/
def entriesCO {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (g : (p : r.Pos) → Option (OpenO (r.Sym p))) : List (EntRO r) :=
  (List.range (2 ^ depth)).filterMap fun j => (posAt j).bind fun p => (g p).map fun op => ⟨p, op⟩

/-- The opened positions of one component with a list of trees, from tree number k on: in the order
of the trees, and in each tree in the order of its leaves (`entriesCO`). -/
def entriesTreesO {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (OpenO (r.Sym p))) : ℕ → List ℕ → List (EntRO r)
  | _, [] => []
  | k, d :: ds => entriesCO (posAt k) d g ++ entriesTreesO posAt g (k + 1) ds

theorem entriesTreesO_one {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (OpenO (r.Sym p))) (k d : ℕ) :
    entriesTreesO posAt g k [d] = entriesCO (posAt k) d g := by
  simp [entriesTreesO]

theorem entriesTreesO_nil {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (OpenO (r.Sym p))) (k : ℕ) :
    entriesTreesO posAt g k [] = [] := rfl

def entriesSBO :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → Option (OpenO (OSym s p))) → EntSO s
  | [], _, _, _ => ()
  | _ :: s, (_, A), (w, W), g =>
      (entriesCO w.posAt0 w.depth0 (fun p => g (.inl p)) ++
          entriesCO w.posAtJ w.depthJ (fun p => g (.inl p)),
        entriesSBO s A W fun p => g (.inr p))

/-- an opened external position, with symbol and salt -/
abbrev EntEO (E : ExtSpec) : Type := E.Pos × OpenO E.Sym

def serEntEO {E : ExtSpec} (sp : Ser E.Pos) (ss : Ser E.Sym) : Ser (EntEO E) :=
  Ser.ofEquiv (β := (E.Pos × E.Sym) × Bits)
    ⟨fun e => ((e.1, e.2.sym), e.2.salt), fun y => (y.1.1, ⟨y.1.2, y.2⟩),
      fun _ => rfl, fun _ => rfl⟩
    (Ser.prod (Ser.prod sp ss) serBits)

def entriesEO {E : ExtSpec} (we : WireE E) (g : E.Pos → Option (OpenO E.Sym)) : List (EntEO E) :=
  we.all.filterMap fun p => (g p).map fun op => (p, op)

/-- what is serialized of a proof string -/
abbrev BTO (lam : ℕ) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) : Type :=
  Bits × List (Dig lam) × Plains Q.loc.shape × EntSO Q.loc.shape × List (EntEO E) × List (Dig lam) ×
    Dig lam × ℕ × List (Dig lam)

section B
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

def encBO (wq : ProtocolQueryLayout lam K Q) (π : BPrfO lam Q) : BTO lam Q :=
  (π.salt, π.roots, π.plains, entriesSBO Q.loc.shape Q.ann wq.sh π.opens, entriesEO wq.ext π.ext,
    π.sibs, π.rtreq, π.slot, π.path)

def serBTO (lam : ℕ) (Q : BatchInteractiveOracleProof Y E) (S : SerS Q.loc.shape) (sp : Ser E.Pos) (ss : Ser E.Sym) :
    Ser (BTO lam Q) :=
  Ser.prod serBits
    (Ser.prod (serDigs lam)
      (Ser.prod (serPlains Q.loc.shape S)
        (Ser.prod (serEntSO Q.loc.shape S)
          (Ser.prod (Ser.lenList (serEntEO sp ss))
            (Ser.prod (serDigs lam) (Ser.prod (serDig lam) (Ser.prod Ser.natG (serDigs lam))))))))

end B

/-! ### Comparison with the serialization with full paths -/

/-- openings without paths, as openings with empty paths -/
def bareF {ι : Type} {σ : ι → Type} (g : (p : ι) → Option (OpenO (σ p))) :
    (p : ι) → Option (Opening lam (σ p)) :=
  fun p => (g p).map OpenO.bare

theorem entriesC_reP {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (g : (p : r.Pos) → Option (OpenO (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    entriesC posAt depth (reP (bareF g) P) =
      (entriesCO posAt depth g).map fun e => ⟨e.1, ⟨e.2.sym, e.2.salt, P e.1⟩⟩ := by
  unfold entriesC entriesCO reP bareF
  rw [List.map_filterMap]
  refine List.filterMap_congr fun j _ => ?_
  cases posAt j with
  | none => rfl
  | some p =>
    show (((g p).map _).map _).map _ = ((g p).map _).map _
    cases g p <;> rfl

/-- The openings g, which have no paths, taken with the paths P: the list of their opened positions,
for all trees of a component from tree number k on, is the list without paths (`entriesTreesO`) with
the path P p laid into the entry of each position p. -/
theorem entriesTrees_reP {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (OpenO (r.Sym p))) (P : r.Pos → List (Dig lam)) :
    ∀ (k : ℕ) (ds : List ℕ),
      entriesTrees posAt (reP (bareF g) P) k ds =
        (entriesTreesO posAt g k ds).map fun e => ⟨e.1, ⟨e.2.sym, e.2.salt, P e.1⟩⟩
  | _, [] => rfl
  | k, d :: ds => by
      rw [entriesTrees, entriesTreesO, List.map_append, entriesC_reP,
        entriesTrees_reP posAt g P (k + 1) ds]

/-- the lists of opened positions, with the paths P -/
def EntSO.up : (s : Shape) → (OPos s → List (Dig lam)) → EntSO s → EntS lam s
  | [], _, _ => ()
  | _ :: s, P, (l, e) =>
    (l.map fun x => ⟨x.1, ⟨x.2.sym, x.2.salt, P (.inl x.1)⟩⟩, EntSO.up s (fun p => P (.inr p)) e)

theorem entriesSB_reP :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (g : (p : OPos s) → Option (OpenO (OSym s p))) (P : OPos s → List (Dig lam)),
      entriesSB s A W (reP (bareF g) P) = EntSO.up s P (entriesSBO s A W g)
  | [], _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), g, P => by
      have h0 := entriesC_reP w.posAt0 w.depth0 (fun p => g (.inl p)) fun p => P (.inl p)
      have hJ := entriesC_reP w.posAtJ w.depthJ (fun p => g (.inl p)) fun p => P (.inl p)
      have h2 := entriesSB_reP s A W (fun p => g (.inr p)) fun p => P (.inr p)
      show (entriesC w.posAt0 w.depth0 _ ++ entriesC w.posAtJ w.depthJ _, entriesSB s A W _) =
        (List.map _ (_ ++ _), _)
      rw [List.map_append]
      exact congrArg₂ Prod.mk (congrArg₂ (· ++ ·) h0 hJ) h2

theorem entriesE_reP {E : ExtSpec} (we : WireE E)
    (g : E.Pos → Option (OpenO E.Sym)) (P : E.Pos → List (Dig lam)) :
    entriesE we (reP (bareF g) P) =
      (entriesEO we g).map fun e => (e.1, ⟨e.2.sym, e.2.salt, P e.1⟩) := by
  unfold entriesE entriesEO reP bareF
  rw [List.map_filterMap]
  refine List.filterMap_congr fun p _ => ?_
  cases g p <;> rfl

theorem bareF_injective {ι : Type} {σ : ι → Type} {g g' : (p : ι) → Option (OpenO (σ p))}
    (h : reP (lam := lam) (bareF g) (fun _ => []) = reP (bareF g') fun _ => []) : g = g' := by
  funext p
  have := congrFun h p
  unfold reP bareF at this
  cases hg : g p <;> cases hg' : g' p <;> rw [hg, hg'] at this
    <;> simp only [Option.map_none, Option.map_some, reduceCtorEq, Option.some.injEq,
      Opening.mk.injEq, OpenO.bare, and_true] at this
  · rename_i a b
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    obtain ⟨rfl, rfl⟩ := this
    rfl

theorem encBO_injective {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {wq : ProtocolQueryLayout lam K Q} (hwq : wq.OKG) :
    Function.Injective (encBO wq) := by
  rintro ⟨s, r, pl, o, e, sb, q, j, pa⟩ ⟨s', r', pl', o', e', sb', q', j', pa'⟩ h
  simp only [encBO, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, h4, h5, rfl, rfl, rfl, rfl⟩ := h
  have e4 : o = o' :=
    bareF_injective (lam := lam)
      (entriesSB_injective _ _ _ hwq.sh (by rw [entriesSB_reP, entriesSB_reP, h4]))
  have e5 : e = e' :=
    bareF_injective (lam := lam)
      (entriesE_injective hwq.ext (by rw [entriesE_reP, entriesE_reP, h5]))
  rw [e4, e5]

/-! ## Part 2. The conditions `FitsBO`, and the bounds -/

/-- in each round at most o_r opened positions, each with a salt of at most sMT bits -/
def FitsEntO (sMT : ℕ) : (s : Shape) → OpenList s → EntSO s → Prop
  | [], _, _ => True
  | _ :: s, (n, o), (l, e) => l.length ≤ n ∧ (∀ x ∈ l, x.2.salt.length ≤ sMT) ∧ FitsEntO sMT s o e

theorem fitsEntO_of_up (sMT : ℕ) :
    ∀ (s : Shape) (Wf : WireS lam K s) (o : OpenList s) (P : OPos s → List (Dig lam)) (e : EntSO s),
      FitsEnt sMT s Wf o (EntSO.up s P e) → FitsEntO sMT s o e
  | [], _, _, _, _, _ => trivial
  | _ :: s, (_, Wf), (n, o), P, (l, e), h => by
      refine ⟨by simpa using h.1, fun x hx => ?_, fitsEntO_of_up sMT s Wf o _ e h.2.2⟩
      exact (h.2.1 _ (List.mem_map_of_mem hx)).1

theorem length_put_serEntRO_le {r : Round} (a : Ser (Σ p : r.Pos, r.Sym p)) {x sMT : ℕ}
    (ha : ∀ z, (a.put z).length ≤ x) (e : EntRO r) (h1 : e.2.salt.length ≤ sMT) :
    ((serEntRO a).put e).length ≤ entBitsO sMT x := by
  unfold serEntRO entBitsO
  rw [Ser.length_put_ofEquiv, Ser.length_put_prod]
  exact Nat.add_le_add (ha _) (length_put_serBits_le h1)

theorem length_put_serEntSO_le (sMT : ℕ) :
    ∀ (s : Shape) (S : SerS s) (b : BitsS s) (o : OpenList s) (e : EntSO s),
      SerS.Within s S b → FitsEntO sMT s o e → ((serEntSO s S).put e).length ≤ entSumO sMT s b o
  | [], _, _, _, _, _, _ => Nat.le_refl _
  | _ :: s, ((a, _), S), ((x, _), b), (n, o), (l, e), hS, hF => by
      show ((Ser.prod (Ser.lenList (serEntRO a)) (serEntSO s S)).put (l, e)).length ≤
        (gam n + n * entBitsO sMT x) + entSumO sMT s b o
      rw [Ser.length_put_prod]
      exact Nat.add_le_add
        (Ser.length_put_lenList_le_gam _ hF.1 fun y hy =>
          length_put_serEntRO_le a hS.1 y (hF.2.1 y hy))
        (length_put_serEntSO_le sMT s S b o e hS.2.2 hF.2.2)

theorem length_put_serEntEO_le {E : ExtSpec} (sp : Ser E.Pos) (ss : Ser E.Sym)
    {x sMT : ℕ} (hx : ∀ p a, (sp.put p).length + (ss.put a).length ≤ x)
    (e : EntEO E) (h1 : e.2.salt.length ≤ sMT) :
    ((serEntEO sp ss).put e).length ≤ entBitsO sMT x := by
  unfold serEntEO entBitsO
  rw [Ser.length_put_ofEquiv, Ser.length_put_prod, Ser.length_put_prod]
  exact Nat.add_le_add (hx _ _) (length_put_serBits_le h1)

/-- the count of Hash/OctopusFacts.lean is the number of Iop/SizesO.lean -/
theorem octB_eq (d nT n : ℕ) : octB d nT n = octMax d nT n := rfl

/-- The sibling digests that nT trees of depth d need at most for at most n opened leaves: a full
path for each (pr = false), or pruned paths (pr = true) -/
def digB (pr : Bool) (d nT n : ℕ) : ℕ := if pr then octMax d nT n else n * d

/-- The sibling digests of the two trees of one round together, for at most n openings in the round.
Neither pruned: n paths of the larger depth. Both pruned: counted as two trees of the larger depth
opened together. Else each tree is counted with all n openings. -/
def digR (p0 pJ : Bool) (d0 dJ n : ℕ) : ℕ :=
  match p0, pJ with
  | false, false => n * max d0 dJ
  | true, true => octMax (max d0 dJ) 2 n
  | _, _ => digB p0 d0 1 n + digB pJ dJ 1 n

/-- the sum over the rounds -/
def sibSum : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → OpenList s → ℕ
  | [], _, _, _ => 0
  | _ :: s, (_, A), (w, W), (n, o) => digR w.pr0 w.prJ w.depth0 w.depthJ n + sibSum s A W o

section B
variable {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}

/-- A bound on the sibling digests of a proof string; nT: the number of trees over external strings,
nE: a bound on the external positions that are read -/
def sibBound (wq : ProtocolQueryLayout lam K Q) (o : OpenList Q.loc.shape) (nE nT : ℕ) : ℕ :=
  sibSum Q.loc.shape Q.ann wq.sh o + digB wq.ext.pr wq.ext.depth nT nE

/-- The properties of a proof string that matter for its size. -/
structure FitsBO (sMT sFS : ℕ) (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) (o : OpenList Q.loc.shape)
    (eN : ExtNums) (nS : ℕ) (t : BTO lam Q) : Prop where
  salt : t.1.length ≤ sFS
  roots : t.2.1.length ≤ cRoots Q.loc.shape Q.ann wq.sh
  ent : FitsEntO sMT Q.loc.shape o t.2.2.2.1
  extN : t.2.2.2.2.1.length ≤ eN.n
  ext : ∀ x ∈ t.2.2.2.2.1, x.2.salt.length ≤ sMT
  sibs : t.2.2.2.2.2.1.length ≤ nS
  slot : t.2.2.2.2.2.2.2.1 ≤ 2 ^ depthReq - 1
  path : t.2.2.2.2.2.2.2.2.length ≤ depthReq

/-- The bound for a proof string, in bits: the salt, the roots, the plain parts, the opened
positions round by round, the external openings, the nS sibling digests, the request root, the slot
number, the request path. -/
def boundBO (sMT sFS : ℕ) (wq : ProtocolQueryLayout lam K Q) (depthReq : ℕ) (b : BitsS Q.loc.shape)
    (o : OpenList Q.loc.shape) (eN : ExtNums) (nS : ℕ) : ℕ :=
  (gam sFS + sFS * 1) +
    ((gam (cRoots Q.loc.shape Q.ann wq.sh) + cRoots Q.loc.shape Q.ann wq.sh * lam) +
      (BitsS.plainBits Q.loc.shape b +
        (entSumO sMT Q.loc.shape b o +
          ((gam eN.n + eN.n * entBitsO sMT eN.x) +
            ((gam nS + nS * lam) +
              (lam + (gam (2 ^ depthReq - 1) + (gam depthReq + depthReq * lam))))))))

theorem length_put_serBTO_le {sMT sFS depthReq nS : ℕ} {wq : ProtocolQueryLayout lam K Q} {S : SerS Q.loc.shape}
    {sp : Ser E.Pos} {ss : Ser E.Sym} {b : BitsS Q.loc.shape} {o : OpenList Q.loc.shape}
    {eN : ExtNums} (hS : SerS.Within Q.loc.shape S b)
    (hx : ∀ p a, (sp.put p).length + (ss.put a).length ≤ eN.x) {t : BTO lam Q}
    (hF : FitsBO sMT sFS wq depthReq o eN nS t) :
    ((serBTO lam Q S sp ss).put t).length ≤ boundBO sMT sFS wq depthReq b o eN nS := by
  unfold serBTO boundBO
  rw [Ser.length_put_prod, Ser.length_put_prod, Ser.length_put_prod,
    Ser.length_put_prod, Ser.length_put_prod, Ser.length_put_prod, Ser.length_put_prod,
    Ser.length_put_prod, Ser.length_put_natG_eq_gam]
  exact Nat.add_le_add (length_put_serBits_le hF.salt)
    (Nat.add_le_add (length_put_serDigs_le hF.roots)
      (Nat.add_le_add (length_put_serPlains_le _ S b _ hS)
        (Nat.add_le_add (length_put_serEntSO_le sMT _ S b o _ hS hF.ent)
          (Nat.add_le_add
            (Ser.length_put_lenList_le_gam _ hF.extN fun y hy =>
              length_put_serEntEO_le sp ss hx y (hF.ext y hy))
            (Nat.add_le_add (length_put_serDigs_le hF.sibs)
              (Nat.add_le_add (le_of_eq (Ser.length_put_bits lam _))
                (Nat.add_le_add (Ser.gam_mono hF.slot) (length_put_serDigs_le hF.path))))))))

end B

/-! ## Part 3. What verifyBO accepts -/

theorem length_filterMap_congr
    {α β γ : Type} (g : α → Option β) (g' : α → Option γ) (h : ∀ a, (g a).isSome = (g' a).isSome) :
    ∀ l : List α, (l.filterMap g).length = (l.filterMap g').length
  | [] => rfl
  | a :: l => by
      have ih := length_filterMap_congr g g' h l
      have ha := h a
      cases h1 : g a <;> cases h2 : g' a <;> rw [h1, h2] at ha
        <;> simp only [Option.isSome_none, Option.isSome_some,
          Bool.false_eq_true, Bool.true_eq_false] at ha
      · rw [List.filterMap_cons_none h1, List.filterMap_cons_none h2, ih]
      · rw [List.filterMap_cons_some h1, List.filterMap_cons_some h2,
          List.length_cons, List.length_cons, ih]

theorem length_planComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    (planComp posAt depth f).2.length = (entriesC posAt depth f).length := by
  unfold planComp entriesC
  refine length_filterMap_congr _ _ (fun j => ?_) _
  cases posAt j with
  | none => rfl
  | some p =>
    show ((f p).map _).isSome = ((f p).map _).isSome
    cases f p <;> rfl

theorem length_planExt {E : ExtSpec} (we : WireE E) (g : E.Pos → Option (Opening lam E.Sym)) :
    (planExt we g).2.length = (entriesE we g).length := by
  unfold planExt entriesE
  refine length_filterMap_congr _ _ (fun p => ?_) _
  cases g p <;> rfl

/-- One tree, or trees verified together, with at most n opened leaves (where pruned: ascending and
in range): the verification consumes at most `digB` digests. -/
theorem needAll_split_le (pr : Bool) (T : Plan lam) (nT n : ℕ) (hq : T.2.length ≤ n)
    (hp : pr = true → T.idx.Pairwise (· < ·) ∧ ∀ j ∈ T.idx, j < nT * 2 ^ T.1) :
    needAll (T.split pr) ≤ digB pr T.1 nT n := by
  cases pr with
  | true =>
    obtain ⟨h1, h2⟩ := hp rfl
    show needAll [T] ≤ octMax T.1 nT n
    have e : needAll [T] = need T.1 T.idx := by simp [needAll, Plan.need]
    rw [e]
    exact need_le_octMax T.1 nT n T.idx h1 h2 (by unfold Plan.idx; rw [List.length_map]; exact hq)
  | false =>
    show needAll (T.2.map fun x => (T.1, [x])) ≤ n * T.1
    have e : ∀ l : List (ℕ × List (Dig lam)),
        needAll (l.map fun x => (T.1, [x])) = l.length * T.1 := by
      intro l
      induction l with
      | nil => simp [needAll]
      | cons x xs ih =>
        have e1 : needAll ((x :: xs).map fun x => (T.1, [x])) =
            Plan.need (T.1, [x]) + needAll (xs.map fun x => (T.1, [x])) := by simp [needAll]
        have e2 : Plan.need ((T.1, [x]) : Plan lam) = T.1 := need_singleton T.1 x.1
        rw [e1, e2, ih, List.length_cons, Nat.succ_mul, Nat.add_comm]
    rw [e]
    exact Nat.mul_le_mul_right _ hq

theorem digB_mono (pr : Bool) (d nT : ℕ) {n n' : ℕ} (h : n ≤ n') :
    digB pr d nT n ≤ digB pr d nT n' := by
  unfold digB
  split_ifs
  · exact octMax_mono d nT h
  · exact Nat.mul_le_mul_right d h

/-- the two trees of a round, with a and b openings, a + b ≤ n -/
theorem digB_add_le (p0 pJ : Bool) (d0 dJ : ℕ) {a b n : ℕ} (h : a + b ≤ n) :
    digB p0 d0 1 a + digB pJ dJ 1 b ≤ digR p0 pJ d0 dJ n := by
  cases p0 <;> cases pJ
  · show a * d0 + b * dJ ≤ n * max d0 dJ
    calc
      a * d0 + b * dJ ≤ a * max d0 dJ + b * max d0 dJ :=
        Nat.add_le_add (Nat.mul_le_mul_left a (le_max_left _ _))
          (Nat.mul_le_mul_left b (le_max_right _ _))
      _ = (a + b) * max d0 dJ := (Nat.add_mul _ _ _).symm
      _ ≤ n * max d0 dJ := Nat.mul_le_mul_right _ h
  · exact Nat.add_le_add (digB_mono false d0 1 (by omega)) (digB_mono true dJ 1 (by omega))
  · exact Nat.add_le_add (digB_mono true d0 1 (by omega)) (digB_mono false dJ 1 (by omega))
  · exact le_trans (octMax_add_le d0 dJ a b) (octMax_mono _ 2 h)

theorem pairwise_idx_planComp {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    (planComp posAt depth f).idx.Pairwise (· < ·) ∧
    ∀ j ∈ (planComp posAt depth f).idx, j < 1 * 2 ^ (planComp posAt depth f).1 := by
  have hs := idx_planComp_sublist posAt depth f
  refine ⟨List.Pairwise.sublist hs List.pairwise_lt_range, fun j hj => ?_⟩
  rw [Nat.one_mul]
  exact List.mem_range.1 (hs.subset hj)

/-- The trees of one component from tree number k on, each verified by itself: the verification
consumes at most the sum, over the trees (x.1: a tree's depth, x.2: its number), of `digB` for one
tree of that depth with as many opened leaves as the proof string holds openings in that tree. -/
theorem needAll_planTrees_le {r : Round} (pr : Bool) (posAt : ℕ → ℕ → Option r.Pos)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ),
      needAll (planTrees pr posAt f k ds).flatten ≤
        ((ds.zipIdx k).map fun x => digB pr x.1 1 (entriesC (posAt x.2) x.1 f).length).sum
  | _, [] => by simp [planTrees, needAll]
  | k, d :: ds => by
      have h0 := needAll_split_le pr (planComp (posAt k) d f) 1 _
        (le_of_eq (length_planComp _ _ _)) fun _ => pairwise_idx_planComp _ _ _
      have h1 := needAll_planTrees_le pr posAt f (k + 1) ds
      show needAll ((planComp (posAt k) d f).split pr ++
          (planTrees pr posAt f (k + 1) ds).flatten) ≤ _
      rw [needAll_append, List.zipIdx_cons, List.map_cons, List.sum_cons]
      exact Nat.add_le_add h0 h1

/-- the opened positions of the trees of one component, counted tree by tree (x.1: a tree's depth,
x.2: its number): the numbers under the sum of `needAll_planTrees_le` add up to this length -/
theorem length_entriesTrees {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (g : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (k : ℕ) (ds : List ℕ),
      (entriesTrees posAt g k ds).length =
        ((ds.zipIdx k).map fun x => (entriesC (posAt x.2) x.1 g).length).sum
  | _, [] => rfl
  | k, d :: ds => by
      rw [entriesTrees, List.length_append, length_entriesTrees posAt g (k + 1) ds,
        List.zipIdx_cons, List.map_cons, List.sum_cons]

theorem needAll_planB_le (sMT : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (f : (p : OPos s) → Option (Opening lam (OSym s p))) (o : OpenList s),
      FitsEnt sMT s (flatS s A W) o (entriesSB s A W f) → needAll (planB s A W f) ≤ sibSum s A W o
  | [], _, _, _, _, _ => Nat.le_refl _
  | _ :: s, (_, A), (w, W), f, (n, o), h => by
      have hl : (entriesC w.posAt0 w.depth0 (fun p => f (.inl p)) ++
            entriesC w.posAtJ w.depthJ fun p => f (.inl p)).length ≤ n := h.1
      rw [List.length_append] at hl
      have h0 := needAll_split_le w.pr0 (planComp w.posAt0 w.depth0 fun p => f (.inl p)) 1 _
        (le_of_eq (length_planComp _ _ _)) fun _ => pairwise_idx_planComp _ _ _
      have hJ := needAll_split_le w.prJ (planComp w.posAtJ w.depthJ fun p => f (.inl p)) 1 _
        (le_of_eq (length_planComp _ _ _)) fun _ => pairwise_idx_planComp _ _ _
      have h2 := needAll_planB_le sMT s A W (fun p => f (.inr p)) o h.2.2
      show needAll (_ ++ (_ ++ planB s A W fun p => f (.inr p))) ≤ _
      rw [needAll_append, needAll_append]
      show _ ≤ digR w.pr0 w.prJ w.depth0 w.depthJ n + sibSum s A W o
      have e0 : (planComp w.posAt0 w.depth0 fun p => f (.inl p)).1 = w.depth0 := rfl
      have eJ : (planComp w.posAtJ w.depthJ fun p => f (.inl p)).1 = w.depthJ := rfl
      rw [e0] at h0
      rw [eJ] at hJ
      have hR := digB_add_le w.pr0 w.prJ w.depth0 w.depthJ hl
      omega

/-- The list `all` of the wire record is ascending in the leaf numbers of the trees over the
external strings, and these are leaf numbers of nT trees. -/
def ExtAsc {E : ExtSpec} (we : WireE E) (nT : ℕ) : Prop :=
  (we.all.map (extIdx we)).Pairwise (· < ·) ∧ ∀ p, extIdx we p < nT * 2 ^ we.depth

theorem needAll_filledAll :
    ∀ (Ts : List (Plan lam)) (s : List (Dig lam)), needAll (filledAll Ts s) = needAll Ts
  | [], _ => rfl
  | T :: Ts, s => by
      have e1 : needAll (filledAll (T :: Ts) s) =
          (T.filled s).need + needAll (filledAll Ts (s.drop T.need)) := by
        simp [needAll, filledAll]
      have e2 : needAll (T :: Ts) = T.need + needAll Ts := by simp [needAll]
      rw [e1, e2, Plan.need_filled, needAll_filledAll Ts]

section B
variable {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
  {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
  {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {tr : Trace (spec lam K L)}

/-- what the size bounds use of the check `usedUp`: no digest is left over -/
theorem usedUp.eq {n : ℕ} {s : List (Dig lam)} (h : usedUp n s) : s.length = n := by
  unfold usedUp at h
  omega

/-- what an accepting run of `verifyBC` has checked of the list of sibling digests -/
theorem length_of_verifyBC {π : OneProtocolProof lam Q} {s : List (Dig lam)}
    (h : RunsIn tr (verifyBC sMT sFS t Q wq embS embP xin embE depthReq cms x π s) true) :
    s.length = needAll (planOf wq π) := by
  unfold verifyBC at h
  obtain ⟨r, -, h⟩ := (runsIn_bind_iff _ _ _).1 h
  rcases r with _ | ⟨ρ, rts, ph⟩
  · exact absurd (runsIn_pure_iff.1 h) (by simp)
  · dsimp only at h
    split_ifs at h with hst
    · unfold afterBC at h
      split at h
      · rename_i Fs hFs
        split_ifs at h with hc
        · rw [hc.2.eq, needF_eq, plan_forestsOf hst hFs]
          rfl
        · exact absurd (runsIn_pure_iff.1 h) (by simp)
      · exact absurd (runsIn_pure_iff.1 h) (by simp)
    · exact absurd (runsIn_pure_iff.1 h) (by simp)

end B

/-- Under the hypotheses below, a proof string that `verifyBO` accepts has exactly as many sibling
digests as the verification consumes, and that is at most `sibBound`. -/
def Spec.sibsAccepted : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (sMT sFS : ℕ) (t : Tag) (Y : Type) (E : ExtSpec)
      (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q)
      (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
      (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig lam)) (x : Y)
      (tr : Trace (spec lam K L)) (π : BPrfO lam Q),
    wq.OKG → ExtInj wq.ext →
    ∀ (o : OpenList Q.loc.shape), Q.loc.OpensLe o →
      ∀ (nE nT : ℕ), (∀ x ρ, (Q.loc.extReads x ρ).card ≤ nE) →
        (wq.ext.pr = true → ExtAsc wq.ext nT) →
        RunsIn tr (verifyBO sMT sFS t Q wq embS embP xin embE depthReq cms x π) true →
        π.sibs.length = needAll (planOf wq π.bare) ∧
        needAll (planOf wq π.bare) ≤ sibBound wq o nE nT

theorem sibsAccepted : Spec.sibsAccepted := by
  intro I X lam K L sMT sFS t Y E Q wq embS embP xin embE depthReq cms x tr π
    hwq hi o ho nE nT hE hA h
  have h1 : π.sibs.length = needAll (planOf wq π.bare) := length_of_verifyBC h
  refine ⟨h1, ?_⟩
  have h2 := (accLe_fill (sMT := sMT) (sFS := sFS) (t := t) (embS := embS) (embP := embP)
      (xin := xin) (embE := embE) (depthReq := depthReq) (cms := cms) (x := x) hwq hi π).2
    tr h
  have hF := fitsB_of_accepted hwq o ho ⟨nE, 0, wq.ext.depth⟩ hE (Nat.le_refl _) h2
  have e : needAll (planOf wq π.bare) = needAll (planOf wq (fillO wq π)) := by
    show _ = needAll (planOf wq (refill wq π.bare π.sibs))
    rw [planOf_refill hwq hi, needAll_filledAll]
  rw [e]
  unfold planOf sibBound
  rw [needAll_append]
  refine Nat.add_le_add (needAll_planB_le sMT _ _ _ _ o hF.ent) ?_
  refine needAll_split_le wq.ext.pr (planExt wq.ext (fillO wq π).ext) nT nE
    (by rw [length_planExt]; exact hF.extN) fun hp => ?_
  obtain ⟨a1, a2⟩ := hA hp
  have hs := idx_planExt_sublist wq.ext (fillO wq π).ext
  refine ⟨List.Pairwise.sublist hs a1, fun j hj => ?_⟩
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 (hs.subset hj)
  exact a2 p

section B
variable {sMT sFS : ℕ} {t : Tag} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {wq : ProtocolQueryLayout lam K Q}
  {embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L}
  {embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)} {xin : Y → Option X}
  {embE : E.Sym → Body L} {depthReq : ℕ} {cms : List (Dig lam)} {x : Y} {tr : Trace (spec lam K L)}

/-- Under the hypotheses below, what `verifyBO` accepts has the properties `FitsBO`. -/
theorem fitsBO_of_accepted (hwq : wq.OKG) (hi : ExtInj wq.ext) (o : OpenList Q.loc.shape)
    (ho : Q.loc.OpensLe o) (eN : ExtNums) (nT : ℕ) (hE : ∀ x ρ, (Q.loc.extReads x ρ).card ≤ eN.n)
    (hA : wq.ext.pr = true → ExtAsc wq.ext nT) {π : BPrfO lam Q}
    (h : RunsIn tr (verifyBO sMT sFS t Q wq embS embP xin embE depthReq cms x π) true) :
    FitsBO sMT sFS wq depthReq o eN (sibBound wq o eN.n nT) (encBO wq π) := by
  have h2 := (accLe_fill (sMT := sMT) (sFS := sFS) (t := t) (embS := embS) (embP := embP)
      (xin := xin) (embE := embE) (depthReq := depthReq) (cms := cms) (x := x) hwq hi π).2
    tr h
  have hF := fitsB_of_accepted hwq o ho ⟨eN.n, eN.x, wq.ext.depth⟩ hE (Nat.le_refl _) h2
  obtain ⟨s1, s2⟩ := sibsAccepted I X lam K L sMT sFS t Y E Q wq embS embP xin embE depthReq cms x
    tr π hwq hi o ho eN.n nT hE hA h
  refine ⟨hF.salt, hF.roots, ?_, ?_, ?_,
    by show π.sibs.length ≤ _; rw [s1]; exact s2, hF.slot, hF.path⟩
  · have he : FitsEnt sMT Q.loc.shape (flatS Q.loc.shape Q.ann wq.sh) o
        (entriesSB Q.loc.shape Q.ann wq.sh (reP (bareF π.opens) _)) := hF.ent
    rw [entriesSB_reP] at he
    exact fitsEntO_of_up sMT _ _ o _ _ he
  · have he : (entriesE wq.ext (reP (bareF π.ext) _)).length ≤ eN.n := hF.extN
    rw [entriesE_reP, List.length_map] at he
    exact he
  · intro y hy
    have he : ∀ z ∈ entriesE wq.ext (reP (bareF π.ext) _),
        z.2.salt.length ≤ sMT ∧ z.2.path.length ≤ wq.ext.depth := hF.ext
    rw [entriesE_reP] at he
    exact (he _ (List.mem_map_of_mem hy)).1

end B

/-! ## Part 4. Keys and proofs -/

section Scheme
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (D : SerLHB L)

def serTO : Ser (BTO lam (BatchInteractiveOracleProof.ofProto L.offline)) :=
  serBTO lam (BatchInteractiveOracleProof.ofProto L.offline) D.T (serPos1 L) D.sg
def serLO : Ser (BTO lam (BatchInteractiveOracleProof.ofProto L.link)) :=
  serBTO lam (BatchInteractiveOracleProof.ofProto L.link) D.Lk (serPos2 L) D.sg
def serOO : Ser (BTO lam L.onlineBatch) := serBTO lam L.onlineBatch D.O (serPos1 L) D.sg

/-- A verification key as a bit string: the root; one bit; Test's proof string, unless that is
`none`. -/
def putIVKO (v : IVKO lam L) : List Bool :=
  (Ser.prod (serDig lam) (Ser.option (serTO D))).put (v.cm, v.piT.map (encBO W.T))

def serPairO : Ser (Dig lam × Option (BTO lam (BatchInteractiveOracleProof.ofProto L.link))) :=
  Ser.prod (serDig lam) (Ser.option (serLO D))
def encPairO (e : Dig lam × Option (BPrfO lam (BatchInteractiveOracleProof.ofProto L.link))) :
    Dig lam × Option (BTO lam (BatchInteractiveOracleProof.ofProto L.link)) :=
  (e.1, e.2.map (encBO W.Lk))

/-- An entry as a bit string: the root of the copy's tree; one bit; Link's proof string, unless it
is `none`. -/
def putPairO (e : Dig lam × Option (BPrfO lam (BatchInteractiveOracleProof.ofProto L.link))) : List Bool :=
  (serPairO D).put (encPairO W e)

/-- A verification key with entries as a bit string: the key without them; their number; the
entries. -/
def putIVKKO (v : IVKKO lam L) : List Bool :=
  (Ser.prod (Ser.prod (serDig lam) (Ser.option (serTO D))) (Ser.lenList (serPairO D))).put
    ((v.1.cm, v.1.piT.map (encBO W.T)), v.2.map (encPairO W))

/-- A proof of `VKO` as a bit string: the number of the copy; one bit; the slot's proof string,
unless it is `none`. -/
def putPrfKO (π : PrfKO lam L) : List Bool :=
  (Ser.prod Ser.natG (Ser.option (serOO D))).put (π.leaf, π.piB.map (encBO W.B))

theorem putIVKO_injective (hW : W.OKG) : Function.Injective (putIVKO W D) := by
  rintro ⟨c, t⟩ ⟨c', t'⟩ h
  have h1 := Ser.put_injective _ h
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, h2⟩ := h1
  rw [Option.map_injective (encBO_injective hW.T) h2]

theorem encPairO_injective (hW : W.OKG) : Function.Injective (encPairO W) := by
  rintro ⟨c, a⟩ ⟨c', a'⟩ h
  simp only [encPairO, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  rw [Option.map_injective (encBO_injective hW.Lk) h2]

theorem putIVKKO_injective (hW : W.OKG) : Function.Injective (putIVKKO W D) := by
  rintro ⟨⟨c, t⟩, l⟩ ⟨⟨c', t'⟩, l'⟩ h
  have h1 := Ser.put_injective _ h
  simp only [Prod.mk.injEq] at h1
  obtain ⟨⟨rfl, h2⟩, h3⟩ := h1
  rw [Option.map_injective (encBO_injective hW.T) h2,
    List.map_injective_iff.2 (encPairO_injective W hW) h3]

theorem putPrfKO_injective (hW : W.OKG) : Function.Injective (putPrfKO W D) := by
  rintro ⟨j, b⟩ ⟨j', b'⟩ h
  have h1 := Ser.put_injective _ h
  simp only [Prod.mk.injEq] at h1
  obtain ⟨rfl, h3⟩ := h1
  rw [Option.map_injective (encBO_injective hW.B) h3]

/-- the sizes, in bits -/
def sizeIVKO (v : IVKO lam L) : ℕ := (putIVKO W D v).length
@[inherit_doc sizeIVKO] def sizePairO
    (e : Dig lam × Option (BPrfO lam (BatchInteractiveOracleProof.ofProto L.link))) : ℕ :=
  (putPairO W D e).length
@[inherit_doc sizeIVKO] def sizePrfKO (π : PrfKO lam L) : ℕ := (putPrfKO W D π).length

/-- Where the trees over the external strings are pruned, the list `all` of the wire record is
ascending: one tree for Test and Batch, two for Link. -/
structure ExtAscOK : Prop where
  T : W.T.ext.pr = true → ExtAsc W.T.ext 1
  Lk : W.Lk.ext.pr = true → ExtAsc W.Lk.ext 2
  B : W.B.ext.pr = true → ExtAsc W.B.ext 1

variable (p : Params) (Z : SizeNums L)

/-- the bounds for the three proof strings, in bits -/
def boundTO : ℕ :=
  boundBO p.sMT p.sFS W.T W.depthReq Z.bT Z.oT (Z.extT W) (sibBound W.T Z.oT Z.eT 1)
@[inherit_doc boundTO] def boundLO : ℕ :=
  boundBO p.sMT p.sFS W.Lk W.depthReq Z.bL Z.oL (Z.extL W) (sibBound W.Lk Z.oL Z.eL 2)
@[inherit_doc boundTO] def boundOO : ℕ :=
  boundBO p.sMT p.sFS W.B W.depthReq Z.bO Z.oO (Z.extO W) (sibBound W.B Z.oO Z.eO 1)

/-- The bound for a verification key, in bits. -/
def boundIVKO : ℕ := lam + (boundTO W p Z + 1)
/-- The bound for an entry, in bits. -/
def boundPairO : ℕ := lam + (boundLO W p Z + 1)
/-- The bound for a proof of `VKO` that names a copy with a number of at most m, in bits. -/
def boundPrfKO (m : ℕ) : ℕ := gam m + (boundOO W p Z + 1)

/-- a key and a proof meet the conditions for the size bounds -/
structure FitsO (v : IVKO lam L) (π : PrfO lam L) : Prop where
  test : ∀ a, v.piT = some a →
    FitsBO p.sMT p.sFS W.T W.depthReq Z.oT (Z.extT W) (sibBound W.T Z.oT Z.eT 1) (encBO W.T a)
  leaf : π.leaf ≤ p.M
  link : ∀ a, π.piL = some a →
    FitsBO p.sMT p.sFS W.Lk W.depthReq Z.oL (Z.extL W) (sibBound W.Lk Z.oL Z.eL 2) (encBO W.Lk a)
  bat : ∀ a, π.piB = some a →
    FitsBO p.sMT p.sFS W.B W.depthReq Z.oO (Z.extO W) (sibBound W.B Z.oO Z.eO 1) (encBO W.B a)

/-- Under `W.OKG`, `ExtAscOK W` and `OpensOK L Z`: what `VO` accepts has the properties `FitsO`,
honest or not. -/
theorem fits_of_acceptedO (hW : W.OKG) (hA : ExtAscOK W) (hO : OpensOK L Z) {tr : Tc W}
    {v : IVKO lam L} {x : X} {π : PrfO lam L} (h : RunsIn tr (VO W p v x π) true) :
    FitsO W p Z v π := by
  unfold VO at h
  split at h
  · rename_i πT πL πB eT eL eB
    split_ifs at h with hleaf
    · simp only [bind_eq, pure_eq, runsIn_bind_iff, runsIn_pure_iff] at h
      obtain ⟨a, ha, b, hb, c, hc, habc⟩ := h
      simp only [Bool.and_eq_true] at habc
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := habc
      refine ⟨fun π' hπ' => ?_, hleaf, fun π' hπ' => ?_, fun π' hπ' => ?_⟩
      · obtain rfl : πT = π' := Option.some.inj (eT.symm.trans hπ')
        exact fitsBO_of_accepted hW.T (extInj_T hW) Z.oT hO.T (Z.extT W) 1 hO.eT hA.T ha
      · obtain rfl : πL = π' := Option.some.inj (eL.symm.trans hπ')
        exact fitsBO_of_accepted hW.Lk (extInj_L hW) Z.oL hO.Lk (Z.extL W) 2 hO.eL hA.Lk hb
      · obtain rfl : πB = π' := Option.some.inj (eB.symm.trans hπ')
        exact fitsBO_of_accepted hW.B (extInj_B hW) Z.oO hO.O (Z.extO W) 1 hO.eO hA.B hc
    · exact absurd (runsIn_pure_iff.1 h) (by simp)
  · exact absurd (runsIn_pure_iff.1 h) (by simp)

/-- If `VO` accepts under the oracle functions f, it accepts with its queries answered from some
trace. -/
theorem runsIn_of_acceptsO (f : Fam (spec lam W.K L)) {v : IVKO lam L} {x : X} {π : PrfO lam L}
    (h : true ∈ ((VO W p v x π).runEager f).support) :
    ∃ tr, RunsIn tr (VO W p v x π) true := by
  rw [← runEager_withTrace_fst f, PMF.support_map] at h
  obtain ⟨c, hc, hc1⟩ := h
  have := runsIn_of_mem_support (detBound_VO W p v x π) f c hc
  rw [hc1] at this
  exact ⟨c.2, this⟩

variable {W D p Z}

theorem sizeIVKO_le_of_fits (hZ : Z.Within D) {v : IVKO lam L}
    {π : PrfO lam L} (h : FitsO W p Z v π) :
    sizeIVKO W D v ≤ boundIVKO W p Z := by
  unfold sizeIVKO putIVKO boundIVKO
  rw [Ser.length_put_prod]
  refine Nat.add_le_add (le_of_eq (Ser.length_put_bits lam _))
    (length_put_option_le _ _ fun t ht => ?_)
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 ht
  exact length_put_serBTO_le (eN := Z.extT W) hZ.T (ext1_le hZ) (h.test a ha)

variable (W D p Z)

/-- Under the four hypotheses of the header (hW, hA, hZ, hO): the verification key on which `VO`
accepts a proof is within the bound. -/
theorem sizeIVKO_le_of_acceptedGr (hW : W.OKG) (hA : ExtAscOK W) (hZ : Z.Within D)
    (hO : OpensOK L Z) (f : Fam (spec lam W.K L)) (v : IVKO lam L) (x : X) (π : PrfO lam L)
    (h : true ∈ ((VO W p v x π).runEager f).support) :
    sizeIVKO W D v ≤ boundIVKO W p Z := by
  obtain ⟨tr, htr⟩ := runsIn_of_acceptsO W p f h
  exact sizeIVKO_le_of_fits hZ (fits_of_acceptedO W p Z hW hA hO htr)

/-- If `VKO` accepts, the key has the entry that the proof names, and `VO` accepts the key without
entries with that entry and the slot's proof string. -/
theorem accepted_KO (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    ∃ e,
      v.2[π.leaf]? = some e ∧ true ∈ ((VO W p v.1 x ⟨0, e.1, e.2, π.piB⟩).runEager f).support := by
  have h' : true ∈ ((VO W p v.1 x (reKO v.2 π)).runEager f).support := h
  unfold reKO at h'
  rcases he : v.2[π.leaf]? with _ | e
  · rw [he] at h'
    have hV : VO W p v.1 x ⟨0, default, none, π.piB⟩ = pure false := by
      unfold VO
      cases v.1.piT <;> rfl
    dsimp only at h'
    rw [hV] at h'
    simp [OComp.runEager] at h'
  · rw [he] at h'
    exact ⟨e, rfl, h'⟩

/-- Under the same four hypotheses: every proof that `VKO` accepts is within the bound, whoever made
the key and the proof; the number of its copy is below the number of entries of the key. -/
theorem sizePrfKO_le_of_acceptedGr (hW : W.OKG) (hA : ExtAscOK W) (hZ : Z.Within D)
    (hO : OpensOK L Z) (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    π.leaf < v.2.length ∧ sizePrfKO W D π ≤ boundPrfKO W p Z (v.2.length - 1) := by
  obtain ⟨e, he, hV⟩ := accepted_KO W p f v x π h
  obtain ⟨tr, htr⟩ := runsIn_of_acceptsO W p f hV
  have hfit := fits_of_acceptedO W p Z hW hA hO htr
  have hlt : π.leaf < v.2.length := (List.getElem?_eq_some_iff.1 he).1
  refine ⟨hlt, ?_⟩
  unfold sizePrfKO putPrfKO boundPrfKO
  rw [Ser.length_put_prod, Ser.length_put_natG_eq_gam]
  refine Nat.add_le_add (Ser.gam_mono (by omega)) (length_put_option_le _ _ fun t ht => ?_)
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 ht
  exact length_put_serBTO_le (eN := Z.extO W) hZ.O (ext1_le hZ) (hfit.bat a ha)

/-- Under the same four hypotheses: the part (cm, piT) of a key on which `VKO` accepts a proof is
within the bound. -/
theorem sizeIVKO_le_of_acceptedKGr (hW : W.OKG) (hA : ExtAscOK W) (hZ : Z.Within D)
    (hO : OpensOK L Z) (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    sizeIVKO W D v.1 ≤ boundIVKO W p Z := by
  obtain ⟨e, -, hV⟩ := accepted_KO W p f v x π h
  exact sizeIVKO_le_of_acceptedGr W D p Z hW hA hZ hO f v.1 x _ hV

/-- Under the same four hypotheses, if `VKO` accepts: the entry that it has read is within the
bound. -/
theorem sizePairO_le_of_acceptedGr (hW : W.OKG) (hA : ExtAscOK W) (hZ : Z.Within D)
    (hO : OpensOK L Z) (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    ∃ e, v.2[π.leaf]? = some e ∧ sizePairO W D e ≤ boundPairO W p Z := by
  obtain ⟨e, he, hV⟩ := accepted_KO W p f v x π h
  obtain ⟨tr, htr⟩ := runsIn_of_acceptsO W p f hV
  have hfit := fits_of_acceptedO W p Z hW hA hO htr
  refine ⟨e, he, ?_⟩
  unfold sizePairO putPairO serPairO encPairO boundPairO
  rw [Ser.length_put_prod]
  refine Nat.add_le_add (le_of_eq (Ser.length_put_bits lam _))
    (length_put_option_le _ _ fun t ht => ?_)
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 ht
  exact length_put_serBTO_le (eN := Z.extL W) hZ.Lk (ext2_le hZ) (hfit.link a ha)

/-! ### The same four theorems for a wire record without proof-of-work bits (`W.OK`) -/

theorem sizeIVKO_le_of_accepted (hW : W.OK) (hA : ExtAscOK W) (hZ : Z.Within D) (hO : OpensOK L Z)
    (f : Fam (spec lam W.K L)) (v : IVKO lam L) (x : X) (π : PrfO lam L)
    (h : true ∈ ((VO W p v x π).runEager f).support) :
    sizeIVKO W D v ≤ boundIVKO W p Z :=
  sizeIVKO_le_of_acceptedGr W D p Z hW.toG hA hZ hO f v x π h

theorem sizePrfKO_le_of_accepted (hW : W.OK) (hA : ExtAscOK W) (hZ : Z.Within D) (hO : OpensOK L Z)
    (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    π.leaf < v.2.length ∧ sizePrfKO W D π ≤ boundPrfKO W p Z (v.2.length - 1) :=
  sizePrfKO_le_of_acceptedGr W D p Z hW.toG hA hZ hO f v x π h

theorem sizeIVKO_le_of_acceptedK (hW : W.OK) (hA : ExtAscOK W) (hZ : Z.Within D) (hO : OpensOK L Z)
    (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    sizeIVKO W D v.1 ≤ boundIVKO W p Z :=
  sizeIVKO_le_of_acceptedKGr W D p Z hW.toG hA hZ hO f v x π h

theorem sizePairO_le_of_accepted (hW : W.OK) (hA : ExtAscOK W) (hZ : Z.Within D) (hO : OpensOK L Z)
    (f : Fam (spec lam W.K L)) (v : IVKKO lam L) (x : X) (π : PrfKO lam L)
    (h : true ∈ ((VKO W p v x π).runEager f).support) :
    ∃ e, v.2[π.leaf]? = some e ∧ sizePairO W D e ≤ boundPairO W p Z :=
  sizePairO_le_of_acceptedGr W D p Z hW.toG hA hZ hO f v x π h

end Scheme

end Compile.Batch
