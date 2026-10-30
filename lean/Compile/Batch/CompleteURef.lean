-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteURef.lean: for fixed oracle functions, under `RealFam` and the hypotheses of
the statements, all chains of a batch and, slot by slot, one execution of the compiled prover with
free empty slots (no query for an empty slot: `proveBU`, Compile/Batch/ProverU.lean) have the
distributions of their counterparts without tokens (Compile/Batch/CompleteURefDefs.lean). "Has the
distribution": `LawS` (Compile/Batch/CompleteRef.lean; tokens and the store: the header there)
(words of this library: lean/GLOSSARY.md).

  Part 1  `rleavesTU`, `reqTU` against `rleavesOU`, `reqRootOU`
  Part 2  `slotLoU`, `slotJoinU`, `joinMU` against `optO` of `slotLoO` and `slotJoinO`
  Part 3  `chainTU` against `chainOU`
  Part 4  one execution: `proveBU` against `proveOU`; where the proof string of a slot with a
          request is `none`; `proveBUX` (Compile/Batch/StarUX.lean): the hash blocks of a slot with
          a request

`RealFam` (Compile/Batch/CompleteChain.lean): the fixed family answers the ghost names `fbw` as
`fb`; a search over nonces then has the distribution of `askG` (`lawS_fbG`,
Compile/Batch/CompleteRef.lean) (not all hypotheses are named here: see its statement). No condition
on the wire record is used.

Limits: nothing on probabilities over the oracles (Compile/Batch/CompleteUUnif.lean).
-/
import Compile.Batch.CompleteRefChain
import Compile.Batch.CompleteURefDefs
import Compile.Batch.CompleteUChain
import Compile.Batch.StarUX

noncomputable section

namespace Compile.Batch.RefU
open Iop Rom Prob Compile.Batch.Cmpl Compile.Batch.CmplU Compile.Batch.Ref

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. The request tree -/

/-- the strings of the slot values -/
def strs (vs : List Bits) (cs : List (Option Tok)) : List (Option Bits) :=
  cs.map (Option.map fun c => vs.getD c [])

theorem strs_of_prefix {vs vs' : List Bits} (hp : vs <+: vs') {cs : List (Option Tok)}
    (h : ∀ c, some c ∈ cs → IsDig lam vs c) : strs vs' cs = strs vs cs :=
  List.map_congr_left fun o ho => by
    cases o with
    | none => rfl
    | some c => exact congrArg some (getD_of_prefix hp (h c ho).1)

theorem lawS_rleafT (c : Tok) (vs : List Bits) :
    LawS f (rleafT (lam := lam) (K := K) (L := L) c) vs (fun d vs' => dv lam vs' d)
      (PMF.pure (f OracleName.rleaf (vs.getD c [] : Bits))) := by
  unfold rleafT
  exact lawS_marked
    ((lawS_pure _ _ _).congr
      (congrArg PMF.pure (isDig_concat vs (f OracleName.rleaf (vs.getD c [] : Bits))).2))

theorem lawS_rleavesTU :
    ∀ (cs : List (Option Tok)) (vs : List Bits), (∀ c, some c ∈ cs → IsDig lam vs c) →
      LawS f (rleavesTU (lam := lam) (K := K) (L := L) cs) vs
        (fun o vs' => o.map (dv lam vs')) ((rleavesOU (strs vs cs)).runEager f)
  | [], vs, _ => lawS_pure _ _ _
  | some c :: t, vs, h => by
      have h1 := LawS.bind (ψ := fun (o : List Tok) vs' => o.map (dv lam vs'))
        (ν := fun d =>
            ((rleavesOU (lam := lam) (K := K) (L := L) (strs vs t)).bind fun r =>
              OComp.pure (d :: r)).runEager f)
        (g := fun d =>
            (rleavesTU (lam := lam) (K := K) (L := L) t).bind fun r => Step.pure (d :: r))
        (lawS_rleafT f c vs) (tri_rleafT f c vs (h c (by simp))).with_prefix fun d vs1 hd => ?_
      · rw [PMF.pure_bind] at h1
        exact h1
      · have ht : ∀ u, some u ∈ t → IsDig lam vs u := fun u hu => h u (by simp [hu])
        beta_reduce
        rw [OComp.runEager_bind, ← strs_of_prefix hd.2 ht]
        refine LawS.bind (lawS_rleavesTU t vs1 fun u hu => (ht u hu).mono hd.2) (tri_prefix _ vs1)
          fun r vs2 hp => (lawS_pure _ _ _).congr ?_
        show PMF.pure _ = PMF.pure _
        rw [List.map_cons, dv_of_prefix hp hd.1.1.1]
  | none :: t, vs, h => by
      show LawS f
        (Step.fresh lam fun d =>
          (rleavesTU (lam := lam) (K := K) (L := L) t).bind fun r => Step.pure (d :: r))
        vs _ (((freshO lam).bind fun u =>
          (rleavesOU (lam := lam) (K := K) (L := L) (strs vs t)).bind fun r =>
            OComp.pure (digD lam u :: r)).runEager f)
      rw [runEager_freshO_bind]
      refine lawS_fresh fun r0 => ?_
      have hp : vs <+: vs ++ [List.ofFn fun i : Fin lam => r0.val.testBit i] :=
        List.prefix_append _ _
      have ht : ∀ u, some u ∈ t → IsDig lam vs u := fun u hu => h u (by simp [hu])
      rw [OComp.runEager_bind, ← strs_of_prefix hp ht]
      refine LawS.bind (lawS_rleavesTU t _ fun u hu => (ht u hu).mono hp) (tri_prefix _ _)
        fun r vs2 hp2 => (lawS_pure _ _ _).congr ?_
      show PMF.pure _ = PMF.pure _
      rw [List.map_cons, dv_of_prefix hp2 (by simp)]
      unfold dv
      rw [getD_concat_length]
      rfl

/-- The root of the request tree over 2^depthReq slots, whose slot values are digests, has the
distribution of reqRootOU on the slot values. -/
theorem lawS_reqTU (depthReq : ℕ) (cs : List (Option Tok)) (vs : List Bits)
    (h : ∀ c, some c ∈ cs → IsDig lam vs c) (hl : cs.length = 2 ^ depthReq) :
    LawS f (reqTU (lam := lam) (K := K) (L := L) depthReq cs) vs (fun rq vs' => dv lam vs' rq.root)
      ((reqRootOU depthReq (strs vs cs)).runEager f) := by
  unfold reqTU reqRootOU
  rw [OComp.runEager_bind]
  refine LawS.bind (lawS_rleavesTU f cs vs h) (tri_rleavesTU f cs vs h) fun ls vs1 hls => ?_
  have e : ((levelsM (rnodeV (L := L) (K := K)) depthReq (ls.map (dv lam vs1))).bind
        fun lv => OComp.pure (rootOf lv)).runEager f =
      PMF.pure (rootOf (levelsF (rnodeFB f) depthReq (ls.map (dv lam vs1)))) := by
    rw [OComp.runEager_bind,
      runEager_of_evalsTo f
        ((evaluates_eager f).levelsM (qN := rnodeV (L := L) (K := K)) (hN := rnodeFB f)
          (fun a b => evalsTo_ask f OracleName.rnode (List.ofFn a, List.ofFn b)) depthReq _)]
    exact PMF.pure_bind _ _
  rw [e]
  refine lawS_const
    (Tri.bind (tri_levelsT (tri_rnodeT f) depthReq ls vs1 hls.1) fun lv vs2 hlv =>
      tri_pure_iff.2 ?_)
  exact rootOf_map (dv lam vs2) (rnodeFB f) depthReq lv _ (by rw [hls.2.1]; exact hl) hlv.2

/-! ## Part 2. Slots and rounds -/

/-- a program that has the distribution of go (h) and whose result always counts as a slot with a
request has the distribution of optO on such a slot -/
theorem lawS_opt {α τ : Type} {c : St lam K L α} {vs : List Bits} {val' : α → List Bits → τ}
    {valU : α → List Bits → Option τ} {go : TypedOracleComputation lam K L τ} (h : LawS f c vs val' (go.runEager f))
    (hT : Tri f c vs fun a vs' => valU a vs' = some (val' a vs')) :
    LawS f c vs valU ((go.bind fun v' => OComp.pure (some v')).runEager f) := by
  refine ((h.map some).congr_fun hT).congr ?_
  rw [OComp.runEager_bind, ← PMF.bind_pure_comp]
  rfl

section Slot
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- a slot, with the strings for which its tokens stand; none for an empty slot -/
def valOfU {s : Shape} (vs : List Bits) (ph : PhT) (z : SlotSt lam K Y s) :
    Option (VSlot lam K X s) :=
  z.2.x.map fun _ => valOf xin vs ph z

theorem valOfU_none {s : Shape} {vs : List Bits} {ph : PhT}
    {z : SlotSt lam K Y s} (h : z.2.x = none) : valOfU xin vs ph z = none := by
  simp [valOfU, h]

theorem valOfU_some {s : Shape} {vs : List Bits} {ph : PhT}
    {z : SlotSt lam K Y s} (h : z.2.x ≠ none) :
    valOfU xin vs ph z = some (valOf xin vs ph z) := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 h
  simp [valOfU, hy]

theorem valOfU_of_prefix {s : Shape} {vs vs' : List Bits} (hp : vs <+: vs') {ph : PhT}
    {z : SlotSt lam K Y s} (h : z.2.x ≠ none → LPre vs ph z.2) :
    valOfU xin vs' ph z = valOfU xin vs ph z := by
  by_cases hx : z.2.x = none
  · rw [valOfU_none xin hx, valOfU_none xin hx]
  · rw [valOfU_some xin hx, valOfU_some xin hx, valOf_of_prefix xin hp (h hx)]

theorem valOfU_shr_of_prefix {s : Shape} {vs vs' : List Bits} (hp : vs <+: vs') (tk0 tk0' : Tok)
    {z : SlotSt lam K Y s} (h : z.2.x ≠ none → z.2.tk < vs.length ∧ z.2.c < vs.length) :
    valOfU xin vs' (.shr tk0') z = valOfU xin vs (.shr tk0) z := by
  by_cases hx : z.2.x = none
  · rw [valOfU_none xin hx, valOfU_none xin hx]
  · rw [valOfU_some xin hx, valOfU_some xin hx,
      valOf_shr_of_prefix xin hp tk0 tk0' (h hx).1 (h hx).2]

theorem valPh_of_prefix' {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ph : PhT}, PhPre vs ph → valPh vs' ph = valPh vs ph
  | .first, _ => rfl
  | .loc, _ => rfl
  | .shr _, h => by simp only [valPh, getD_of_prefix hp h]
  | .aft, _ => rfl

variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
  (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem tri_slotLoU_x (ph : PhT) (z : SlotSt lam K Y (r :: s)) (vs : List Bits) :
    Tri f (slotLoU sMT t cms xin a w emb plJ i ph z) vs fun z' _ => z'.2.x = z.2.x := by
  by_cases hx : z.2.x = none
  · rw [slotLoU_none sMT t cms xin a w i emb plJ ph hx]
    exact tri_pure_iff.2 rfl
  · rw [slotLoU_some sMT t cms xin a w i emb plJ ph hx]
    exact tri_slotLo_x f sMT t cms xin a w emb plJ i ph z vs

theorem tri_slotJoin_x (z : SlotSt lam K Y (r :: s)) (vs : List Bits) :
    Tri f (slotJoin sMT t a w emb plJ i z) vs fun z' _ => z'.2.x = z.2.x := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  unfold slotJoin
  exact tri_withTree_any f sMT _ _ _ _ vs _ fun tr vs1 => tri_marked_iff.2 (tri_pure_iff.2 rfl)

theorem tri_slotJoinU_x (z : SlotSt lam K Y (r :: s)) (vs : List Bits) :
    Tri f (slotJoinU sMT t a w emb plJ i z) vs fun z' _ => z'.2.x = z.2.x := by
  by_cases hx : z.2.x = none
  · rw [slotJoinU_none sMT t a w i emb plJ hx]
    exact tri_pure_iff.2 rfl
  · rw [slotJoinU_some sMT t a w i emb plJ hx]
    exact tri_slotJoin_x f sMT t a w emb plJ i z vs

/-- A local round in one slot. -/
theorem lawS_slotLoU (hf : RealFam f) (ph : PhT) (z : SlotSt lam K Y (r :: s)) (vs : List Bits)
    (hpre : z.2.x ≠ none → LPre vs ph z.2) :
    LawS f (slotLoU sMT t cms xin a w emb plJ i ph z) vs
      (fun z' vs' => valOfU xin vs' ph.afterLo z')
      ((optO (slotLoO sMT t cms a w emb plJ i (valPh vs ph)) (valOfU xin vs ph z)).runEager f) := by
  by_cases hx : z.2.x = none
  · rw [slotLoU_none sMT t cms xin a w i emb plJ ph hx, valOfU_none xin hx]
    exact (lawS_pure _ _ _).congr (congrArg PMF.pure (valOfU_none xin hx))
  · rw [slotLoU_some sMT t cms xin a w i emb plJ ph hx, valOfU_some xin hx]
    exact lawS_opt f (lawS_slotLo f sMT t cms xin a w emb plJ i hf ph z vs (hpre hx))
      ((tri_slotLo_x f sMT t cms xin a w emb plJ i ph z vs).mono fun z' vs' h =>
        valOfU_some xin (by rw [h]; exact hx))

/-- The joining round in one slot. The slot is seen as in the phase after the round (tk0 is any
token). -/
theorem lawS_slotJoinU (tk0 : Tok) (z : SlotSt lam K Y (r :: s)) (vs : List Bits)
    (hpre : z.2.x ≠ none → z.2.tk < vs.length) :
    LawS f (slotJoinU sMT t a w emb plJ i z) vs (fun z' vs' => valOfU xin vs' (.shr tk0) z')
      ((optO (slotJoinO sMT t a w emb plJ i) (valOfU xin vs .loc z)).runEager f) := by
  by_cases hx : z.2.x = none
  · rw [slotJoinU_none sMT t a w i emb plJ hx, valOfU_none xin hx]
    exact (lawS_pure _ _ _).congr (congrArg PMF.pure (valOfU_none xin hx))
  · rw [slotJoinU_some sMT t a w i emb plJ hx, valOfU_some xin hx]
    exact lawS_opt f (lawS_slotJoin f sMT t xin a w emb plJ i tk0 z vs (hpre hx))
      ((tri_slotJoin_x f sMT t a w emb plJ i z vs).mono fun z' vs' h =>
        valOfU_some xin (by rw [h]; exact hx))

/-- if the token tk of a slot with a request is in the store: after the joining round the tokens of
such a slot point into the store -/
theorem tri_slotJoinU_lt (z : SlotSt lam K Y (r :: s)) (vs : List Bits)
    (hpre : z.2.x ≠ none → z.2.tk < vs.length) :
    Tri f (slotJoinU sMT t a w emb plJ i z) vs fun z' vs' =>
      z'.2.x ≠ none → z'.2.tk < vs'.length ∧ IsDig lam vs' z'.2.c := by
  by_cases hx : z.2.x = none
  · rw [slotJoinU_none sMT t a w i emb plJ hx]
    exact tri_pure_iff.2 fun h => absurd hx h
  · rw [slotJoinU_some sMT t a w i emb plJ hx]
    obtain ⟨⟨m, k⟩, acc⟩ := z
    refine ((tri_slotJoin f sMT t a w emb plJ i m k acc vs (hpre hx)).with_prefix).mono ?_
    rintro z' vs' ⟨⟨tr, c, q, -, -, hc, -, rfl⟩, hp⟩ -
    exact ⟨lt_of_lt_of_le (hpre hx) hp.length_le, hc⟩

end Slot

section Join
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)
variable {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- the joining round in all slots -/
theorem lawS_joinMU (tk0 : Tok) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits),
      (∀ z ∈ zs, z.2.x ≠ none → z.2.tk < vs.length) →
      LawS f (joinMU sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs) vs
        (fun o vs' => o.1.map (valOfU xin vs' (.shr tk0)))
        ((eachO
          (optO (slotJoinO sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i))
          (zs.map (valOfU xin vs .loc))).runEager f)
  | [], vs, _ => lawS_pure _ _ _
  | z :: zs, vs, h => by
      rw [List.map_cons, runEager_eachO_cons]
      refine LawS.bind (lawS_slotJoinU f sMT t xin a w _ _ i tk0 z vs (h z (by simp)))
        (tri_slotJoinU_lt f sMT t a w _ _ i z vs (h z (by simp))).with_prefix fun z' vs1 hz' => ?_
      obtain ⟨hz', hp1⟩ := hz'
      have e : zs.map (valOfU xin vs .loc) =
          zs.map (valOfU xin vs1 .loc) := List.map_congr_left fun u hu =>
        (valOfU_of_prefix xin hp1 (ph := .loc) fun hx =>
          ⟨h u (by simp [hu]) hx, h u (by simp [hu]) hx⟩).symm
      rw [e]
      refine LawS.bind
        (lawS_joinMU tk0 zs vs1 fun u hu hx => lt_of_lt_of_le (h u (by simp [hu]) hx) hp1.length_le)
        (tri_prefix _ vs1) fun o vs2 hp => ((lawS_pure _ _ _).congr ?_)
      exact congrArg (fun v => PMF.pure (v :: List.map (valOfU xin vs2 (.shr tk0)) o.1))
        (valOfU_shr_of_prefix xin hp tk0 tk0 fun hx => ⟨(hz' hx).1, (hz' hx).2.1⟩)

/-- what the joining round in all slots ensures, under the hypothesis of `lawS_joinMU`, without any
on the wire record -/
theorem tri_joinMU_lt :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits),
      (∀ z ∈ zs, z.2.x ≠ none → z.2.tk < vs.length) →
      Tri f (joinMU sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs) vs
        fun o vs' =>
      o.1.length = zs.length ∧
      (o.2 = o.1.map fun z => csOf z.2) ∧
      ∀ z1 ∈ o.1, z1.2.x ≠ none → z1.2.tk < vs'.length ∧ IsDig lam vs' z1.2.c
  | [], _, _ => tri_pure_iff.2 ⟨rfl, rfl, fun _ h => by cases h⟩
  | z :: zs, vs, h => by
      refine Tri.bind (tri_slotJoinU_lt f sMT t a w _ _ i z vs (h z (by simp))).with_prefix
        fun z' vs1 hz' => ?_
      refine Tri.bind
        (tri_joinMU_lt zs vs1 fun u hu hx =>
          lt_of_lt_of_le (h u (by simp [hu]) hx) hz'.2.length_le).with_prefix
        fun o vs2 ho => tri_pure_iff.2 ⟨by simp [ho.1.1], ?_, fun z1 hz1 hx => ?_⟩
      · show (z'.2.x.map fun _ => z'.2.c) :: o.2 = _
        rw [ho.1.2.1]
        rfl
      · rcases List.mem_cons.1 hz1 with rfl | hz1
        · exact ⟨lt_of_lt_of_le (hz'.1 hx).1 ho.2.length_le, (hz'.1 hx).2.mono ho.2⟩
        · exact ho.1.2.2 z1 hz1 hx

end Join

/-! ## Part 3. The chain -/

section Chain
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

/-- the hash blocks that a slot with a request has gathered; the empty list for an empty slot -/
def blkA (acc : SlotAcc lam K Y) : List (Blk lam K) := (acc.x.map fun _ => acc.blocks).getD []

theorem blocksU_valOfU {s : Shape} (vs : List Bits) (ph : PhT) (z : SlotSt lam K Y s) :
    blocksU (valOfU xin vs ph z) = blkA z.2 := by
  obtain ⟨st, acc⟩ := z
  unfold blocksU valOfU blkA
  cases acc.x <;> rfl

theorem valOfU_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (vs : List Bits) (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    valOfU xin vs ph (hear w bl noted z) = (valOfU xin vs ph z).map (hearO w bl) := by
  have hx : (hear w bl noted z).2.x = z.2.x := rfl
  by_cases h : z.2.x = none
  · rw [valOfU_none xin (hx.trans h), valOfU_none xin h]
    rfl
  · rw [valOfU_some xin (by rw [hx]; exact h), valOfU_some xin h, valOf_hear]
    rfl

/-- Under the hypotheses below, all chains of a batch have the distribution of chainOU. (The
hypotheses: `RealFam`: the ghost names `fbw t j` are answered as `fb t`; `RoundSplits.FmtFrom`
(Iop/BatchFmt.lean): from the phase ph on, every round has a format, and a component that is not
sent is empty; there are 2 ^ depthReq slots, or `AllLo`: there is no shared round; `PhPre`: the
token of the phase points into the store; `LPre`, for every slot with a request: the tokens of the
slot and of the phase point into the store, and, once the chains have joined, the string of its slot
value is a digest (`IsDig`, Compile/Batch/CompleteTree.lean).) -/
theorem lawS_chainTU (hf : RealFam f) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (vs : List Bits),
      RoundSplits.FmtFrom s A (fph ph) → (zs.length = 2 ^ depthReq ∨ AllLo s A) → PhPre vs ph →
      (∀ z ∈ zs, z.2.x ≠ none → LPre vs ph z.2) →
      LawS f (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
        vs (fun out _ => out.1.map blkA)
        ((chainOU sMT t cms depthReq s A W embS embP i (valPh vs ph) σ0
          (zs.map (valOfU xin vs ph))).runEager f)
  | [], _, _, _, _, _, ph, _, zs, a0, vs, _, _, _, _ => by
      refine (lawS_pure _ _ _).congr ?_
      show PMF.pure _ = PMF.pure _
      congr 1
      rw [List.map_map, List.map_map]
      exact List.map_congr_left fun z _ => (blocksU_valOfU xin vs ph z).symm
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, vs, hF, hN, hph, hpre => by
      have hF2 : (match a.kind, fph ph with
          | .lo, ph => a.NoShared ∧ RoundSplits.FmtFrom s A ph.afterLo
          | .sh, .loc => RoundSplits.FmtFrom s A .shr
          | .sh, .shr => a.NoSlot ∧ RoundSplits.FmtFrom s A .shr
          | .sh, .first => False
          | .sh, .aft => False) := hF
      by_cases hk : a.kind = .lo
      · rw [hk] at hF2
        rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph,
          chainOU_lo sMT t cms depthReq w W embS embP i (m0, k0) _ hk, OComp.runEager_bind]
        have hstep : ∀ (z : SlotSt lam K Y (r :: s)) (v : List Bits),
            (vs <+: v ∧ (z.2.x ≠ none → LPre vs ph z.2)) →
            Tri f (slotLoU sMT t cms xin a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i ph z)
              v fun z' v' => z'.2.x ≠ none → LPre v' ph.afterLo z'.2 := by
          rintro ⟨⟨m, k⟩, acc⟩ v ⟨hpv, hz⟩
          by_cases hx : acc.x = none
          · rw [slotLoU_none sMT t cms xin a w i _ _ ph (z := ⟨⟨m, k⟩, acc⟩) hx]
            exact tri_pure_iff.2 fun h => absurd hx h
          · rw [slotLoU_some sMT t cms xin a w i _ _ ph (z := ⟨⟨m, k⟩, acc⟩) hx]
            refine ((tri_slotLo f sMT t cms xin a w _ _ i hf ph m k acc v
              ((hz hx).2.mono hpv)).with_prefix).mono ?_
            rintro z' v' ⟨⟨tr, tl, q, nc, dd, -, -, -, htl, -, rfl⟩, hp'⟩ -
            exact ⟨htl, slotPre_afterLo (hpv.trans hp') htl (hz hx).2 _ _ _ _ _⟩
        refine LawS.bind
          (φ := fun (zs' : List (SlotSt lam K Y s)) v' => zs'.map (valOfU xin v' ph.afterLo))
          (Q := fun zs' v' =>
              zs'.length = zs.length ∧ ∀ z' ∈ zs', z'.2.x ≠ none → LPre v' ph.afterLo z'.2)
          ?_ ?_ fun zs1 vs1 h1 => ?_
        · have h := lawS_eachM f
            (slotLoU sMT t cms xin a w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i ph)
            (optO (slotLoO sMT t cms a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i (valPh vs ph)))
            (fun v z => valOfU xin v ph z) (fun v z' => valOfU xin v ph.afterLo z')
              (fun z v => vs <+: v ∧ (z.2.x ≠ none → LPre vs ph z.2))
            (fun z' v => z'.2.x ≠ none → LPre v ph.afterLo z'.2)
            (fun z v v' hp h =>
              ⟨⟨h.1.trans hp, h.2⟩, valOfU_of_prefix xin hp fun hx => (h.2 hx).mono h.1⟩)
            (fun z' v v' hp h => valOfU_of_prefix xin hp h) hstep (fun z v h => by
              have h2 := lawS_slotLoU f sMT t cms xin a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i hf ph z v fun hx => (h.2 hx).mono h.1
              rwa [valPh_of_prefix' h.1 hph] at h2) zs vs fun z hz => ⟨List.prefix_refl _, hpre z hz⟩
          exact h
        · refine (tri_eachM (f := f) _
              (fun (z : SlotSt lam K Y (r :: s)) v => vs <+: v ∧ (z.2.x ≠ none → LPre vs ph z.2))
              (fun (_ : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) v =>
                z'.2.x ≠ none → LPre v ph.afterLo z'.2)
              (fun z v v' hp h => ⟨h.1.trans hp, h.2⟩) (fun z z' v v' hp h hx => (h hx).mono hp)
              hstep zs vs fun z hz => ⟨List.prefix_refl _, hpre z hz⟩).mono
            fun zs' v' h => ?_
          exact ⟨h.length_eq.symm, fun z' hz' => (forall₂_mem_right h z' hz').choose_spec.2⟩
        · have ih := lawS_chainTU hf s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
            ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs1
            { a0 with trees := a0.trees ++ [none] } vs1 (by rw [fph_afterLo]; exact hF2.2)
              (hN.imp (fun h => by rw [h1.1]; exact h) fun h => h.2)
            (phPre_afterLo _ _) h1.2
          rwa [valPh_afterLo vs vs1 ph] at ih
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        rw [hk'] at hF2
        have hlen : zs.length = 2 ^ depthReq := hN.resolve_right fun h => hk h.1
        cases ph with
        | first => exact False.elim hF2
        | aft => exact False.elim hF2
        | loc =>
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk', valPh,
            chainOU_join sMT t cms depthReq w W embS embP i (m0, k0) _ hk', OComp.runEager_bind]
          refine LawS.bind
            (lawS_joinMU f sMT t xin a A w embS embP i 0 zs vs fun z hz hx => (hpre z hz hx).1)
            (tri_joinMU_lt f sMT t a A w embS embP i zs vs fun z hz hx => (hpre z hz hx).1)
            fun o vs1 ho => ?_
          obtain ⟨ho1, ho2, ho3⟩ := ho
          have hdig : ∀ c, some c ∈ o.2 → IsDig lam vs1 c := by
            intro c hc
            rw [ho2] at hc
            obtain ⟨z1, hz1, hx1, rfl⟩ := mem_csOf hc
            exact (ho3 z1 hz1 hx1).2
          have hlen1 : o.2.length = 2 ^ depthReq := by rw [ho2, List.length_map, ho1]; exact hlen
          have hcs : ((o.1.map (valOfU xin vs1 (.shr 0))).map (Option.map fun v => v.c)) =
              strs vs1 o.2 := by
            unfold strs
            rw [ho2, List.map_map, List.map_map]
            refine List.map_congr_left fun z _ => ?_
            obtain ⟨st, acc⟩ := z
            simp only [Function.comp_apply, valOfU, csOf]
            cases acc.x <;> rfl
          rw [OComp.runEager_bind, hcs]
          refine LawS.bind (lawS_reqTU f depthReq o.2 vs1 hdig hlen1)
            (tri_reqTU f depthReq o.2 vs1 hdig).with_prefix fun rq vs2 hrq => ?_
          obtain ⟨⟨lv, hrq, hlv⟩, hp2⟩ := hrq
          have hrqd : IsDig lam vs2 rq.root := hrq.isDig_root (by rw [hlv.1]; exact hlen1)
          rw [OComp.runEager_bind]
          refine lawS_withTree f sMT w.has0 w.depth0 _ _ vs2 _ _ fun tr0 vs2' hp2' htr0 => ?_
          rw [OComp.runEager_bind]
          refine lawS_fbG f t i hf w.gr0 w.chal rq.root [] tr0 (fun _ => Head.f4 cms)
            (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) _ vs2' _ _
            (.f4 cms (List.ofFn (dv lam vs2 rq.root))) (rootV lam vs2' tr0) (fun vs3 hp3 => ⟨by
              show Head.f4 cms (vs3.getD rq.root []) = _
              rw [getD_of_prefix (hp2'.trans hp3) hrqd.1, ← hrqd.2], htr0.rootV_of_prefix hp3⟩) fun nc dd vs3 hp23 => ?_
          generalize (⟨i,
              .f4 cms (List.ofFn (dv lam vs2 rq.root)),
              rootV lam vs2' tr0,
              embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩ : FbIn lam L t) = q4
          have hp3 : vs3 <+: vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2] := List.prefix_append _ _
          have ih := lawS_chainTU hf s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
            (i + 1) (.shr vs3.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q4).1)))
            (o.1.map (hear w (f (OracleName.fb t) q4).1 true))
            ⟨a0.trees ++ [tr0], a0.toks ++ [vs3.length], some rq,
              nc.toList ++ a0.nons, dd ++ a0.dead⟩
            (vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2]) hF2
            (Or.inl (by rw [List.length_map, ho1]; exact hlen))
            (by simp [PhPre]) (fun z' hz' hx' => by
              obtain ⟨z1, hz1, rfl⟩ := List.mem_map.1 hz'
              have h3 := ho3 z1 hz1 hx'
              exact ⟨lt_of_lt_of_le h3.1 (hp2.trans (hp2'.trans (hp23.trans hp3))).length_le,
                by simp,
                h3.2.mono (hp2.trans (hp2'.trans (hp23.trans hp3)))⟩)
          have e1 : valPh (vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2]) (.shr vs3.length) =
              .shr (List.ofFn (f (OracleName.fb t) q4).2) := by
            simp only [valPh, getD_concat_length]
          have e2 : (o.1.map (hear w (f (OracleName.fb t) q4).1 true)).map
                (valOfU xin (vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2]) (.shr vs3.length)) =
              (o.1.map (valOfU xin vs1 (.shr 0))).map
                (Option.map (hearO w (f (OracleName.fb t) q4).1)) := by
            rw [List.map_map, List.map_map]
            refine List.map_congr_left fun z1 hz1 => ?_
            rw [Function.comp_apply, Function.comp_apply, valOfU_hear,
              valOfU_shr_of_prefix xin (hp2.trans (hp2'.trans (hp23.trans hp3))) 0 _
                fun hx => ⟨(ho3 z1 hz1 hx).1, (ho3 z1 hz1 hx).2.1⟩]
          rw [e1, e2] at ih
          exact ih
        | shr tk0 =>
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0, valPh,
            chainOU_shr sMT t cms depthReq w W embS embP i (m0, k0) _ hk', OComp.runEager_bind]
          refine lawS_withTree f sMT w.has0 w.depth0 _ _ vs _ _ fun tr0 vs2 hp2 htr0 => ?_
          rw [OComp.runEager_bind]
          refine lawS_fbG f t i hf w.gr0 w.chal tk0 [] tr0 (fun _ => Head.f5)
            (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) _ vs2 _ _
            (.f5 (vs.getD tk0 [])) (rootV lam vs2 tr0) (fun vs3 hp3 => ⟨by
              show Head.f5 (vs3.getD tk0 []) = _
              rw [getD_of_prefix (hp2.trans hp3) hph], htr0.rootV_of_prefix hp3⟩) fun nc dd vs3 hp23 => ?_
          generalize (⟨i,
              .f5 (vs.getD tk0 []),
              rootV lam vs2 tr0,
              embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩ : FbIn lam L t) = q5
          have hp3 : vs3 <+: vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2] := List.prefix_append _ _
          have ih := lawS_chainTU hf s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
            (i + 1) (.shr vs3.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q5).1)))
            (zs.map (hear w (f (OracleName.fb t) q5).1 false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [vs3.length],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
            (vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2]) hF2.2
            (Or.inl (by rw [List.length_map]; exact hlen)) (by simp [PhPre]) (fun z' hz' hx' => by
              obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hz'
              have h3 := hpre z hz hx'
              exact ⟨lt_of_lt_of_le h3.1 (hp2.trans (hp23.trans hp3)).length_le,
                by simp,
                h3.2.2.mono (hp2.trans (hp23.trans hp3))⟩)
          have e1 : valPh (vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2]) (.shr vs3.length) =
              .shr (List.ofFn (f (OracleName.fb t) q5).2) := by
            simp only [valPh, getD_concat_length]
          have e2 : (zs.map (hear w (f (OracleName.fb t) q5).1 false)).map
                (valOfU xin (vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2]) (.shr vs3.length)) =
              (zs.map (valOfU xin vs (.shr tk0))).map
                (Option.map (hearO w (f (OracleName.fb t) q5).1)) := by
            rw [List.map_map, List.map_map]
            refine List.map_congr_left fun z hz => ?_
            rw [Function.comp_apply, Function.comp_apply, valOfU_hear,
              valOfU_shr_of_prefix xin (hp2.trans (hp23.trans hp3)) tk0 _ fun hx =>
                ⟨(hpre z hz hx).1, (hpre z hz hx).2.2.1⟩]
          rw [e1, e2] at ih
          exact ih

end Chain

/-! ## Part 4. One execution -/

section KeepX
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

theorem tri_joinMU_x {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits),
      Tri f (joinMU sMT t a w emb plJ i zs) vs fun o _ =>
        (o.1.map fun z => z.2.x) = zs.map fun z => z.2.x
  | [], _ => tri_pure_iff.2 rfl
  | z :: zs, vs => by
      refine Tri.bind (tri_slotJoinU_x f sMT t a w emb plJ i z vs) fun z' vs1 hz' =>
        Tri.bind (tri_joinMU_x a w emb plJ i zs vs1) fun o vs2 ho => tri_pure_iff.2 ?_
      show z'.2.x :: (o.1.map fun z => z.2.x) = z.2.x :: _
      rw [hz', ho]

/-- under `FmtFrom`, what the slots hold does not change along the chain -/
theorem tri_chainTU_x :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (vs : List Bits),
      RoundSplits.FmtFrom s A (fph ph) →
      Tri f (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) vs
        fun out _ => (out.1.map fun acc => acc.x) = zs.map fun z => z.2.x
  | [], _, _, _, _, _, _, _, zs, _, _, _ => tri_pure_iff.2 (by rw [List.map_map]; rfl)
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, vs, hF => by
      have hF2 : (match a.kind, fph ph with
          | .lo, ph => a.NoShared ∧ RoundSplits.FmtFrom s A ph.afterLo
          | .sh, .loc => RoundSplits.FmtFrom s A .shr
          | .sh, .shr => a.NoSlot ∧ RoundSplits.FmtFrom s A .shr
          | .sh, .first => False
          | .sh, .aft => False) := hF
      by_cases hk : a.kind = .lo
      · rw [hk] at hF2
        rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        refine Tri.bind
          (tri_eachM (f := f) _ (fun _ _ => True)
            (fun (z : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) _ => z'.2.x = z.2.x)
            (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
            (fun z v _ => tri_slotLoU_x f sMT t cms xin a w _ _ i ph z v) zs vs fun _ _ => trivial)
          fun zs1 vs1 h1 => ?_
        refine (tri_chainTU_x s A W _ _ (i + 1) ph.afterLo _ zs1 _ vs1
            (by rw [fph_afterLo]; exact hF2.2)).mono
          fun out _ h => ?_
        rw [h]
        exact forall₂_map_eq (fun (z : SlotSt lam K Y (r :: s)) => z.2.x)
          (fun (z : SlotSt lam K Y s) => z.2.x) (fun _ _ h => h) h1
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        rw [hk'] at hF2
        cases ph with
        | first => exact False.elim hF2
        | aft => exact False.elim hF2
        | loc =>
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine Tri.bind (tri_joinMU_x f sMT t a w _ _ i zs vs) fun o vs1 ho => ?_
          refine Tri.bind (tri_true' _ vs1) fun rq vs2 _ =>
            tri_withTree_any f sMT _ _ _ _ vs2 _ fun tr0 vs3 =>
              tri_fbG_any f t _ _ _ _ _ _ _ _ _ _ _ _ (fun nc dd bl tl vs4 => ?_) _
          refine (tri_chainTU_x s A W _ _ (i + 1) (.shr _) _ _ _ _ hF2).mono fun out _ h => ?_
          rw [h, map_x_hear, ho]
        | shr tk0 =>
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine tri_withTree_any f sMT _ _ _ _ vs _ fun tr0 vs3 =>
            tri_fbG_any f t _ _ _ _ _ _ _ _ _ _ _ _ (fun nc dd bl tl vs4 => ?_) _
          refine (tri_chainTU_x s A W _ _ (i + 1) (.shr _) _ _ _ _ hF2.2).mono fun out _ h => ?_
          rw [h, map_x_hear]

end KeepX

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- what a slot is at the start -/
theorem tri_initSlotU (c0 : H.Coin0) (xo : Option Y) (v : List Bits) :
    Tri f (initSlotU sFS Q H wp w c0 xo) v fun z' v' =>
      (z'.2.x ≠ none → LPre v' .first z'.2) ∧ z'.2.x.map Prod.fst = xo := by
  cases xo with
  | none => exact tri_pure_iff.2 ⟨fun h => absurd rfl h, rfl⟩
  | some x =>
    refine Tri.bind (tri_drawT f wp.coin v) fun cj v0 hv0 =>
      tri_fresh_iff.2 fun r => tri_pure_iff.2 ?_
    exact ⟨fun _ => ⟨by simp, by show v0.length < _; simp⟩, rfl⟩

theorem lawS_initSlotU (c0 : H.Coin0) (x : Option Y) (vs : List Bits) :
    LawS f (initSlotU sFS Q H wp w c0 x) vs
      (fun z' vs' => valOfU (fun y : Y × H.Coin => xin y.1) vs' .first z')
      ((optO (fun x => initO sFS Q H wp xin w c0 (some x)) x).runEager f) := by
  cases x with
  | none => exact lawS_pure _ _ _
  | some x =>
    refine lawS_opt f (lawS_initSlot f sFS Q H wp xin w c0 (some x) vs)
      ((tri_initSlotU f sFS Q H wp w c0 (some x) vs).mono fun z' vs' h => valOfU_some _ ?_)
    intro hn
    rw [hn] at h
    exact absurd h.2 (by simp)

/-- One execution, from any store, under the hypotheses below: whether the proof string of a slot
that holds x, and for which one is made, is `none` has the distribution of `noneAt` of the output of
proveOU. Of the external trees only the roots matter. -/
theorem lawS_proveBU (hf : RealFam f) (hF : Q.ann.Fmt) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (n : ℕ) (x : Y)
    (hn : xs[n]? = some (some x)) (hfl : fl n = true) (vs : List Bits) :
    LawS f (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      vs (fun πs _ => (πs.getD n none).isNone)
      (((proveOU sMT sFS t Q H wq wp embS embP xin depthReq
          (trees.map TreeH.root) w xs).runEager f).map
        (noneAt Q H wq wp w x n)) := by
  unfold proveBU proveOU
  rw [runEager_drawO_bind, PMF.map_bind]
  refine lawS_drawT_bind f wp.coin0 _ vs _ _ fun r0 => ?_
  generalize wp.coin0.e r0 = c0
  rw [OComp.runEager_bind, PMF.map_bind]
  refine LawS.bind
    (φ := fun (zs : List (SlotSt lam K (Y × H.Coin) Q.loc.shape)) v' =>
        zs.map (valOfU (fun y : Y × H.Coin => xin y.1) v' .first))
    (Q := fun zs v' =>
        List.Forall₂
          (fun xo (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) =>
            (z'.2.x ≠ none → LPre v' .first z'.2) ∧ z'.2.x.map Prod.fst = xo)
          xs zs)
    ?_ ?_ fun zs vs1 hzs => ?_
  · have h := lawS_eachM f (initSlotU sFS Q H wp w c0)
      (optO fun x => initO sFS Q H wp xin w c0 (some x)) (fun _ xo => xo)
      (fun v z' => valOfU (fun y : Y × H.Coin => xin y.1) v .first z')
        (fun _ _ => True) (fun z' v => z'.2.x ≠ none → LPre v .first z'.2)
      (fun _ _ _ _ _ => ⟨trivial, rfl⟩) (fun z' v v' hp h => valOfU_of_prefix _ hp h)
        (fun xo v _ => (tri_initSlotU f sFS Q H wp w c0 xo v).mono fun _ _ h => h.1)
      (fun xo v _ => lawS_initSlotU f sFS Q H wp xin w c0 xo v) xs vs fun _ _ => trivial
    rwa [List.map_id'] at h
  · exact tri_eachM (f := f) _ (fun _ _ => True)
      (fun xo (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) v =>
        (z'.2.x ≠ none → LPre v .first z'.2) ∧ z'.2.x.map Prod.fst = xo)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ hp h => ⟨fun hx => (h.1 hx).mono hp, h.2⟩)
      (fun xo v _ => tri_initSlotU f sFS Q H wp w c0 xo v) xs vs fun _ _ => trivial
  · rw [← PMF.bind_pure_comp]
    refine LawS.bind
      (lawS_chainTU f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq hf
        Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hF
        (hN.imp (fun h => by rw [← hzs.length_eq]; exact h) id) trivial
        fun z hz => (forall₂_mem_right hzs z hz).choose_spec.2.1)
      (tri_chainTU_x f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq
        Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hF)
      fun out vs2 hx => ?_
    -- the slot number n of the result holds x
    have hlen : out.1.length = xs.length := by
      have := congrArg List.length hx
      rw [List.length_map, List.length_map] at this
      rw [this, hzs.length_eq]
    have hnl : n < out.1.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.1 hn).1
    have hxn : (out.1[n]).x.map Prod.fst = some x := by
      have h1 : (out.1.map fun acc => acc.x)[n]? = some (out.1[n]).x := by simp [hnl]
      rw [hx, List.getElem?_map] at h1
      obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.1 h1
      obtain ⟨xo, hxo, -, hxz⟩ := forall₂_getElem?_right hzs n z hz
      rw [← hzx, hxz]
      exact Option.some.inj (hxo.symm.trans hn)
    obtain ⟨⟨x', cj⟩, hacc, hx'⟩ := Option.map_eq_some_iff.1 hxn
    obtain rfl : x' = x := hx'
    refine lawS_const
      ((tri_finishAll_none f Q H wq wp trees w fl c0 out.2 out.1 0 n out.1[n] x' cj vs2
          (List.getElem?_eq_getElem hnl) hacc (by rw [Nat.zero_add]; exact hfl)).mono
        fun πs _ h => ?_)
    rw [h]
    unfold noneAt
    simp [List.getD_eq_getElem?_getD, hnl, blkA, hacc]

/-- One execution that also outputs the hash blocks (Compile/Batch/StarUX.lean), from any store,
under the hypotheses below: the hash blocks that a slot with a request has seen have the
distribution that they have in proveOU. Of the external trees only the roots matter; which proof
strings are made does not matter. (Slot by slot: of an empty slot proveBUX outputs the hash blocks
of the shared rounds and proveOU nothing.) -/
theorem lawS_proveBUX (hf : RealFam f) (hF : Q.ann.Fmt) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (n : ℕ) (x : Y)
    (hn : xs[n]? = some (some x)) (vs : List Bits) :
    LawS f (proveBUX sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      vs (fun o _ => o.2.getD n [])
      (((proveOU sMT sFS t Q H wq wp embS embP xin depthReq
          (trees.map TreeH.root) w xs).runEager f).map
        fun bss => bss.getD n []) := by
  unfold proveBUX proveOU
  rw [runEager_drawO_bind, PMF.map_bind]
  refine lawS_drawT_bind f wp.coin0 _ vs _ _ fun r0 => ?_
  generalize wp.coin0.e r0 = c0
  rw [OComp.runEager_bind, PMF.map_bind]
  refine LawS.bind
    (φ := fun (zs : List (SlotSt lam K (Y × H.Coin) Q.loc.shape)) v' =>
        zs.map (valOfU (fun y : Y × H.Coin => xin y.1) v' .first))
    (Q := fun zs v' =>
        List.Forall₂
          (fun xo (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) =>
            (z'.2.x ≠ none → LPre v' .first z'.2) ∧ z'.2.x.map Prod.fst = xo)
          xs zs)
    ?_ ?_ fun zs vs1 hzs => ?_
  · have h := lawS_eachM f (initSlotU sFS Q H wp w c0)
      (optO fun x => initO sFS Q H wp xin w c0 (some x)) (fun _ xo => xo)
      (fun v z' => valOfU (fun y : Y × H.Coin => xin y.1) v .first z')
        (fun _ _ => True) (fun z' v => z'.2.x ≠ none → LPre v .first z'.2)
      (fun _ _ _ _ _ => ⟨trivial, rfl⟩) (fun z' v v' hp h => valOfU_of_prefix _ hp h)
        (fun xo v _ => (tri_initSlotU f sFS Q H wp w c0 xo v).mono fun _ _ h => h.1)
      (fun xo v _ => lawS_initSlotU f sFS Q H wp xin w c0 xo v) xs vs fun _ _ => trivial
    rwa [List.map_id'] at h
  · exact tri_eachM (f := f) _ (fun _ _ => True)
      (fun xo (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) v =>
        (z'.2.x ≠ none → LPre v .first z'.2) ∧ z'.2.x.map Prod.fst = xo)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ hp h => ⟨fun hx => (h.1 hx).mono hp, h.2⟩)
      (fun xo v _ => tri_initSlotU f sFS Q H wp w c0 xo v) xs vs fun _ _ => trivial
  · rw [← PMF.bind_pure_comp]
    refine LawS.bind
      (lawS_chainTU f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq hf
        Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hF
        (hN.imp (fun h => by rw [← hzs.length_eq]; exact h) id) trivial
        fun z hz => (forall₂_mem_right hzs z hz).choose_spec.2.1)
      (tri_chainTU_x f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq
        Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hF)
      fun out vs2 hx => ?_
    have hlen : out.1.length = xs.length := by
      have := congrArg List.length hx
      rw [List.length_map, List.length_map] at this
      rw [this, hzs.length_eq]
    have hnl : n < out.1.length := by
      rw [hlen]
      exact (List.getElem?_eq_some_iff.1 hn).1
    have hxn : (out.1[n]).x.map Prod.fst = some x := by
      have h1 : (out.1.map fun acc => acc.x)[n]? = some (out.1[n]).x := by simp [hnl]
      rw [hx, List.getElem?_map] at h1
      obtain ⟨z, hz, hzx⟩ := Option.map_eq_some_iff.1 h1
      obtain ⟨xo, hxo, -, hxz⟩ := forall₂_getElem?_right hzs n z hz
      rw [← hzx, hxz]
      exact Option.some.inj (hxo.symm.trans hn)
    obtain ⟨⟨x', cj⟩, hacc, hx'⟩ := Option.map_eq_some_iff.1 hxn
    refine lawS_const (Tri.bind (tri_true' _ vs2) fun πs vs3 _ => tri_pure_iff.2 ?_)
    simp [List.getD_eq_getElem?_getD, hnl, blkA, hacc]

end Prove

end Compile.Batch.RefU
