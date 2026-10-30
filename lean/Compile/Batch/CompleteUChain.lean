-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteUChain.lean: the verifier recomputes the Fiat-Shamir chain of a slot with a
request, whatever the leaves of the empty slots in the request tree are.

All chains of a batch of the prover with free empty slots (no query for an empty slot: `chainTU`,
Compile/Batch/ProverU.lean) against the chain of one slot (`recomputeChain`, Compile/Batch/Verifier.lean),
for fixed oracle functions. The request tree is a Merkle tree with one leaf for each slot: the hash
of the slot value (one hash for the slot's chain, made in the joining round, the first shared round
after a local one) or, for an empty slot, a fresh string (words of this library: lean/GLOSSARY.md).

  Part 1  The request tree `reqTU` against `reqCheck`: the leaf of an empty slot is an arbitrary
          digest; under the hypotheses of the statements, the path of the leaf of a slot value still
          checks (`ReqOKU`, `LeafAt`, `tri_reqTU`, `reqCheck_honestU`).
  Part 2  `slotLoU`, `slotJoinU`, `joinMU`: for a slot with a request the lemmas `tri_slotLo`,
          `tri_slotJoin` of Compile/Batch/CompleteChain.lean; nothing for an empty slot. The rounds
          of `chainTU`, unfolded.
  Part 3  The joining round in all slots (`tri_joinMU`; of an empty slot only that it is unchanged);
          the chain (`tri_chainTU`), under the hypotheses of the statement: for every slot with a
          request what Compile/Batch/CompleteChain.lean ensures (`SlotDone`); of an empty slot only
          that it stays empty.

Rounds with proof-of-work bits are treated as in Compile/Batch/CompleteChain.lean. Two hypotheses
are those of that file: the fixed family answers the ghost names `fbw` as `fb` (`RealFam`), and the
wire record satisfies `RoundsQueryLayout.OKG`. (A ghost name `fbw t k` is an oracle of the analysis, which no
algorithm of the scheme ever queries: `OracleName`, Compile/Batch/Oracles.lean.) As there, the searches go
through `tri_fbG`, and V's chain is run on the plain parts with the numbers of the final attempts
written in (`SlotDone`'s nJ, n0s). Among the further hypotheses, one is new here, `PhOK`: the token
of the phase (.shr tk0) is in the store. In Compile/Batch/CompleteChain.lean `SlotPre` of any slot
gives this; here all slots may be empty, and `tri_fbG` needs the same header of the query under
every longer store.

Limits: nothing on probabilities. Nothing on whether a proof-of-work check is passed. Nothing on the
proof strings (Compile/Batch/CompleteUAcc.lean).
-/
import Compile.Batch.CompleteChain
import Compile.Batch.ProverU

noncomputable section

namespace Compile.Batch.CmplU
open Iop Rom
open Compile.Batch.Cmpl

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. The request tree -/

/-- The request tree is correct, relative to a store: its tokens stand for the levels over the leaf
digests lv. -/
def ReqOKU (vs : List Bits) (rq : TTree) (depthReq : ℕ) (lv : List (Dig lam)) : Prop :=
  (∀ lvl ∈ rq.levels, ∀ u ∈ lvl, IsDig lam vs u) ∧
  rq.levels.map (List.map (dv lam vs)) = levelsF (rnodeFB f) depthReq lv

/-- the leaf digests lv fit the slot values cs (none: an empty slot): the leaf of a slot value is
its hash; nothing is said of the leaf of an empty slot -/
def LeafAt (vs : List Bits) (cs : List (Option Tok)) (lv : List (Dig lam)) : Prop :=
  lv.length = cs.length ∧
  ∀ (j : ℕ) (c : Tok), cs[j]? = some (some c) → lv[j]? = some (rleafFB f (dv lam vs c))

variable {f} in
theorem ReqOKU.mono {vs vs' : List Bits} (hp : vs <+: vs') {rq : TTree} {depthReq : ℕ}
    {lv : List (Dig lam)} (h : ReqOKU f vs rq depthReq lv) : ReqOKU f vs' rq depthReq lv :=
  ⟨fun lvl hl u hu => (h.1 lvl hl u hu).mono hp, by
    rw [← h.2]
    exact List.map_congr_left fun lvl hl => map_dv_of_prefix hp (h.1 lvl hl)⟩

variable {f} in
theorem ReqOKU.isDig_root {vs : List Bits} {rq : TTree} {depthReq : ℕ} {lv : List (Dig lam)}
    (h : ReqOKU f vs rq depthReq lv) (hl : lv.length = 2 ^ depthReq) : IsDig lam vs rq.root := by
  obtain ⟨lvl, hm, hr⟩ := rootOf_mem (dv lam vs) (rnodeFB f) depthReq rq.levels _ hl h.2
  exact h.1 lvl hm _ hr

variable {f} in
theorem LeafAt.mono {vs vs' : List Bits} (hp : vs <+: vs') {cs : List (Option Tok)}
    {lv : List (Dig lam)} (h : LeafAt f vs cs lv) (hd : ∀ c, some c ∈ cs → IsDig lam vs c) :
    LeafAt f vs' cs lv :=
  ⟨h.1, fun j c hj => by rw [dv_of_prefix hp (hd c (List.mem_of_getElem? hj)).1]; exact h.2 j c hj⟩

theorem tri_rleavesTU :
    ∀ (cs : List (Option Tok)) (vs : List Bits), (∀ c, some c ∈ cs → IsDig lam vs c) →
      Tri f (rleavesTU (lam := lam) (K := K) (L := L) cs) vs fun o vs' =>
        (∀ t ∈ o, IsDig lam vs' t) ∧ LeafAt f vs cs (o.map (dv lam vs'))
  | [], _, _ => tri_pure_iff.2 ⟨fun _ h => (by cases h), rfl, fun j c h => by simp at h⟩
  | some c :: t, vs, h => by
      refine Tri.bind (tri_rleafT f c vs (h c (by simp))).with_prefix fun d vs1 hd => ?_
      refine Tri.bind (tri_rleavesTU t vs1 fun u hu => (h u (by simp [hu])).mono hd.2).with_prefix
        fun r vs2 hr => tri_pure_iff.2 ⟨?_, ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hd.1.1.mono hr.2
        · exact hr.1.1 u hu
      · have := hr.1.2.1
        simp only [List.length_map, List.length_cons] at this ⊢
        omega
      · intro j c' hj
        cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
          subst hj
          simp only [List.map_cons, List.getElem?_cons_zero]
          rw [dv_of_prefix hr.2 hd.1.1.1, hd.1.2]
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          simp only [List.map_cons, List.getElem?_cons_succ]
          rw [hr.1.2.2 j c' hj,
            dv_of_prefix hd.2 (h c' (List.mem_cons_of_mem _ (List.mem_of_getElem? hj))).1]
  | none :: t, vs, h => by
      refine tri_fresh_iff.2 fun r0 => ?_
      have hd := isDig_concat vs (fun i : Fin lam => r0.val.testBit i)
      have hp : vs <+: vs ++ [List.ofFn fun i : Fin lam => r0.val.testBit i] :=
        List.prefix_append _ _
      refine Tri.bind (tri_rleavesTU t _ fun u hu => (h u (by simp [hu])).mono hp).with_prefix
        fun r vs2 hr => tri_pure_iff.2 ⟨?_, ?_, ?_⟩
      · intro u hu
        rcases List.mem_cons.1 hu with rfl | hu
        · exact hd.1.mono hr.2
        · exact hr.1.1 u hu
      · have := hr.1.2.1
        simp only [List.length_map, List.length_cons] at this ⊢
        omega
      · intro j c' hj
        cases j with
        | zero => simp at hj
        | succ j =>
          simp only [List.getElem?_cons_succ] at hj
          simp only [List.map_cons, List.getElem?_cons_succ]
          rw [hr.1.2.2 j c' hj,
            dv_of_prefix hp (h c' (List.mem_cons_of_mem _ (List.mem_of_getElem? hj))).1]

theorem tri_reqTU (depthReq : ℕ) (cs : List (Option Tok)) (vs : List Bits)
    (h : ∀ c, some c ∈ cs → IsDig lam vs c) :
    Tri f (reqTU (lam := lam) (K := K) (L := L) depthReq cs) vs fun rq vs' =>
      ∃ lv, ReqOKU f vs' rq depthReq lv ∧ LeafAt f vs cs lv := by
  refine Tri.bind (tri_rleavesTU f cs vs h) fun ls vs1 hls => ?_
  exact Tri.bind (tri_levelsT (tri_rnodeT f) depthReq ls vs1 hls.1) fun lv vs2 hlv =>
    tri_pure_iff.2 ⟨ls.map (dv lam vs1), ⟨hlv.1, hlv.2⟩, hls.2⟩

/-- Under the hypotheses below: the check of the leaf of a slot value in an honest request tree
accepts, whatever the other leaves are. -/
theorem reqCheck_honestU {vs : List Bits} {rq : TTree} {depthReq : ℕ} {lv : List (Dig lam)}
    (h : ReqOKU f vs rq depthReq lv) (hl : lv.length = 2 ^ depthReq) {j : ℕ} (hj : j < 2 ^ depthReq)
    {c : Dig lam} (hc : lv[j]? = some (rleafFB f c)) :
    EvalsTo f (reqCheck (L := L) (K := K) depthReq (dv lam vs rq.root) j
        ((pathOf rq.levels j).map (dv lam vs)) c) true := by
  rw [pathOf_map (dv lam vs) (rnodeFB f) depthReq rq.levels _ j hl hj h.2]
  have hr : dv lam vs rq.root = _ := rootOf_map (dv lam vs) (rnodeFB f) depthReq rq.levels _ hl h.2
  rw [hr]
  unfold reqCheck
  rw [if_pos ⟨length_pathOf_levelsF _ _ _ _, hj⟩]
  have h2 : climbF (rnodeFB f) (pathOf (levelsF (rnodeFB f) depthReq lv) j)
        j (f OracleName.rleaf (List.ofFn c)) =
      rootOf (levelsF (rnodeFB f) depthReq lv) := by
    have h3 : f OracleName.rleaf (List.ofFn c) = lv.getD j default := by
      rw [List.getD_eq_getElem?_getD, hc]
      rfl
    rw [h3]
    exact climbF_pathOf (rnodeFB f) depthReq _ j hl hj
  refine (evaluates_eager f).bind (evalsTo_ask f OracleName.rleaf (List.ofFn c)) ((evaluates_eager f).bind
            ((evaluates_eager f).climbM (qN := rnodeV (L := L) (K := K)) (hN := rnodeFB f)
              (fun a b => evalsTo_ask f OracleName.rnode (List.ofFn a, List.ofFn b)) _ j _) ?_)
  rw [h2, decide_eq_true rfl]
  exact (evaluates_eager f).pure true

/-! ## Part 2. The rounds -/

/-- the slot value of a slot with a request; none for an empty slot -/
def csOf {Y : Type} (acc : SlotAcc lam K Y) : Option Tok := acc.x.map fun _ => acc.c

section Unfold
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)
  {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m0 : a.M0)
  (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0)

theorem chainTU_lo (hk : a.kind = .lo) (ph : PhT) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      (eachM
        (slotLoU sMT t cms xin a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        zs).bind fun zs' =>
          chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl

theorem chainTU_join (hk : a.kind = .sh) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0 =
      (joinMU sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqTU depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

theorem chainTU_shr (hk : a.kind = .sh) (tk0 : Tok) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) zs a0
      = tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

variable (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))

theorem slotLoU_some (ph : PhT) {z : SlotSt lam K Y (r :: s)} (h : z.2.x ≠ none) :
    slotLoU sMT t cms xin a w emb plJ i ph z = slotLo sMT t cms xin a w emb plJ i ph z := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 h
  simp only [slotLoU, hy]

theorem slotLoU_none (ph : PhT) {z : SlotSt lam K Y (r :: s)} (h : z.2.x = none) :
    slotLoU sMT t cms xin a w emb plJ i ph z = Step.pure (z.1.2 (w.chal (blk0 lam K)), z.2) := by
  simp only [slotLoU, h]

theorem slotJoinU_some {z : SlotSt lam K Y (r :: s)} (h : z.2.x ≠ none) :
    slotJoinU sMT t a w emb plJ i z = slotJoin sMT t a w emb plJ i z := by
  obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 h
  simp only [slotJoinU, hy]

theorem slotJoinU_none {z : SlotSt lam K Y (r :: s)} (h : z.2.x = none) :
    slotJoinU sMT t a w emb plJ i z = Step.pure z := by
  simp only [slotJoinU, h]

end Unfold

/-! ## Part 3. The chain -/

section Chain
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

/-- the request tree, by the phase: there is none before the chains have joined; afterwards its
leaves fit the slot values cs of the slots -/
def ReqInvU (vs : List Bits) (ph : PhT) (req : Option TTree) (cs : List (Option Tok)) : Prop :=
  (¬ chainsHaveJoined ph → req = none) ∧
  (chainsHaveJoined ph →
    ∃ rq lv,
      req = some rq ∧ ReqOKU f vs rq depthReq lv ∧ LeafAt f vs cs lv ∧ cs.length = 2 ^ depthReq)

variable {f depthReq} in
theorem ReqInvU.step {vs vs' : List Bits} (hp : vs <+: vs') {ph ph' : PhT} {req : Option TTree}
    {cs cs' : List (Option Tok)} (h : ReqInvU f depthReq vs ph req cs) (hj : chainsHaveJoined ph' ↔ chainsHaveJoined ph)
    (hcs : cs' = cs) (hd : chainsHaveJoined ph → ∀ c, some c ∈ cs → IsDig lam vs c) :
    ReqInvU f depthReq vs' ph' req cs' := by
  subst hcs
  refine ⟨fun hn => h.1 fun hh => hn (hj.2 hh), fun hh => ?_⟩
  obtain ⟨rq, lv, h1, h2, h3, h4⟩ := h.2 (hj.1 hh)
  exact ⟨rq, lv, h1, h2.mono hp, h3.mono hp (hd (hj.1 hh)), h4⟩

/-- What the chain ensures for one slot: it stays empty, or it keeps its request and has what
Compile/Batch/CompleteChain.lean ensures. -/
def SlotDoneU (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph phE : PhT) (vs0 : List Bits) (σ0 : SStrat s A) (t0s : List (Option TTree)) (n0s : List ℕ)
    (req' : Option TTree) (vs' : List Bits) (z : SlotSt lam K Y s) (acc' : SlotAcc lam K Y) :
    Prop :=
  acc'.x = z.2.x ∧
  (z.2.x ≠ none → SlotDone f sMT t cms xin s A W embS embP i ph phE vs0 σ0 t0s n0s req' vs' z acc')

/-- the token of the phase is in the store -/
def PhOK (vs : List Bits) : PhT → Prop
  | .shr tk0 => tk0 < vs.length
  | _ => True

theorem phOK_afterLo (vs : List Bits) (ph : PhT) : PhOK vs ph.afterLo := by cases ph <;> trivial

theorem mem_csOf {s : Shape} {zs : List (SlotSt lam K Y s)} {c : Tok}
    (h : some c ∈ zs.map fun z => csOf z.2) :
    ∃ z ∈ zs, z.2.x ≠ none ∧ z.2.c = c := by
  obtain ⟨z, hz, hc⟩ := List.mem_map.1 h
  obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hc
  exact ⟨z, hz, by rw [hy]; simp, rfl⟩

section Join
variable {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- what the joining round ensures for one slot -/
def JoinPostU (vs : List Bits) (z z' : SlotSt lam K Y (r :: s)) (vs' : List Bits) : Prop :=
  (z.2.x = none ∧ z' = z) ∨ (z.2.x ≠ none ∧ JoinPost f sMT t a A w embS embP i vs z z' vs')

variable {f sMT t a A w embS embP i} in
theorem JoinPostU.mono {vs : List Bits} {z z' : SlotSt lam K Y (r :: s)} {vs1 vs2 : List Bits}
    (hp : vs1 <+: vs2) (h : JoinPostU f sMT t a A w embS embP i vs z z' vs1) :
    JoinPostU f sMT t a A w embS embP i vs z z' vs2 :=
  h.imp id fun h => ⟨h.1, h.2.mono hp⟩

variable {f sMT t a A w embS embP i} in
theorem JoinPostU.x_eq {vs : List Bits} {z z' : SlotSt lam K Y (r :: s)} {vs1 : List Bits}
    (h : JoinPostU f sMT t a A w embS embP i vs z z' vs1) : z'.2.x = z.2.x := by
  rcases h with ⟨-, rfl⟩ | ⟨-, tr, c, q, -, -, -, -, rfl⟩ <;> rfl

/-- the joining round in all slots; vs0 is the store at the start of the round -/
theorem tri_joinMU (vs0 : List Bits) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits), vs0 <+: vs →
      (∀ z ∈ zs, z.2.x ≠ none → z.2.tk < vs0.length) →
      Tri f (joinMU sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs) vs
        fun o vs' =>
      List.Forall₂ (fun z z' => JoinPostU f sMT t a A w embS embP i vs0 z z' vs') zs o.1 ∧
      o.2 = o.1.map fun z => csOf z.2
  | [], _, _, _ => tri_pure_iff.2 ⟨.nil, rfl⟩
  | ⟨⟨m, k⟩, acc⟩ :: zs, vs, hp, h => by
      have h0 : Tri f (slotJoinU sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ⟨⟨m, k⟩, acc⟩) vs fun z' vs' =>
          JoinPostU f sMT t a A w embS embP i vs0 ⟨⟨m, k⟩, acc⟩ z' vs' := by
        by_cases hx : acc.x = none
        · rw [slotJoinU_none sMT t a w i _ _ (z := ⟨⟨m, k⟩, acc⟩) hx]
          exact tri_pure_iff.2 (Or.inl ⟨hx, rfl⟩)
        · have hz : acc.tk < vs0.length := h ⟨⟨m, k⟩, acc⟩ (by simp) hx
          rw [slotJoinU_some sMT t a w i _ _ (z := ⟨⟨m, k⟩, acc⟩) hx]
          refine (tri_slotJoin f sMT t a w _ _ i m k acc vs
            (lt_of_lt_of_le hz hp.length_le)).mono ?_
          rintro z' vs1 ⟨tr, c, q, hq, htr, hc, hcv, rfl⟩
          exact Or.inr ⟨hx, tr, c, q, by rw [← getD_of_prefix hp hz]; exact hq, htr, hc, hcv, rfl⟩
      refine Tri.bind h0.with_prefix fun z' vs1 hz' => ?_
      refine Tri.bind
        (tri_joinMU vs0 zs vs1 (hp.trans hz'.2) fun u hu => h u (by simp [hu])).with_prefix
        fun o vs2 ho => tri_pure_iff.2 ⟨.cons ?_ ho.1.1, ?_⟩
      · exact hz'.1.mono ho.2
      · show (z'.2.x.map fun _ => z'.2.c) :: o.2 = _
        rw [ho.1.2]
        rfl

end Join

/-- The chain, under `RealFam` and the hypotheses below. Whatever the coins: after all rounds, for
every slot with a request whose strategy is the shared strategy with one of its own, the verifier's
chain recomputes the slot's verifier messages, and the slot's trees and the shared ones are kept
correctly (`RoundsOK`); the request tree, if there is one, has at the leaf of every slot with a
request the hash of its slot value. -/
theorem tri_chainTU (hf : RealFam f) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
    (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (vs : List Bits),
    RoundsQueryLayout.OKG s A W → A.Coherent → RoundSplits.FmtFrom s A (fph ph) →
    (zs.length = 2 ^ depthReq ∨ AllLo s A) → (∀ z ∈ zs, z.2.x ≠ none → SlotPre vs ph z.2) →
    PhOK vs ph → ReqInvU f depthReq vs ph a0.req (zs.map fun z => csOf z.2) →
    Tri f (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) vs fun out vs' =>
      ∃ (phE : PhT) (t0s : List (Option TTree)) (n0s : List ℕ),
        out.2.trees = a0.trees ++ t0s ∧
        out.2.nons = n0s.reverse ++ a0.nons ∧
        ReqInvU f depthReq vs' phE out.2.req (out.1.map csOf) ∧
        (chainsHaveJoined ph → out.2.req = a0.req) ∧
        List.Forall₂
          (SlotDoneU f sMT t cms xin s A W embS embP i ph phE vs σ0 t0s n0s out.2.req vs') zs out.1
  | [], _, _, _, _, _, ph, _, zs, a0, vs, _, _, _, _, hpre, _, hreq => by
      refine tri_pure_iff.2
        ⟨ph, [], [], by simp, by simp,
          by simpa [List.map_map, Function.comp_def] using hreq, fun _ => rfl, ?_⟩
      refine (List.forall₂_map_right_iff).2 ((List.forall₂_same).2 fun z hz => ?_)
      exact ⟨rfl,
        fun hx =>
          ⟨rfl, ⟨[], by simp⟩, hpre z hz hx, fun _ => rfl, [], [], [], by simp, by simp, by simp,
            fun _ _ _ _ _ _ => ⟨(), ⟨rfl, rfl⟩, rfl⟩⟩⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, vs, hW, hC, hF, hN, hpre, hph, hreq => by
      have hF2 : (match a.kind, fph ph with
          | .lo, ph => a.NoShared ∧ RoundSplits.FmtFrom s A ph.afterLo
          | .sh, .loc => RoundSplits.FmtFrom s A .shr
          | .sh, .shr => a.NoSlot ∧ RoundSplits.FmtFrom s A .shr
          | .sh, .first => False
          | .sh, .aft => False) := hF
      by_cases hk : a.kind = .lo
      · -- a local round
        rw [hk] at hF2
        rw [chainTU_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        refine Tri.bind
          ((tri_eachM (f := f) _
            (fun (z : SlotSt lam K Y (r :: s)) v => vs <+: v ∧ (z.2.x ≠ none → SlotPre vs ph z.2))
            (fun (z : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) v =>
              (z.2.x = none ∧ z'.2 = z.2) ∨
              (z.2.x ≠ none ∧ SlotPre vs ph z.2 ∧
                LoPost f sMT t cms xin a A w embS embP i ph vs z z' v))
            (fun z v v' hp h => ⟨h.1.trans hp, h.2⟩)
            (fun z z' v v' hp h => h.imp id fun h => ⟨h.1, h.2.1, h.2.2.mono hp⟩) ?_ zs vs
            (fun z hz => ⟨List.prefix_refl _, hpre z hz⟩)).with_prefix)
          fun zs1 vs1 h1 => ?_
        · rintro ⟨⟨m, k⟩, acc⟩ v ⟨hpv, hz⟩
          by_cases hx : acc.x = none
          · rw [slotLoU_none sMT t cms xin a w i _ _ ph (z := ⟨⟨m, k⟩, acc⟩) hx]
            exact tri_pure_iff.2 (Or.inl ⟨hx, rfl⟩)
          · rw [slotLoU_some sMT t cms xin a w i _ _ ph (z := ⟨⟨m, k⟩, acc⟩) hx]
            refine (tri_slotLo f sMT t cms xin a w _ _ i hf ph m k acc v ((hz hx).mono hpv)).mono ?_
            rintro z' v' ⟨tr, tl, q, nc, dd, hnc, hq, htr, htl, hv, rfl⟩
            exact Or.inr
              ⟨hx, hz hx, tr, tl, q, nc, dd, hnc,
                by rw [← headLo_of_prefix cms hpv _ _ (hz hx)]; exact hq, htr, htl, hv, rfl⟩
        · obtain ⟨h1, hp⟩ := h1
          have hcs : (zs1.map fun z => csOf z.2) = zs.map fun z => csOf z.2 :=
            forall₂_map_eq (fun z => csOf z.2) (fun z => csOf z.2) (fun z z1 hz => by
              rcases hz with ⟨-, hz⟩ | ⟨-, -, tr, tl, q, nc, dd, -, -, -, -, -, rfl⟩
              · exact congrArg csOf hz
              · rfl) h1
          refine ((tri_chainTU hf s A W _ _ (i + 1) ph.afterLo _ zs1
            { a0 with trees := a0.trees ++ [none] } vs1 hW.2 hC.2
            (by rw [fph_afterLo]; exact hF2.2)
            (hN.imp (fun h => by rw [← h1.length_eq]; exact h) fun h => h.2)
            ?_ (phOK_afterLo vs1 ph)
            (hreq.step hp (joined_afterLo_iff ph) hcs fun hj c hc => by
              obtain ⟨z, hz, hx, rfl⟩ := mem_csOf hc
              exact isDig_c_of_pre (hpre z hz hx) hj)).with_prefix).mono ?_
          · intro z1 hz1 hx1
            obtain ⟨z, -, hz⟩ := forall₂_mem_right h1 z1 hz1
            rcases hz with ⟨hx, hz⟩ | ⟨-, hz, tr, tl, q, nc, dd, -, -, -, htl, -, rfl⟩
            · rw [hz] at hx1
              exact absurd hx hx1
            · exact slotPre_afterLo hp htl hz _ _ _ _ _
          · rintro out vs' ⟨⟨phE, t0s, n0s, e1, e0, e2, e3, e4⟩, hp'⟩
            refine ⟨phE, none :: t0s, n0s, by rw [e1]; simp, e0, e2,
              fun hj => e3 (joined_afterLo hj), forall₂_comp (fun z z1 acc' hz1 hz2 => ?_) h1 e4⟩
            rcases hz1 with ⟨hx, hz⟩ | ⟨hx, hz, hlo⟩
            · exact ⟨by rw [hz2.1, hz], fun hn => absurd hx hn⟩
            · have hx1 : z1.2.x = z.2.x := by
                obtain ⟨tr, tl, q, nc, dd, -, -, -, -, -, rfl⟩ := hlo
                rfl
              exact ⟨by rw [hz2.1, hx1],
                fun _ => slotDone_lo hk hF2.1 hW.1 hz hp hp' hlo (hz2.2 (by rw [hx1]; exact hx))⟩
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
          -- the joining round
          rw [chainTU_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine Tri.bind
            (tri_joinMU f sMT t a A w embS embP i vs zs vs (List.prefix_refl _) hpre).with_prefix
            fun o vs1 ho => ?_
          obtain ⟨⟨ho1, ho2⟩, hp1⟩ := ho
          have hdig : ∀ c, some c ∈ o.2 → IsDig lam vs1 c := by
            intro c hc
            rw [ho2] at hc
            obtain ⟨z1, hz1, hx1, rfl⟩ := mem_csOf hc
            obtain ⟨z, -, hz⟩ := forall₂_mem_right ho1 z1 hz1
            rcases hz with ⟨hx, rfl⟩ | ⟨-, tr, c, q, -, -, hcd, -, rfl⟩
            · exact absurd hx hx1
            · exact hcd
          refine Tri.bind (tri_reqTU f depthReq o.2 vs1 hdig).with_prefix fun rq vs2 hrq => ?_
          refine tri_withTree f sMT w.has0 w.depth0 _ _ vs2 _ fun tr0 vs2a hp2a htr0a => ?_
          obtain ⟨⟨lv, hrq, hlv⟩, hp2⟩ := hrq
          have hlen1 : o.2.length = 2 ^ depthReq := by
            rw [ho2, List.length_map, ← ho1.length_eq]; exact hlen
          have hrqd : IsDig lam vs2 rq.root := hrq.isDig_root (by rw [hlv.1]; exact hlen1)
          refine tri_fbG f t i hf w.gr0 w.chal _ _ tr0 _ _ _ _ _ vs2a _
            (Head.f4 cms (vs2a.getD rq.root [])) (rootV lam vs2a tr0)
            (fun v hv => ⟨by rw [getD_of_prefix hv (hrqd.mono hp2a).1], htr0a.rootV_of_prefix hv⟩)
            fun nc dd vs2' hpb hnc => ?_
          have hp2' : vs2 <+: vs2' := hp2a.trans hpb
          have htr0 := htr0a.mono hpb
          rw [← getD_of_prefix hpb (hrqd.mono hp2a).1, ← htr0a.rootV_of_prefix hpb]
          generalize hq4 : (⟨i, Head.f4 cms (vs2'.getD rq.root []), rootV lam vs2' tr0,
            embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩ : FbIn lam L t) = q4
          have hp3 : vs2' <+: vs2' ++ [List.ofFn (f (OracleName.fb t) q4).2] := List.prefix_append _ _
          have hcs : ((o.1.map (hear w (f (OracleName.fb t) q4).1 true)).map fun z => csOf z.2) = o.2 := by
            rw [ho2, List.map_map]
            exact List.map_congr_left fun z _ => rfl
          refine ((tri_chainTU hf s A W _ _ (i + 1) (.shr vs2'.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q4).1)))
            (o.1.map (hear w (f (OracleName.fb t) q4).1 true))
            ⟨a0.trees ++ [tr0], a0.toks ++ [vs2'.length], some rq,
              nc.toList ++ a0.nons, dd ++ a0.dead⟩
            (vs2' ++ [List.ofFn (f (OracleName.fb t) q4).2]) hW.2 hC.2 hF2
            (Or.inl (by rw [List.length_map, ← ho1.length_eq]; exact hlen))
            ?_ (show vs2'.length < _ by simp) ⟨fun hn => absurd trivial hn,
            fun _ =>
              ⟨rq, lv, rfl, hrq.mono (hp2'.trans hp3), ?_,
                by rw [hcs]; exact hlen1⟩⟩).with_prefix).mono ?_
          · intro z' hz' hx'
            obtain ⟨z1, hz1, rfl⟩ := List.mem_map.1 hz'
            obtain ⟨z, -, hz⟩ := forall₂_mem_right ho1 z1 hz1
            rcases hz with ⟨hx, rfl⟩ | ⟨-, tr, c, q, -, -, hcd, -, rfl⟩
            · exact absurd hx hx'
            · exact ⟨by simp, hcd.mono (hp2.trans (hp2'.trans hp3))⟩
          · rw [hcs]
            exact hlv.mono (hp2.trans (hp2'.trans hp3)) hdig
          · rintro out vs' ⟨⟨phE, t0s, n0s, e1, e0, e2, e3, e4⟩, hp'⟩
            refine ⟨phE, tr0 :: t0s, nc.toList ++ n0s, by rw [e1]; simp,
              by rw [e0]; cases nc <;> simp, e2, fun hj => hj.elim, ?_⟩
            refine forall₂_comp (fun z z1 acc' hz1 hz2 => ?_) ho1 ((List.forall₂_map_left_iff).1 e4)
            have hx1 : (hear w (f (OracleName.fb t) q4).1 true z1).2.x = z.2.x := hz1.x_eq
            refine ⟨by rw [hz2.1, hx1], fun hx => ?_⟩
            rcases hz1 with ⟨hx0, -⟩ | ⟨-, hz1⟩
            · exact absurd hx0 hx
            refine slotDone_join hk' hC.1 hW.1 hnc hp' (hz1.mono (hp2.trans (hp2'.trans hp3)))
              (hrqd.mono (hp2'.trans hp3)) (htr0.mono hp3) ?_ (getD_concat_length _ _)
              (e3 trivial) (hz2.2 (by rw [hx1]; exact hx))
            rw [getD_of_prefix hp3 (hrqd.mono hp2').1, htr0.rootV_of_prefix hp3, ← hq4]
        | shr tk0 =>
          -- a later shared round
          rw [chainTU_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine tri_withTree f sMT w.has0 w.depth0 _ _ vs _ fun tr0 vs2a hp2a htr0a => ?_
          have htk0 : tk0 < vs.length := hph
          refine tri_fbG f t i hf w.gr0 w.chal _ _ tr0 _ _ _ _ _ vs2a _
            (Head.f5 (vs2a.getD tk0 [])) (rootV lam vs2a tr0)
            (fun v hv =>
              ⟨by rw [getD_of_prefix hv (lt_of_lt_of_le htk0 hp2a.length_le)],
                htr0a.rootV_of_prefix hv⟩)
            fun nc dd vs2 hpb hnc => ?_
          have hp2 : vs <+: vs2 := hp2a.trans hpb
          have htr0 := htr0a.mono hpb
          rw [← getD_of_prefix hpb (lt_of_lt_of_le htk0 hp2a.length_le),
            ← htr0a.rootV_of_prefix hpb]
          generalize hq5 : (⟨i, Head.f5 (vs2.getD tk0 []), rootV lam vs2 tr0,
            embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩ : FbIn lam L t) = q5
          have hp3 : vs2 <+: vs2 ++ [List.ofFn (f (OracleName.fb t) q5).2] := List.prefix_append _ _
          have hcs : ((zs.map (hear w (f (OracleName.fb t) q5).1 false)).map fun z => csOf z.2) =
              zs.map fun z => csOf z.2 := by
            rw [List.map_map]
            exact List.map_congr_left fun z _ => rfl
          refine ((tri_chainTU hf s A W _ _ (i + 1) (.shr vs2.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q5).1)))
            (zs.map (hear w (f (OracleName.fb t) q5).1 false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [vs2.length],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
            (vs2 ++ [List.ofFn (f (OracleName.fb t) q5).2]) hW.2 hC.2 hF2.2
            (Or.inl (by rw [List.length_map]; exact hlen)) ?_ (show vs2.length < _ by simp)
            (hreq.step (hp2.trans hp3) Iff.rfl hcs fun _ c hc => by
              obtain ⟨z, hz, hx, rfl⟩ := mem_csOf hc
              exact (hpre z hz hx).2)).with_prefix).mono ?_
          · intro z' hz' hx'
            obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hz'
            exact ⟨by simp, (hpre z hz hx').2.mono (hp2.trans hp3)⟩
          · rintro out vs' ⟨⟨phE, t0s, n0s, e1, e0, e2, e3, e4⟩, hp'⟩
            refine ⟨phE, tr0 :: t0s, nc.toList ++ n0s, by rw [e1]; simp,
              by rw [e0]; cases nc <;> simp, e2, fun _ => e3 trivial, ?_⟩
            have h0 : List.Forall₂
                (fun (z z1 : SlotSt lam K Y (r :: s)) =>
                  (z.2.x ≠ none → SlotPre vs (.shr tk0) z.2) ∧ z1 = z)
                zs zs :=
              (List.forall₂_same).2 fun z hz => ⟨hpre z hz, rfl⟩
            refine forall₂_comp (fun z z1 acc' hz1 hz2 => ?_) h0 ((List.forall₂_map_left_iff).1 e4)
            obtain ⟨hz, rfl⟩ := hz1
            refine ⟨hz2.1, fun hx => ?_⟩
            refine slotDone_shr hk' hC.1 hW.1 hF2.1 hnc (hz hx) (hp2.trans hp3) hp' (htr0.mono hp3)
              ?_ (getD_concat_length _ _) (hz2.2 hx)
            rw [← getD_of_prefix hp2 (hz hx).1, htr0.rootV_of_prefix hp3, ← hq5]

end Chain

end Compile.Batch.CmplU
