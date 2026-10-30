-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteRefChain.lean: for fixed oracle functions with `RealFam`
(Compile/Batch/CompleteChain.lean), and under further hypotheses, all chains of a batch, and one
execution of the compiled prover, have the distributions of their counterparts without tokens
(Compile/Batch/CompleteRefDefs.lean) (words of this library: lean/GLOSSARY.md). Towards completeness
of the compiled scheme whose rounds may have proof-of-work bits.

  Part 1  the chain: `chainT` against `chainO`
  Part 2  one execution: `proveB` against `proveO`; where the proof string of a slot is `none`

Notation: `LawS f c vs φ μ` (Compile/Batch/CompleteRef.lean): a proposition: μ is the distribution
of φ of the output and the final store of the erased program c, started with the store vs, over its
coins, for fixed oracle functions; `Tri f c vs Q` (Compile/EraseKit.lean): a proposition: under the
oracle functions f, whatever the coins, the erased program c, started with the store vs, returns a
value a and a store vs' with Q a vs'; `vs`: a `List Bits`: the store: the list of strings for which
the tokens stand (the head of Compile/Batch/CompleteRef.lean); `a0`: an `Acc0`
(Compile/Batch/Prover.lean): what the shared part has accumulated; `fl`: `ℕ → Bool`: for which slots
a proof string is made (`proveB`, Compile/Batch/Prover.lean); `cms`: a `List (Dig lam)`: the
external roots (`verifyB`, Compile/Batch/Verifier.lean); `xin`: `Y → Option X`: `xin x` is the x of
`recomputeChain` (Compile/Batch/Verifier.lean): the whole instance (none: Test, Link); `embS`, `embP` say
how symbols and plain parts are written into queries (`verifyB`, Compile/Batch/Verifier.lean).
-/
import Compile.Batch.CompleteRef
import Compile.Batch.ProverG
import Compile.Batch.StarX

noncomputable section

namespace Compile.Batch.Ref
open Iop Rom Prob Compile.Batch.Cmpl

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-! ## Part 1. The chain -/

section Chain
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

/-- the token of the phase points into the store -/
def PhPre (vs : List Bits) : PhT → Prop
  | .shr tk0 => tk0 < vs.length
  | _ => True

theorem valPh_afterLo (vs vs' : List Bits) (ph : PhT) :
    valPh vs' ph.afterLo = (valPh vs ph).afterLo := by cases ph <;> rfl

theorem phPre_afterLo (vs : List Bits) (ph : PhT) : PhPre vs ph.afterLo := by cases ph <;> trivial

theorem valOf_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (vs : List Bits) (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    valOf xin vs ph (hear w bl noted z) = hearO w bl (valOf xin vs ph z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  cases ph <;> rfl

theorem runEager_askV_bind {β : Type} (o : OracleName)
    (q : domOf lam L o) (g : rngOf lam K o → TypedOracleComputation lam K L β) :
    ((askTypedOracle (K := K) (L := L) o q).bind g).runEager f = (g (f o q)).runEager f := rfl

/-- Under the hypotheses below, all chains of a batch have the distribution of chainO. (The
hypotheses: `RealFam`: the ghost names `fbw t j` are answered as `fb t`; `RoundSplits.FmtFrom`
(Iop/BatchFmt.lean): from the phase ph on, every round has a format, and a component that is not
sent is empty; there are 2 ^ depthReq slots, or `AllLo`: there is no shared round; `PhPre`: the
token of the phase points into the store; `LPre`, for every slot: the tokens of the slot and of the
phase point into the store, and, once the chains have joined, the string of its slot value is a
digest (`IsDig`, Compile/Batch/CompleteTree.lean).) -/
theorem lawS_chainT (hf : RealFam f) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (vs : List Bits),
      RoundSplits.FmtFrom s A (fph ph) → (zs.length = 2 ^ depthReq ∨ AllLo s A) →
      PhPre vs ph → (∀ z ∈ zs, LPre vs ph z.2) →
      LawS f (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) vs
        (fun out _ => out.1.map fun acc => acc.blocks)
        ((chainO sMT t cms depthReq s A W embS embP i (valPh vs ph)
          σ0 (zs.map (valOf xin vs ph))).runEager f)
  | [], _, _, _, _, _, ph, _, zs, a0, vs, _, _, _, _ => by
      refine (lawS_pure _ _ _).congr ?_
      show PMF.pure _ = PMF.pure _
      congr 1
      rw [List.map_map, List.map_map]
      rfl
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, vs, hF, hN, hph, hpre => by
      have hF2 : (match a.kind, fph ph with
          | .lo, ph => a.NoShared ∧ RoundSplits.FmtFrom s A ph.afterLo
          | .sh, .loc => RoundSplits.FmtFrom s A .shr
          | .sh, .shr => a.NoSlot ∧ RoundSplits.FmtFrom s A .shr
          | .sh, .first => False
          | .sh, .aft => False) := hF
      by_cases hk : a.kind = .lo
      · rw [hk] at hF2
        rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph,
          chainO_lo sMT t cms depthReq a A w W embS embP i m0 k0 _ hk, OComp.runEager_bind]
        have hstep : ∀ (z : SlotSt lam K Y (r :: s)) (v : List Bits), (vs <+: v ∧ LPre vs ph z.2) →
            Tri f (slotLo sMT t cms xin a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i ph z)
              v fun z' v' => LPre v' ph.afterLo z'.2 := by
          rintro ⟨⟨m, k⟩, acc⟩ v ⟨hpv, hz⟩
          refine ((tri_slotLo f sMT t cms xin a w _ _ i hf ph m k acc
            v (hz.2.mono hpv)).with_prefix).mono ?_
          rintro z' v' ⟨⟨tr, tl, q, nc, dd, -, -, -, htl, -, rfl⟩, hp'⟩
          exact ⟨htl, slotPre_afterLo (hpv.trans hp') htl hz.2 _ _ _ _ _⟩
        refine LawS.bind
          (φ := fun (zs' : List (SlotSt lam K Y s)) v' => zs'.map (valOf xin v' ph.afterLo))
          (Q := fun zs' v' => zs'.length = zs.length ∧ ∀ z' ∈ zs', LPre v' ph.afterLo z'.2)
          ?_ ?_ fun zs1 vs1 h1 => ?_
        · have h := lawS_eachM f
            (slotLo sMT t cms xin a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
            (slotLoO sMT t cms a w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i (valPh vs ph))
            (fun v z => valOf xin v ph z)
              (fun v z' => valOf xin v ph.afterLo z') (fun z v => vs <+: v ∧ LPre vs ph z.2)
            (fun z' v => LPre v ph.afterLo z'.2)
            (fun z v v' hp h => ⟨⟨h.1.trans hp, h.2⟩, valOf_of_prefix xin hp (h.2.mono h.1)⟩)
            (fun z' v v' hp h => valOf_of_prefix xin hp h) hstep (fun z v h => by
              have h2 := lawS_slotLo f sMT t cms xin a w (fun p => embS (.inl p))
                (fun α => embP (.inl (.inr α))) i hf ph z v (h.2.mono h.1)
              rwa [valPh_of_prefix h.1 h.2.2] at h2) zs vs fun z hz => ⟨List.prefix_refl _, hpre z hz⟩
          exact h
        · refine (tri_eachM (f := f) _
              (fun (z : SlotSt lam K Y (r :: s)) v => vs <+: v ∧ LPre vs ph z.2)
              (fun (_ : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) v =>
                LPre v ph.afterLo z'.2)
              (fun z v v' hp h => ⟨h.1.trans hp, h.2⟩) (fun z z' v v' hp h => h.mono hp) hstep zs vs
              fun z hz => ⟨List.prefix_refl _, hpre z hz⟩).mono
            fun zs' v' h => ?_
          exact ⟨h.length_eq.symm, fun z' hz' => (forall₂_mem_right h z' hz').choose_spec.2⟩
        · have ih := lawS_chainT hf s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
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
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk', valPh,
            chainO_join sMT t cms depthReq a A w W embS embP i m0 k0 _ hk', OComp.runEager_bind]
          refine LawS.bind
            (Q := fun o v' =>
                o.1.length = zs.length ∧
                (o.2 = o.1.map fun z => z.2.c) ∧
                ∀ z1 ∈ o.1, z1.2.tk < v'.length ∧ IsDig lam v' z1.2.c)
            (lawS_joinM f sMT t xin a A w embS embP i 0 zs vs fun z hz => (hpre z hz).1) ?_
            fun o vs1 ho => ?_
          · refine ((tri_joinM f sMT t a A w embS embP i vs zs vs (List.prefix_refl _)
              fun z hz => (hpre z hz).1).with_prefix).mono ?_
            rintro o v' ⟨⟨h1, h2⟩, hp⟩
            refine ⟨h1.length_eq.symm, h2, fun z1 hz1 => ?_⟩
            obtain ⟨z, hz, tr, c, q, -, -, hc, -, rfl⟩ := forall₂_mem_right h1 z1 hz1
            exact ⟨lt_of_lt_of_le (hpre z hz).1 hp.length_le, hc⟩
          obtain ⟨ho1, ho2, ho3⟩ := ho
          have hdig : ∀ c ∈ o.2, IsDig lam vs1 c := by
            intro c hc
            rw [ho2] at hc
            obtain ⟨z1, hz1, rfl⟩ := List.mem_map.1 hc
            exact (ho3 z1 hz1).2
          have hlen1 : o.2.length = 2 ^ depthReq := by rw [ho2, List.length_map, ho1]; exact hlen
          have hcs : ((o.1.map (valOf xin vs1 (.shr 0))).map fun v => v.c) =
              o.2.map fun c => vs1.getD c [] := by
            rw [ho2, List.map_map, List.map_map]
            rfl
          rw [OComp.runEager_bind, hcs]
          refine LawS.bind (lawS_reqT f depthReq o.2 vs1 hdig hlen1)
            (tri_reqT f depthReq o.2 vs1 hdig).with_prefix fun rq vs2 hrq => ?_
          obtain ⟨hrq, hp2⟩ := hrq
          have hrqd : IsDig lam vs2 rq.root := hrq.isDig_root (by simpa using hlen1)
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
          have ih := lawS_chainT hf s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
            (i + 1) (.shr vs3.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q4).1)))
            (o.1.map (hear w (f (OracleName.fb t) q4).1 true))
            ⟨a0.trees ++ [tr0], a0.toks ++ [vs3.length], some rq,
              nc.toList ++ a0.nons, dd ++ a0.dead⟩
            (vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2]) hF2
            (Or.inl (by rw [List.length_map, ho1]; exact hlen)) (by simp [PhPre]) (fun z' hz' => by
              obtain ⟨z1, hz1, rfl⟩ := List.mem_map.1 hz'
              have h3 := ho3 z1 hz1
              exact ⟨lt_of_lt_of_le h3.1 (hp2.trans (hp2'.trans (hp23.trans hp3))).length_le,
                by simp,
                h3.2.mono (hp2.trans (hp2'.trans (hp23.trans hp3)))⟩)
          have e1 : valPh (vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2]) (.shr vs3.length) =
              .shr (List.ofFn (f (OracleName.fb t) q4).2) := by
            simp only [valPh, getD_concat_length]
          have e2 : (o.1.map (hear w (f (OracleName.fb t) q4).1 true)).map
                (valOf xin (vs3 ++ [List.ofFn (f (OracleName.fb t) q4).2]) (.shr vs3.length)) =
              (o.1.map (valOf xin vs1 (.shr 0))).map (hearO w (f (OracleName.fb t) q4).1) := by
            rw [List.map_map, List.map_map]
            refine List.map_congr_left fun z1 hz1 => ?_
            rw [Function.comp_apply, Function.comp_apply, valOf_hear,
              valOf_shr_of_prefix xin (hp2.trans (hp2'.trans (hp23.trans hp3))) 0 _
                (ho3 z1 hz1).1 (ho3 z1 hz1).2.1]
          rw [e1, e2] at ih
          exact ih
        | shr tk0 =>
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0, valPh,
            chainO_shr sMT t cms depthReq a A w W embS embP i m0 k0 _ hk', OComp.runEager_bind]
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
          have ih := lawS_chainT hf s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
            (i + 1) (.shr vs3.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q5).1)))
            (zs.map (hear w (f (OracleName.fb t) q5).1 false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [vs3.length],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
            (vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2]) hF2.2
            (Or.inl (by rw [List.length_map]; exact hlen)) (by simp [PhPre]) (fun z' hz' => by
              obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hz'
              have h3 := hpre z hz
              exact ⟨lt_of_lt_of_le h3.1 (hp2.trans (hp23.trans hp3)).length_le,
                by simp,
                h3.2.2.mono (hp2.trans (hp23.trans hp3))⟩)
          have e1 : valPh (vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2]) (.shr vs3.length) =
              .shr (List.ofFn (f (OracleName.fb t) q5).2) := by
            simp only [valPh, getD_concat_length]
          have e2 : (zs.map (hear w (f (OracleName.fb t) q5).1 false)).map
                (valOf xin (vs3 ++ [List.ofFn (f (OracleName.fb t) q5).2]) (.shr vs3.length)) =
              (zs.map (valOf xin vs (.shr tk0))).map (hearO w (f (OracleName.fb t) q5).1) := by
            rw [List.map_map, List.map_map]
            refine List.map_congr_left fun z hz => ?_
            rw [Function.comp_apply, Function.comp_apply, valOf_hear,
              valOf_shr_of_prefix xin (hp2.trans (hp23.trans hp3)) tk0 _
                (hpre z hz).1 (hpre z hz).2.2.1]
          rw [e1, e2] at ih
          exact ih

end Chain

/-! ## Part 2. One execution -/

section KeepX
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

/-- whatever holds after k, for every tree or none and every store, holds after the tree and k -/
theorem tri_withTree_any {β : Type} (has : Bool) (d : ℕ) (leaf : ℕ → Body L)
    (k : Option TTree → St lam K L β) (vs : List Bits)
    (Q : β → List Bits → Prop) (h : ∀ tr vs1, Tri f (k tr) vs1 Q) :
    Tri f (withTree sMT has d leaf k) vs Q := by
  cases has with
  | true => exact Tri.bind (tri_true' _ vs) fun tr vs1 _ => h (some tr) vs1
  | false => exact h none vs

/-- whatever holds after k, for every list of trees and every store, holds after the trees and k -/
theorem tri_withTrees_any {β : Type} :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) (k : List TTree → St lam K L β) (vs : List Bits)
      (Q : β → List Bits → Prop),
      (∀ trs vs1, Tri f (k trs) vs1 Q) → Tri f (withTrees sMT ds leaf k) vs Q
  | [], _, _, vs, _, h => h [] vs
  | _ :: ds, leaf, k, vs, Q, h =>
    Tri.bind (tri_true' _ vs) fun tr vs1 _ =>
      tri_withTrees_any ds (fun n => leaf (n + 1)) (fun trs => k (tr :: trs)) vs1 Q
        fun trs vs2 => h (tr :: trs) vs2

/-- whatever holds after k, for all that the search may pass on and every store, holds after the
search and k -/
theorem tri_fbG_any {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (i : ℕ) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) (Q : β → List Bits → Prop)
    (h : ∀ nc dd bl tl vs1, Tri f (k nc dd bl tl) vs1 Q) (vs : List Bits) :
    Tri f (fbG gr chal t i tk us root hd hinj emb α k) vs Q :=
  fbG_ind (Φ := fun c => ∀ vs, Tri f c vs Q) gr (fun _ _ hk _ => tri_marked_iff.2 (hk _ _ _))
    (fun _ _ _ hk _ => tri_marked_iff.2 (hk _ _ _)) h vs

theorem tri_slotLo_x {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (z : SlotSt lam K Y (r :: s)) (vs : List Bits) :
    Tri f (slotLo sMT t cms xin a w emb plJ i ph z) vs fun z' _ => z'.2.x = z.2.x := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  unfold slotLo
  refine tri_withTree_any f sMT _ _ _ _ vs _ fun tr vs1 => ?_
  cases ph <;> simp only [fbSlotG]
    <;> exact tri_fbG_any f t _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ _ _ _ => tri_pure_iff.2 rfl) _

theorem tri_joinM_x {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits),
      Tri f (joinM sMT t a w emb plJ i zs) vs fun o _ =>
        (o.1.map fun z => z.2.x) = zs.map fun z => z.2.x
  | [], _ => tri_pure_iff.2 rfl
  | ⟨⟨m, k⟩, acc⟩ :: zs, vs => by
      have h0 : Tri f (slotJoin sMT t a w emb plJ i ((m, k), acc)) vs fun z' _ =>
          z'.2.x = acc.x := by
        unfold slotJoin
        exact tri_withTree_any f sMT _ _ _ _ vs _ fun tr vs1 =>
          tri_marked_iff.2 (tri_pure_iff.2 rfl)
      refine Tri.bind h0 fun z' vs1 hz' =>
        Tri.bind (tri_joinM_x a w emb plJ i zs vs1) fun o vs2 ho => tri_pure_iff.2 ?_
      show z'.2.x :: (o.1.map fun z => z.2.x) = acc.x :: _
      rw [hz', ho]

theorem map_x_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    (noted : Bool) (zs : List (SlotSt lam K Y (r :: s))) :
    ((zs.map (hear w bl noted)).map fun z => z.2.x) = zs.map fun z => z.2.x := by
  rw [List.map_map]
  exact List.map_congr_left fun z _ => rfl

/-- under `FmtFrom`, what the slots hold does not change along the chain -/
theorem tri_chainT_x :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (vs : List Bits),
      RoundSplits.FmtFrom s A (fph ph) →
      Tri f (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) vs
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
        rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        refine Tri.bind
          (tri_eachM (f := f) _ (fun _ _ => True)
            (fun (z : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) _ => z'.2.x = z.2.x)
            (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
            (fun z v _ => tri_slotLo_x f sMT t cms xin a w _ _ i ph z v) zs vs fun _ _ => trivial)
          fun zs1 vs1 h1 => ?_
        refine (tri_chainT_x s A W _ _ (i + 1) ph.afterLo _ zs1 _ vs1
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
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine Tri.bind (tri_joinM_x f sMT t a w _ _ i zs vs) fun o vs1 ho => ?_
          refine Tri.bind (tri_true' _ vs1) fun rq vs2 _ =>
            tri_withTree_any f sMT _ _ _ _ vs2 _ fun tr0 vs3 =>
              tri_fbG_any f t _ _ _ _ _ _ _ _ _ _ _ _ (fun nc dd bl tl vs4 => ?_) _
          refine (tri_chainT_x s A W _ _ (i + 1) (.shr _) _ _ _ _ hF2).mono fun out _ h => ?_
          rw [h, map_x_hear, ho]
        | shr tk0 =>
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine tri_withTree_any f sMT _ _ _ _ vs _ fun tr0 vs3 =>
            tri_fbG_any f t _ _ _ _ _ _ _ _ _ _ _ _ (fun nc dd bl tl vs4 => ?_) _
          refine (tri_chainT_x s A W _ _ (i + 1) (.shr _) _ _ _ _ hF2.2).mono fun out _ h => ?_
          rw [h, map_x_hear]

end KeepX

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

/-- the proof string of a slot is `none` exactly if its verifier randomness is in the withheld set
-/
theorem tri_finishSlot_none (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    Tri f (finishSlot Q H wq wp trees w c0 a0 j x cj acc) vs fun o _ =>
      o.isNone = @decide (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x)
            (wp.decW w x _) := by
  unfold finishSlot
  dsimp only
  by_cases hw : rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x
  · rw [if_pos hw]
    exact tri_pure_iff.2 (by simp [hw])
  · rw [if_neg hw]
    refine tri_reveal_iff.2
      (Tri.bind (tri_true' _ vs) fun g1 vs1 _ =>
        Tri.bind (tri_true' _ vs1) fun g2 vs2 _ => tri_pure_iff.2 ?_)
    simp [hw]

theorem tri_finishAll_none (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (accs : List (SlotAcc lam K (Y × H.Coin))) (j0 n : ℕ)
    (acc : SlotAcc lam K (Y × H.Coin)) (x : Y) (cj : H.Coin) (vs : List Bits),
    accs[n]? = some acc → acc.x = some (x, cj) → fl (j0 + n) = true →
    Tri f (finishAll Q H wq wp trees w fl c0 a0 j0 accs) vs fun πs _ =>
      (πs.getD n none).isNone =
        @decide (rhoOf Q.loc.shape Q.ann wq.sh acc.blocks ∈ H.one.withheld w x) (wp.decW w x _)
  | [], _, _, _, _, _, _, h, _, _ => by simp at h
  | acc0 :: accs, j0, 0, acc, x, cj, vs, h, hx, hfl => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      have h0 : Tri f (match acc0.x with
          | some (x, cj) =>
            if fl j0 then finishSlot Q H wq wp trees w c0 a0 j0 x cj acc0 else pure none
          | none => pure none) vs fun o _ =>
            o.isNone = @decide (rhoOf Q.loc.shape Q.ann wq.sh acc0.blocks ∈ H.one.withheld w x)
                  (wp.decW w x _) := by
        rw [hx]
        simp only [show fl j0 = true from hfl, if_true]
        exact tri_finishSlot_none f Q H wq wp trees w c0 a0 j0 x cj acc0 vs
      exact Tri.bind h0 fun π vs1 hπ => Tri.bind (tri_true' _ vs1) fun r vs2 _ => tri_pure_iff.2 hπ
  | acc0 :: accs, j0, n + 1, acc, x, cj, vs, h, hx, hfl => by
      simp only [List.getElem?_cons_succ] at h
      refine Tri.bind (tri_true' _ vs) fun π vs1 _ =>
        Tri.bind (tri_finishAll_none fl c0 a0 accs (j0 + 1) n acc x cj vs1 h hx
            (by rw [show j0 + 1 + n = j0 + (n + 1) by omega]; exact hfl))
          fun r vs2 hr => tri_pure_iff.2 hr

theorem tri_drawT_ref {β : Type} (e : Enum β) (vs : List Bits) :
    Tri f (drawT (lam := lam) (K := K) (L := L) e) vs fun _ vs' => vs' = vs :=
  tri_sample_iff.2 fun _ => tri_pure_iff.2 rfl

theorem lawS_drawT_bind {β γ δ : Type} (e : Enum β) (g : β → St lam K L γ) (vs : List Bits)
    (ψ : γ → List Bits → δ) (ν : Fin (e.n + 1) → PMF δ) (h : ∀ r, LawS f (g (e.e r)) vs ψ (ν r)) :
    LawS f ((drawT e).bind g) vs ψ ((unif (Fin (e.n + 1))).bind ν) :=
  lawS_sample (k := fun r => g (e.e r)) h

theorem lawS_initSlot (c0 : H.Coin0) (x : Option Y) (vs : List Bits) :
    LawS f (initSlot sFS Q H wp w c0 x) vs
      (fun z' vs' => valOf (fun y : Y × H.Coin => xin y.1) vs' .first z')
      ((initO sFS Q H wp xin w c0 x).runEager f) := by
  unfold initSlot initO
  rw [runEager_drawO_bind]
  refine lawS_drawT_bind f wp.coin _ vs _ _ fun rj => ?_
  rw [runEager_freshO_bind]
  refine lawS_fresh fun r => ((lawS_pure _ _ _).congr ?_)
  show PMF.pure _ = PMF.pure _
  congr 1
  unfold valOf
  simp only [cOf]
  rw [getD_concat_length]
  cases x <;> rfl

/-- One execution, from any store, under the hypotheses below: whether the proof string of a slot
that holds x, and for which one is made, is `none` has the distribution of `noneAt` of proveO's
output. Of the external trees only the roots matter. -/
theorem lawS_proveB (hf : RealFam f) (hF : Q.ann.Fmt) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (n : ℕ) (x : Y)
    (hn : xs[n]? = some (some x)) (hfl : fl n = true) (vs : List Bits) :
    LawS f (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      vs (fun πs _ => (πs.getD n none).isNone)
      (((proveO sMT sFS t Q H wq wp embS embP xin depthReq
          (trees.map TreeH.root) w xs).runEager f).map
        (noneAt Q H wq wp w x n)) := by
  unfold proveB proveO
  rw [runEager_drawO_bind, PMF.map_bind]
  refine lawS_drawT_bind f wp.coin0 _ vs _ _ fun r0 => ?_
  generalize wp.coin0.e r0 = c0
  rw [OComp.runEager_bind, PMF.map_bind]
  have hinit : ∀ (xo : Option Y) (v : List Bits), True → Tri f (initSlot sFS Q H wp w c0 xo) v fun z' v' =>
      LPre v' .first z'.2 ∧ z'.2.x.map Prod.fst = xo := by
    intro xo v _
    refine Tri.bind (tri_drawT_ref f wp.coin v) fun cj v0 hv0 =>
      tri_fresh_iff.2 fun r => tri_pure_iff.2 ?_
    refine ⟨⟨by simp, by show v0.length < _; simp⟩, ?_⟩
    cases xo <;> rfl
  refine LawS.bind
    (φ := fun (zs : List (SlotSt lam K (Y × H.Coin) Q.loc.shape)) v' =>
        zs.map (valOf (fun y : Y × H.Coin => xin y.1) v' .first))
    (Q := fun zs v' =>
        List.Forall₂
          (fun xo (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) =>
            LPre v' .first z'.2 ∧ z'.2.x.map Prod.fst = xo)
          xs zs)
    ?_ ?_ fun zs vs1 hzs => ?_
  · have h := lawS_eachM f (initSlot sFS Q H wp w c0) (initO sFS Q H wp xin w c0) (fun _ xo => xo)
      (fun v z' => valOf (fun y : Y × H.Coin => xin y.1) v .first z')
        (fun _ _ => True) (fun z' v => LPre v .first z'.2)
      (fun _ _ _ _ _ => ⟨trivial, rfl⟩) (fun z' v v' hp h => valOf_of_prefix _ hp h)
        (fun xo v h => (hinit xo v h).mono fun _ _ h => h.1)
      (fun xo v _ => lawS_initSlot f sFS Q H wp xin w c0 xo v) xs vs fun _ _ => trivial
    rwa [List.map_id'] at h
  · exact tri_eachM (f := f) _ (fun _ _ => True)
      (fun xo (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) v =>
        LPre v .first z'.2 ∧ z'.2.x.map Prod.fst = xo)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ hp h => ⟨h.1.mono hp, h.2⟩)
      hinit xs vs fun _ _ => trivial
  · rw [← PMF.bind_pure_comp]
    refine LawS.bind
      (lawS_chainT f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq hf
        Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hF
        (hN.imp (fun h => by rw [← hzs.length_eq]; exact h) id) trivial
        fun z hz => (forall₂_mem_right hzs z hz).choose_spec.2.1)
      (tri_chainT_x f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq
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
    simp [List.getD_eq_getElem?_getD, hnl]

/-- One execution that also outputs the hash blocks (Compile/Batch/StarX.lean), from any store,
under the hypotheses below: the hash blocks that the slots have seen have the distribution of
proveO. Of the external trees only the roots matter; which proof strings are made does not matter.
-/
theorem lawS_proveBX (hf : RealFam f) (hF : Q.ann.Fmt) (fl : ℕ → Bool) (xs : List (Option Y))
    (hN : xs.length = 2 ^ depthReq ∨ AllLo Q.loc.shape Q.ann) (vs : List Bits) :
    LawS f (proveBX sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs (fun o _ => o.2)
      ((proveO sMT sFS t Q H wq wp embS embP xin depthReq
        (trees.map TreeH.root) w xs).runEager f) := by
  unfold proveBX proveO
  rw [runEager_drawO_bind]
  refine lawS_drawT_bind f wp.coin0 _ vs _ _ fun r0 => ?_
  generalize wp.coin0.e r0 = c0
  rw [OComp.runEager_bind]
  have hinit : ∀ (xo : Option Y) (v : List Bits),
      True → Tri f (initSlot sFS Q H wp w c0 xo) v fun z' v' => LPre v' .first z'.2 := by
    intro xo v _
    refine Tri.bind (tri_drawT_ref f wp.coin v) fun cj v0 hv0 =>
      tri_fresh_iff.2 fun r => tri_pure_iff.2 ?_
    exact ⟨by simp, by show v0.length < _; simp⟩
  refine LawS.bind
    (φ := fun (zs : List (SlotSt lam K (Y × H.Coin) Q.loc.shape)) v' =>
        zs.map (valOf (fun y : Y × H.Coin => xin y.1) v' .first))
    (Q := fun zs v' =>
        List.Forall₂
          (fun (_ : Option Y) (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) => LPre v' .first z'.2)
          xs zs)
    ?_ ?_ fun zs vs1 hzs => ?_
  · have h := lawS_eachM f (initSlot sFS Q H wp w c0) (initO sFS Q H wp xin w c0) (fun _ xo => xo)
      (fun v z' => valOf (fun y : Y × H.Coin => xin y.1) v .first z')
        (fun _ _ => True) (fun z' v => LPre v .first z'.2)
      (fun _ _ _ _ _ => ⟨trivial, rfl⟩) (fun z' v v' hp h => valOf_of_prefix _ hp h) hinit
      (fun xo v _ => lawS_initSlot f sFS Q H wp xin w c0 xo v) xs vs fun _ _ => trivial
    rwa [List.map_id'] at h
  · exact tri_eachM (f := f) _ (fun _ _ => True)
      (fun (_ : Option Y) (z' : SlotSt lam K (Y × H.Coin) Q.loc.shape) v => LPre v .first z'.2)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ hp h => h.mono hp) hinit xs vs fun _ _ => trivial
  · rw [← PMF.bind_pure
        ((chainO sMT t (trees.map TreeH.root) depthReq Q.loc.shape Q.ann wq.sh embS embP 0 .first
          (H.strat0 w c0) _).runEager f)]
    refine LawS.bind
      (lawS_chainT f sMT t (trees.map TreeH.root) (fun y : Y × H.Coin => xin y.1) depthReq hf
        Q.loc.shape Q.ann wq.sh embS embP 0 .first (H.strat0 w c0) zs ⟨[], [], none, [], []⟩ vs1 hF
        (hN.imp (fun h => by rw [← hzs.length_eq]; exact h) id) trivial
        fun z hz => (forall₂_mem_right hzs z hz).choose_spec.2)
      (tri_true' _ vs1) fun out vs2 _ => ?_
    exact lawS_const (Tri.bind (tri_true' _ vs2) fun πs vs3 _ => tri_pure_iff.2 rfl)

end Prove

end Compile.Batch.Ref
