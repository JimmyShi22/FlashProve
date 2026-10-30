-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CountU.lean: the prover with free empty slots (`proveBU`, Compile/Batch/ProverU.lean:
for an empty slot it makes only a fresh leaf of the request tree over all slots) makes only the
marked queries (`Step.marked`, Rom/Defer.lean) of its requests, of the shared part and of the inner
nodes of the request tree (words of this library: lean/GLOSSARY.md).

  `mPU W m`  The bound for one batch with at most m requests: `Disc.mPB W`
             (Compile/Batch/SpecDiscipline.lean) with m in the place of the number maxBatchSize of slots,
             except for the inner nodes of the request tree, which has maxBatchSize leaves.
  `markPpU`  Every path of the program `PpU` (Compile/Batch/StarU.lean) on at most B requests makes
             at most mPU W B o marked queries to each oracle o (`Compile.MarkLe`,
             Compile/MarkLe.lean). (The statement also takes `L.maxBatchSize` = 2 ^ `W.depthReq`, which is not
             used.)

The proof goes through the programs of Compile/Batch/TokTree.lean, Compile/Batch/Prover.lean,
Compile/Batch/ProverU.lean and Compile/Batch/StarU.lean with `Compile.MarkQ`:

  Part 1  trees
  Part 2  programs without marked queries: openings, proof strings
  Part 3  the rounds. `mq_fbG`: a search makes one query to fb t and at most one to each ghost name
          fbw t k, k below the maximal number of further attempts (`Disc.MFb`). An empty slot makes
          no marked query.
  Part 4  the numbers (`MChU`: `Disc.MCh` of Compile/Batch/DisciplineCnt.lean with m requests and N
          leaves of the request tree), from the arithmetic of Compile/Batch/DisciplineChainNum.lean
  Part 5  the chains, one execution, the prover

Notation:
  `lam`: a natural number; a hash block has lam bits (`Dig`, Iop/Wire.lean);
  `L`: an `BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with the
    honest sides;
  `W`: in `mPU`, `markPpU` a `QueryLayout lam L` (Iop/BatchWire.lean): the wire record: parameters of
    the compiler, beside `Params`; before `mPU` a `RoundsQueryLayout lam K s A` (Iop/BatchWire.lean): a
    `WireRB` for each round;
  `WP`: a `WireBP L` (Iop/BatchWireP.lean): the prover's data for the three protocols, and the
    enumeration of the encoding randomness;
  `p`: a `Params` (Compile/Star.lean): the numbers `sMT`, `sFS`, `M` (the number of copies is M +
    1) and `s1`;
  `fr`: a map ℕ → Bool; for which requests a proof string is made at all (the head of
    Compile/Batch/Star.lean);
  `MarkQ c M Q` (Compile/MarkLe.lean): every path of the program makes at most M o marked queries
    to o and ends in a result with the property Q.

Limits: nothing on the rules of deferred programming, on ordinary queries (`PpU` makes none) or on
lengths of tokens. The bound is not tight: in every round both kinds of trees are counted.
-/
import Compile.MarkLe
import Compile.Batch.StarU
import Compile.Batch.DisciplineChainNum
import Compile.Batch.ChainUnfold

noncomputable section

namespace Compile.Batch.CountU
open Iop Rom Compile
open Compile.Disc (cnt1)
open Compile.Batch.Disc (MCh MLo MFb jn joins)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- no marked query -/
abbrev Z0 : OracleName → ℕ := fun _ => 0
/-- n queries to the oracle o -/
abbrev c1 (lam K : ℕ) (L : BatchProtocol I X) (o : OracleName) (n : ℕ) : OracleName → ℕ := cnt1 (S := spec lam K L) o n

theorem c1_add (o : OracleName) (a b : ℕ) (o' : OracleName) :
    c1 lam K L o a o' + c1 lam K L o b o' = c1 lam K L o (a + b) o' := by
  simp only [c1, cnt1]
  split <;> rfl

theorem c1_mono (o : OracleName) {a b : ℕ} (h : a ≤ b) (o' : OracleName) :
    c1 lam K L o a o' ≤ c1 lam K L o b o' := by
  simp only [c1, cnt1]
  split
  · exact h
  · exact le_rfl

/-! ## Part 1. Trees -/

theorem mq_one {β : Type} {o : OracleName} {t : Tok} {us : List Tok}
    {pt : Bits → List Bits → (spec lam K L).Dom o} {inj : ∀ vs, Function.Injective fun v => pt v vs}
    {k : (split lam K L).Vis o → Tok → St lam K L β} {Q : β → Prop}
    (h : ∀ v t', MarkQ (k v t') Z0 Q) :
    MarkQ (Step.marked (S := spec lam K L) (sp := split lam K L) o t us pt inj k) (c1 lam K L o 1)
      Q :=
  (MarkQ.marked h).mono (fun _ x => x) fun _ => le_rfl

/-- a function of the result adds no marked query -/
theorem mq_map {α β : Type} {c : St lam K L α} {M : OracleName → ℕ} {Q : α → Prop} {Q' : β → Prop}
    {f : α → β} (h : MarkQ c M Q) (hf : ∀ a, Q a → Q' (f a)) :
    MarkQ (c.bind fun a => Step.pure (f a)) M Q' :=
  MarkQ.bind_le (M₂ := Z0) h hf fun _ => le_rfl

theorem mq_leafT (sMT : ℕ) (b : Body L) :
    MarkQ (leafT (lam := lam) (K := K) sMT b) (c1 lam K L OracleName.leaf 1) fun _ => True :=
  fun _ => mq_one fun _ _ => trivial
theorem mq_nodeT (a b : Tok) :
    MarkQ (nodeT (lam := lam) (K := K) (L := L) a b) (c1 lam K L OracleName.node 1) fun _ => True :=
  mq_one fun _ _ => trivial
theorem mq_rnodeT (a b : Tok) :
    MarkQ (rnodeT (lam := lam) (K := K) (L := L) a b) (c1 lam K L OracleName.rnode 1) fun _ => True :=
  mq_one fun _ _ => trivial
theorem mq_rleafT (c : Tok) :
    MarkQ (rleafT (lam := lam) (K := K) (L := L) c) (c1 lam K L OracleName.rleaf 1) fun _ => True :=
  mq_one fun _ _ => trivial

theorem mq_leavesT (sMT : ℕ) :
    ∀ l : List (Body L),
      MarkQ (leavesT (lam := lam) (K := K) sMT l) (c1 lam K L OracleName.leaf l.length) fun x =>
        x.1.length = l.length
  | [] => rfl
  | b :: t => by
    show MarkQ
      ((leafT sMT b).bind fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
      _ _
    refine MarkQ.bind_le (mq_leafT sMT b)
      (fun x _ => mq_map (mq_leavesT sMT t) fun r hr => ?_) fun o => ?_
    · show (x.2 :: r.1).length = _
      simp [hr]
    · rw [c1_add]
      exact c1_mono _ (by simp; omega) o

section Levels
variable {hN : Tok → Tok → St lam K L Tok}
  {o : OracleName} (H : ∀ a b, MarkQ (hN a b) (c1 lam K L o 1) fun _ => True)
include H

theorem mq_pairUp :
    ∀ (n : ℕ) (l : List Tok), l.length ≤ n →
      MarkQ (pairUp hN l) (c1 lam K L o (l.length / 2)) fun r => r.length = (l.length + 1) / 2
  | _, [], _ => rfl
  | _, [x], _ => (by simp : [x].length = ([x].length + 1) / 2)
  | 0, _ :: _ :: _, h => by simp at h
  | n + 1, a :: b :: t, h => by
    show MarkQ ((hN a b).bind fun c => (pairUp hN t).bind fun r => Step.pure (c :: r)) _ _
    refine MarkQ.bind_le (H a b)
      (fun c _ => mq_map (mq_pairUp n t (by simp at h; omega)) fun r hr => ?_) fun o' => ?_
    · show (c :: r).length = _
      simp only [List.length_cons, hr]
      omega
    · rw [c1_add]
      exact c1_mono _ (by simp only [List.length_cons]; omega) o'

theorem mq_levelsM :
    ∀ (d : ℕ) (l : List Tok), MarkQ (levelsM hN d l) (c1 lam K L o l.length) fun _ => True
  | 0, _ => trivial
  | d + 1, l => by
    show MarkQ ((pairUp hN l).bind fun u => (levelsM hN d u).bind fun r => Step.pure (l :: r)) _ _
    refine MarkQ.bind_le (M₂ := c1 lam K L o ((l.length + 1) / 2)) (mq_pairUp H l.length l le_rfl)
      (fun u hu => ?_) fun o' => ?_
    · rw [← hu]
      exact mq_map (mq_levelsM d u) fun _ _ => trivial
    · rw [c1_add]
      exact c1_mono _ (by omega) o'

end Levels

/-- the queries of one tree over 2^d leaves -/
abbrev mTree (lam K : ℕ) (L : BatchProtocol I X) (d : ℕ) : OracleName → ℕ := fun o =>
  c1 lam K L OracleName.leaf (2 ^ d) o + c1 lam K L OracleName.node (2 ^ d) o

theorem mq_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    MarkQ (commitT (lam := lam) (K := K) sMT d leaf) (mTree lam K L d) fun _ => True := by
  show MarkQ
    ((leavesT sMT ((List.range (2 ^ d)).map leaf)).bind fun x =>
      (levelsM nodeT d x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TTree))
    _ _
  refine MarkQ.bind_le (M₂ := c1 lam K L OracleName.node (2 ^ d)) (mq_leavesT sMT _)
    (fun x hx => ?_) fun o => ?_
  · have hx' : x.1.length = 2 ^ d := by simpa using hx
    rw [← hx']
    exact mq_map (mq_levelsM mq_nodeT d x.1) fun _ _ => trivial
  · simp

/-- the tree over a component, if it has one, and then what follows. The bound counts the tree in
both cases: a component without a tree makes no query -/
theorem mq_withTree {β : Type} (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} {M₂ M : OracleName → ℕ} {Q : β → Prop} (h : ∀ tr, MarkQ (k tr) M₂ Q)
    (hM : ∀ o, mTree lam K L d o + M₂ o ≤ M o) :
    MarkQ (withTree sMT has d leaf k) M Q := by
  cases has with
  | true => exact MarkQ.bind_le (mq_commitT sMT d leaf) (fun tr _ => h (some tr)) hM
  | false => exact (h none).mono (fun _ x => x) fun o => le_trans (Nat.le_add_left _ _) (hM o)

/-- The trees over a component, and then what follows: the queries of the trees add up. A component
without a tree is the empty list: the sum is 0. -/
theorem mq_withTrees {β : Type} {Q : β → Prop} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β} {M₂ M : OracleName → ℕ},
      (∀ trs, MarkQ (k trs) M₂ Q) →
      (∀ o, (ds.map fun d => mTree lam K L d o).sum + M₂ o ≤ M o) →
      MarkQ (withTrees sMT ds leaf k) M Q
  | [], _, _, _, _, h, hM =>
    (h []).mono (fun _ x => x) fun o => le_trans (Nat.le_add_left _ _) (hM o)
  | d :: ds, leaf, _, M₂, _, h, hM =>
    MarkQ.bind_le (M₂ := fun o => (ds.map fun d => mTree lam K L d o).sum + M₂ o)
      (mq_commitT sMT d (leaf 0))
      (fun tr _ =>
        mq_withTrees sMT ds (fun n => leaf (n + 1)) (fun trs => h (tr :: trs)) fun _ => le_rfl)
      fun o => le_of_eq_of_le (Nat.add_assoc _ _ _).symm (hM o)

/-- the queries of the trees of the depths ds, at the oracle o: `Disc.MTrees`
(Compile/Batch/DisciplineCnt.lean) -/
theorem sum_mTree (ds : List ℕ) (o : OracleName) :
    (ds.map fun d => mTree lam K L d o).sum = Disc.MTrees lam K L ds o := by
  induction ds with
  | nil => exact (Disc.MTrees_nil o).symm
  | cons d ds ih => rw [List.map_cons, List.sum_cons, ih, Disc.MTrees_cons]

theorem mq_rleavesTU :
    ∀ cs : List (Option Tok),
      MarkQ (rleavesTU (lam := lam) (K := K) (L := L) cs)
        (c1 lam K L OracleName.rleaf (cs.countP Option.isSome)) fun r => r.length = cs.length
  | [] => rfl
  | some c :: t => by
    show MarkQ ((rleafT c).bind fun d => (rleavesTU t).bind fun r => Step.pure (d :: r)) _ _
    refine MarkQ.bind_le (mq_rleafT c)
      (fun d _ => mq_map (mq_rleavesTU t) fun r hr => ?_) fun o => ?_
    · show (d :: r).length = _
      simp [hr]
    · rw [c1_add]
      exact c1_mono _ (by rw [List.countP_cons_of_pos (by rfl)]; omega) o
  | none :: t => by
    intro d
    refine (mq_map (mq_rleavesTU t) fun r hr => ?_).mono (fun _ x => x) fun o =>
      c1_mono _ (by simp) o
    show (d :: r).length = _
    simp [hr]

theorem mq_reqTU (depthReq : ℕ) (cs : List (Option Tok)) :
    MarkQ (reqTU (lam := lam) (K := K) (L := L) depthReq cs)
      (fun o => c1 lam K L OracleName.rleaf (cs.countP Option.isSome) o + c1 lam K L OracleName.rnode cs.length o)
      fun _ => True := by
  refine MarkQ.bind_le (mq_rleavesTU cs) (fun ls hls => ?_) fun _ => le_rfl
  rw [← hls]
  exact mq_map (mq_levelsM mq_rnodeT depthReq ls) fun _ _ => trivial


/-! ## Part 2. Programs without marked queries -/

theorem mq_drawT {β : Type} (e : Enum β) :
    MarkQ (drawT (lam := lam) (K := K) (L := L) e) Z0 fun _ => True := fun _ => trivial

theorem mq_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    MarkQ (openT (lam := lam) (K := K) (L := L) t j a) Z0 fun _ => True := fun _ => trivial

theorem mq_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    MarkQ (openE (K := K) (L := L) t j a) Z0 fun _ => True := by
  unfold openE
  split
  · exact fun _ => trivial
  · exact trivial

/-- two programs without marked queries, one after the other -/
theorem mq0_bind {α β : Type} {c : St lam K L α} {g : α → St lam K L β}
    (hc : MarkQ c Z0 fun _ => True) (hg : ∀ a, MarkQ (g a) Z0 fun _ => True) :
    MarkQ (c.bind g) Z0 fun _ => True :=
  MarkQ.bind_le hc (fun a _ => hg a) fun _ => le_rfl

theorem mq_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, MarkQ (opensComp (K := K) (L := L) dec posAt o tr isRead f js) Z0 fun _ => True
  | [] => trivial
  | j :: js => by
    unfold opensComp
    refine mq0_bind (mq_opensComp dec posAt o tr isRead f js) fun f' => ?_
    cases posAt j with
    | none => exact trivial
    | some p =>
      by_cases hr : isRead p = true
      · simp only [hr, if_true]
        exact mq0_bind (mq_openT tr j _) fun _ => trivial
      · simp only [hr, Bool.false_eq_true, if_false]
        exact trivial

theorem mq_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ tr : Option TTree,
      MarkQ (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) Z0 fun _ => True
  | some tr => mq_opensComp dec posAt o tr isRead f _
  | none => trivial

theorem mq_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      MarkQ (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f) Z0 fun _ => True
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    mq0_bind (mq_opensTrees dec posAt o isRead (k + 1) ds trs f) fun f' =>
      mq_opensComp dec (posAt k) o tr isRead f' _

theorem mq_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      MarkQ (opensB (L := L) s A W τ tjs t0s isRead) Z0 fun _ => True
  | [], _, _, _, _, _, _ => trivial
  | r :: s, (_, A), (wr, W), (m, _, τ), tjs, t0s, isRead => by
    unfold opensB
    exact mq0_bind (mq_opensOpt _ _ _ _ _ _ _) fun _ =>
      mq0_bind (mq_opensOpt _ _ _ _ _ _ _) fun _ =>
        mq0_bind (mq_opensB s A W τ _ _ _) fun _ => trivial

theorem mq_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos, MarkQ (opensExtB (K := K) (L := L) we y trees isRead ps) Z0 fun _ => True
  | [] => trivial
  | p :: ps => by
    unfold opensExtB
    refine mq0_bind (mq_opensExtB we y trees isRead ps) fun f => ?_
    by_cases hr : isRead p = true
    · simp only [hr, if_true]
      exact mq0_bind (mq_openE _ _ _) fun _ => trivial
    · simp only [hr, Bool.false_eq_true, if_false]
      exact trivial

section Finish
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
  (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (trees : List (TreeH lam)) (wt : Wt)

theorem mq_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    MarkQ (finishSlot (L := L) Q H wq wp trees wt c0 a0 j x cj acc) Z0 fun _ => True := by
  dsimp only [finishSlot]
  split
  · exact trivial
  · exact fun vs =>
      mq0_bind (mq_opensB _ _ _ _ _ _ _) fun _ => mq0_bind (mq_opensExtB _ _ _ _ _) fun _ => trivial

theorem mq_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      MarkQ (finishAll (L := L) Q H wq wp trees wt fl c0 a0 j zs) Z0 fun _ => True
  | _, [] => trivial
  | j, acc :: zs => by
    unfold finishAll
    refine mq0_bind ?_ fun _ => mq0_bind (mq_finishAll fl c0 a0 (j + 1) zs) fun _ => trivial
    cases acc.x with
    | none => exact trivial
    | some y =>
      obtain ⟨x, cj⟩ := y
      show MarkQ (if fl j then finishSlot Q H wq wp trees wt c0 a0 j x cj acc else pure none) _ _
      split
      · exact mq_finishSlot Q H wq wp trees wt c0 a0 j x cj acc
      · exact trivial

end Finish

/-! ## Part 3. The rounds -/

/-- does the slot hold a request -/
abbrev isF {Y : Type} {s : Shape} (z : SlotSt lam K Y s) : Bool := z.2.x.isSome

/-- do f in each entry: on an entry of the first kind at most M marked queries, on one of the second
kind none; the kinds are kept -/
theorem mq_eachM {σ τ : Type} (f : σ → St lam K L τ) (φ : σ → Bool) (φ' : τ → Bool) (M : OracleName → ℕ)
    (hf : ∀ a, φ a = true → MarkQ (f a) M fun b => φ' b = true)
    (he : ∀ a, φ a = false → MarkQ (f a) Z0 fun b => φ' b = false) :
    ∀ l : List σ, MarkQ (eachM f l) (fun o => l.countP φ * M o) fun r =>
      r.countP φ' = l.countP φ ∧ r.length = l.length
  | [] => ⟨rfl, rfl⟩
  | a :: l => by
    show MarkQ ((f a).bind fun b => (eachM f l).bind fun r => Step.pure (b :: r)) _ _
    cases ha : φ a with
    | true =>
      refine MarkQ.bind_le (hf a ha)
        (fun b hb => mq_map (mq_eachM f φ φ' M hf he l) fun r hr => ?_) fun o => ?_
      · rw [List.countP_cons_of_pos hb, List.countP_cons_of_pos ha, hr.1,
          List.length_cons, List.length_cons, hr.2]
        exact ⟨rfl, rfl⟩
      · rw [List.countP_cons_of_pos ha, Nat.succ_mul]
        omega
    | false =>
      refine MarkQ.bind_le (he a ha)
        (fun b hb => mq_map (mq_eachM f φ φ' M hf he l) fun r hr => ?_) fun o => ?_
      · rw [List.countP_cons_of_neg (by simp [hb]), List.countP_cons_of_neg (by simp [ha]), hr.1,
          List.length_cons, List.length_cons, hr.2]
        exact ⟨rfl, rfl⟩
      · rw [List.countP_cons_of_neg (by simp [ha])]
        simp

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) {r : Round}
  {s : Shape} (a : RAnn r) (w : WireRB lam K r a) (emb : (p : r.Pos) → r.Sym p → Body L)
  (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem mq_fbT {β : Type} (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} {M : OracleName → ℕ}
    {Q : β → Prop} (h : ∀ bl tl, MarkQ (k bl tl) M Q) :
    MarkQ (fbT t i tk us root hd hinj pl k) (fun o => c1 lam K L (OracleName.fb t) 1 o + M o) Q :=
  MarkQ.marked h

theorem mq_fbTw {β : Type} (j : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} {M : OracleName → ℕ}
    {Q : β → Prop} (h : ∀ bl tl, MarkQ (k bl tl) M Q) :
    MarkQ (fbTw t j i tk us root hd hinj pl k) (fun o => c1 lam K L (OracleName.fbw t j) 1 o + M o) Q :=
  MarkQ.marked h

/-- one query to each ghost name fbw t k, j ≤ k < j + n -/
def MW (t : Tag) (j n : ℕ) : OracleName → ℕ
  | .fbw t' k => if t' = t then (if j ≤ k ∧ k < j + n then 1 else 0) else 0
  | _ => 0

omit i in
theorem MW_step (j n : ℕ) (o : OracleName) :
    c1 lam K L (OracleName.fbw t j) 1 o + MW t (j + 1) n o ≤ MW t j (n + 1) o := by
  cases o with
  | fbw t' k =>
    by_cases ht : t' = t
    · subst ht
      by_cases hk : k = j
      · subst hk
        have e1 : c1 lam K L (OracleName.fbw t' k) 1 (OracleName.fbw t' k) = 1 := if_pos rfl
        have e2 : MW t' (k + 1) n (OracleName.fbw t' k) = 0 := by simp [MW]
        have e3 : MW t' k (n + 1) (OracleName.fbw t' k) = 1 := by simp [MW]
        rw [e1, e2, e3]
      · have e1 : c1 lam K L (OracleName.fbw t' j) 1 (OracleName.fbw t' k) = 0 :=
          if_neg fun e => hk (OracleName.fbw.inj e).2
        rw [e1, Nat.zero_add]
        show (if t' = t' then (if j + 1 ≤ k ∧ k < j + 1 + n then 1 else 0) else 0) ≤
          (if t' = t' then (if j ≤ k ∧ k < j + (n + 1) then 1 else 0) else 0)
        rw [if_pos rfl, if_pos rfl]
        by_cases h1 : j + 1 ≤ k ∧ k < j + 1 + n
        · rw [if_pos h1, if_pos ⟨by omega, by omega⟩]
        · rw [if_neg h1]
          exact Nat.zero_le _
    · have e1 : c1 lam K L (OracleName.fbw t j) 1 (OracleName.fbw t' k) = 0 := if_neg fun e => ht (OracleName.fbw.inj e).1
      have e2 : MW t (j + 1) n (OracleName.fbw t' k) = 0 := if_neg ht
      rw [e1, e2]
      exact Nat.zero_le _
  | _ => simp [c1, cnt1, MW]

omit i in
theorem MW_fb (m : ℕ) (o : OracleName) : c1 lam K L (OracleName.fb t) 1 o + MW t 0 m o ≤ MFb t m o := by
  cases o with
  | fb t' =>
    by_cases ht : t' = t
    · subst ht
      have e1 : c1 lam K L (OracleName.fb t') 1 (OracleName.fb t') = 1 := if_pos rfl
      have e3 : MFb t' m (OracleName.fb t') = 1 := if_pos rfl
      rw [e1, e3]
      exact le_rfl
    · have e1 : c1 lam K L (OracleName.fb t) 1 (OracleName.fb t') = 0 := if_neg fun e => ht (OracleName.fb.inj e)
      rw [e1]
      exact Nat.zero_le _
  | fbw t' k =>
    have e1 : c1 lam K L (OracleName.fb t) 1 (OracleName.fbw t' k) = 0 := if_neg fun e => by cases e
    rw [e1, Nat.zero_add]
    show (if t' = t then (if 0 ≤ k ∧ k < 0 + m then 1 else 0) else 0) ≤
      (if t' = t then (if k < m then 1 else 0) else 0)
    by_cases ht : t' = t
    · rw [if_pos ht, if_pos ht]
      by_cases h1 : 0 ≤ k ∧ k < 0 + m
      · rw [if_pos h1, if_pos (by omega)]
      · rw [if_neg h1]
        exact Nat.zero_le _
    · rw [if_neg ht]
      exact Nat.zero_le _
  | _ => simp [c1, cnt1, MW, MFb]

theorem mq_fbW {β C P : Type} (g : GrW C P) (chal : Blk lam K → C) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb' : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : ℕ → List Tok → Blk lam K → Tok → St lam K L β} {M : OracleName → ℕ} {Q : β → Prop}
    (h : ∀ m dd bl tl, MarkQ (k m dd bl tl) M Q) :
    ∀ n j dd,
      MarkQ (fbW g chal t i tk us root hd hinj emb' α k n j dd) (fun o => MW t j (n + 1) o + M o) Q
  | 0, j, dd => (mq_fbTw t i j tk us root hd hinj _ fun bl tl => h _ _ bl tl).mono (fun _ x => x) fun o =>
      Nat.add_le_add_right ((Nat.le_add_right _ _).trans
        (MW_step (lam := lam) (K := K) (L := L) t j 0 o)) _
  | n + 1, j, dd => (mq_fbTw (M := fun o => MW t (j + 1) (n + 1) o + M o) t i j tk us root hd hinj _ fun bl tl => by
      split
      · exact (h _ _ bl tl).mono (fun _ x => x) fun o => Nat.le_add_left _ _
      · exact mq_fbW g chal tk us root hd hinj emb' α h n (j + 1) (tl :: dd)).mono (fun _ x => x) fun o =>
        (le_of_eq (Nat.add_assoc _ _ _).symm).trans
          (Nat.add_le_add_right (MW_step (lam := lam) (K := K) (L := L) t j (n + 1) o) _)

/-- A Fiat-Shamir query, with proof-of-work bits or without: one query to fb t, and at most one to
each ghost name fbw t k, k below the maximal number of further attempts. -/
theorem mq_fbG {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (tk : Tok)
    (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb' : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {M : OracleName → ℕ} {Q : β → Prop}
    (h : ∀ nc dd bl tl, MarkQ (k nc dd bl tl) M Q) :
    MarkQ (fbG gr chal t i tk us root hd hinj emb' α k) (fun o => MFb t (moreOf gr) o + M o) Q := by
  have h0 : ∀ m o, c1 lam K L (OracleName.fb t) 1 o ≤ MFb t m o := fun m o =>
    (Nat.le_add_right _ _).trans (MW_fb t m o)
  cases gr with
  | none =>
    exact (mq_fbT t i tk us root hd hinj _ fun bl tl => h none [] bl tl).mono (fun _ x => x)
      fun o => Nat.add_le_add_right (h0 _ o) _
  | some g =>
    show MarkQ (fbTG g chal t i tk us root hd hinj emb' α fun m => k (some m))
      (fun o => MFb t g.more o + M o) Q
    unfold fbTG
    split
    · exact (mq_fbT t i tk us root hd hinj _ fun bl tl => h _ _ bl tl).mono (fun _ x => x)
        fun o => Nat.add_le_add_right (h0 _ o) _
    · rename_i n hn
      refine (mq_fbT (M := fun o => MW t 0 (n + 1) o + M o)
          t i tk us root hd hinj _ fun bl tl => ?_).mono
        (fun _ x => x) fun o => ?_
      · split
        · exact (h _ _ bl tl).mono (fun _ x => x) fun o => Nat.le_add_left _ _
        · exact mq_fbW t i g chal tk us root hd hinj emb' α (fun m => h (some m)) n 0 [tl]
      · rw [hn]
        exact (le_of_eq (Nat.add_assoc _ _ _).symm).trans
          (Nat.add_le_add_right (MW_fb (lam := lam) (K := K) (L := L) t (n + 1) o) _)

/-- the same as `mq_fbG`, for the query of a slot in a local round -/
theorem mq_fbSlotG {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C) (x : Option X)
    (ph : PhT) (tk c : Tok) (root : Option Tok) (emb' : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {M : OracleName → ℕ} {Q : β → Prop}
    (h : ∀ nc dd bl tl, MarkQ (k nc dd bl tl) M Q) :
    MarkQ (fbSlotG gr chal t i cms x ph tk c root emb' α k)
      (fun o => MFb t (moreOf gr) o + M o) Q := by
  cases ph <;> exact mq_fbG t i gr chal _ _ _ _ _ emb' α h

theorem mq_slotLo (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    MarkQ (slotLo sMT t cms xin a w emb plJ i ph z)
      (MLo lam K L t w.depthJ (moreOf w.grJ)) fun z' => z'.2.x = z.2.x := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotLo]
  refine mq_withTree (M₂ := MFb t (moreOf w.grJ)) sMT w.hasJ w.depthJ _
    (fun tr => ?_) fun _ => le_rfl
  refine MarkQ.mono (fun _ x => x) (mq_fbSlotG (M := Z0) t cms i w.grJ w.chal _ ph _ _ _ plJ _ ?_)
    fun o => le_of_eq (Nat.add_zero _)
  exact fun _ _ _ _ => rfl

theorem mq_slotLoU_full (ph : PhT) (z : SlotSt lam K Y (r :: s)) (h : isF z = true) :
    MarkQ (slotLoU sMT t cms xin a w emb plJ i ph z)
      (MLo lam K L t w.depthJ (moreOf w.grJ)) fun z' => isF z' = true := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 h
  have e : slotLoU sMT t cms xin a w emb plJ i ph z = slotLo sMT t cms xin a w emb plJ i ph z := by
    simp only [slotLoU, hy]
  rw [e]
  exact (mq_slotLo sMT t cms xin a w emb plJ i ph z).mono
    (fun z' hz' => by simp only [isF, hz']; exact h) fun _ => le_rfl

theorem mq_slotLoU_empty (ph : PhT) (z : SlotSt lam K Y (r :: s)) (h : isF z = false) :
    MarkQ (slotLoU sMT t cms xin a w emb plJ i ph z) Z0 fun z' => isF z' = false := by
  have hx : z.2.x = none := by simpa [isF] using h
  have e : slotLoU sMT t cms xin a w emb plJ i ph z =
      Step.pure (z.1.2 (w.chal (blk0 lam K)), z.2) := by
    simp only [slotLoU, hx]
  rw [e]
  exact h

/-- the queries of one slot in the joining round -/
abbrev mJoin (lam K : ℕ) (L : BatchProtocol I X) (t : Tag) (dJ : ℕ) : OracleName → ℕ := fun o =>
  c1 lam K L OracleName.leaf (2 ^ dJ) o + c1 lam K L OracleName.node (2 ^ dJ) o + c1 lam K L (OracleName.g t) 1 o

theorem mq_slotJoin (z : SlotSt lam K Y (r :: s)) :
    MarkQ (slotJoin sMT t a w emb plJ i z) (mJoin lam K L t w.depthJ) fun z' => z'.2.x = z.2.x := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  refine mq_withTree (M₂ := c1 lam K L (OracleName.g t) 1) sMT w.hasJ w.depthJ _
    (fun tr => ?_) fun _ => le_rfl
  exact mq_one fun _ _ => rfl

/-- the joining round in all slots -/
theorem mq_joinMU :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      MarkQ (joinMU sMT t a w emb plJ i zs)
        (fun o => zs.countP isF * mJoin lam K L t w.depthJ o) fun o =>
          o.1.countP isF = zs.countP isF ∧
          o.1.length = zs.length ∧
          o.2.countP Option.isSome = zs.countP isF ∧
          o.2.length = zs.length
  | [] => ⟨rfl, rfl, rfl, rfl⟩
  | z :: zs => by
    unfold joinMU
    cases hz : isF z with
    | true =>
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hz
      have e : slotJoinU sMT t a w emb plJ i z = slotJoin sMT t a w emb plJ i z := by
        simp only [slotJoinU, hy]
      rw [e]
      refine MarkQ.bind_le (mq_slotJoin sMT t a w emb plJ i z)
        (fun z' hz' => mq_map (mq_joinMU zs) fun o ho => ?_) fun o => ?_
      · have hF : isF z' = true := by simp only [isF, hz']; exact hz
        have hS : (z'.2.x.map fun _ => z'.2.c).isSome = true := by simpa [isF] using hF
        rw [List.countP_cons_of_pos hF, List.countP_cons_of_pos hz,
          List.countP_cons_of_pos hS, ho.1, ho.2.2.1]
        simp [ho.2.1, ho.2.2.2]
      · rw [List.countP_cons_of_pos hz, Nat.succ_mul]
        omega
    | false =>
      have hx : z.2.x = none := by simpa [isF] using hz
      have e : slotJoinU sMT t a w emb plJ i z = Step.pure z := by simp only [slotJoinU, hx]
      rw [e]
      refine (mq_map (mq_joinMU zs) fun o ho => ?_).mono (fun _ x => x) fun o => ?_
      · have hS : ¬ (z.2.x.map fun _ => z.2.c).isSome = true := by simp [hx]
        rw [List.countP_cons_of_neg (by simp [hz]), List.countP_cons_of_neg (by simp [hz]),
          List.countP_cons_of_neg hS, ho.1, ho.2.2.1]
        simp [ho.2.1, ho.2.2.2]
      · rw [List.countP_cons_of_neg (by simp [hz])]

theorem countP_hear (bl : Blk lam K) (noted : Bool) (zs : List (SlotSt lam K Y (r :: s))) :
    (zs.map (hear w bl noted)).countP isF = zs.countP isF := by
  rw [List.countP_map]
  rfl

end Rounds


/-! ## Part 4. The numbers -/

/-- The marked queries of the rounds that are left (bounds), with at most m requests and N leaves of
the request tree, from the phase ph on -/
def MChU (t : Tag) (ph : PhT) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (m N : ℕ) : OracleName → ℕ
  | .rnode => jn ph s A * N
  | o => MCh t ph s A W m o

theorem MChU_of_ne (t : Tag) (ph : PhT) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (m N : ℕ)
    {o : OracleName} (ho : o ≠ OracleName.rnode) :
    MChU t ph s A W m N o = MCh t ph s A W m o := by
  cases o <;> first | rfl | exact absurd rfl ho

theorem c1_of_ne {o₀ o : OracleName} (h : o ≠ o₀) (n : ℕ) : c1 lam K L o₀ n o = 0 := if_neg h

section Num
variable {r : Round} {s : Shape} (t : Tag) (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
  (W : RoundsQueryLayout lam K s A) (m N : ℕ)

theorem MChU_shr_eq (tl tl' : Tok) (o : OracleName) :
    MChU t (.shr tl) s A W m N o = MChU t (.shr tl') s A W m N o := by cases o <;> rfl

theorem MChU_lo (ph : PhT) (hk : a.kind = .lo) (o : OracleName) :
    m * MLo lam K L t w.depthJ (moreOf w.grJ) o + MChU t ph.afterLo s A W m N o ≤
      MChU t ph (r :: s) (a, A) (w, W) m N o := by
  by_cases ho : o = OracleName.rnode
  · subst ho
    simp [MChU, MLo, MFb, cnt1, Disc.Num.jn_afterLo A hk ph]
  · rw [MChU_of_ne _ _ _ _ _ _ _ ho, MChU_of_ne _ _ _ _ _ _ _ ho]
    exact Disc.MCh_lo t ph a A w W m hk o

theorem MChU_f5 (tk0 tl : Tok) (o : OracleName) :
    mTree lam K L w.depth0 o + (MFb t (moreOf w.gr0) o + MChU t (.shr tl) s A W m N o) ≤
      MChU t (.shr tk0) (r :: s) (a, A) (w, W) m N o := by
  by_cases ho : o = OracleName.rnode
  · subst ho
    simp [MChU, mTree, MFb, cnt1, jn]
  · rw [MChU_of_ne _ _ _ _ _ _ _ ho, MChU_of_ne _ _ _ _ _ _ _ ho]
    have h := Disc.MCh_f5 (L := L) t tk0 tl a A w W m o
    simp only [mTree, c1]
    omega

theorem MChU_join (tl : Tok) (hk : a.kind = .sh) (o : OracleName) :
    m * mJoin lam K L t w.depthJ o +
        ((c1 lam K L OracleName.rleaf m o + c1 lam K L OracleName.rnode N o) +
          (mTree lam K L w.depth0 o + (MFb t (moreOf w.gr0) o + MChU t (.shr tl) s A W m N o))) ≤
      MChU t .loc (r :: s) (a, A) (w, W) m N o := by
  by_cases ho : o = OracleName.rnode
  · subst ho
    simp [MChU, mJoin, mTree, MFb, cnt1, jn, Disc.Num.joins_cons_sh A hk]
  · rw [MChU_of_ne _ _ _ _ _ _ _ ho, MChU_of_ne _ _ _ _ _ _ _ ho, c1_of_ne ho]
    have h := Disc.MCh_join (L := L) t tl a A w W m hk o
    have e : cnt1 (S := spec lam K L) OracleName.rnode m o = 0 := c1_of_ne ho m
    rw [e] at h
    simp only [mTree, mJoin, c1]
    omega

theorem MChU_skip (ph : PhT) (hk : a.kind = .sh) (hph : ph = .first ∨ ph = .aft) (o : OracleName) :
    MChU t ph s A W m N o ≤ MChU t ph (r :: s) (a, A) (w, W) m N o := by
  by_cases ho : o = OracleName.rnode
  · subst ho
    have h := Disc.MCh_skip t ph a A w W N hk hph OracleName.rnode
    exact h
  · rw [MChU_of_ne _ _ _ _ _ _ _ ho, MChU_of_ne _ _ _ _ _ _ _ ho]
    exact Disc.MCh_skip t ph a A w W m hk hph o

end Num

/-! ## Part 5. The Fiat-Shamir chains, one execution, the prover -/

/-- All chains of a batch with at most m requests in at most N slots. -/
theorem mq_chainTU {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam))
    (xin : Y → Option X) (depthReq m N : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      zs.countP isF ≤ m → zs.length ≤ N →
      MarkQ (chainTU sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
        (MChU t ph s A W m N) fun _ => True
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, hm, hN => by
    have hkk : a.kind = .lo ∨ a.kind = .sh := by cases a.kind <;> simp
    rcases hkk with hk | hk
    · rw [SkipU.chainTU_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
      refine MarkQ.bind_le
        (mq_eachM _ isF isF (MLo lam K L t w.depthJ (moreOf w.grJ))
          (mq_slotLoU_full sMT t cms xin a w _ _ i ph)
          (mq_slotLoU_empty sMT t cms xin a w _ _ i ph) zs)
        (fun zs' h =>
          mq_chainTU sMT t cms xin depthReq m N s A W _ _ (i + 1) ph.afterLo _ zs' _
            (by rw [h.1]; exact hm) (by rw [h.2]; exact hN)) fun o => ?_
      exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) _).trans
        (MChU_lo t a A w W m N ph hk o)
    · cases ph with
      | loc =>
        rw [SkipU.chainTU_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
        refine MarkQ.bind_le
          (M₂ := fun o =>
              (c1 lam K L OracleName.rleaf m o + c1 lam K L OracleName.rnode N o) +
                (mTree lam K L w.depth0 o + (MFb t (moreOf w.gr0) o + MChU t (.shr 0) s A W m N o)))
          (mq_joinMU sMT t a w _ _ i zs) (fun o ho => ?_) fun o => ?_
        · refine MarkQ.bind_le
            ((mq_reqTU depthReq o.2).mono (fun _ x => x) fun o' =>
              Nat.add_le_add (c1_mono _ (by rw [ho.2.2.1]; exact hm) o')
                (c1_mono _ (by rw [ho.2.2.2]; exact hN) o'))
            (fun rq _ => ?_) fun _ => le_rfl
          refine mq_withTree sMT w.has0 w.depth0 _ (fun tr0 => ?_) fun _ => le_rfl
          refine mq_fbG t i w.gr0 w.chal _ _ _ _ _ _ _ fun nc dd bl tl => ?_
          exact (mq_chainTU sMT t cms xin depthReq m N s A W _ _ (i + 1) (.shr tl) _ _ _
              (by rw [countP_hear, ho.1]; exact hm)
              (by rw [List.length_map, ho.2.1]; exact hN)).mono
            (fun _ x => x) fun o' => le_of_eq (MChU_shr_eq t A W m N tl 0 o')
        · exact (Nat.add_le_add_right (Nat.mul_le_mul_right _ hm) _).trans
            (MChU_join t a A w W m N 0 hk o)
      | shr tk0 =>
        rw [SkipU.chainTU_shr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
        refine mq_withTree (M₂ := fun o => MFb t (moreOf w.gr0) o + MChU t (.shr 0) s A W m N o)
          sMT w.has0 w.depth0 _ (fun tr0 => ?_) fun o => MChU_f5 t a A w W m N tk0 0 o
        refine mq_fbG t i w.gr0 w.chal _ _ _ _ _ _ _ fun nc dd bl tl => ?_
        exact (mq_chainTU sMT t cms xin depthReq m N s A W _ _ (i + 1) (.shr tl) _ _ _
            (by rw [countP_hear]; exact hm) (by rw [List.length_map]; exact hN)).mono
          (fun _ x => x) fun o' => le_of_eq (MChU_shr_eq t A W m N tl 0 o')
      | first =>
        rw [SkipU.chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (Or.inl rfl)]
        exact (mq_chainTU sMT t cms xin depthReq m N s A W _ _ (i + 1) .first _ _ _
            (by rw [countP_hear]; exact hm) (by rw [List.length_map]; exact hN)).mono
          (fun _ x => x) (MChU_skip t a A w W m N .first hk (Or.inl rfl))
      | aft =>
        rw [SkipU.chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (Or.inr rfl)]
        exact (mq_chainTU sMT t cms xin depthReq m N s A W _ _ (i + 1) .aft _ _ _
            (by rw [countP_hear]; exact hm) (by rw [List.length_map]; exact hN)).mono
          (fun _ x => x) (MChU_skip t a A w W m N .aft hk (Or.inr rfl))

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (wt : Wt)

/-- One execution on at most m requests in at most N slots. -/
theorem mq_proveBU (fl : ℕ → Bool) (xs : List (Option Y)) {m N : ℕ}
    (hm : xs.countP Option.isSome ≤ m) (hN : xs.length ≤ N) :
    MarkQ (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees wt fl xs)
      (MChU t .first Q.loc.shape Q.ann wq.sh m N) fun _ => True := by
  unfold proveBU
  refine MarkQ.bind_le (M₁ := Z0) (mq_drawT wp.coin0) (fun c0 _ => ?_) fun o =>
    le_of_eq (Nat.zero_add _)
  refine MarkQ.bind_le
    (mq_eachM (initSlotU sFS Q H wp wt c0) Option.isSome isF Z0
      (fun x hx => ?_) (fun x hx => ?_) xs)
    (fun zs hz => ?_) fun o =>
      le_of_eq
        (by simp : xs.countP Option.isSome * Z0 o + MChU t .first Q.loc.shape Q.ann wq.sh m N o = _)
  · obtain ⟨y, rfl⟩ := Option.isSome_iff_exists.1 hx
    exact fun _ _ => rfl
  · obtain rfl : x = none := by simpa using hx
    exact rfl
  · exact MarkQ.bind_le (M₂ := Z0)
      (mq_chainTU sMT t _ _ depthReq m N _ _ _ embS embP 0 .first _ zs _
        (by rw [hz.1]; exact hm) (by rw [hz.2]; exact hN))
      (fun out _ => mq_finishAll Q H wq wp trees wt fl c0 out.2 0 out.1) fun _ => le_rfl

end Prove

/-- of the slots of a batch at most as many hold a request as there are requests -/
theorem countP_slotsOfReq {N : ℕ} (σ : Equiv.Perm (Fin N)) (xs : List X) :
    (slotsOfReq σ xs).countP Option.isSome ≤ xs.length := by
  unfold slotsOfReq
  rw [List.countP_map, List.countP_eq_length_filter]
  have hnd : (((List.finRange N).filter (Option.isSome ∘ fun j => xs[(σ.symm j).val]?)).map
      fun j => (σ.symm j).val).Nodup :=
    ((List.nodup_finRange N).filter _).map fun a b h => σ.symm.injective (Fin.ext h)
  have hsub : (((List.finRange N).filter (Option.isSome ∘ fun j => xs[(σ.symm j).val]?)).map
        fun j => (σ.symm j).val) ⊆
      List.range xs.length := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hn
    have h2 := (List.mem_filter.1 hj).2
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (show (xs[(σ.symm j).val]?).isSome = true from h2)
    exact List.mem_range.2 (List.getElem?_eq_some_iff.1 hx).1
  have := (List.subperm_of_subset hnd hsub).length_le
  simpa using this

end Compile.Batch.CountU

namespace Compile.Batch
open Iop Rom Compile CountU

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The marked queries of one batch with at most m requests (bounds): those of m slots, of the
shared part, and of the inner nodes of the request tree with its maxBatchSize leaves. -/
def mPU (W : QueryLayout lam L) (m : ℕ) : OracleName → ℕ
  | .leaf => cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh m
  | .node => cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh m
  | .rleaf => Disc.joins L.onlineBatch.loc.shape L.onlineBatch.ann * m
  | .rnode => Disc.joins L.onlineBatch.loc.shape L.onlineBatch.ann * L.maxBatchSize
  | .fb t' => if t' = Tag.onl then (m + 1) * L.onlineBatch.loc.shape.length else 0
  | .fbw t' k => if t' = Tag.onl then cTry k m L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh else 0
  | .g t' => if t' = Tag.onl then Disc.joins L.onlineBatch.loc.shape L.onlineBatch.ann * m else 0
  | _ => 0

theorem mPU_eq (W : QueryLayout lam L) (m : ℕ) (o : OracleName) :
    MChU Tag.onl .first L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh m L.maxBatchSize o = mPU W m o := by cases o <;> rfl

/-- with all slots full it is the bound of the prover that hashes every slot -/
theorem mPU_N (W : QueryLayout lam L) : mPU W L.maxBatchSize = Disc.mPB W := by
  funext o
  cases o <;> rfl

/-- The prover with free empty slots, on at most B requests, makes at most mPU W B marked queries.
(The hypothesis on the number of slots is not used.) -/
theorem markPpU (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (k : IskH lam L) (fr : ℕ → Bool)
    (xs : List X) {B : ℕ} (_hN : L.maxBatchSize = 2 ^ W.depthReq) (hB : xs.length ≤ B) :
    MarkLe (PpU W WP p k fr xs) (mPU W B) := by
  refine MarkQ.markLe (Q := fun _ => True) fun j => ?_
  refine MarkQ.bind_le (M₁ := Z0) (mq_drawT WP.perm) (fun σ _ => ?_) fun o =>
    le_of_eq (Nat.zero_add _)
  unfold PpJU
  split
  · exact trivial
  · rename_i lf _
    refine (mq_map
        (mq_proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs) (m := B) (N := L.maxBatchSize)
          ((countP_slotsOfReq σ xs).trans hB) (by simp [slotsOfReq]))
        fun _ _ => trivial).mono
      (fun _ x => x) fun o => le_of_eq (mPU_eq W B o)

end Compile.Batch
