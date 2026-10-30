-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyWalkProofs.lean: the proofs of CompileK/HonestKeyWalk.lean: a walk over the
program of the honest committer, for a price on oracle names.

The head of CompileK/HonestKeyWalk.lean says what the statements say and what they do not. Nothing
assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.

Why: the programs are those of the token language (`Cp`, Compile/Batch/Star.lean), in which try
number k + 1 of a search (the first is try 0) is written under a ghost name fbw t k; the calculus is
`SWV` of Compile/CostV.lean at a weight that reads the name of an evaluation alone (`HkSW u`).

Main names:
  `HkNoEv c`: the program c makes no evaluation at all (drawing coins, the start of a slot,
    openings, argument strings): it costs 0 at every price, an oracle with empty answers included.
  `hkGhost u`: the price u with, at a ghost name, the price of its real name; the ghost names are
    written back (`costV_realQ_pre`, Compile/Batch/OneCallCostW.lean).
  `hkw_fbG`: a chain query: all tries (`fbG_cost`, Compile/Batch/ProverG.lean).
  `hkw_chainT`: all chains of a batch in which every slot works; the analogue of `swv_chainT`
    (Compile/Batch/OneCallCostR.lean), step for step, with the counts replaced.
  `hkw_Cp`: the committer's program.
  `honestKey_cost`, `honestKey_typed`, `honestKey_notOnl`, `honestKey_strings`, `honestKey_sum`: the
    proofs of the statements of these names in `Spec` (CompileK/HonestKeyWalk.lean).

Terms: lean/GLOSSARY.md.
-/
import CompileK.HonestKeyWalk
import CompileK.HonestKeyBlocks
import CompileK.CountsHonest

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.CostP (SWV)
open Compile.Batch.Need (phK phK_afterLo)
open Compile.Batch.CompleteUnif (OnlyQ NotFb)
open Compile.Batch.OneCall (cCBW cProve1W cSlotW cSharedW pre costV_realQ_pre)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Programs that make no evaluation -/

/-- The program makes no evaluation. -/
def HkNoEv {α : Type} : St lam K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, HkNoEv (k r)
  | .plain _ _ _ => False
  | .fresh _ k => ∀ t, HkNoEv (k t)
  | .marked _ _ _ _ _ _ => False
  | .reveal _ k => ∀ vs, HkNoEv (k vs)

theorem HkNoEv.bind {α β : Type} {c : St lam K L α} {g : α → St lam K L β}
    (h : HkNoEv c) (hg : ∀ a, HkNoEv (g a)) : HkNoEv (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih => exact h.elim
  | fresh l k ih => exact fun t => ih t (h t)
  | marked o t us pt inj k ih => exact h.elim
  | reveal ts k ih => exact fun vs => ih vs (h vs)

/-- A program that makes no evaluation costs nothing, at every weight. -/
theorem HkNoEv.swv {α : Type} {c : St lam K L α} (h : HkNoEv c)
    (w : (o : OracleName) → domOf lam L o → rngOf lam K o → ℕ) :
    SWV (S := spec lam K L) (sp := split lam K L) w c 0 (fun _ => True) := by
  induction c with
  | pure a => trivial
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih => exact h.elim
  | fresh l k ih => exact fun t => ih t (h t)
  | marked o t us pt inj k ih => exact h.elim
  | reveal ts k ih => exact fun vs => ih vs (h vs)

theorem hkn_showT (t : Tok) : HkNoEv (showT (lam := lam) (K := K) (L := L) t) := fun _ => trivial
theorem hkn_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    HkNoEv (openT (lam := lam) (K := K) (L := L) t j a) := fun _ => trivial
theorem hkn_drawT {β : Type} (e : Enum β) : HkNoEv (drawT (lam := lam) (K := K) (L := L) e) :=
  fun _ => trivial

theorem hkn_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, HkNoEv (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => trivial
  | j :: js => (hkn_opensComp dec posAt o tr isRead f js).bind fun f' => by
      show HkNoEv (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => trivial
      | some p =>
        show HkNoEv (if isRead p then _ else _)
        cases isRead p
        · trivial
        · exact (hkn_openT _ _ _).bind fun _ => trivial

theorem hkn_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    HkNoEv (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => trivial
  | some tr => exact hkn_opensComp dec posAt o tr isRead f _

theorem hkn_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      HkNoEv (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    (hkn_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      hkn_opensComp dec (posAt k) o tr isRead f' _

theorem hkn_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      HkNoEv (opensB (L := L) s A Ws τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, Ws), (_, _, τ), tjs, t0s, _ =>
      (hkn_opensOpt _ _ _ _ _ _ _).bind fun _ =>
        (hkn_opensOpt _ _ _ _ _ _ _).bind fun _ =>
          (hkn_opensB s A Ws τ tjs.tail t0s.tail _).bind fun _ => trivial

theorem hkn_openE {σ : Type} (tr : TreeH lam) (j : ℕ) (a : σ) :
    HkNoEv (openE (K := K) (L := L) tr j a) := by
  unfold openE
  cases tr.salts.getD j none with
  | none => trivial
  | some x => exact fun _ => trivial

theorem hkn_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps, HkNoEv (opensExtB (K := K) (L := L) we y trees isRead ps)
  | [] => trivial
  | q :: ps => (hkn_opensExtB we y trees isRead ps).bind fun f => by
      show HkNoEv (if isRead q then _ else _)
      cases isRead q
      · trivial
      · exact (hkn_openE _ _ _).bind fun _ => trivial

section Fin
variable {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
  (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (trees : List (TreeH lam)) (w : Wt)

theorem hkn_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    HkNoEv (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · trivial
  · exact fun vs =>
      (hkn_opensB _ _ _ _ _ _ _).bind fun f => (hkn_opensExtB _ _ _ _ _).bind fun _ => trivial

theorem hkn_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      HkNoEv (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs)
  | _, [] => trivial
  | j, acc :: zs => HkNoEv.bind (by
      cases acc.x with
      | none => trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        show HkNoEv (if fl j then _ else _)
        cases fl j
        · trivial
        · exact hkn_finishSlot Q H wq wp trees w c0 a0 j x cj acc) fun _ => (hkn_finishAll fl c0 a0 (j + 1) zs).bind fun _ => trivial

theorem hkn_initSlot (sFS : ℕ) (c0 : H.Coin0) (x : Option Y) :
    HkNoEv (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) :=
  (hkn_drawT wp.coin).bind fun _ _ => trivial

end Fin

/-! ## The walk, at a price on names -/

/-- The price u, with at a ghost name the price of its real name. -/
def hkGhost (u : OracleName → ℕ) : OracleName → ℕ
  | .fbw t _ => u (.fb t)
  | o => u o

/-- The calculus `SWV` at the weight that reads the name of an evaluation alone: on every path of
the program c the prices add up to at most m, and its result has the property P. -/
abbrev HkSW (u : OracleName → ℕ) {α : Type} (c : St lam K L α) (m : ℕ) (P : α → Prop) : Prop :=
  SWV (S := spec lam K L) (sp := split lam K L) (fun o _ _ => hkGhost u o) c m P

variable (u : OracleName → ℕ)

theorem hkw_zero {α : Type} {c : St lam K L α} (h : HkNoEv c) : HkSW u c 0 (fun _ => True) :=
  h.swv _

/-! ### Trees -/

theorem hkw_leafT (sMT : ℕ) (b : Body L) :
    HkSW u (leafT (lam := lam) (K := K) sMT b) (u .leaf) (fun _ => True) :=
  fun _ _ => ⟨u .leaf, 0, fun _ _ _ _ => le_rfl, le_rfl, fun _ => trivial⟩
theorem hkw_nodeT (a b : Tok) :
    HkSW u (nodeT (lam := lam) (K := K) (L := L) a b) (u .node) (fun _ => True) :=
  fun _ => ⟨u .node, 0, fun _ _ _ _ => le_rfl, le_rfl, fun _ => trivial⟩
theorem hkw_rleafT (c : Tok) :
    HkSW u (rleafT (lam := lam) (K := K) (L := L) c) (u .rleaf) (fun _ => True) :=
  fun _ => ⟨u .rleaf, 0, fun _ _ _ _ => le_rfl, le_rfl, fun _ => trivial⟩
theorem hkw_rnodeT (a b : Tok) :
    HkSW u (rnodeT (lam := lam) (K := K) (L := L) a b) (u .rnode) (fun _ => True) :=
  fun _ => ⟨u .rnode, 0, fun _ _ _ _ => le_rfl, le_rfl, fun _ => trivial⟩
theorem hkw_nodeE (a b : Dig lam) :
    HkSW u (nodeE (K := K) (L := L) a b) (u .node) (fun _ => True) :=
  fun _ => ⟨0, le_rfl, trivial⟩

theorem hkw_leafE (sMT : ℕ) (b : Body L) (blind : Bool) :
    HkSW u (leafE (lam := lam) (K := K) sMT b blind) (u .leaf) (fun _ => True) := by
  unfold leafE
  cases blind
  · exact fun _ => ⟨0, le_rfl, trivial⟩
  · exact SWV.bind' (hkw_leafT u sMT b) (m' := 0)
      (fun x _ => SWV.bind' (hkw_zero u (hkn_showT x.2)) (m' := 0) (fun _ _ => trivial) le_rfl)
      le_rfl

theorem hkw_leavesT (sMT : ℕ) :
    ∀ l : List (Body L), HkSW u (leavesT (lam := lam) (K := K) sMT l)
      (l.length * u .leaf) fun o => o.1.length = l.length
  | [] => rfl
  | b :: t => SWV.bind' (hkw_leafT u sMT b) (m' := t.length * u .leaf) (fun x _ => SWV.bind' (hkw_leavesT sMT t) (m' := 0) (fun r hr => by
      show (x.2 :: r.1).length = (b :: t).length
      rw [List.length_cons, List.length_cons, hr]) le_rfl) (by rw [List.length_cons, Nat.succ_mul]; omega)

theorem hkw_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool),
      HkSW u (leavesE (lam := lam) (K := K) sMT l) (l.length * u .leaf) fun o =>
        o.1.length = l.length
  | [] => rfl
  | (b, bl) :: t => SWV.bind' (hkw_leafE u sMT b bl) (m' := t.length * u .leaf) (fun x _ => SWV.bind' (hkw_leavesE sMT t) (m' := 0) (fun r hr => by
      show (x.1 :: r.1).length = ((b, bl) :: t).length
      rw [List.length_cons, List.length_cons, hr]) le_rfl) (by rw [List.length_cons, Nat.succ_mul]; omega)

theorem hkw_rleavesT :
    ∀ l : List Tok,
      HkSW u (rleavesT (lam := lam) (K := K) (L := L) l) (l.length * u .rleaf) fun o =>
        o.length = l.length
  | [] => rfl
  | c :: t => SWV.bind' (hkw_rleafT u c) (m' := t.length * u .rleaf) (fun d _ => SWV.bind' (hkw_rleavesT t) (m' := 0) (fun r hr => by
      show (d :: r).length = (c :: t).length
      rw [List.length_cons, List.length_cons, hr]) le_rfl) (by rw [List.length_cons, Nat.succ_mul]; omega)

/-- One level: n / 2 vertices above n entries; (n + 1) / 2 entries are left. -/
theorem hkw_pairUp {D : Type} {node : D → D → St lam K L D} {c : ℕ}
    (hn : ∀ a b, HkSW u (node a b) c (fun _ => True)) :
    ∀ l : List D, HkSW u (pairUp node l) (l.length / 2 * c) fun l' => l'.length = (l.length + 1) / 2
  | [] => SWV.pure (a := []) (P := fun l' => l'.length = (([] : List D).length + 1) / 2) (by simp) _
  | [a] => SWV.pure (a := [a]) (P := fun l' => l'.length = ([a].length + 1) / 2) (by simp) _
  | a :: b :: t => SWV.bind' (hn a b) (m' := t.length / 2 * c) (fun x _ => SWV.bind' (hkw_pairUp hn t) (m' := 0) (fun r hr => by
      show (x :: r).length = ((a :: b :: t).length + 1) / 2
      rw [List.length_cons, List.length_cons, List.length_cons, hr]
      omega) le_rfl) (by
      rw [List.length_cons, List.length_cons,
        show (t.length + 1 + 1) / 2 = t.length / 2 + 1 by omega, Nat.succ_mul]
      omega)

/-- All levels above n entries: at most n − 1 vertices. -/
theorem hkw_levelsM {D : Type} {node : D → D → St lam K L D} {c : ℕ}
    (hn : ∀ a b, HkSW u (node a b) c (fun _ => True)) :
    ∀ (d : ℕ) (l : List D), HkSW u (levelsM node d l) ((l.length - 1) * c) (fun _ => True)
  | 0, _ => trivial
  | d + 1, l => SWV.bind' (hkw_pairUp u hn l) (m' := ((l.length + 1) / 2 - 1) * c) (fun x hx => SWV.bind' (hx ▸ hkw_levelsM hn d x) (m' := 0) (fun _ _ => trivial) le_rfl) (by
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right _ (by omega))

theorem hkw_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    HkSW u (commitT (lam := lam) (K := K) sMT d leaf) (hkTr u d) (fun _ => True) :=
  SWV.bind' (hkw_leavesT u sMT _) (m' := (2 ^ d - 1) * u .node) (fun x hx => SWV.bind' (hkw_levelsM u (hkw_nodeT u) d x.1) (m' := 0) (fun _ _ => trivial) (by
    rw [hx, List.length_map, List.length_range]; exact le_rfl)) (by rw [List.length_map, List.length_range]; exact le_rfl)

theorem hkw_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    HkSW u (commitE (lam := lam) (K := K) sMT d leaf) (hkTr u d) (fun _ => True) :=
  SWV.bind' (hkw_leavesE u sMT _) (m' := (2 ^ d - 1) * u .node) (fun x hx => SWV.bind' (hkw_levelsM u (hkw_nodeE u) d x.1) (m' := 0) (fun _ _ => trivial) (by
    rw [hx, List.length_map, List.length_range]; exact le_rfl)) (by rw [List.length_map, List.length_range]; exact le_rfl)

theorem hkw_reqT (depthReq : ℕ) (cs : List Tok) :
    HkSW u (reqT (lam := lam) (K := K) (L := L) depthReq cs)
      (cs.length * u .rleaf + (cs.length - 1) * u .rnode) (fun _ => True) :=
  SWV.bind' (hkw_rleavesT u cs) (m' := (cs.length - 1) * u .rnode)
    (fun x hx =>
      SWV.bind' (hkw_levelsM u (hkw_rnodeT u) depthReq x) (m' := 0)
        (fun _ _ => trivial) (by rw [hx]; exact le_rfl)) le_rfl

theorem hkw_withTree {β : Type} (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} {n : ℕ} {P : β → Prop} (hk : ∀ tr, HkSW u (k tr) n P) :
    HkSW u (withTree sMT has depth leaf k) (hkTr u depth + n) P := by
  cases has with
  | true => exact SWV.bind' (hkw_commitT u sMT depth leaf) (fun tr _ => hk (some tr)) le_rfl
  | false => exact (hk none).mono (fun _ h => h) (Nat.le_add_left _ _)

/-- The trees over a component: each is charged `hkTr u d` at its depth d. A component without a
tree is charged nothing. -/
theorem hkw_withTrees {β : Type} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β} {n : ℕ}
      {P : β → Prop},
      (∀ trs, HkSW u (k trs) n P) →
      HkSW u (withTrees sMT ds leaf k) ((ds.map (hkTr u)).sum + n) P
  | [], _, _, _, _, hk => (hk []).mono (fun _ h => h) (Nat.le_add_left _ _)
  | d :: ds, leaf, _, _, _, hk =>
    SWV.bind' (hkw_commitT u sMT d (leaf 0))
      (fun tr _ => hkw_withTrees sMT ds (fun m => leaf (m + 1)) fun trs => hk (tr :: trs))
      (by rw [List.map_cons, List.sum_cons]; omega)

/-! ### Chain queries -/

section Eval
variable {β C P : Type} (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok)
  (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))

theorem hkw_fbT (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β} {n : ℕ}
    {Q : β → Prop} (hk : ∀ bl tl, HkSW u (k bl tl) n Q) :
    HkSW u (fbT t i tk us root hd hinj pl k) (u (.fb t) + n) Q :=
  fun v => ⟨u (.fb t), n, fun _ _ _ _ => le_rfl, le_rfl, fun tl => hk v tl⟩

theorem hkw_fbTw (j : ℕ) (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Blk lam K → Tok → St lam K L β}
    {n : ℕ} {Q : β → Prop} (hk : ∀ bl tl, HkSW u (k bl tl) n Q) :
    HkSW u (fbTw t j i tk us root hd hinj pl k) (u (.fb t) + n) Q :=
  fun v => ⟨u (.fb t), n, fun _ _ _ _ => le_rfl, le_rfl, fun tl => hk v tl⟩

/-- A chain query, with a search or without: all tries. -/
theorem hkw_fbG (gr : Option (GrW C P)) (chal : Blk lam K → C)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {n : ℕ} {Q : β → Prop}
    (hk : ∀ nc dd bl tl, HkSW u (k nc dd bl tl) n Q) :
    HkSW u (fbG gr chal t i tk us root hd hinj emb α k) (triesOf gr * u (.fb t) + n) Q :=
  fbG_cost (Φ := fun m x => HkSW u x m Q) gr (fun _ _ _ hab h => h.mono (fun _ h => h) hab)
    (fun _ pl _ h => hkw_fbT u t i tk us root hd hinj pl h)
    (fun _ j pl _ h => hkw_fbTw u t i tk us root hd hinj j pl h) hk

end Eval

section Eval2
variable {β C P : Type}

theorem hkw_fbSlotG (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β} {n : ℕ} {Q : β → Prop}
    (hk : ∀ nc dd bl tl, HkSW u (k nc dd bl tl) n Q) :
    HkSW u (fbSlotG gr chal t i cms x ph tk c root emb α k) (triesOf gr * u (.fb t) + n) Q := by
  cases ph <;> exact hkw_fbG u _ _ _ _ _ _ _ gr chal emb α hk

end Eval2

theorem hkw_gT {β : Type} (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Tok → St lam K L β} {n : ℕ}
    {Q : β → Prop} (hk : ∀ c, HkSW u (k c) n Q) :
    HkSW u (gT t i tk root pl k) (u (.g t) + n) Q :=
  fun _ => ⟨u (.g t), n, fun _ _ _ _ => le_rfl, le_rfl, fun c => hk c⟩

theorem hkw_eachM {σ τ : Type} {f : σ → St lam K L τ} (c : ℕ)
    (hf : ∀ a, HkSW u (f a) c (fun _ => True)) :
    ∀ l : List σ, HkSW u (eachM f l) (l.length * c) fun l' => l'.length = l.length
  | [] => rfl
  | a :: t =>
      SWV.bind' (hf a) (m' := t.length * c) (fun b _ => SWV.bind' (hkw_eachM c hf t) (m' := 0) (fun r hr => by
        show (b :: r).length = (a :: t).length
        rw [List.length_cons, List.length_cons, hr]) le_rfl) (by rw [List.length_cons, Nat.succ_mul]; omega)

/-! ### The counts, unfolded -/

section Unfold
variable (t : Tag) (Ns : ℕ) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
  (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)

theorem hkSlot_lo (hk : a.kind = .lo) (ph : Need.PhK) :
    hkSlot u t (r :: s) (a, A) (w, W) ph =
      (hkTr u w.depthJ + triesOf w.grJ * u (.fb t)) + hkSlot u t s A W ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem hkSlot_join (hk : a.kind = .sh) :
    hkSlot u t (r :: s) (a, A) (w, W) .loc =
      (hkTr u w.depthJ + u (.g t) + u .rleaf) + hkSlot u t s A W .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem hkSlot_sh (hk : a.kind = .sh) (ph : Need.PhK) (hph : ph = .first ∨ ph = .shr ∨ ph = .aft) :
    hkSlot u t (r :: s) (a, A) (w, W) ph = hkSlot u t s A W ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl | rfl <;> rfl
theorem hkShared_lo (hk : a.kind = .lo) (ph : Need.PhK) :
    hkShared u t Ns (r :: s) (a, A) (w, W) ph = hkShared u t Ns s A W ph.afterLo := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl
theorem hkShared_join (hk : a.kind = .sh) :
    hkShared u t Ns (r :: s) (a, A) (w, W) .loc =
      ((Ns - 1) * u .rnode + hkTr u w.depth0 + triesOf w.gr0 * u (.fb t)) +
        hkShared u t Ns s A W .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem hkShared_shr (hk : a.kind = .sh) :
    hkShared u t Ns (r :: s) (a, A) (w, W) .shr =
      (hkTr u w.depth0 + triesOf w.gr0 * u (.fb t)) + hkShared u t Ns s A W .shr := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl
theorem hkShared_none (hk : a.kind = .sh) (ph : Need.PhK) (hph : ph = .first ∨ ph = .aft) :
    hkShared u t Ns (r :: s) (a, A) (w, W) ph = hkShared u t Ns s A W ph := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rcases hph with rfl | rfl <;> rfl

end Unfold

/-! ### The rounds and the chains -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

section One
variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
  (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

theorem hkw_tree0 {β : Type} (m0 : a.M0) {k : Option TTree → St lam K L β} {n : ℕ}
    {P : β → Prop} (hk : ∀ tr, HkSW u (k tr) n P) :
    HkSW u (tree0 sMT a w emb m0 k) (hkTr u w.depth0 + n) P :=
  hkw_withTree u sMT _ _ _ hk

theorem hkw_slotJoin (z : SlotSt lam K Y (r :: s)) :
    HkSW u (slotJoin sMT t a w emb plJ i z) (hkTr u w.depthJ + u (.g t)) (fun _ => True) := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotJoin]
  exact hkw_withTree u sMT _ _ _ (n := u (.g t) + 0) fun _ => hkw_gT u t i _ _ _ fun _ => trivial

theorem hkw_joinM :
    ∀ zs : List (SlotSt lam K Y (r :: s)),
      HkSW u (joinM sMT t a w emb plJ i zs) (zs.length * (hkTr u w.depthJ + u (.g t)))
        fun o => o.1.length = zs.length ∧ o.2.length = zs.length
  | [] => ⟨rfl, rfl⟩
  | z :: zs =>
      SWV.bind' (hkw_slotJoin u sMT t a w emb plJ i z) (m' := zs.length * (hkTr u w.depthJ + u (.g t))) (fun z' _ => SWV.bind' (hkw_joinM zs) (m' := 0) (fun o ho => by
        show (z' :: o.1).length = (z :: zs).length ∧ (z'.2.c :: o.2).length = (z :: zs).length
        rw [List.length_cons, List.length_cons, List.length_cons, ho.1, ho.2]
        exact ⟨rfl, rfl⟩) le_rfl) (by rw [List.length_cons, Nat.succ_mul]; omega)

theorem hkw_slotLo (ph : PhT) (z : SlotSt lam K Y (r :: s)) :
    HkSW u (slotLo sMT t cms xin a w emb plJ i ph z)
      (hkTr u w.depthJ + triesOf w.grJ * u (.fb t)) (fun _ => True) := by
  obtain ⟨⟨mm, k⟩, acc⟩ := z
  dsimp only [slotLo]
  exact hkw_withTree u sMT _ _ _ (n := triesOf w.grJ * u (.fb t) + 0) fun _ =>
    hkw_fbSlotG u _ _ t i cms _ ph _ _ _ _ _ fun _ _ _ _ => trivial

end One

variable (depthReq : ℕ)

/-- All chains of a batch in which every slot works. n: the number of slots. -/
theorem hkw_chainT :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (n : ℕ),
      zs.length = n →
      HkSW u (chainT sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
        (hkShared u t n s A Ws (phK ph) + n * hkSlot u t s A Ws (phK ph)) (fun _ => True)
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | r :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, n, hz => by
      by_cases hk : a.kind = .lo
      · rw [Need.chainT_lo sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk ph,
          hkShared_lo u t n a A w Ws hk, hkSlot_lo u t a A w Ws hk, ← phK_afterLo]
        refine SWV.bind'
          (hkw_eachM u (hkTr u w.depthJ + triesOf w.grJ * u (.fb t))
            (fun z => hkw_slotLo u sMT t cms xin a w _ _ i ph z) zs)
          (fun zs' hz' => hkw_chainT s A Ws _ _ (i + 1) _ _ zs' _ n (hz'.trans hz)) (le_of_eq ?_)
        rw [hz]
        ring
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [Need.chainT_join sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk']
          show HkSW u _
            (hkShared u t n (r :: s) (a, A) (w, Ws) .loc +
              n * hkSlot u t (r :: s) (a, A) (w, Ws) .loc) (fun _ => True)
          rw [hkShared_join u t n a A w Ws hk', hkSlot_join u t a A w Ws hk']
          refine SWV.bind' (hkw_joinM u sMT t a w _ _ i zs)
            (m' := (n * u .rleaf + (n - 1) * u .rnode) +
                (hkTr u w.depth0 +
                  (triesOf w.gr0 * u (.fb t) +
                    (hkShared u t n s A Ws .shr + n * hkSlot u t s A Ws .shr))))
            (fun o ho => ?_) (le_of_eq ?_)
          · have e2 : o.2.length = n := ho.2.trans hz
            have hq := hkw_reqT (K := K) (L := L) (lam := lam) u depthReq o.2
            rw [e2] at hq
            exact SWV.bind' hq
              (fun rq _ =>
                hkw_tree0 u sMT a w _ m0 fun tr0 =>
                  hkw_fbG u _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
                    hkw_chainT s A Ws _ _ (i + 1) (.shr tl) _ _ _ n
                      (by rw [List.length_map]; exact ho.1.trans hz)) le_rfl
          · rw [hz]
            generalize n - 1 = q
            ring
        | shr tk0 =>
          rw [Need.chainT_shr sMT t cms xin depthReq a A w Ws embS embP i m0 k0 zs a0 hk' tk0]
          show HkSW u _
            (hkShared u t n (r :: s) (a, A) (w, Ws) .shr +
              n * hkSlot u t (r :: s) (a, A) (w, Ws) .shr) (fun _ => True)
          rw [hkShared_shr u t n a A w Ws hk', hkSlot_sh u t a A w Ws hk' _ (.inr (.inl rfl))]
          exact (hkw_tree0 u sMT a w _ m0
              (n := triesOf w.gr0 * u (.fb t) +
                  (hkShared u t n s A Ws .shr + n * hkSlot u t s A Ws .shr)) fun tr0 =>
                    hkw_fbG u _ _ _ _ _ _ _ _ _ _ _ fun nc dd bl tl =>
                      hkw_chainT s A Ws _ _ (i + 1) (.shr tl) _ _ _ n
                        (by rw [List.length_map]; exact hz)).mono
            (fun _ h => h) (le_of_eq (by ring))
        | first =>
          rw [Need.chainT_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inl rfl)]
          show HkSW u _
            (hkShared u t n (r :: s) (a, A) (w, Ws) .first +
              n * hkSlot u t (r :: s) (a, A) (w, Ws) .first) (fun _ => True)
          rw [hkShared_none u t n a A w Ws hk' _ (.inl rfl),
            hkSlot_sh u t a A w Ws hk' _ (.inl rfl)]
          exact hkw_chainT s A Ws _ _ (i + 1) .first _ _ _ n (by rw [List.length_map]; exact hz)
        | aft =>
          rw [Need.chainT_none sMT t cms xin depthReq a A w Ws embS embP i m0
              k0 zs a0 hk' _ (.inr rfl)]
          show HkSW u _
            (hkShared u t n (r :: s) (a, A) (w, Ws) .aft +
              n * hkSlot u t (r :: s) (a, A) (w, Ws) .aft) (fun _ => True)
          rw [hkShared_none u t n a A w Ws hk' _ (.inr rfl),
            hkSlot_sh u t a A w Ws hk' _ (.inr (.inr rfl))]
          exact hkw_chainT s A Ws _ _ (i + 1) .aft _ _ _ n (by rw [List.length_map]; exact hz)

end Rounds

/-! ### One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

theorem hkw_proveB (fl : ℕ → Bool) (xs : List (Option Y)) :
    HkSW u (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      (hkShared u t xs.length Q.loc.shape Q.ann wq.sh .first +
        xs.length * hkSlot u t Q.loc.shape Q.ann wq.sh .first)
      (fun _ => True) := by
  unfold proveB
  refine SWV.bind' (hkw_zero u (hkn_drawT wp.coin0))
    (fun c0 _ =>
      SWV.bind' (hkw_eachM u 0 (fun a => hkw_zero u (hkn_initSlot Q H wp w sFS c0 a)) xs)
        (fun zs hz =>
          SWV.bind' (hkw_chainT u sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _ xs.length hz)
            (m' := 0)
            (fun out _ => hkw_zero u (hkn_finishAll Q H wq wp trees w fl c0 out.2 0 out.1)) le_rfl)
        le_rfl) (le_of_eq ?_)
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

end Prove

/-! ### The committer's program -/

section Star
variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

theorem hkw_nodeP' (i : I) : HkSW u (nodeP' W WP p i) (hkTr u W.depth) (fun _ => True) :=
  SWV.bind' (hkw_zero u (hkn_drawT WP.ri)) (m' := hkTr u W.depth)
    (fun _ _ => SWV.bind' (hkw_commitE u p.sMT W.depth _) (m' := 0) (fun _ _ => trivial) le_rfl)
    (le_of_eq (Nat.zero_add _))

theorem hkw_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    HkSW u (proveT W WP p tree i r) (hkProve1 u .test W.T) (fun _ => True) :=
  SWV.bind' (hkw_proveB u p.sMT p.sFS Tag.test _ _ W.T WP.T _ _ _ W.depthReq _ _ _ [some ()]) (m' := 0) (fun _ _ => trivial) (le_of_eq (by
    show _ + 1 * _ + 0 = _
    rw [Nat.one_mul, Nat.add_zero]
    rfl))

theorem hkw_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    HkSW u (proveLk W WP p root tree i r₀ r) (hkProve1 u .link W.Lk) (fun _ => True) :=
  SWV.bind' (hkw_proveB u p.sMT p.sFS Tag.link _ _ W.Lk WP.Lk _ _ _ W.depthReq _ _ _ [some ()]) (m' := 0) (fun _ _ => trivial) (le_of_eq (by
    show _ + 1 * _ + 0 = _
    rw [Nat.one_mul, Nat.add_zero]
    rfl))

theorem hkw_leavesC (i : I) (root : Node lam L) :
    ∀ n, HkSW u (leavesC W WP p i root n)
      (n * (hkTr u W.depth + hkProve1 u .link W.Lk)) (fun _ => True)
  | 0 => trivial
  | n + 1 =>
    SWV.bind' (hkw_nodeP' u W WP p i)
      (m' := hkProve1 u .link W.Lk + n * (hkTr u W.depth + hkProve1 u .link W.Lk))
      (fun nd _ =>
        SWV.bind' (hkw_proveLk u W WP p _ _ _ _ _)
          (fun _ _ => SWV.bind' (hkw_leavesC i root n) (m' := 0) (fun _ _ => trivial) le_rfl)
          le_rfl)
      (le_of_eq (by rw [Nat.succ_mul]; omega))

/-- The committer's program. -/
theorem hkw_Cp (i : I) : HkSW u (Cp W WP p i) (hkCom W p u) (fun _ => True) :=
  SWV.bind' (hkw_nodeP' u W WP p i)
    (m' := hkProve1 u .test W.T + (p.M + 1) * (hkTr u W.depth + hkProve1 u .link W.Lk))
    (fun root _ =>
      SWV.bind' (hkw_proveT u W WP p _ _ _)
        (fun _ _ =>
          SWV.bind' (hkw_leavesC u W WP p i root (p.M + 1)) (m' := 0) (fun _ _ => trivial) le_rfl)
        le_rfl)
    (le_of_eq (by unfold hkCom; omega))

/-- The committer, the ghost names written back. -/
theorem hk_costV_C (i : I) : (C W WP p i).CostBoundV (fun o _ _ => u o) (hkCom W p u) :=
  costV_realQ_pre (fun o _ _ => u o)
    _ _ ((((hkw_Cp u W WP p i).erase []).map _).weight fun o _ _ => by cases o <;> exact le_rfl)

end Star

/-! ## Two small tools on oracle algorithms -/

theorem hk_query_of_cost {S : OSpec} {α : Type} {c : OComp S α} :
    ∀ {t : ℕ}, c.CostBound (fun _ => 1) t → c.QueryBound t := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro t ⟨t', rfl, h⟩
    rw [Nat.add_comm]
    exact fun r => ih r (h r)

theorem hk_onlyQ_of_cost {S : OSpec} {α : Type} {w : S.ι → ℕ} {P : (o : S.ι) → S.Dom o → Prop}
    (hw : ∀ o q, w o = 0 → P o q) {c : OComp S α} :
    c.CostBound w 0 → OnlyQ P c := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h r => ih r (h r)
  | query o q k ih =>
    rintro ⟨t', e, h⟩
    have e1 : w o = 0 := by omega
    have e2 : t' = 0 := by omega
    subst e2
    exact ⟨hw o q e1, fun r => ih r (h r)⟩

/-! ## The counts at two prices -/

theorem hkTr_zero {u : OracleName → ℕ} (h1 : u .leaf = 0) (h2 : u .node = 0) (d : ℕ) : hkTr u d = 0 := by
  unfold hkTr
  rw [h1, h2, Nat.mul_zero, Nat.mul_zero]

section Zero
variable {u : OracleName → ℕ} {t : Tag} (h1 : u .leaf = 0) (h2 : u .node = 0) (h3 : u .rleaf = 0)
  (h4 : u .rnode = 0) (h5 : u (.g t) = 0) (h6 : u (.fb t) = 0)
include h1 h2 h3 h5 h6

theorem hkSlot_zero :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ph : Need.PhK), hkSlot u t s A W ph = 0
  | [], _, _, _ => rfl
  | r :: s, (a, A), (w, W), ph => by
    by_cases hk : a.kind = .lo
    · rw [hkSlot_lo u t a A w W hk, hkSlot_zero s A W, hkTr_zero h1 h2, h6, Nat.mul_zero]
    · have hk' : a.kind = .sh := by
        cases h : a.kind with
        | lo => exact absurd h hk
        | sh => rfl
      cases ph with
      | loc => rw [hkSlot_join u t a A w W hk', hkSlot_zero s A W, hkTr_zero h1 h2, h5, h3]
      | first => rw [hkSlot_sh u t a A w W hk' _ (.inl rfl), hkSlot_zero s A W]
      | shr => rw [hkSlot_sh u t a A w W hk' _ (.inr (.inl rfl)), hkSlot_zero s A W]
      | aft => rw [hkSlot_sh u t a A w W hk' _ (.inr (.inr rfl)), hkSlot_zero s A W]

omit h3 h5 in
include h4 in
theorem hkShared_zero (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ph : Need.PhK), hkShared u t Ns s A W ph = 0
  | [], _, _, _ => rfl
  | r :: s, (a, A), (w, W), ph => by
    by_cases hk : a.kind = .lo
    · rw [hkShared_lo u t Ns a A w W hk, hkShared_zero Ns s A W]
    · have hk' : a.kind = .sh := by
        cases h : a.kind with
        | lo => exact absurd h hk
        | sh => rfl
      cases ph with
      | loc =>
        rw [hkShared_join u t Ns a A w W hk', hkShared_zero Ns s A W, hkTr_zero h1 h2, h4, h6,
          Nat.mul_zero, Nat.mul_zero]
      | shr =>
        rw [hkShared_shr u t Ns a A w W hk', hkShared_zero Ns s A W,
          hkTr_zero h1 h2, h6, Nat.mul_zero]
      | first => rw [hkShared_none u t Ns a A w W hk' _ (.inl rfl), hkShared_zero Ns s A W]
      | aft => rw [hkShared_none u t Ns a A w W hk' _ (.inr rfl), hkShared_zero Ns s A W]

end Zero

theorem hkTr_one (d : ℕ) : hkTr (fun _ => 1) d = Need.tr d := by
  unfold hkTr Need.tr
  rw [Nat.mul_one, Nat.mul_one]

theorem hk_tries {C P : Type} (g : Option (GrW C P)) : triesOf g * 1 = moreOf g * 1 + 1 := by
  cases g <;> simp [triesOf, moreOf]

theorem hkSlot_one (t : Tag) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ph : Need.PhK),
      hkSlot (fun _ => 1) t s A W ph = cSlotW 1 (fun _ => 1) s A W i ph
  | [], _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), i, ph => by
    by_cases hk : a.kind = .lo
    · rw [hkSlot_lo _ t a A w W hk, OneCall.cSlotW_lo _ _ a A w W i hk,
        hkSlot_one t s A W (i + 1), hkTr_one, hk_tries]
      rfl
    · have hk' : a.kind = .sh := by
        cases h : a.kind with
        | lo => exact absurd h hk
        | sh => rfl
      cases ph with
      | loc =>
        rw [hkSlot_join _ t a A w W hk', OneCall.cSlotW_join _ _ a A w W i hk',
          hkSlot_one t s A W (i + 1), hkTr_one]
        rfl
      | first =>
        rw [hkSlot_sh _ t a A w W hk' _ (.inl rfl),
          OneCall.cSlotW_sh _ _ a A w W i hk' _ (.inl rfl), hkSlot_one t s A W (i + 1)]
      | shr =>
        rw [hkSlot_sh _ t a A w W hk' _ (.inr (.inl rfl)),
          OneCall.cSlotW_sh _ _ a A w W i hk' _ (.inr (.inl rfl)), hkSlot_one t s A W (i + 1)]
      | aft =>
        rw [hkSlot_sh _ t a A w W hk' _ (.inr (.inr rfl)),
          OneCall.cSlotW_sh _ _ a A w W i hk' _ (.inr (.inr rfl)), hkSlot_one t s A W (i + 1)]

theorem hkShared_one (t : Tag) (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ph : Need.PhK),
      hkShared (fun _ => 1) t Ns s A W ph = cSharedW 1 (fun _ => 1) Ns s A W i ph
  | [], _, _, _, _ => rfl
  | r :: s, (a, A), (w, W), i, ph => by
    by_cases hk : a.kind = .lo
    · rw [hkShared_lo _ t Ns a A w W hk, OneCall.cSharedW_lo _ _ _ a A w W i hk,
        hkShared_one t Ns s A W (i + 1)]
    · have hk' : a.kind = .sh := by
        cases h : a.kind with
        | lo => exact absurd h hk
        | sh => rfl
      cases ph with
      | loc =>
        rw [hkShared_join _ t Ns a A w W hk', OneCall.cSharedW_join _ _ _ a A w W i hk',
          hkShared_one t Ns s A W (i + 1), hkTr_one, hk_tries, Nat.mul_one]
        rfl
      | shr =>
        rw [hkShared_shr _ t Ns a A w W hk', OneCall.cSharedW_shr _ _ _ a A w W i hk',
          hkShared_one t Ns s A W (i + 1), hkTr_one, hk_tries]
        rfl
      | first =>
        rw [hkShared_none _ t Ns a A w W hk' _ (.inl rfl),
          OneCall.cSharedW_none _ _ _ a A w W i hk' _ (.inl rfl), hkShared_one t Ns s A W (i + 1)]
      | aft =>
        rw [hkShared_none _ t Ns a A w W hk' _ (.inr rfl),
          OneCall.cSharedW_none _ _ _ a A w W i hk' _ (.inr rfl), hkShared_one t Ns s A W (i + 1)]

/-! ## The statements -/

theorem honestKey_cost : Spec.honestKey_cost := fun _ _ _ _ W WP p u i =>
  (hk_costV_C u W WP p i).toCost fun _ _ _ => le_rfl

theorem honestKey_typed : Spec.honestKey_typed := fun I X lam L W WP p i =>
  hk_query_of_cost (honestKey_cost I X lam L W WP p (fun _ => 1) i)

theorem honestKey_notOnl : Spec.honestKey_notOnl := fun I X lam L W WP p i => by
  have h := honestKey_cost I X lam L W WP p (fun o => if o = OracleName.fb Tag.onl then 1 else 0) i
  have z : hkCom W p (fun o => if o = OracleName.fb Tag.onl then 1 else 0) = 0 := by
    unfold hkCom hkProve1
    rw [hkTr_zero rfl rfl, hkSlot_zero rfl rfl rfl rfl rfl, hkSlot_zero rfl rfl rfl rfl rfl,
      hkShared_zero rfl rfl rfl rfl, hkShared_zero rfl rfl rfl rfl, Nat.mul_zero]
  rw [z] at h
  refine hk_onlyQ_of_cost (fun o _ ho e => ?_) h
  rw [if_pos e] at ho
  exact absurd ho (by decide)

theorem honestKey_strings : Spec.honestKey_strings := fun I X lam L W WP p Wn m i hl => by
  have e : m.blocks = blk W.K := funext fun o => honestKey_blocks I X L lam W.K m hl o
  have h := honestKey_cost I X lam L W WP p (blk W.K) i
  rw [← e] at h
  have h2 := queryBound_overOne_of_cost m
    ((C W WP p i).bind fun o => .pure ((o.1, linksOf (keyOf o.2.1)), o.2)) _
    (OComp.CostBound.bind (t := 0) (fun _ => OComp.CostBound.pure _ 0) h)
  rw [e] at h2
  exact h2

theorem honestKey_sum : Spec.honestKey_sum := fun _ _ _ _ W p => by
  unfold hkCom hkProve1 cCBW cProve1W
  rw [hkTr_one, hkSlot_one .test _ _ _ 0, hkSlot_one .link _ _ _ 0,
    hkShared_one .test 1 _ _ _ 0, hkShared_one .link 1 _ _ _ 0]

end Compile.Batch
