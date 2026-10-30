-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/GhostRouted.lean: for every well-formed wire record (`W.OKG`), the committer's and the
prover's programs `Cp`, `Pp` are routed (`RoutedT`, `Spec.routedCp`, `Spec.routedPp` of
Compile/Batch/SpecGhost.lean). With it: `Spec.argB_via` (words of this library: lean/GLOSSARY.md).
Routed means: they query `fb t` only where the plain part in the query contains the nonce for 0, or
the component that the query holds has no proof-of-work record; and they query the ghost name
`fbw t k` only where the plain part contains the nonce for k + 1.
The programs write attempt 0 of a search over nonces as a query to `fb t` and attempt k + 1 as a
query to `fbw t k`. The query of a local round holds the slot's component, that of a shared round
the shared one.
Of `W.OKG` the proof uses only that the proof-of-work records are well-formed, round by round
(`GrLaw`, `GrLawB`). So the same holds for a wire record that has no such record at all and meets no
other condition (`W.NoTest`, which is not in this library): `rt_Cp`, `rt_Pp`, `C_via_law`,
`P_via_law` (in this file, under `GrLawB`), and `argB_via_law`, which is not in this library.
The proof is by structural induction on the programs; `RoutedT` is preserved by bind
(`RoutedT.bind`). The programs on trees, openings and coins (Compile/Batch/TokTree.lean,
Compile/Batch/Prover.lean) query neither `fb` nor `fbw`. What remains is the search over nonces:
    `rt_fbW`   attempt number j + 1 writes the nonce for j + 1 and queries `fbw t j`; the numbers
               stay within `g.more`, so the nonce is read back (`GrW.OK.get_put`)
    `ClsAt`    the invariant of the induction over the rounds (`clsPB`)

Notation: `fb t` (`OracleName`, Compile/Batch/Oracles.lean): Fiat-Shamir for the protocol t; `fbw t k`: an
oracle of the analysis, never queried by the scheme: proof-of-work attempt k + 1 is written as a
query to `fbw t k`, and `realQ` maps it back to `fb t`; the three protocols: Test, Link, Batch
(`BatchProtocol`, Iop/Batch.lean), with the tags `Tag.test`, `.link`, `.onl` and the wire records `W.T`,
`W.Lk`, `W.B`; `clsPB s A Ws pl` (Compile/Batch/SpecGhost.lean): the number that the nonce in a
plain part denotes; 0 if the component has no proof-of-work bits; `shW W t`: the wire records of the
rounds of a protocol; `g`: a `GrW C P` (Iop/BatchWire.lean), a proof-of-work record; `g.more`: the
honest prover tries the nonces 0, .., more; `g.put`: the plain part with the nonce for the number k
written over its nonce; `g.get`: the number for which the nonce of a plain part stands; `g.ok`: the
test: all test bits are 0; 0 and J in `gr0`, `grJ`, `P0`, `Pj`: of the shared component m_0, of a
slot's component m_j (`WireRB`, Iop/BatchWire.lean; `RAnn`, Iop/Batch.lean); `St lam K L α`
(Compile/Batch/TokTree.lean): `Step (spec lam K L) (split lam K L) α`, a token program (`Step`,
Rom/Defer.lean); `Tok`: `ℕ`.

Limits: see the header of Compile/Batch/SpecGhost.lean. The provers with no query for an empty slot
(`proveBU`, Compile/Batch/ProverU.lean), with stops, and the forms of the scheme with a seed are not
covered here.

The induction follows that of Compile/Batch/NeedBlocks.lean.
-/
import Compile.Batch.Ghost

noncomputable section

namespace Compile.Batch
open Iop Rom Compile.GlueB

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L}

/-- a routed program followed by routed programs is routed -/
theorem RoutedT.bind {α β : Type} {c : St lam W.K L α} {g : α → St lam W.K L β}
    (h : RoutedT W c) (hg : ∀ a, RoutedT W (g a)) : RoutedT W (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih =>
      cases o with
      | fb t => exact ⟨h.1, fun r => ih r (h.2 r)⟩
      | fbw t j => exact ⟨h.1, fun r => ih r (h.2 r)⟩
      | leaf => exact fun r => ih r (h r)
      | node => exact fun r => ih r (h r)
      | rleaf => exact fun r => ih r (h r)
      | rnode => exact fun r => ih r (h r)
      | g t => exact fun r => ih r (h r)
      | ann => exact fun r => ih r (h r)
      | other => exact fun r => ih r (h r)
  | fresh ℓ k ih => exact fun u => ih u (h u)
  | marked o t us pt inj k ih =>
      cases o with
      | fb t' => exact ⟨h.1, fun v u => ih v u (h.2 v u)⟩
      | fbw t' j => exact ⟨h.1, fun v u => ih v u (h.2 v u)⟩
      | leaf => exact fun v u => ih v u (h v u)
      | node => exact fun v u => ih v u (h v u)
      | rleaf => exact fun v u => ih v u (h v u)
      | rnode => exact fun v u => ih v u (h v u)
      | g t' => exact fun v u => ih v u (h v u)
      | ann => exact fun v u => ih v u (h v u)
      | other => exact fun v u => ih v u (h v u)
  | reveal ts k ih => exact fun vs => ih vs (h vs)

namespace Ghost

variable (W)

local notation "Rt" => RoutedT W

theorem rt_pure {α : Type} (a : α) : Rt (Step.pure a : St lam W.K L α) := trivial

/-! ## Trees, openings, coins: neither fb nor fbw -/

theorem rt_leafT (sMT : ℕ) (b : Body L) : Rt (leafT (lam := lam) (K := W.K) sMT b) := fun _ _ _ =>
  trivial
theorem rt_nodeT (a b : Tok) : Rt (nodeT (lam := lam) (K := W.K) (L := L) a b) := fun _ _ => trivial

theorem rt_leavesT (sMT : ℕ) : ∀ l : List (Body L), Rt (leavesT (lam := lam) (K := W.K) sMT l)
  | [] => trivial
  | b :: t => (rt_leafT W sMT b).bind fun _ => (rt_leavesT sMT t).bind fun _ => trivial

theorem rt_pairUp {D : Type} {node : D → D → St lam W.K L D} (hn : ∀ a b, Rt (node a b)) :
    ∀ l : List D, Rt (pairUp node l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => (hn a b).bind fun _ => (rt_pairUp hn t).bind fun _ => trivial

theorem rt_levelsM {D : Type} {node : D → D → St lam W.K L D} (hn : ∀ a b, Rt (node a b)) :
    ∀ (d : ℕ) (l : List D), Rt (levelsM node d l)
  | 0, _ => trivial
  | d + 1, l => (rt_pairUp W hn l).bind fun u => (rt_levelsM hn d u).bind fun _ => trivial

theorem rt_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    Rt (commitT (lam := lam) (K := W.K) sMT d leaf) :=
  (rt_leavesT W sMT _).bind fun x => (rt_levelsM W (rt_nodeT W) d x.1).bind fun _ => trivial

theorem rt_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    Rt (openT (lam := lam) (K := W.K) (L := L) t j a) := fun _ => trivial
theorem rt_showT (t : Tok) : Rt (showT (lam := lam) (K := W.K) (L := L) t) := fun _ => trivial
theorem rt_rleafT (c : Tok) : Rt (rleafT (lam := lam) (K := W.K) (L := L) c) := fun _ _ => trivial
theorem rt_rnodeT (a b : Tok) : Rt (rnodeT (lam := lam) (K := W.K) (L := L) a b) := fun _ _ =>
  trivial

theorem rt_rleavesT : ∀ l : List Tok, Rt (rleavesT (lam := lam) (K := W.K) (L := L) l)
  | [] => trivial
  | c :: t => (rt_rleafT W c).bind fun _ => (rt_rleavesT t).bind fun _ => trivial

theorem rt_reqT (d : ℕ) (cs : List Tok) : Rt (reqT (lam := lam) (K := W.K) (L := L) d cs) :=
  (rt_rleavesT W cs).bind fun ls => (rt_levelsM W (rt_rnodeT W) d ls).bind fun _ => trivial

theorem rt_leafE (sMT : ℕ) (b : Body L) (blind : Bool) :
    Rt (leafE (lam := lam) (K := W.K) sMT b blind) := by
  unfold leafE
  cases blind
  · exact fun _ => trivial
  · exact (rt_leafT W sMT b).bind fun x => (rt_showT W x.2).bind fun _ => trivial

theorem rt_nodeE (a b : Dig lam) : Rt (nodeE (K := W.K) (L := L) a b) := fun _ => trivial

theorem rt_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool), Rt (leavesE (lam := lam) (K := W.K) sMT l)
  | [] => trivial
  | (b, bl) :: t => (rt_leafE W sMT b bl).bind fun _ => (rt_leavesE sMT t).bind fun _ => trivial

theorem rt_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    Rt (commitE (lam := lam) (K := W.K) sMT d leaf) :=
  (rt_leavesE W sMT _).bind fun x => (rt_levelsM W (rt_nodeE W) d x.1).bind fun _ => trivial

theorem rt_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    Rt (openE (K := W.K) (L := L) t j a) := by
  unfold openE
  cases t.salts.getD j none with
  | none => trivial
  | some s => exact fun _ => trivial

theorem rt_drawT {β : Type} (e : Enum β) : Rt (drawT (lam := lam) (K := W.K) (L := L) e) := fun _ =>
  trivial

theorem rt_eachM {σ τ : Type} {f : σ → St lam W.K L τ} (hf : ∀ a, Rt (f a)) :
    ∀ l : List σ, Rt (eachM f l)
  | [] => trivial
  | a :: t => (hf a).bind fun _ => (rt_eachM hf t).bind fun _ => trivial

theorem rt_withTree {β : Type} (sMT : ℕ) (has : Bool) (depth : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam W.K L β} (hk : ∀ tr, Rt (k tr)) :
    Rt (withTree sMT has depth leaf k) := by
  cases has
  · exact hk none
  · exact (rt_commitT W sMT depth leaf).bind fun tr => hk (some tr)

theorem rt_withTrees {β : Type} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam W.K L β},
      (∀ trs, Rt (k trs)) → Rt (withTrees sMT ds leaf k)
  | [], _, _, hk => hk []
  | d :: ds, leaf, _, hk =>
    (rt_commitT W sMT d (leaf 0)).bind fun tr =>
      rt_withTrees sMT ds (fun n => leaf (n + 1)) fun trs => hk (tr :: trs)

theorem rt_gT {β : Type} (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Tok → St lam W.K L β} (hk : ∀ c, Rt (k c)) :
    Rt (gT t i tk root pl k) := fun _ c => hk c

theorem rt_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, Rt (opensComp (K := W.K) (L := L) dec posAt o tr isRead f js)
  | [] => trivial
  | j :: js => (rt_opensComp dec posAt o tr isRead f js).bind fun f' => by
      show Rt (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => trivial
      | some p =>
        show Rt (if isRead p then _ else _)
        cases isRead p
        · trivial
        · exact (rt_openT W tr j _).bind fun _ => trivial

theorem rt_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Rt (opensOpt (K := W.K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => trivial
  | some tr => exact rt_opensComp W dec posAt o tr isRead f _

theorem rt_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      Rt (opensTrees (K := W.K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    (rt_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      rt_opensComp W dec (posAt k) o tr isRead f' _

theorem rt_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      Rt (opensB (L := L) s A Ws τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, Ws), (_, _, τ), tjs, t0s, _ =>
      (rt_opensOpt W _ _ _ _ _ _ _).bind fun _ =>
        (rt_opensOpt W _ _ _ _ _ _ _).bind fun _ =>
          (rt_opensB s A Ws τ tjs.tail t0s.tail _).bind fun _ => trivial

theorem rt_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos, Rt (opensExtB (K := W.K) (L := L) we y trees isRead ps)
  | [] => trivial
  | p :: ps => (rt_opensExtB we y trees isRead ps).bind fun f => by
      show Rt (if isRead p then
          (openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)).bind
            fun op => Step.pure (@Function.update _ _ we.dec f p (some op)) else Step.pure f)
      cases isRead p
      · trivial
      · exact (rt_openE W _ _ _).bind fun _ => trivial

/-! ## The search over nonces -/

section Loop
variable {β C P : Type} (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))

theorem rt_fbT {pl : PlainPart (shapeOf L t) (annOf L t)} (hc : clsPB _ _ (shW W t) pl = 0)
    {k : Blk lam W.K → Tok → St lam W.K L β} (hk : ∀ bl tl, Rt (k bl tl)) :
    Rt (fbT t i tk us root hd hinj pl k) :=
  ⟨fun _ _ => hc, hk⟩

theorem rt_fbTw (j : ℕ) {pl : PlainPart (shapeOf L t) (annOf L t)} (hc : clsPB _ _ (shW W t) pl = j + 1)
    {k : Blk lam W.K → Tok → St lam W.K L β} (hk : ∀ bl tl, Rt (k bl tl)) :
    Rt (fbTw t j i tk us root hd hinj pl k) :=
  ⟨fun _ _ => hc, hk⟩

variable (g : GrW C P) (chal : Blk lam W.K → C) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)

/-- The attempts after the first are routed, under `hp`, `hk` and j + 1 + n = `g.more`. -/
theorem rt_fbW (hp : ∀ m, m ≤ g.more → clsPB _ _ (shW W t) (emb (g.put m α)) = m)
    {k : ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} (hk : ∀ m dd bl tl, Rt (k m dd bl tl)) :
    ∀ (n j : ℕ) (dd : List Tok),
      j + 1 + n = g.more → Rt (fbW g chal t i tk us root hd hinj emb α k n j dd)
  | 0, j, dd, e =>
    rt_fbTw W t i tk us root hd hinj j (hp (j + 1) (by omega)) fun bl tl => hk _ _ _ _
  | n + 1, j, dd, e => rt_fbTw W t i tk us root hd hinj j (hp (j + 1) (by omega)) fun bl tl => by
      show Rt (if g.ok (chal bl) then _ else _)
      cases g.ok (chal bl)
      · exact rt_fbW hp hk n (j + 1) (tl :: dd) (by omega)
      · exact hk _ _ _ _

/-- The whole search is routed, under `hp`, `hk`. -/
theorem rt_fbTG (hp : ∀ m, m ≤ g.more → clsPB _ _ (shW W t) (emb (g.put m α)) = m)
    {k : ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β} (hk : ∀ m dd bl tl, Rt (k m dd bl tl)) :
    Rt (fbTG g chal t i tk us root hd hinj emb α k) := by
  unfold fbTG
  split
  · exact rt_fbT W t i tk us root hd hinj (hp 0 (Nat.zero_le _)) fun bl tl => hk _ _ _ _
  · rename_i n hn
    refine rt_fbT W t i tk us root hd hinj (hp 0 (Nat.zero_le _)) fun bl tl => ?_
    show Rt (if g.ok (chal bl) then _ else _)
    cases g.ok (chal bl)
    · exact rt_fbW W t i tk us root hd hinj g chal emb α hp hk n 0 [tl] (by omega)
    · exact hk _ _ _ _

/-- `fbG` is routed, with proof-of-work bits or without, under `h0`, `hp`, `hk`. -/
theorem rt_fbG (gr : Option (GrW C P)) (h0 : gr = none → clsPB _ _ (shW W t) (emb α) = 0)
    (hp : ∀ g, gr = some g → ∀ m, m ≤ g.more → clsPB _ _ (shW W t) (emb (g.put m α)) = m)
    {k : Option ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β}
    (hk : ∀ m dd bl tl, Rt (k m dd bl tl)) :
    Rt (fbG gr chal t i tk us root hd hinj emb α k) := by
  cases gr with
  | none => exact rt_fbT W t i tk us root hd hinj (h0 rfl) fun bl tl => hk _ _ _ _
  | some g =>
    exact rt_fbTG W t i tk us root hd hinj g chal emb α (hp g rfl)
      (k := fun m => k (some m)) fun m dd bl tl => hk (some m) dd bl tl

theorem rt_fbSlotG (gr : Option (GrW C P)) (cms : List (Dig lam)) (x : Option X) (ph : PhT)
    (c : Tok) (h0 : gr = none → clsPB _ _ (shW W t) (emb α) = 0)
    (hp : ∀ g, gr = some g → ∀ m, m ≤ g.more → clsPB _ _ (shW W t) (emb (g.put m α)) = m)
    {k : Option ℕ → List Tok → Blk lam W.K → Tok → St lam W.K L β}
    (hk : ∀ m dd bl tl, Rt (k m dd bl tl)) :
    Rt (fbSlotG gr chal t i cms x ph tk c root emb α k) := by
  cases ph <;> exact rt_fbG W t i _ _ root _ _ chal emb α gr h0 hp hk

end Loop

/-! ## The rounds -/

/-- The invariant of the induction over the rounds: `embP` keeps the number that a nonce
represents. -/
def ClsAt (t : Tag) {s : Shape} {A : RoundSplits s} (Ws : RoundsQueryLayout lam W.K s A)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) : Prop :=
  ∀ z, clsPB _ _ (shW W t) (embP z) = clsPB s A Ws z

/-- The proof-of-work records are well-formed (`GrW.OK`), round by round: all that the proof uses of
the conditions on a wire record. -/
def GrLaw {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → Prop
  | [], _, _ => True
  | _ :: s, (_, A), (w, Ws) =>
    ((∀ g, w.gr0 = some g → g.OK) ∧ ∀ g, w.grJ = some g → g.OK) ∧ GrLaw s A Ws

theorem GrLaw.of_okg {K : ℕ} :
    ∀ {s : Shape} {A : RoundSplits s} {Ws : RoundsQueryLayout lam K s A}, RoundsQueryLayout.OKG s A Ws → GrLaw s A Ws
  | [], _, _, _ => trivial
  | _ :: _, (_, _), (_, _), h => ⟨⟨h.1.gr0_ok, h.1.grJ_ok⟩, GrLaw.of_okg h.2⟩

/-- `GrLaw` for the three protocols -/
structure GrLawB : Prop where
  T : GrLaw _ _ W.T.sh
  Lk : GrLaw _ _ W.Lk.sh
  B : GrLaw _ _ W.B.sh

variable {W} in
theorem GrLawB.of_okg (h : W.OKG) : GrLawB W := ⟨.of_okg h.T.sh, .of_okg h.Lk.sh, .of_okg h.B.sh⟩

section Round
variable {W} {t : Tag} {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam W.K r a} {Ws : RoundsQueryLayout lam W.K s A} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)}
  (hE : ClsAt W t (s := r :: s) (A := (a, A)) (w, Ws) embP)
include hE

theorem ClsAt.tail : ClsAt W t Ws fun z => embP (.inr z) := fun z => hE (.inr z)

theorem clsJ_none (h : w.grJ = none) (α : a.Pj) :
    clsPB _ _ (shW W t) (embP (.inl (.inr α))) = 0 := by
  rw [hE]
  show (match w.grJ with | none => 0 | some g => g.get α) = 0
  rw [h]

theorem clsJ_put (hw : ∀ g, w.grJ = some g → g.OK) (g : GrW r.Chal a.Pj) (h : w.grJ = some g)
    (α : a.Pj) (m : ℕ) (hm : m ≤ g.more) :
    clsPB _ _ (shW W t) (embP (.inl (.inr (g.put m α)))) = m := by
  rw [hE]
  show (match w.grJ with | none => 0 | some g' => g'.get (g.put m α)) = m
  rw [h]
  exact (hw g h).get_put m α hm

theorem cls0_none (h : w.gr0 = none) (α : a.P0) :
    clsPB _ _ (shW W t) (embP (.inl (.inl α))) = 0 := by
  rw [hE]
  show (match w.gr0 with | none => 0 | some g => g.get α) = 0
  rw [h]

theorem cls0_put (hw : ∀ g, w.gr0 = some g → g.OK) (g : GrW r.Chal a.P0) (h : w.gr0 = some g)
    (α : a.P0) (m : ℕ) (hm : m ≤ g.more) :
    clsPB _ _ (shW W t) (embP (.inl (.inl (g.put m α)))) = m := by
  rw [hE]
  show (match w.gr0 with | none => 0 | some g' => g'.get (g.put m α)) = m
  rw [h]
  exact (hw g h).get_put m α hm

end Round

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem rt_slotLo {r : Round} {s : Shape} {a : RAnn r} {A : RoundSplits s} {w : WireRB lam W.K r a}
    {Ws : RoundsQueryLayout lam W.K s A} {embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)}
    (hE : ClsAt W t (s := r :: s) (A := (a, A)) (w, Ws) embP) (hw : ∀ g, w.grJ = some g → g.OK)
    (emb : (p : r.Pos) → r.Sym p → Body L) (i : ℕ) (ph : PhT) (z : SlotSt lam W.K Y (r :: s)) :
    Rt (slotLo sMT t cms xin a w emb (fun α => embP (.inl (.inr α))) i ph z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  simp only [slotLo]
  refine rt_withTree W sMT _ _ _ fun tr => ?_
  refine rt_fbSlotG W t i _ _ w.chal (fun α => embP (.inl (.inr α))) _ w.grJ cms _ ph _
    (fun h => clsJ_none hE h _) (fun g h m hm => clsJ_put hE hw g h _ m hm) ?_
  exact fun _ _ _ _ => trivial

theorem rt_slotJoin {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam W.K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (z : SlotSt lam W.K Y (r :: s)) :
    Rt (slotJoin sMT t a w emb plJ i z) := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  simp only [slotJoin]
  refine rt_withTree W sMT _ _ _ fun tr => ?_
  refine rt_gT W t i _ _ _ ?_
  exact fun _ => trivial

theorem rt_joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam W.K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam W.K Y (r :: s)), Rt (joinM sMT t a w emb plJ i zs)
  | [] => trivial
  | z :: zs =>
    (rt_slotJoin W sMT t a w emb plJ i z).bind fun _ =>
      (rt_joinM a w emb plJ i zs).bind fun _ => trivial

theorem rt_tree0 {β : Type} {r : Round} (a : RAnn r) (w : WireRB lam W.K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0)
    {k : Option TTree → St lam W.K L β} (hk : ∀ tr, Rt (k tr)) : Rt (tree0 sMT a w emb m0 k) :=
  rt_withTree W sMT _ _ _ hk

/-- All chains of a batch are routed, under `GrLaw` and `ClsAt`. -/
theorem rt_chainT (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam W.K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam W.K Y s)) (a0 : Acc0),
      GrLaw s A Ws → ClsAt W t Ws embP →
      Rt (chainT sMT t cms xin depthReq s A Ws embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, _, _, _, _ => trivial
  | _ :: s, (a, A), (w, Ws), embS, embP, i, ph, (m0, k0), zs, a0, hW, hE => by
      simp only [chainT]
      split
      · exact (rt_eachM W (rt_slotLo W sMT t cms xin hE hW.1.2 _ i _) zs).bind
          fun zs' => rt_chainT depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)
      · exact (rt_joinM W sMT t a w _ _ i zs).bind fun o =>
            (rt_reqT W depthReq o.2).bind fun rq => rt_tree0 W sMT a w _ m0 fun tr0 =>
          rt_fbG W t i _ _ _ _ _ w.chal (fun α => embP (.inl (.inl α))) _ w.gr0
              (fun h => cls0_none hE h _)
              (fun g h m hm => cls0_put hE hW.1.1 g h _ m hm) fun _ _ _ _ =>
            rt_chainT depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)
      · exact rt_tree0 W sMT a w _ m0 fun tr0 =>
          rt_fbG W t i _ _ _ _ _ w.chal (fun α => embP (.inl (.inl α))) _ w.gr0
              (fun h => cls0_none hE h _)
              (fun g h m hm => cls0_put hE hW.1.1 g h _ m hm) fun _ _ _ _ =>
            rt_chainT depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)
      · exact rt_chainT depthReq s A Ws _ _ _ _ _ _ _ hW.2 (ClsAt.tail hE)

end Rounds

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam W.K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)

theorem rt_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam W.K (Y × H.Coin)) :
    Rt (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · trivial
  · exact fun vs =>
      (rt_opensB W _ _ _ _ _ _ _).bind fun f => (rt_opensExtB W _ _ _ _ _).bind fun g => trivial

theorem rt_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam W.K (Y × H.Coin))),
      Rt (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs)
  | _, [] => trivial
  | j, acc :: zs => RoutedT.bind (by
      cases acc.x with
      | none => trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        show Rt (if fl j then _ else _)
        cases fl j
        · trivial
        · exact rt_finishSlot W Q H wq wp trees w c0 a0 j x cj acc) fun _ => (rt_finishAll fl c0 a0 (j + 1) zs).bind fun _ => trivial

theorem rt_initSlot (c0 : H.Coin0) (x : Option Y) : Rt (initSlot (L := L) sFS Q H wp w c0 x) :=
  (rt_drawT W wp.coin).bind fun _ _ => trivial

/-- The compiled prover is routed, if the proof-of-work records are well-formed and `embP` keeps the
number that a nonce represents. -/
theorem rt_proveB (hW : GrLaw Q.loc.shape Q.ann wq.sh) (hE : ClsAt W t wq.sh embP)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    Rt (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) :=
  (rt_drawT W wp.coin0).bind fun c0 =>
      (rt_eachM W (rt_initSlot W sFS Q H wp w c0) xs).bind fun zs =>
    (rt_chainT W sMT t _ _ depthReq _ _ _ _ _ 0 _ _ zs _ hW hE).bind fun out =>
      rt_finishAll W Q H wq wp trees w fl c0 out.2 0 out.1

end Prove

/-! ## The committer and the prover -/

variable (WP : WireBP L) (p : Params)

theorem rt_nodeP' (i : I) : Rt (nodeP' W WP p i) :=
  (rt_drawT W WP.ri).bind fun _ => (rt_commitE W p.sMT W.depth _).bind fun _ => trivial

variable (hW : GrLawB W)
include hW

theorem rt_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) : Rt (proveT W WP p tree i r) :=
  (rt_proveB W _ _ Tag.test _ _ W.T _ _ id _ _ _ _ hW.T (fun _ => rfl) _ _).bind fun _ => trivial

theorem rt_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    Rt (proveLk W WP p root tree i r₀ r) :=
  (rt_proveB W _ _ Tag.link _ _ W.Lk _ _ id _ _ _ _ hW.Lk (fun _ => rfl) _ _).bind fun _ => trivial

theorem rt_leavesC (i : I) (root : Node lam L) : ∀ n, Rt (leavesC W WP p i root n)
  | 0 => trivial
  | n + 1 =>
    (rt_nodeP' W WP p i).bind fun _ =>
      (rt_proveLk W WP p hW _ _ _ _ _).bind fun _ => (rt_leavesC i root n).bind fun _ => trivial

theorem rt_Cp (i : I) : Rt (Cp W WP p i) :=
  (rt_nodeP' W WP p i).bind fun _ =>
    (rt_proveT W WP p hW _ _ _).bind fun _ => (rt_leavesC W WP p hW i _ _).bind fun _ => trivial

theorem rt_PpJ (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    Rt (PpJ W WP p k fr xs j σ) := by
  unfold PpJ
  cases k.leaves[j]? with
  | none => trivial
  | some lf =>
    exact (rt_proveB W _ _ Tag.onl _ _ W.B _ _ id _ _ _ _ hW.B (fun _ => rfl) _ _).bind
      fun _ => trivial

theorem rt_Pp (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) : Rt (Pp W WP p k fr xs) := fun j =>
  (rt_drawT W WP.perm).bind fun σ => rt_PpJ W WP p hW k fr xs j.val σ

end Ghost

/-- The committer's program is routed, for `W.OKG`. -/
theorem routedCp : Spec.routedCp := fun _ _ _ _ W WP p i hW => Ghost.rt_Cp W WP p (.of_okg hW) i

/-- The prover's program is routed, for `W.OKG`. -/
theorem routedPp : Spec.routedPp := fun _ _ _ _ W WP p k fr xs hW =>
  Ghost.rt_Pp W WP p (.of_okg hW) k fr xs

/-- For `W.OKG`: the scheme is `argBT` with C and P translated by `ghost W`. -/
theorem argB_via : Spec.argB_via := argB_via_of routedCp routedPp

/-- C and P are `Ctok`, `Ptok` (the erased programs) translated by `ghost W`, if the proof-of-work
records are well-formed. -/
theorem C_via_law {W : QueryLayout lam L} (WP : WireBP L) (p : Params) (hW : Ghost.GrLawB W) (i : I) :
    C W WP p i = (Ctok W WP p i).via (ghost W) :=
  realQ_via I X lam L W _ _
    (Routed.bind (routedErase I X lam L W _ _ [] (Ghost.rt_Cp W WP p hW i)) fun _ => trivial)
@[inherit_doc C_via_law]
theorem P_via_law {W : QueryLayout lam L} (WP : WireBP L) (p : Params) (hW : Ghost.GrLawB W)
    (k : ISK lam L) (b : List (X × Unit)) :
    P W WP p k b = (Ptok W WP p k b).via (ghost W) :=
  realQ_via I X lam L W _ _
    (Routed.bind
      (routedErase I X lam L W _ _ k.2 (Ghost.rt_Pp W WP p hW k.1 (fun _ => true) (b.map Prod.fst)))
      fun _ => trivial)

end Compile.Batch
