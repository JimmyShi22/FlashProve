-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/NoFb.lean: programs that never query a Fiat-Shamir oracle: trees, openings, coins;
  a fresh encoding of the index and its tree (`nodeP'`); tools for what is derived from a seed
  (`OnlyQ.blocks`, `OnlyQ.derive`) (words of this library: lean/GLOSSARY.md).
    `NoFbS c`            the program c queries neither a Fiat-Shamir oracle `fb t` nor a ghost name
                         `fbw t j` (`OracleName`, Compile/Batch/Oracles.lean). By recursion on the program
    `NoFbS.erase`        its erasure queries no `fb t` (`OnlyQ (NotFb t)`,
                         Compile/Batch/CompleteUnif.lean), from every store
    `OnlyQ.tossN`, `OnlyQ.blocks`, `OnlyQ.derive`
        making samples from small ones, and deriving them from a seed whose oracle is not `fb t`,
        preserves that no `fb t` is queried. Generic in the family of oracles and in the property
  Used in Compile/Batch/Kept.lean, Compile/Batch/KeptWalk.lean, Compile/Batch/MeanSeed.lean.
  The induction follows that of Compile/Batch/GhostRouted.lean.
-/
import Compile.Batch.CompleteUnif
import Compile.Batch.Star
import Rom.Blocks

noncomputable section

namespace Compile.Batch.CompleteUnif
open Rom

variable {S : OSpec} {α : Type} {P : (o : S.ι) → S.Dom o → Prop}

theorem OnlyQ.tossN (v : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (v + 1)) → OComp S α),
      (∀ x, OnlyQ P (f x)) → OnlyQ P (OComp.tossN v m f)
  | 0, _, h => h _
  | m + 1, _, h => fun _ => OnlyQ.tossN v m _ fun _ => h _

theorem OnlyQ.blocks (bk : CoinPlan) : ∀ {c : OComp S α}, OnlyQ P c → OnlyQ P (c.blocks bk)
  | .pure _, _ => trivial
  | .query _ _ _, h => ⟨h.1, fun r => OnlyQ.blocks bk (h.2 r)⟩
  | .sample _ _, h => OnlyQ.tossN _ _ _ fun _ => OnlyQ.blocks bk (h _)

theorem OnlyQ.derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) (hσ : ∀ j, P σ.o (σ.pt s j)) :
    ∀ {c : OComp S α}, OnlyQ P c → ∀ j, OnlyQ P (c.derive σ s j)
  | .pure _, _, _ => trivial
  | .query _ _ _, h, j => ⟨h.1, fun r => OnlyQ.derive σ s hσ (h.2 r) j⟩
  | .sample _ _, h, j => ⟨hσ j, fun _ => OnlyQ.derive σ s hσ (h _) (j + 1)⟩

end Compile.Batch.CompleteUnif

namespace Compile.Batch
open Iop Rom Compile.Batch.CompleteUnif

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- neither a Fiat-Shamir oracle nor a ghost name -/
def NF : OracleName → Prop
  | .fb _ => False
  | .fbw _ _ => False
  | _ => True

/-- The program queries neither a Fiat-Shamir oracle nor a ghost name. -/
def NoFbS {α : Type} : St lam K L α → Prop
  | .pure _ => True
  | .sample _ k => ∀ r, NoFbS (k r)
  | .plain o _ k => NF o ∧ ∀ r, NoFbS (k r)
  | .fresh _ k => ∀ t, NoFbS (k t)
  | .marked o _ _ _ _ k => NF o ∧ ∀ v t, NoFbS (k v t)
  | .reveal _ k => ∀ vs, NoFbS (k vs)

theorem NF.notFb {o : OracleName} (h : NF o) (t : Tag) (q : domOf lam L o) : NotFb t o q := by
  cases o <;> first | exact False.elim h | exact fun e => OracleName.noConfusion e

theorem NoFbS.bind {α β : Type} {c : St lam K L α} {g : α → St lam K L β}
    (h : NoFbS c) (hg : ∀ a, NoFbS (g a)) : NoFbS (c.bind g) := by
  induction c with
  | pure a => exact hg a
  | sample n k ih => exact fun r => ih r (h r)
  | plain o q k ih => exact ⟨h.1, fun r => ih r (h.2 r)⟩
  | fresh l k ih => exact fun t => ih t (h t)
  | marked o t us pt inj k ih => exact ⟨h.1, fun v t => ih v t (h.2 v t)⟩
  | reveal ts k ih => exact fun vs => ih vs (h vs)

/-- If `NoFbS c`, the erasure of c queries no Fiat-Shamir oracle `fb t`, from every store. -/
theorem NoFbS.erase {α : Type} {c : St lam K L α} (h : NoFbS c) (t : Tag) :
    ∀ vs, OnlyQ (S := spec lam K L) (NotFb t) (erase c vs) := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun vs r => ih r (h r) vs
  | plain o q k ih => exact fun vs => ⟨h.1.notFb t _, fun r => ih r (h.2 r) vs⟩
  | fresh l k ih => exact fun vs r => ih _ (h _) _
  | marked o t' us pt inj k ih => exact fun vs => ⟨h.1.notFb t _, fun r => ih _ _ (h.2 _ _) _⟩
  | reveal ts k ih => exact fun vs => ih _ (h _) vs

/-! ## The lemmas, program by program -/

theorem nf_leafT (sMT : ℕ) (b : Body L) : NoFbS (leafT (lam := lam) (K := K) sMT b) := fun _ =>
  ⟨trivial, fun _ _ => trivial⟩
theorem nf_showT (t : Tok) : NoFbS (showT (lam := lam) (K := K) (L := L) t) := fun _ => trivial
theorem nf_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    NoFbS (openT (lam := lam) (K := K) (L := L) t j a) := fun _ => trivial
theorem nf_nodeE (a b : Dig lam) : NoFbS (nodeE (K := K) (L := L) a b) :=
  ⟨trivial, fun _ => trivial⟩
theorem nf_drawT {β : Type} (e : Enum β) : NoFbS (drawT (lam := lam) (K := K) (L := L) e) :=
  fun _ => trivial

theorem nf_pairUp {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, NoFbS (node a b)) :
    ∀ l : List D, NoFbS (pairUp node l)
  | [] => trivial
  | [_] => trivial
  | a :: b :: t => (hn a b).bind fun _ => (nf_pairUp hn t).bind fun _ => trivial

theorem nf_levelsM {D : Type} {node : D → D → St lam K L D} (hn : ∀ a b, NoFbS (node a b)) :
    ∀ (d : ℕ) (l : List D), NoFbS (levelsM node d l)
  | 0, _ => trivial
  | d + 1, l => (nf_pairUp hn l).bind fun u => (nf_levelsM hn d u).bind fun _ => trivial

theorem nf_leafE (sMT : ℕ) (b : Body L) (blind : Bool) :
    NoFbS (leafE (lam := lam) (K := K) sMT b blind) := by
  unfold leafE
  cases blind
  · exact ⟨trivial, fun _ => trivial⟩
  · exact (nf_leafT sMT b).bind fun x => (nf_showT x.2).bind fun _ => trivial

theorem nf_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool), NoFbS (leavesE (lam := lam) (K := K) sMT l)
  | [] => trivial
  | (b, bl) :: t => (nf_leafE sMT b bl).bind fun _ => (nf_leavesE sMT t).bind fun _ => trivial

theorem nf_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    NoFbS (commitE (lam := lam) (K := K) sMT d leaf) :=
  (nf_leavesE sMT _).bind fun x => (nf_levelsM nf_nodeE d x.1).bind fun _ => trivial

theorem nf_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, NoFbS (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => trivial
  | j :: js => (nf_opensComp dec posAt o tr isRead f js).bind fun f' => by
      show NoFbS (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => trivial
      | some p =>
        show NoFbS (if isRead p then _ else _)
        cases isRead p
        · trivial
        · exact (nf_openT _ _ _).bind fun _ => trivial

theorem nf_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    NoFbS (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => trivial
  | some tr => exact nf_opensComp dec posAt o tr isRead f _

/-- Opening the positions read in the trees of one component, from tree number k on, queries neither
a Fiat-Shamir oracle nor a ghost name. The depths and the trees are two lists of any lengths: where
either list ends, nothing more is opened. -/
theorem nf_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      NoFbS (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    (nf_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      nf_opensComp dec (posAt k) o tr isRead f' _

theorem nf_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (Ws : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      NoFbS (opensB (L := L) s A Ws τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, Ws), (_, _, τ), tjs, t0s, _ =>
      (nf_opensOpt _ _ _ _ _ _ _).bind fun _ =>
        (nf_opensOpt _ _ _ _ _ _ _).bind fun _ =>
          (nf_opensB s A Ws τ tjs.tail t0s.tail _).bind fun _ => trivial

theorem nf_nodeP' {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (i : I) :
    NoFbS (nodeP' W WP p i) :=
  (nf_drawT WP.ri).bind fun _ => (nf_commitE p.sMT W.depth _).bind fun _ => trivial

end Compile.Batch
