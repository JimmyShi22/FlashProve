-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedShape.lean: the samples of the committer C of the compiled scheme have a total
weight that does not depend on the path, and its programs never query the auxiliary oracle. (Words
of this library: lean/GLOSSARY.md.)

A sample with m + 1 outcomes has the weight μ m, μ arbitrary.

Why. In Rom/SpecDerive.lean the label of a derived sample is its number in the run. The prover of
Compile/Batch/SeedStar.lean derives only the `Node` of the sampled copy again, so it must know the
number of the first sample of that `Node`. So the samples of everything that C does before that
`Node` must have the same total weight on all paths. And coins can be derived through the auxiliary
oracle `OracleName.other` only if the scheme itself never queries that oracle.

The compiled prover takes all slots through the rounds together, and what a round samples depends on
the number of slots that the round before has returned. The rule of `Compile.Seed.Sh` for a sequence
requires the weight of the second part for all results of the first. So there is a form with a
postcondition, `ShQ o₀ μ Q n c`: every
path of the token program c has samples of the total weight n, c never queries the oracle o₀, and
every result of c has the property Q.

The lemmas, in the order of Compile/Batch/TokTree.lean, Prover.lean, Star.lean:
* trees: in a token tree over a prover message (`commitT`) every one of the 2 ^ depth leaves is
  salted, and a request tree has no salts; in a tree over an encoded index a leaf is salted or not
  by its position alone;
* the rounds: the number of slots is preserved by every round (`shq_eachM`, `shq_joinM`);
* after the chains the openings and proof strings take no sample;
* `sh_proveB`: one execution of the compiled prover on n slots has the weight `cProveB` .. n, for
  all arguments: any tag, protocol, wire records, flags, slots (full or empty).

So the numbers `cChainB`, `cProveB`, `cNode`, `cLeaf`, `off` of Compile/Batch/SeedStar.lean are the
weights that their docstrings state.

Notation: `cProveB` .. n: `cProveB μ sMT sFS wq wp n`: the weighted number of uniform samples of one
execution of the compiled prover with n slots; `off` .. (M + 1): `off W WP p μ (p.M + 1)`; `off j`:
the weighted number of samples of C before copy j (both: Compile/Batch/SeedStar.lean); `sMT`, `sFS`:
natural numbers: the length of the salt of a leaf, and of the salt of a chain
(Compile/Batch/Verifier.lean); `fbT`: a Fiat-Shamir query: charged to tk; its other tokens are us
and then the root, if the component has a tree; `fbTw`: fbT under the ghost name fbw t j: the same
input, the same charge; `fbG`: a Fiat-Shamir query, with a proof-of-work record or without (these
three: Compile/Batch/Prover.lean).

Limits: nothing is said about probabilities, the number of oracle queries, or the verifier
(Compile/Batch/SeedAvoid.lean). A weight counts what the Lean program samples; an empty slot samples
what a full one does (the paragraph "Empty slots" of Compile/Batch/Prover.lean).
-/
import Compile.Batch.SeedStar
import Compile.Batch.ProverG
import Compile.Batch.RealQ

open Rom Iop

namespace Compile.Batch
namespace Seed

open Compile.Seed (Sh Wt cLeaves cTree)

/-! ## The predicate with a postcondition -/

section Gen
variable {S : OSpec} {sp : Split S} {α β : Type}

/-- every path has samples of the total weight n, the oracle o₀ is never queried, and every result
has the property Q -/
inductive ShQ (o₀ : S.ι) (μ : ℕ → ℕ) (Q : α → Prop) : ℕ → Step S sp α → Prop
  | pure (a : α) (h : Q a) : ShQ o₀ μ Q 0 (.pure a)
  | sample {n : ℕ} (m : ℕ) {k : Fin (m + 1) → Step S sp α} (h : ∀ r, ShQ o₀ μ Q n (k r)) :
      ShQ o₀ μ Q (n + μ m) (.sample m k)
  | plain {n : ℕ} (o : S.ι) (ho : o ≠ o₀) (q : S.Dom o)
      {k : S.Rng o → Step S sp α} (h : ∀ r, ShQ o₀ μ Q n (k r)) : ShQ o₀ μ Q n (.plain o q k)
  | fresh {n : ℕ} (ℓ : ℕ) {k : Tok → Step S sp α} (h : ∀ t, ShQ o₀ μ Q n (k t)) :
      ShQ o₀ μ Q (n + μ (2 ^ ℓ - 1)) (.fresh ℓ k)
  | marked {n : ℕ} (o : S.ι) (ho : o ≠ o₀) (t : Tok) (us : List Tok)
      (pt : Bits → List Bits → S.Dom o) (inj : ∀ vs, Function.Injective fun v => pt v vs)
      {k : sp.Vis o → Tok → Step S sp α} (h : ∀ v t', ShQ o₀ μ Q n (k v t')) :
      ShQ o₀ μ Q n (.marked o t us pt inj k)
  | reveal {n : ℕ} (ts : List Tok) {k : List Bits → Step S sp α} (h : ∀ w, ShQ o₀ μ Q n (k w)) :
      ShQ o₀ μ Q n (.reveal ts k)

variable {o₀ : S.ι} {μ : ℕ → ℕ} {Q : α → Prop} {Q' : β → Prop}

theorem ShQ.cast {n m : ℕ} {c : Step S sp α} (h : ShQ o₀ μ Q n c) (e : n = m) : ShQ o₀ μ Q m c :=
  e ▸ h

/-- a sequence: the second part is considered only on results of the first that have the property Q
-/
theorem ShQ.bind {n m : ℕ} {c : Step S sp α} {g : α → Step S sp β}
    (hc : ShQ o₀ μ Q n c) (hg : ∀ a, Q a → ShQ o₀ μ Q' m (g a)) :
    ShQ o₀ μ Q' (n + m) (c.bind g) := by
  induction hc with
  | pure a h => simpa [Step.bind] using hg a h
  | @sample n m' k _ ih => exact (ShQ.sample m' ih).cast (by omega)
  | plain o ho q _ ih => exact .plain o ho q ih
  | @fresh n ℓ k _ ih => exact (ShQ.fresh ℓ ih).cast (by omega)
  | marked o ho t us pt inj _ ih => exact .marked o ho t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

/-- forget the postcondition -/
theorem ShQ.sh {n : ℕ} {c : Step S sp α} (h : ShQ o₀ μ Q n c) : Sh o₀ μ n c := by
  induction h with
  | pure a _ => exact .pure a
  | sample m _ ih => exact .sample m ih
  | plain o ho q _ ih => exact .plain o ho q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o ho t us pt inj _ ih => exact .marked o ho t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

/-- a postcondition that all values have -/
theorem ShQ.ofSh {n : ℕ} {c : Step S sp α} (h : Sh o₀ μ n c) (hQ : ∀ a, Q a) : ShQ o₀ μ Q n c := by
  induction h with
  | pure a => exact .pure a (hQ a)
  | sample m _ ih => exact .sample m ih
  | plain o ho q _ ih => exact .plain o ho q ih
  | fresh ℓ _ ih => exact .fresh ℓ ih
  | marked o ho t us pt inj _ ih => exact .marked o ho t us pt inj ih
  | reveal ts _ ih => exact .reveal ts ih

/-- a sequence without a postcondition on its result -/
theorem ShQ.bindSh {n m : ℕ} {c : Step S sp α} {g : α → Step S sp β}
    (hc : ShQ o₀ μ Q n c) (hg : ∀ a, Q a → Sh o₀ μ m (g a)) : Sh o₀ μ (n + m) (c.bind g) :=
  (hc.bind (Q' := fun _ => True) fun a ha => .ofSh (hg a ha) fun _ => trivial).sh

/-- a sequence whose first part may return anything -/
theorem ShQ.ofBind {n m : ℕ} {c : Step S sp α} {g : α → Step S sp β}
    (hc : Sh o₀ μ n c) (hg : ∀ a, ShQ o₀ μ Q' m (g a)) :
    ShQ o₀ μ Q' (n + m) (c.bind g) :=
  (ShQ.ofSh (Q := fun _ => True) hc fun _ => trivial).bind fun a _ => hg a

end Gen

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (μ : ℕ → ℕ)

local notation "Sho" => Sh (S := spec lam K L) (sp := split lam K L) OracleName.other μ
local notation "ShoQ" => ShQ (S := spec lam K L) (sp := split lam K L) OracleName.other μ

/-! ## Trees (Compile/Batch/TokTree.lean) -/

theorem sh_leafT (sMT : ℕ) (b : Body L) :
    Sho (μ (2 ^ sMT - 1)) (leafT (lam := lam) (K := K) sMT b) :=
  (Sh.fresh _ fun _ => .marked _ (by intro h; cases h) _ _ _ _ fun _ _ => .pure _).cast
    (Nat.zero_add _)

theorem sh_nodeT (a b : Tok) : Sho 0 (nodeT (lam := lam) (K := K) (L := L) a b) :=
  .marked _ (by intro h; cases h) _ _ _ _ fun _ _ => .pure _

theorem sh_leavesT (sMT : ℕ) :
    ∀ l : List (Body L), Sho (l.length * μ (2 ^ sMT - 1)) (leavesT (lam := lam) (K := K) sMT l)
  | [] => (Sh.pure _).cast (Nat.zero_mul _).symm
  | b :: t => by
      have h := (sh_leafT (lam := lam) (K := K) μ sMT b).bind
        (g := fun x => (leavesT sMT t).bind fun r => Step.pure (x.2 :: r.1, x.1 :: r.2))
        fun x => (sh_leavesT sMT t).bind0 fun r => .pure _
      refine h.cast ?_
      rw [List.length_cons, Nat.succ_mul]
      omega

theorem sh_pairUp {D : Type} {hN : D → D → St lam K L D} (h : ∀ a b, Sho 0 (hN a b)) :
    ∀ l : List D, Sho 0 (pairUp hN l)
  | [] => .pure _
  | [_] => .pure _
  | a :: b :: t => (h a b).bind0 fun _ => (sh_pairUp h t).bind0 fun _ => .pure _

theorem sh_levelsM {D : Type} {hN : D → D → St lam K L D} (h : ∀ a b, Sho 0 (hN a b)) :
    ∀ (d : ℕ) (l : List D), Sho 0 (levelsM hN d l)
  | 0, _ => .pure _
  | d + 1, l => (sh_pairUp μ h l).bind0 fun u => (sh_levelsM h d u).bind0 fun _ => .pure _

/-- every one of the 2 ^ d leaves of a token tree over a prover message is salted -/
theorem sh_commitT (sMT d : ℕ) (leaf : ℕ → Body L) :
    Sho (2 ^ d * μ (2 ^ sMT - 1)) (commitT (lam := lam) (K := K) sMT d leaf) :=
  ((sh_leavesT μ sMT _).bind0 fun x =>
      (sh_levelsM μ (sh_nodeT μ) d x.1).bind0 fun _ => .pure _).cast
    (by rw [List.length_map, List.length_range])

theorem sh_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    Sho 0 (openT (lam := lam) (K := K) (L := L) t j a) :=
  .reveal _ fun _ => .pure _

theorem sh_showT (t : Tok) : Sho 0 (showT (lam := lam) (K := K) (L := L) t) :=
  .reveal _ fun _ => .pure _

theorem sh_rleafT (c : Tok) : Sho 0 (rleafT (lam := lam) (K := K) (L := L) c) :=
  .marked _ (by intro h; cases h) _ _ _ _ fun _ _ => .pure _

theorem sh_rnodeT (a b : Tok) : Sho 0 (rnodeT (lam := lam) (K := K) (L := L) a b) :=
  .marked _ (by intro h; cases h) _ _ _ _ fun _ _ => .pure _

theorem sh_rleavesT : ∀ l : List Tok, Sho 0 (rleavesT (lam := lam) (K := K) (L := L) l)
  | [] => .pure _
  | c :: t => (sh_rleafT μ c).bind0 fun _ => (sh_rleavesT t).bind0 fun _ => .pure _

theorem sh_reqT (d : ℕ) (cs : List Tok) : Sho 0 (reqT (lam := lam) (K := K) (L := L) d cs) :=
  (sh_rleavesT μ cs).bind0 fun ls => (sh_levelsM μ (sh_rnodeT μ) d ls).bind0 fun _ => .pure _

theorem sh_leafE (sMT : ℕ) (b : Body L) (bl : Bool) :
    Sho (if bl then μ (2 ^ sMT - 1) else 0) (leafE (lam := lam) (K := K) sMT b bl) := by
  unfold leafE
  cases bl
  · exact .plain _ (by intro h; cases h) _ fun _ => .pure _
  · exact (sh_leafT μ sMT b).bind0 fun x => (sh_showT μ x.2).bind0 fun _ => .pure _

theorem sh_nodeE (a b : Dig lam) : Sho 0 (nodeE (K := K) (L := L) a b) :=
  .plain _ (by intro h; cases h) _ fun _ => .pure _

theorem sh_leavesE (sMT : ℕ) :
    ∀ l : List (Body L × Bool),
      Sho (cLeaves l * μ (2 ^ sMT - 1)) (leavesE (lam := lam) (K := K) sMT l)
  | [] => (Sh.pure _).cast (Nat.zero_mul _).symm
  | (b, bl) :: t => by
      have h := (sh_leafE (lam := lam) (K := K) μ sMT b bl).bind
        (g := fun x => (leavesE sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2))
        fun x => (sh_leavesE sMT t).bind0 fun r => .pure _
      refine h.cast ?_
      unfold cLeaves
      rw [List.countP_cons]
      cases bl
      · simp
      · simp only [if_true, Nat.add_mul, Nat.one_mul]
        omega

theorem sh_commitE (sMT d : ℕ) (leaf : ℕ → Body L × Bool) :
    Sho (cTree d leaf * μ (2 ^ sMT - 1)) (commitE (lam := lam) (K := K) sMT d leaf) :=
  (sh_leavesE μ sMT _).bind0 fun x => (sh_levelsM μ (sh_nodeE μ) d x.1).bind0 fun _ => .pure _

theorem sh_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) :
    Sho 0 (openE (K := K) (L := L) t j a) := by
  unfold openE
  cases t.salts.getD j none with
  | none => exact .pure _
  | some s => exact .reveal _ fun _ => .pure _

/-! ## The rounds (Compile/Batch/Prover.lean) -/

/-- do f in each slot: as many results as slots -/
theorem shq_eachM {σ τ : Type} {f : σ → St lam K L τ} {n : ℕ} (h : ∀ a, Sho n (f a)) :
    ∀ l : List σ, ShoQ (fun r => r.length = l.length) (l.length * n) (eachM f l)
  | [] =>
    (ShQ.pure (Q := fun r : List τ => r.length = ([] : List σ).length) [] rfl).cast
      (Nat.zero_mul _).symm
  | a :: t => by
      have h1 := ShQ.ofBind (Q' := fun r : List τ => r.length = (a :: t).length)
        (g := fun b => (eachM f t).bind fun r => Step.pure (b :: r)) (h a) fun b =>
          ((shq_eachM h t).bind (m := 0) fun r hr =>
            .pure _ (by rw [List.length_cons, List.length_cons, hr]))
      refine h1.cast ?_
      rw [List.length_cons, Nat.succ_mul]
      omega

theorem sh_fbT {β : Type} {n : ℕ} (t : Tag) (i : ℕ) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} (h : ∀ bl tl, Sho n (k bl tl)) :
    Sho n (fbT t i tk us root hd hinj pl k) :=
  .marked _ (by intro h; cases h) _ _ _ _ h

theorem sh_fbSlot {β : Type} {n : ℕ} (t : Tag) (i : ℕ) (cms : List (Dig lam)) (x : Option X)
    (ph : PhT) (tk c : Tok) (root : Option Tok) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} (h : ∀ bl tl, Sho n (k bl tl)) :
    Sho n (fbSlot t i cms x ph tk c root pl k) := by
  cases ph <;> exact .marked _ (by intro h; cases h) _ _ _ _ h

theorem sh_fbTw {β : Type} {n : ℕ} (t : Tag) (j i : ℕ) (tk : Tok) (us : List Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L β} (h : ∀ bl tl, Sho n (k bl tl)) :
    Sho n (fbTw t j i tk us root hd hinj pl k) :=
  .marked _ (by intro h; cases h) _ _ _ _ h

/-- The search over nonces takes no sample: whatever the number of attempts, the weight is that of
what follows -/
theorem sh_fbG {β C P : Type} {n : ℕ} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag)
    (i : ℕ) (tk : Tok) (us : List Tok) (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h : ∀ nc dd bl tl, Sho n (k nc dd bl tl)) :
    Sho n (fbG gr chal t i tk us root hd hinj emb α k) :=
  fbG_ind (Φ := fun c => Sho n c) gr (fun pl _ h' => sh_fbT μ t i tk us root hd hinj pl h')
    (fun j pl _ h' => sh_fbTw μ t j i tk us root hd hinj pl h') h

theorem sh_fbSlotG {β C P : Type} {n : ℕ} (gr : Option (GrW C P)) (chal : Blk lam K → C) (t : Tag)
    (i : ℕ) (cms : List (Dig lam)) (x : Option X) (ph : PhT) (tk c : Tok) (root : Option Tok)
    (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β}
    (h : ∀ nc dd bl tl, Sho n (k nc dd bl tl)) :
    Sho n (fbSlotG gr chal t i cms x ph tk c root emb α k) :=
  fbSlotG_ind (Φ := fun c => Sho n c) gr ph
    (fun tk us hd hinj pl _ h' => sh_fbT μ t i tk us root hd hinj pl h')
    (fun j tk us hd hinj pl _ h' => sh_fbTw μ t j i tk us root hd hinj pl h') h

theorem sh_gT {β : Type} {n : ℕ} (t : Tag) (i : ℕ) (tk : Tok) (root : Option Tok)
    (pl : PlainPart (shapeOf L t) (annOf L t)) {k : Tok → St lam K L β} (h : ∀ c, Sho n (k c)) :
    Sho n (gT (lam := lam) t i tk root pl k) :=
  .marked _ (by intro h; cases h) _ _ _ _ fun _ c => h c

/-- the tree over a component, if it has one, and then k -/
theorem sh_withTree {β : Type} {n : ℕ} (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → Body L)
    {k : Option TTree → St lam K L β} (h : ∀ tr, Sho n (k tr)) :
    Sho (nLv has d * μ (2 ^ sMT - 1) + n) (withTree sMT has d leaf k) := by
  cases has with
  | true => exact ((sh_commitT μ sMT d leaf).bind fun tr => h (some tr)).cast (by simp [nLv])
  | false => exact (h none).cast (by simp [nLv])

/-- the trees over a component, one after the other, and then k: every leaf of every tree is salted,
so the trees weigh as many salts as the sum of 2 ^ d over the depths d in ds; if ds is empty, the
weight is that of k alone -/
theorem sh_withTrees {β : Type} {n : ℕ} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L β},
      (∀ trs, Sho n (k trs)) →
      Sho ((ds.map (2 ^ ·)).sum * μ (2 ^ sMT - 1) + n) (withTrees sMT ds leaf k)
  | [], _, _, h => (h []).cast (by simp)
  | d :: ds, leaf, _, h =>
    ((sh_commitT μ sMT d (leaf 0)).bind fun tr =>
      sh_withTrees sMT ds (fun j => leaf (j + 1)) fun trs => h (tr :: trs)).cast
      (by rw [List.map_cons, List.sum_cons, Nat.add_mul, Nat.add_assoc])

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem sh_slotLo {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) :
    ∀ z : SlotSt lam K Y (r :: s),
      Sho (nLv w.hasJ w.depthJ * μ (2 ^ sMT - 1)) (slotLo sMT t cms xin a w emb plJ i ph z)
  | ((m, k), acc) => by
      show Sho _
        (withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
          fbSlotG w.grJ w.chal t i cms (acc.x.bind xin) ph acc.tk acc.c (tr.map TTree.root) plJ
            (a.plain m.2).2 fun nc dd bl tl =>
              Step.pure (k (w.chal bl),
                  { acc with
                    tk := tl, blocks := acc.blocks ++ [bl],
                    trees := acc.trees ++ [tr], toks := acc.toks ++ [tl],
                    nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead }))
      exact sh_withTree μ sMT w.hasJ w.depthJ _ (n := 0) fun tr =>
        sh_fbSlotG μ _ _ t i cms _ ph _ _ _ _ _ fun _ _ _ _ => .pure _

theorem sh_slotJoin {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ z : SlotSt lam K Y (r :: s),
      Sho (nLv w.hasJ w.depthJ * μ (2 ^ sMT - 1)) (slotJoin sMT t a w emb plJ i z)
  | ((m, k), acc) => by
      show Sho _
        (withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) fun tr =>
          gT t i acc.tk (tr.map TTree.root) (plJ (a.plain m.2).2) fun c =>
            Step.pure
              ((m, k), { acc with c := c, trees := acc.trees ++ [tr], toks := acc.toks ++ [c] }))
      exact sh_withTree μ sMT w.hasJ w.depthJ _ (n := 0) fun tr =>
        sh_gT μ t i _ _ _ fun _ => .pure _

/-- the joining round in all slots: as many slots as before -/
theorem shq_joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) :
    ∀ zs : List (SlotSt lam K Y (r :: s)), ShoQ (fun o => o.1.length = zs.length)
      (zs.length * (nLv w.hasJ w.depthJ * μ (2 ^ sMT - 1))) (joinM sMT t a w emb plJ i zs)
  | [] =>
    (ShQ.pure (Q := fun o : List (SlotSt lam K Y (r :: s)) × List Tok =>
            o.1.length = ([] : List (SlotSt lam K Y (r :: s))).length)
        ([], []) rfl).cast
      (Nat.zero_mul _).symm
  | z :: zs => by
      have h1 := ShQ.ofBind
        (Q' := fun o : List (SlotSt lam K Y (r :: s)) × List Tok => o.1.length = (z :: zs).length)
        (g := fun z' =>
            (joinM sMT t a w emb plJ i zs).bind fun o => Step.pure (z' :: o.1, z'.2.c :: o.2))
        (sh_slotJoin μ sMT t a w emb plJ i z) fun z' =>
          ((shq_joinM a w emb plJ i zs).bind (m := 0) fun o ho =>
            .pure _ (by show (z' :: o.1).length = _; rw [List.length_cons, List.length_cons, ho]))
      refine h1.cast ?_
      rw [List.length_cons, Nat.succ_mul]
      omega

theorem sh_tree0 {β : Type} {n : ℕ} {r : Round} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0)
    {k : Option TTree → St lam K L β} (h : ∀ tr, Sho n (k tr)) :
    Sho (nLv w.has0 w.depth0 * μ (2 ^ sMT - 1) + n) (tree0 sMT a w emb m0 k) :=
  sh_withTree μ sMT _ _ _ h

theorem phOf_afterLo (ph : PhT) : phOf ph.afterLo = (phOf ph).afterLo := by cases ph <;> rfl

/-- All chains of a batch: `cChainB` counts the leaves of their trees. -/
theorem sh_chainT (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
        (zs : List (SlotSt lam K Y s)) (a0 : Acc0),
      Sho (cChainB s A W (phOf ph) zs.length * μ (2 ^ sMT - 1))
        (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0)
  | [], _, _, _, _, _, _, _, _, _ => (Sh.pure _).cast (Nat.zero_mul _).symm
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0 => by
      obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
      cases kind with
      | lo =>
        refine ((shq_eachM μ
            (sh_slotLo μ sMT t cms xin _ w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i ph) zs).bindSh
          (m := cChainB s A W (phOf ph).afterLo zs.length * μ (2 ^ sMT - 1)) fun zs' h' =>
            (sh_chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
                ph.afterLo _ zs' _).cast
              (by rw [h', phOf_afterLo])).cast ?_
        show _ = (zs.length * nLv w.hasJ w.depthJ + cChainB s A W (phOf ph).afterLo zs.length) *
            μ (2 ^ sMT - 1)
        rw [Nat.add_mul, Nat.mul_assoc]
      | sh =>
        cases ph with
        | first =>
          exact (sh_chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              .first _ (zs.map (hear w (blk0 lam K) false)) _).cast
            (by rw [List.length_map]; rfl)
        | aft =>
          exact (sh_chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
              .aft _ (zs.map (hear w (blk0 lam K) false)) _).cast
            (by rw [List.length_map]; rfl)
        | loc =>
          refine ((shq_joinM μ sMT t _ w (fun p => embS (.inl p))
              (fun α => embP (.inl (.inr α))) i zs).bindSh
            (m := nLv w.has0 w.depth0 * μ (2 ^ sMT - 1) +
                cChainB s A W .shr zs.length * μ (2 ^ sMT - 1)) fun o ho =>
                  ((sh_reqT μ depthReq o.2).bind fun rq =>
                      sh_tree0 μ sMT _ w (fun p => embS (.inl p)) m0 fun tr0 =>
                        sh_fbG μ _ _ _ _ _ _ _ _ _ _ _ fun _ _ bl tl =>
                          (sh_chainT depthReq s A W (fun p => embS (.inr p))
                              (fun z => embP (.inr z)) (i + 1) (.shr tl) _
                              (o.1.map (hear w bl true)) _).cast
                            (by rw [List.length_map, ho]; rfl)).cast
                    (Nat.zero_add _)).cast ?_
          show _ = (zs.length * nLv w.hasJ w.depthJ +
                nLv w.has0 w.depth0 + cChainB s A W .shr zs.length) * μ (2 ^ sMT - 1)
          rw [Nat.add_mul, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
        | shr tk0 =>
          refine (sh_tree0 μ sMT _ w (fun p => embS (.inl p)) m0 fun tr0 =>
            sh_fbG μ _ _ _ _ _ _ _ _ _ _ _ fun _ _ bl tl =>
              (sh_chainT depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
                  (.shr tl) _ (zs.map (hear w bl false)) _).cast
                (m := cChainB s A W .shr zs.length * μ (2 ^ sMT - 1))
                (by rw [List.length_map]; rfl)).cast ?_
          show _ = (nLv w.has0 w.depth0 + cChainB s A W .shr zs.length) * μ (2 ^ sMT - 1)
          rw [Nat.add_mul]

end Rounds

/-! ## From the chains to the proof strings: the openings take no sample -/

theorem sh_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, Sho 0 (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => .pure _
  | j :: js => (sh_opensComp dec posAt o tr isRead f js).bind0 fun f' => by
      show Sho 0 (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => exact .pure _
      | some p =>
        show Sho 0 (if isRead p then _ else _)
        cases isRead p
        · exact .pure _
        · exact (sh_openT μ tr j _).bind0 fun _ => .pure _

theorem sh_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    Sho 0 (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => exact .pure _
  | some tr => exact sh_opensComp μ dec posAt o tr isRead f _

/-- the openings in the trees of a component take no sample, whatever the lengths of the list of
depths and of the list of trees -/
theorem sh_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      Sho 0 (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => .pure _
  | _, _ :: _, [], _ => .pure _
  | k, _ :: ds, tr :: trs, f =>
    (sh_opensTrees dec posAt o isRead (k + 1) ds trs f).bind0 fun f' =>
      sh_opensComp μ dec (posAt k) o tr isRead f' _

theorem sh_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      Sho 0 (opensB (L := L) s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => .pure _
  | _ :: s, (_, A), (_, W), (_, _, τ), tjs, t0s, _ =>
      (sh_opensOpt μ _ _ _ _ _ _ _).bind0 fun _ =>
        (sh_opensOpt μ _ _ _ _ _ _ _).bind0 fun _ =>
          (sh_opensB s A W τ tjs.tail t0s.tail _).bind0 fun _ => .pure _

theorem sh_opensExtB {E : ExtSpec} (we : WireE E) (y : E.Str)
    (trees : List (TreeH lam)) (isRead : E.Pos → Bool) :
    ∀ ps : List E.Pos, Sho 0 (opensExtB (K := K) (L := L) we y trees isRead ps)
  | [] => .pure _
  | p :: ps => (sh_opensExtB we y trees isRead ps).bind0 fun f => by
      show Sho 0
        (if isRead p then
          (openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)).bind
            fun op => Step.pure (@Function.update _ _ we.dec f p (some op)) else Step.pure f)
      cases isRead p
      · exact .pure _
      · exact (sh_openE μ _ _ _).bind0 fun _ => .pure _

theorem sh_drawT {β : Type} (e : Enum β) : Sho (μ e.n) (drawT (lam := lam) (K := K) (L := L) e) :=
  (Sh.sample _ fun _ => .pure _).cast (Nat.zero_add _)

/-! ## One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt' : Type} (H : BatchHonestProver Q Wt') (wq : ProtocolQueryLayout lam K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt')

theorem sh_finishSlot (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    Sho 0 (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) := by
  unfold finishSlot
  dsimp only
  split_ifs
  · exact .pure _
  · exact .reveal _ fun vs =>
      (sh_opensB μ _ _ _ _ _ _ _).bind0 fun f => (sh_opensExtB μ _ _ _ _ _).bind0 fun g => .pure _

theorem sh_finishAll (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      Sho 0 (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs)
  | _, [] => .pure _
  | j, acc :: zs => by
      refine Sh.bind0 (c := match acc.x with
        | some (x, cj) => if fl j then finishSlot Q H wq wp trees w c0 a0 j x cj acc else pure none
        | none => pure none) ?_ fun π => (sh_finishAll fl c0 a0 (j + 1) zs).bind0 fun r => .pure _
      cases acc.x with
      | none => exact .pure _
      | some y =>
        obtain ⟨x, cj⟩ := y
        show Sho 0 (if fl j then _ else _)
        cases fl j
        · exact .pure _
        · exact sh_finishSlot μ Q H wq wp trees w c0 a0 j x cj acc

theorem sh_initSlot (c0 : H.Coin0) (x : Option Y) :
    Sho (μ wp.coin.n + μ (2 ^ sFS - 1))
      (initSlot (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x) :=
  (sh_drawT μ wp.coin).bind fun _ => (Sh.fresh _ fun _ => .pure _).cast (Nat.zero_add _)

/-- One execution of the compiled prover on the slots xs has the weight `cProveB` .. xs.length, and
never queries the auxiliary oracle: for all arguments. -/
theorem sh_proveB (fl : ℕ → Bool) (xs : List (Option Y)) :
    Sho (cProveB μ sMT sFS wq wp xs.length)
      (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) :=
  (sh_drawT μ wp.coin0).bind fun c0 =>
      (shq_eachM μ (sh_initSlot μ sFS Q H wp w c0) xs).bindSh fun zs hz =>
    ((sh_chainT μ sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _).cast (by rw [hz]; rfl)).bind0
      fun out => sh_finishAll μ Q H wq wp trees w fl c0 out.2 0 out.1

end Prove

/-! ## The committer (Compile/Batch/Star.lean) -/

section Star
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (μ : ℕ → ℕ)

local notation "ShW" => Sh (S := spec lam W.K L) (sp := split lam W.K L) OracleName.other μ

theorem cTree_node (f : Fin L.wordLength → Body L) :
    cTree W.depth (fun j => if h : j < L.wordLength then (f ⟨j, h⟩, true) else (none, false)) =
      ((List.range (2 ^ W.depth)).filter fun j => decide (j < L.wordLength)).length := by
  unfold cTree cLeaves
  rw [List.countP_map, List.countP_eq_length_filter]
  congr 1
  refine List.filter_congr fun j _ => ?_
  show (if h : j < L.wordLength then (f ⟨j, h⟩, true) else ((none : Body L), false)).2 = _
  by_cases h : j < L.wordLength
  · rw [dif_pos h, decide_eq_true h]
  · rw [dif_neg h, decide_eq_false h]

theorem sh_nodeP' (i : I) : ShW (cNode W WP p μ) (nodeP' W WP p i) := by
  unfold nodeP' cNode
  refine (sh_drawT μ WP.ri).bind fun r => ?_
  have h := sh_commitE (lam := lam) (K := W.K) (L := L) μ p.sMT W.depth fun j =>
    if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true) else (none, false)
  rw [cTree_node W fun j => some (.inl (L.encodeIndex i r j))] at h
  exact h.bind0 fun _ => .pure _

theorem sh_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    ShW (cProveB μ p.sMT p.sFS W.T WP.T 1) (proveT W WP p tree i r) :=
  (sh_proveB μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [some ()]).bind0 fun _ => .pure _

theorem sh_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    ShW (cProveB μ p.sMT p.sFS W.Lk WP.Lk 1) (proveLk W WP p root tree i r₀ r) :=
  (sh_proveB μ _ _ _ _ _ _ _ _ _ _ _ _ _ _ [some ()]).bind0 fun _ => .pure _

theorem sh_leavesC (i : I) (root : Node lam L) :
    ∀ n, ShW (n * cLeaf W WP p μ) (leavesC W WP p i root n)
  | 0 => (Sh.pure _).cast (by omega)
  | n + 1 => by
      have h := (sh_nodeP' W WP p μ i).bind
        (g := fun nd =>
            (proveLk W WP p root.tree nd.tree i root.r nd.r).bind fun π =>
              (leavesC W WP p i root n).bind fun rest => Step.pure (⟨nd, π⟩ :: rest)) fun nd =>
                (sh_proveLk W WP p μ _ _ _ _ _).bind fun π =>
                  (sh_leavesC i root n).bind0 fun _ => .pure _
      refine h.cast ?_
      unfold cLeaf
      rw [Nat.succ_mul]
      omega

theorem sh_Cp (i : I) : ShW (off W WP p μ (p.M + 1)) (Cp W WP p i) :=
  ((sh_nodeP' W WP p μ i).bind fun _ =>
      (sh_proveT W WP p μ _ _ _).bind fun _ =>
        (sh_leavesC W WP p μ i _ (p.M + 1)).bind0 fun _ => .pure _).cast
    (by unfold off; omega)

/-! ### What `erase` makes of the programs, on every store -/

/-- the weight of the `Node` of a copy or of the first encoding -/
theorem wt_nodeP' (i : I) (vs : List Bits) : Wt μ (cNode W WP p μ) (erase (nodeP' W WP p i) vs) :=
  (sh_nodeP' W WP p μ i).wt vs

/-- the weight of the compiled Test -/
theorem wt_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) (vs : List Bits) :
    Wt μ (cProveB μ p.sMT p.sFS W.T WP.T 1) (erase (proveT W WP p tree i r) vs) :=
  (sh_proveT W WP p μ tree i r).wt vs

/-- the weight of a compiled Link -/
theorem wt_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) (vs : List Bits) :
    Wt μ (cProveB μ p.sMT p.sFS W.Lk WP.Lk 1) (erase (proveLk W WP p root tree i r₀ r) vs) :=
  (sh_proveLk W WP p μ root tree i r₀ r).wt vs

/-- the weight of n copies -/
theorem wt_leavesC (i : I) (root : Node lam L) (n : ℕ) (vs : List Bits) :
    Wt μ (n * cLeaf W WP p μ) (erase (leavesC W WP p i root n) vs) :=
  (sh_leavesC W WP p μ i root n).wt vs

/-- the whole committer: `off` .. (M + 1) is the weight of all its samples -/
theorem wt_C (i : I) : Wt μ (off W WP p μ (p.M + 1)) (C W WP p i) :=
  wt_realQ (((sh_Cp W WP p μ i).wt []).bind (m := 0) fun _ => .pure _)

theorem avoids_nodeP' (i : I) (vs : List Bits) : (erase (nodeP' W WP p i) vs).Avoids OracleName.other :=
  (sh_nodeP' W WP p (fun _ => 0) i).avoids vs

theorem avoids_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) (vs : List Bits) :
    (erase (proveT W WP p tree i r) vs).Avoids OracleName.other :=
  (sh_proveT W WP p (fun _ => 0) tree i r).avoids vs

theorem avoids_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) (vs : List Bits) :
    (erase (proveLk W WP p root tree i r₀ r) vs).Avoids OracleName.other :=
  (sh_proveLk W WP p (fun _ => 0) root tree i r₀ r).avoids vs

theorem avoids_leavesC (i : I) (root : Node lam L) (n : ℕ) (vs : List Bits) :
    (erase (leavesC W WP p i root n) vs).Avoids OracleName.other :=
  (sh_leavesC W WP p (fun _ => 0) i root n).avoids vs

theorem avoids_C (i : I) : (C W WP p i).Avoids OracleName.other :=
  avoids_realQ OracleName.other (fun _ h => by cases h) _
    (Derive.Avoids.bind ((sh_Cp W WP p (fun _ => 0) i).avoids []) fun _ => trivial)

end Star

/-- The compiled prover never queries the auxiliary oracle: for every tag, protocol, wire record,
flags, list of slots and store. -/
theorem avoids_proveB {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (sMT sFS : ℕ) (t : Tag) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt' : Type} (H : BatchHonestProver Q Wt') (wq : ProtocolQueryLayout lam K Q)
    (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
    (trees : List (TreeH lam)) (w : Wt') (fl : ℕ → Bool) (xs : List (Option Y)) (vs : List Bits) :
    (erase (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs).Avoids OracleName.other :=
  (sh_proveB (fun _ => 0) sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs).avoids vs

end Seed
end Compile.Batch
