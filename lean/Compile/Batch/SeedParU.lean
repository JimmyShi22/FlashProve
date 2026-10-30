-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedParU.lean: the compiled prover that makes no query and builds no tree for an empty
slot does not look at the numbers of its tokens, if there are 2^depthReq slots. (Words of this
library: lean/GLOSSARY.md.)

`par_proveBU`: the prover `proveBU` of Compile/Batch/ProverU.lean, given the trees over the encoded
indices with their tokens shown through `Life2.up` and run on a store, and the same prover given the
trees themselves and run on the store without the δ strings after the first N₀, make the same
queries, take the same samples and return the same proof strings (`Compile.Seed.Par`,
Compile/SeedKit.lean).

One hypothesis: the number of slots is 2^depthReq. Without it the statement is false: with no slot
at all, say, the root of the request tree is the default value 0, which the Fiat-Shamir query of the
joining round then reads.

Empty slots. In `proveBU` the tokens of a slot without a request are default values (the number 0,
an empty list), which no program reads, and its list of trees does not follow the rounds. So the
relation of the two runs (`RelAccU`) requires of an empty slot that it is the same in both runs, and
of a slot with a request what Compile/Batch/SeedParSlot.lean requires.

Notation: `N₀`, `δ`: natural numbers; `up N₀ δ v`: v if v < N₀, else v + δ
(Compile/Step1_life2_Virt.lean); `Par N₀ δ r c c'`: the two programs run alike, the first on a
store, the second on the store without the δ strings after the first N₀ (Compile/SeedKit.lean); `b`
in `RelAccU b dJ a a'`: a `Bool`, handed to `upAcc N₀ δ b`: the field c is under `up` only if b is
true (Compile/Batch/SeedParSlot.lean); `par_chainTU` has `chainsHaveJoined ph` there; `dJ`, `d0`: lists of
natural numbers: the depths of the rounds already done; `sMT`, `sFS`: natural numbers: the length of
the salt of a leaf, and of the salt of a chain (Compile/Batch/Verifier.lean); `RelFin`: the relation
that the proof strings need: of a slot without a request it asks only that it is empty in both runs
(Compile/Batch/SeedParSlot.lean); `FullLv d lv`: d + 1 levels of the lengths 2^d, .., 2, 1
(Compile/Batch/SeedParTree.lean).

Limits: nothing about distributions; nothing about the prover `proveB`, in which an empty slot is
hashed like any other.
-/
import Compile.Batch.SeedParSlot
import Compile.Batch.ProverU

noncomputable section

open Rom Iop

namespace Compile.Batch
namespace Seed

open Life2 (up)
open Compile.Seed (Par upTree)
open List (Forall₂)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {Y : Type} (N₀ δ : ℕ)

/-! ## Part 1. The relation of the two runs; the rounds -/

/-- the state of a slot: a slot with a request as in `RelAcc`; an empty slot is the same in both
runs -/
def RelAccU (b : Bool) (dJ : List ℕ) (a a' : SlotAcc lam K Y) : Prop :=
  (a'.x ≠ none ∧ RelAcc N₀ δ b dJ a a') ∨ (a'.x = none ∧ a = a')

def RelZU {s : Shape} (b : Bool) (dJ : List ℕ) (z z' : SlotSt lam K Y s) : Prop :=
  z.1 = z'.1 ∧ RelAccU N₀ δ b dJ z.2 z'.2

variable {N₀ δ}

theorem RelZU.fin {s : Shape} {b : Bool} {dJ : List ℕ}
    {z z' : SlotSt lam K Y s} (h : RelZU N₀ δ b dJ z z') : RelFin N₀ δ dJ z.2 z'.2 := by
  rcases h.2 with ⟨_, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by rw [h2.1]; rfl, fun _ => ⟨b, h2⟩⟩
  · exact ⟨by rw [h2], fun h => absurd h1 h⟩

/-- for a slot with a request, `RelZ` gives `RelZU` -/
theorem RelZU.live {s : Shape} {b : Bool} {dJ : List ℕ} {z z' : SlotSt lam K Y s}
    (h : RelZ N₀ δ b dJ z z') (hx : z'.2.x ≠ none) : RelZU N₀ δ b dJ z z' :=
  ⟨h.1, .inl ⟨hx, h.2⟩⟩

/-- the two cases of the relation -/
theorem RelZU.cases {s : Shape} {b : Bool} {dJ : List ℕ}
    {z z' : SlotSt lam K Y s} (h : RelZU N₀ δ b dJ z z') :
    (∃ y, z.2.x = some y ∧ z'.2.x = some y ∧ RelZ N₀ δ b dJ z z') ∨ (z'.2.x = none ∧ z = z') := by
  rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · obtain ⟨y, hy⟩ := Option.ne_none_iff_exists'.1 h1
    exact .inl ⟨y, by rw [h2.1]; exact hy, hy, h.1, h2⟩
  · exact .inr ⟨h1, Prod.ext h.1 h2⟩

section Rounds
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem par_slotLoU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZU N₀ δ (chainsHaveJoined ph) dJ z z') :
    Par N₀ δ (RelZU N₀ δ (chainsHaveJoined ph) (dJ ++ [w.depthJ]))
      (slotLoU sMT t cms xin a w emb plJ i (upPh N₀ δ ph) z)
      (slotLoU sMT t cms xin a w emb plJ i ph z') := by
  unfold slotLoU
  rcases h.cases with ⟨y, h1, h2, h3⟩ | ⟨h1, rfl⟩
  · rw [h1, h2]
    exact (par_slotLo sMT t cms xin a w emb plJ i ph z z' h3).mono fun o o' ho =>
      RelZU.live ho.1 (by rw [ho.2, h2]; exact fun e => by cases e)
  · rw [h1]
    exact Par.pure ⟨rfl, .inr ⟨h1, rfl⟩⟩

theorem par_slotJoinU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    {b : Bool} {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZU N₀ δ b dJ z z') :
    Par N₀ δ (RelZU N₀ δ true (dJ ++ [w.depthJ])) (slotJoinU sMT t a w emb plJ i z)
      (slotJoinU sMT t a w emb plJ i z') := by
  unfold slotJoinU
  rcases h.cases with ⟨y, h1, h2, h3⟩ | ⟨h1, rfl⟩
  · rw [h1, h2]
    exact (par_slotJoin sMT t a w emb plJ i z z' h3).mono fun o o' ho =>
      RelZU.live ho.1 (by rw [ho.2, h2]; exact fun e => by cases e)
  · rw [h1]
    exact Par.pure ⟨rfl, .inr ⟨h1, rfl⟩⟩

/-- the slot value of a slot after the joining round, or none: related by up in the two runs -/
theorem RelZU.cval {s : Shape} {dJ : List ℕ}
    {z z' : SlotSt lam K Y s} (h : RelZU N₀ δ true dJ z z') :
    (z.2.x.map fun _ => z.2.c) = (z'.2.x.map fun _ => z'.2.c).map (up N₀ δ) := by
  rcases h.cases with ⟨y, h1, h2, h3⟩ | ⟨h1, rfl⟩
  · rw [h1, h2, h3.c_eq]
    rfl
  · rw [h1]
    rfl

theorem par_joinMU {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    {b : Bool} {dJ : List ℕ} :
    ∀ {zs zs' : List (SlotSt lam K Y (r :: s))}, Forall₂ (RelZU N₀ δ b dJ) zs zs' →
      Par N₀ δ (fun o o' =>
          Forall₂ (RelZU N₀ δ true (dJ ++ [w.depthJ])) o.1 o'.1 ∧
          o.2 = o'.2.map (Option.map (up N₀ δ)) ∧
          o'.2.length = zs'.length ∧
          o'.1.length = zs'.length)
        (joinMU sMT t a w emb plJ i zs) (joinMU sMT t a w emb plJ i zs')
  | _, _, .nil => Par.pure ⟨.nil, rfl, rfl, rfl⟩
  | _, _, @Forall₂.cons _ _ _ z z' zs zs' h1 h2 => by
    show Par N₀ δ _
      ((slotJoinU sMT t a w emb plJ i z).bind fun y =>
        (joinMU sMT t a w emb plJ i zs).bind fun o =>
          Step.pure (y :: o.1, (y.2.x.map fun _ => y.2.c) :: o.2))
      ((slotJoinU sMT t a w emb plJ i z').bind fun y =>
        (joinMU sMT t a w emb plJ i zs').bind fun o =>
          Step.pure (y :: o.1, (y.2.x.map fun _ => y.2.c) :: o.2))
    refine (par_slotJoinU sMT t a w emb plJ i z z' h1).bind fun y y' hy =>
        (par_joinMU a w emb plJ i h2).bind fun o o' ho =>
      Par.pure ⟨.cons hy ho.1, ?_, congrArg (· + 1) ho.2.2.1, congrArg (· + 1) ho.2.2.2⟩
    show (y.2.x.map fun _ => y.2.c) :: o.2 =
      (y'.2.x.map fun _ => y'.2.c).map (up N₀ δ) :: o'.2.map (Option.map (up N₀ δ))
    rw [hy.cval, ho.2.1]

end Rounds

theorem relZU_hear_noted {r : Round} {s : Shape} {a : RAnn r}
    (w : WireRB lam K r a) (bl : Blk lam K) {b : Bool} {dJ : List ℕ}
    (z z' : SlotSt lam K Y (r :: s)) (h : RelZU N₀ δ b dJ z z') :
    RelZU N₀ δ b dJ (hear w bl true z) (hear w bl true z') := by
  rcases h.cases with ⟨y, _, h2, h3⟩ | ⟨h1, rfl⟩
  · exact RelZU.live (relZ_hear_noted w bl z z' h3)
      (by show z'.2.x ≠ none; rw [h2]; exact fun e => by cases e)
  · exact ⟨rfl, .inr ⟨h1, rfl⟩⟩

theorem relZU_hear {r : Round} {s : Shape} {a : RAnn r} (w : WireRB lam K r a) (bl : Blk lam K)
    {b : Bool} {dJ : List ℕ} (z z' : SlotSt lam K Y (r :: s)) (h : RelZU N₀ δ b dJ z z') :
    RelZU N₀ δ b (dJ ++ [w.depthJ]) (hear w bl false z) (hear w bl false z') := by
  rcases h.cases with ⟨y, _, h2, h3⟩ | ⟨h1, rfl⟩
  · exact RelZU.live (relZ_hear w bl z z' h3)
      (by show z'.2.x ≠ none; rw [h2]; exact fun e => by cases e)
  · exact ⟨rfl, .inr ⟨h1, rfl⟩⟩

theorem par_rleavesTU :
    ∀ cs : List (Option Tok), Par N₀ δ (fun a a' => a = a'.map (up N₀ δ) ∧ a'.length = cs.length)
      (rleavesTU (lam := lam) (K := K) (L := L) (cs.map (Option.map (up N₀ δ)))) (rleavesTU cs)
  | [] => Par.pure ⟨rfl, rfl⟩
  | some c :: t => by
    show Par N₀ δ _
      ((rleafT (up N₀ δ c)).bind fun d =>
        (rleavesTU (t.map (Option.map (up N₀ δ)))).bind fun r => Step.pure (d :: r))
      ((rleafT c).bind fun d => (rleavesTU t).bind fun r => Step.pure (d :: r))
    refine (par_rleafT c).bind fun d d' h => (par_rleavesTU t).bind fun r r' h' => ?_
    subst h
    obtain ⟨rfl, h2⟩ := h'
    exact Par.pure ⟨rfl, congrArg (· + 1) h2⟩
  | none :: t => by
    show Par N₀ δ _
      (Step.fresh lam fun d =>
        (rleavesTU (t.map (Option.map (up N₀ δ)))).bind fun r => Step.pure (d :: r))
      (Step.fresh lam fun d => (rleavesTU t).bind fun r => Step.pure (d :: r))
    refine Par.fresh lam fun d _ => (par_rleavesTU t).bind fun r r' h' => ?_
    obtain ⟨rfl, h2⟩ := h'
    exact Par.pure ⟨rfl, congrArg (· + 1) h2⟩

/-- The request tree over 2^depthReq slots, some of them empty: its tokens are related by up, and
its levels are full. -/
theorem par_reqTU (depthReq : ℕ) (cs : List (Option Tok)) (hc : cs.length = 2 ^ depthReq) :
    Par N₀ δ (fun a a' => a = upTT N₀ δ a' ∧ FullLv depthReq a'.levels)
      (reqTU (lam := lam) (K := K) (L := L) depthReq (cs.map (Option.map (up N₀ δ))))
      (reqTU depthReq cs) := by
  unfold reqTU
  refine (par_rleavesTU cs).bind fun ls ls' h => ?_
  obtain ⟨rfl, h1⟩ := h
  refine (par_levelsT parNode_rnodeT depthReq ls' (h1.trans hc)).bind fun lv lv' h' => ?_
  obtain ⟨rfl, hf⟩ := h'
  exact Par.pure ⟨rfl, hf⟩

/-! ## Part 2. The equations of chainTU, by the kind of the round and the phase -/

section Eqs
variable (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ) {r : Round}
  {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
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
  conv_lhs => unfold chainTU
  split <;> first | rfl | simp_all

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
  conv_lhs => unfold chainTU
  split <;> first | rfl | simp_all

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
  conv_lhs => unfold chainTU
  split <;> first | rfl | simp_all

theorem chainTU_skip (hk : a.kind = .sh) (ph : PhT) (hph : ph = .first ∨ ph = .aft) :
    chainTU sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      chainTU sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
        ph (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
        { a0 with trees := a0.trees ++ [none] } := by
  conv_lhs => unfold chainTU
  rcases hph with rfl | rfl <;> (split <;> first | rfl | simp_all)

end Eqs

/-! ## Part 3. The induction over the rounds -/

/-- All chains of a batch (`chainTU`, Compile/Batch/ProverU.lean). Under the hypotheses below, the
chains from the states with their tokens under `up N₀ δ` (`RelZU`: an empty slot is the same in both
runs) and the chains from the states themselves run alike (`Par`, Compile/SeedKit.lean), and their
results are related by `RelFin` (the slots) and `upAcc0` (the shared part). dJ, d0: the depths of
the rounds already done. -/
theorem par_chainTU (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph phu : PhT) (st0 : SStrat s A)
        (zs zs' : List (SlotSt lam K Y s)) (a0 a0u : Acc0) (dJ d0 : List ℕ),
      phu = upPh N₀ δ ph → a0u = upAcc0 N₀ δ a0 → Forall₂ (RelZU N₀ δ (chainsHaveJoined ph) dJ) zs zs' →
      zs'.length = 2 ^ depthReq → Good0 depthReq d0 a0 →
      Par N₀ δ (fun o o' =>
          Forall₂ (RelFin N₀ δ (dJ ++ depthsJ s A W)) o.1 o'.1 ∧
          o'.1.length = 2 ^ depthReq ∧
          o.2 = upAcc0 N₀ δ o'.2 ∧
          Good0 depthReq (d0 ++ depths0 s A W) o'.2)
        (chainTU sMT t cms xin depthReq s A W embS embP i phu st0 zs a0u)
        (chainTU sMT t cms xin depthReq s A W embS embP i ph st0 zs' a0)
  | [], _, _, _, _, _, _, _, _, zs, zs', a0, _, dJ, d0, _, ha, hz, hl, h0 => by
    subst ha
    refine Par.pure ⟨?_, by simpa using hl, rfl, ?_⟩
    · simp only [depthsJ, List.append_nil]
      exact forall₂_map (fun _ _ h => h.fin) hz
    · simpa only [depths0, List.append_nil] using h0
  | r :: s, (a, A), (w, W), embS, embP, i, ph, _, (m0, k0), zs, zs', a0, _, dJ, d0, rfl, rfl, hz, hl, h0 => by
    have eJ : dJ ++ depthsJ (r :: s) (a, A) (w, W) = (dJ ++ [w.depthJ]) ++ depthsJ s A W := by
      simp [depthsJ]
    have e0 : d0 ++ depths0 (r :: s) (a, A) (w, W) = (d0 ++ [w.depth0]) ++ depths0 s A W := by
      simp [depths0]
    rw [eJ, e0]
    rcases kind_cases a.kind with hk | hk
    · rw [chainTU_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk,
        chainTU_lo _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
      refine Par.bind (par_eachM (fun z z' h => par_slotLoU sMT t cms xin a w _ _ i ph z z' h) hz)
        fun ys ys' hy => ?_
      exact par_chainTU sMT t cms xin depthReq s A W _ _ (i + 1) ph.afterLo _ _ ys ys'
        { a0 with trees := a0.trees ++ [none] } _ (dJ ++ [w.depthJ]) (d0 ++ [w.depth0])
        (upPh_afterLo ph) (by simp [upAcc0]) (by rw [joined_afterLo]; exact hy.1)
        (hy.2.trans hl) ⟨h0.1.snoc_none _, h0.2⟩
    · cases ph with
      | loc =>
        simp only [upPh]
        rw [chainTU_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk,
          chainTU_join _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
        refine Par.bind (par_joinMU sMT t a w _ _ i hz) fun o o' ho => ?_
        obtain ⟨h1, h2, h3, h4⟩ := ho
        rw [h2]
        refine Par.bind (par_reqTU depthReq o'.2 (h3.trans hl)) fun rq rq' hq => ?_
        obtain ⟨rfl, hfq⟩ := hq
        refine par_tree0 sMT a w _ m0 fun tr0 hf0 => ?_
        rw [root_upTT hfq, map_root_up hf0]
        refine par_fbG w.gr0 w.chal t i rq'.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
          (fun _ => f4_inj cms) _ _ fun nc dd bl tl _ => ?_
        exact par_chainTU sMT t cms xin depthReq s A W _ _ (i + 1) (.shr tl) _ _ _ _
          { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq',
            nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
          _ (dJ ++ [w.depthJ]) (d0 ++ [w.depth0]) rfl (by simp [upAcc0])
          (forall₂_map (relZU_hear_noted w bl) h1) (by rw [List.length_map]; exact h4.trans hl)
          ⟨h0.1.snoc hf0, fun _ e => by cases e; exact hfq⟩
      | shr tk0 =>
        simp only [upPh]
        rw [chainTU_shr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk,
          chainTU_shr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk]
        refine par_tree0 sMT a w _ m0 fun tr0 hf0 => ?_
        rw [map_root_up hf0]
        refine par_fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
          (fun _ => f5_inj) _ _ fun nc dd bl tl _ => ?_
        exact par_chainTU sMT t cms xin depthReq s A W _ _ (i + 1) (.shr tl) _ _ _ _
          { a0 with
            trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
            nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
          _ (dJ ++ [w.depthJ]) (d0 ++ [w.depth0]) rfl (by simp [upAcc0])
          (forall₂_map (relZU_hear w bl) hz)
          (by rw [List.length_map]; exact hl) ⟨h0.1.snoc hf0, h0.2⟩
      | first =>
        simp only [upPh]
        rw [chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (.inl rfl),
          chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (.inl rfl)]
        exact par_chainTU sMT t cms xin depthReq s A W _ _ (i + 1) .first _ _ _ _
          { a0 with trees := a0.trees ++ [none] } _ (dJ ++ [w.depthJ]) (d0 ++ [w.depth0]) rfl
          (by simp [upAcc0]) (forall₂_map (relZU_hear w _) hz)
          (by rw [List.length_map]; exact hl) ⟨h0.1.snoc_none _, h0.2⟩
      | aft =>
        simp only [upPh]
        rw [chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (.inr rfl),
          chainTU_skip _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hk _ (.inr rfl)]
        exact par_chainTU sMT t cms xin depthReq s A W _ _ (i + 1) .aft _ _ _ _
          { a0 with trees := a0.trees ++ [none] } _ (dJ ++ [w.depthJ]) (d0 ++ [w.depth0]) rfl
          (by simp [upAcc0]) (forall₂_map (relZU_hear w _) hz)
          (by rw [List.length_map]; exact hl) ⟨h0.1.snoc_none _, h0.2⟩

/-! ## Part 4. One execution -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
  (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

theorem par_initSlotU (c0 : H.Coin0) (x : Option Y) :
    Par N₀ δ (RelZU N₀ δ false []) (initSlotU (lam := lam) (K := K) (L := L) sFS Q H wp w c0 x)
      (initSlotU sFS Q H wp w c0 x) := by
  cases x with
  | none => exact Par.pure ⟨rfl, .inr ⟨rfl, rfl⟩⟩
  | some x =>
    exact (par_initSlot sFS Q H wp w c0 (some x)).mono fun z z' h =>
      RelZU.live h.1 fun e => by rw [e] at h; exact absurd h.2 (by simp)

/-- The compiled prover `proveBU` does not look at the numbers of its tokens, if the number of slots
is 2^depthReq. -/
theorem par_proveBU (fl : ℕ → Bool) (xs : List (Option Y)) (hx : xs.length = 2 ^ depthReq) :
    Par N₀ δ Eq
      (proveBU sMT sFS t Q H wq wp embS embP xin depthReq (trees.map (upTree N₀ δ)) w fl xs)
      (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) := by
  unfold proveBU
  refine Par.bind (par_drawT wp.coin0) fun c0 c0' h => ?_
  subst h
  refine Par.bind
    (par_eachM (r := Eq) (fun x x' h => by subst h; exact par_initSlotU sFS Q H wp w c0 x)
      (List.forall₂_same.2 fun _ _ => rfl))
    fun zs zs' hz => ?_
  have hroots : (trees.map (upTree N₀ δ)).map TreeH.root = trees.map TreeH.root := by
    rw [List.map_map]
    rfl
  rw [hroots]
  refine Par.bind
    (par_chainTU sMT t (trees.map TreeH.root) (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape
      Q.ann wq.sh embS embP 0 .first .first (H.strat0 w c0) zs zs' ⟨[], [], none, [], []⟩
      ⟨[], [], none, [], []⟩ [] [] rfl rfl hz.1 (hz.2.trans hx) ⟨.nil, fun _ e => by cases e⟩)
    fun o o' ho => ?_
  obtain ⟨h1, h2, h3, h4⟩ := ho
  rw [h3]
  exact par_finishAll Q H wq wp trees w fl c0 h4 0 h1 (by omega)

end Prove

end Seed
end Compile.Batch
