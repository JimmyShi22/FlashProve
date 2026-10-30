-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Late2.lean: the chains of a batch (`chainT`, with its phases `PhT`:
Compile/Batch/Prover.lean) and the hashing of all chains of a batch in `LStep`, without points
(`skB`, Compile/Batch/Mirror.lean) are related by `Rom.Late`, under the hypotheses of `ChainStmt`
(proved, for `RoundsQueryLayout.OKG` and a coherent annotation, in Compile/Batch/Late2b.lean): the statement
(`ChainStmt`), with what the context knows at the end, and the step for a local round (`chain_lo`);
the rest: Compile/Batch/Late2b.lean (words of this library: lean/GLOSSARY.md; context, closure:
`Ctx`, `Clo`, Rom/DeferLate.lean).

How tokens are kept apart. At each moment the tokens to which a later query to a Fiat-Shamir oracle
or to g may still be charged are the active tokens: for each slot the token that its next query
holds, and in the shared rounds the last shared chaining value. They are distinct and older than the
bound (the n of `Late`: a new token has a number ≥ n). Everything else below the bound gets at most
closures without data (`baseC`, Compile/Batch/Mirror.lean) from then on (`Fr`). A token leaves the
active ones when it is charged; the new active token is younger than the bound.
A component without a tree (`has0`, `hasJ` false: Iop/BatchWire.lean). No tree is made there, the
accumulators note none, and the closure of the round's query writes no root. So a tree is an
`Option TTree`, and `TreeKO` is only about a tree that is there.
A round with proof-of-work bits (`grJ`, `gr0`: Iop/BatchWire.lean; the search over nonces: `fbG`,
Compile/Batch/Prover.lean; Compile/Batch/LateG.lean). All attempts of a search are charged to one
token, the active one: attempt 0 at `fb t`, attempt j + 1 at the ghost name `fbw t j`. So the
context learns several closures at that token (`setFb`), and `ctxB`, which supplies them at the
release, has to be told how many: the number of the final attempt. The accumulators note these
numbers, the newest first (`nons`); `SlotK` and `ChainPost` say that the lists which `ctxB` goes
through are these, in the order of the rounds (nN, nN0): this needs the search's guarantee `Kept`
(Compile/Batch/ProverG.lean): a number is passed on exactly if the round has such bits. The chaining
values of the attempts before the final one (`dead`; nD, nD0) are never active and never charged:
nothing but closures without data is ever recorded for them, so they can be shown at the release.
The conditions on the wire record are used in one place (`bodyAt_shared`: `place_posAt0`), in the
form for wire records whose rounds may have proof-of-work bits (`WireRB.OKG`).

Notation:
  `ChainStmt s A W`: the statement for one shape;
  `LoFact`: what is known of a slot at the end of a local round: Γ1 is the context then, Act' the
    active tokens then;
  `SlotK`: what is known of a slot at the end, seen from a round in the middle (its letters: see
    its doc comment);
  `Kept gr nc dd` (Compile/Batch/ProverG.lean): what the search guarantees of what it passes on;
  `fb t`, `fbw t j` (`OracleName`, Compile/Batch/Oracles.lean): the Fiat-Shamir oracle of the protocol t;
    an oracle of the analysis: the honest prover's program writes attempt number j + 1 as a query to
    `fbw t j`, at the same input;
  `setFb gr t l …` (Compile/Batch/Mirror.lean): the closures of the Fiat-Shamir queries of one
    round, associated with the first token of l;
  `nons`, `dead` (fields of `SlotAcc`, `Acc0`, Compile/Batch/Prover.lean): the numbers of the
    final attempts, the newest first; the chaining values of the attempts before the final ones;
  release (the head of Rom/Defer.lean): `reveal ts` releases every evaluation charged to a token
    of ts;
  `t`: a `Tag` (Compile/Oracles.lean): `test`, `link` or `onl` (in `Fr.set` a `Tok`);
  `cms`: a list of digests; in `chainsU` (Compile/Batch/SeedLazyDefs.lean): the roots of the trees
    over the external strings;
  `sMT`: a natural number; the length of the salt of a leaf (Compile/Batch/Verifier.lean);
  `depthReq`: a natural number; depth of a request tree (`QueryLayout.depthReq`, Iop/BatchWire.lean);
  `S0`: an `SStrat s A` (Iop/Batch.lean): a strategy for the shared part: m_0 in every round;
  `a0`: an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated.
-/
import Compile.Batch.LateG

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Active tokens and frames -/

/-- the token to which the next query of the slot is charged -/
def curOf {Y : Type} (ph : PhT) (acc : SlotAcc lam K Y) : ℕ :=
  match ph with
  | .shr _ => acc.c
  | _ => acc.tk

/-- below n and off the active tokens, Γ' records nothing beyond Γ but closures without data -/
def Fr (Act : List Tok) (n : ℕ) (Γ Γ' : Cx lam K L) : Prop :=
  ∀ u, n > u → u ∉ Act → ∀ o pt, Γ' u o = some pt → Γ u o = some pt ∨ baseC u o = some pt

theorem Fr.refl (Act : List Tok) (n : ℕ) (Γ : Cx lam K L) : Fr Act n Γ Γ := fun _ _ _ _ _ h =>
  Or.inl h

theorem Fr.of_ext {n : ℕ} {Γ Γ' : Cx lam K L} (h : Ext n Γ Γ') (Act : List Tok) : Fr Act n Γ Γ' :=
  fun u hu _ => h u hu

theorem Fr.trans {Act Act' : List Tok} {n n' : ℕ} {Γ Γ' Γ'' : Cx lam K L} (h : Fr Act n Γ Γ')
    (h' : Fr Act' n' Γ' Γ'') (hn : n ≤ n') (hA : ∀ a ∈ Act', a ∈ Act ∨ n ≤ a) :
    Fr Act n Γ Γ'' := fun u hu hua o pt hp =>
  (h' u (by omega) (fun hm => (hA u hm).elim hua (by omega)) o pt hp).elim (h u hu hua o pt) Or.inr

theorem Fr.set {Act : List Tok} {n : ℕ} (Γ : Cx lam K L) {t : Tok} (ht : t ∈ Act)
    (o : OracleName) (pt : Clo (spec lam K L) o) :
    Fr Act n Γ (Γ.set t o pt) := fun u _ hua o' pt' hp => by
  have hne : u ≠ t := fun e => hua (by rw [e]; exact ht)
  rw [Ctx.set_ne_tok Γ hne] at hp
  exact Or.inl hp

theorem Cov.fr {Act : List Tok} {n : ℕ} {Γ Γ' P : Cx lam K L} {u : Tok} (h : Cov Γ u P)
    (hF : Fr Act n Γ Γ') (hu : n > u) (hua : u ∉ Act) (hP : BaseUp P u) : Cov Γ' u P :=
  fun o pt hp => (hF u hu hua o pt hp).elim (h o pt) (hP o pt)

theorem Base.cov {Γ P : Cx lam K L} {u : Tok} (h : Base Γ u) (hP : BaseUp P u) : Cov Γ u P :=
  fun o pt hp => hP o pt (h o pt hp)

/-! ## One query -/

/-- the closure of the Fiat-Shamir query of a slot in a local round -/
def cloSlot (K : ℕ) (t : Tag) (cms : List (Dig lam)) (x : Option X) (i : ℕ) (ph : PhT)
    (has : Bool) (pl : PlainPart (shapeOf L t) (annOf L t)) : Clo (spec lam K L) (OracleName.fb t) :=
  match ph with
  | .first => cloFb K t i (fun _ => Head.f1 cms (x.map L.early)) has 0 pl
  | .shr _ => cloFb K t i (fun vs => Head.f3 (vs.headD [])) has 1 pl
  | _ => cloFb K t i (fun _ => Head.f2 (lateInstancePart L i x)) has 0 pl

/-- the header of the query of a slot in a local round, and the index of the root among the other
tokens of the query (the index: `rtOf`, below), by the phase -/
def hdOf (cms : List (Dig lam)) (x : Option X) (i : ℕ) (ph : PhT) : List Bits → Bits → Head lam X :=
  match ph with
  | .first => fun _ => Head.f1 cms (x.map L.early)
  | .shr _ => fun vs => Head.f3 (vs.headD [])
  | _ => fun _ => Head.f2 (lateInstancePart L i x)

def rtOf (ph : PhT) : ℕ :=
  match ph with
  | .shr _ => 1
  | _ => 0

theorem cloSlot_eq (t : Tag) (cms : List (Dig lam)) (x : Option X) (i : ℕ) (ph : PhT)
    (has : Bool) (pl : PlainPart (shapeOf L t) (annOf L t)) :
    cloSlot K t cms x i ph has pl = cloFb K t i (hdOf (L := L) cms x i ph) has (rtOf ph) pl := by
  cases ph <;> rfl

/-- The queries of a slot in a local round, with proof-of-work bits or without, under the hypotheses
below: the context learns the closures of all attempts made. -/
theorem late_fbSlotG {α β : Type} {post : ℕ → Cx lam K L → α → β → Prop} {r : Round} {a : RAnn r}
    (w : WireRB lam K r a) {P : Type} (gr : Option (GrW r.Chal P)) (t : Tag) (i : ℕ)
    (cms : List (Dig lam)) (x : Option X) (ph : PhT) {Y : Type} (acc : SlotAcc lam K Y)
    (root : Option Tok) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (pl : P)
    {k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L α}
    {k' : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β} {n : ℕ} {Γ : Cx lam K L}
    (has : Bool) (hs : root.isSome = has)
    (h : ∀ nc dd bl tl, Kept gr nc dd → n ≤ tl → (∀ u ∈ dd, n ≤ u ∧ u < tl) →
      Late post (tl + 1)
        (setFb gr t [curOf ph acc] i (hdOf (L := L) cms x i ph) has (rtOf ph) emb pl (nc.getD 0) Γ)
        (k nc dd bl tl) (k' nc dd bl tl)) :
    Late post n Γ (fbSlotG gr w.chal t i cms x ph acc.tk acc.c root emb pl k)
      (fbSlotGL w gr (ansB w) t ph acc.tk acc.c root none k') := by
  cases ph with
  | first => exact late_fbG w gr t i acc.tk [] root _ _ emb pl has hs h
  | loc => exact late_fbG w gr t i acc.tk [] root _ _ emb pl has hs h
  | shr tk0 => exact late_fbG w gr t i acc.c [tk0] root _ _ emb pl has hs h
  | aft => exact late_fbG w gr t i acc.tk [] root _ _ emb pl has hs h

/-- A Fiat-Shamir query of the shared chain, under the hypotheses below: the root is the only other
token of the query, if there is one. -/
theorem late_fbT0 {α β : Type} {post : ℕ → Cx lam K L → α → β → Prop} (t : Tag) (i : ℕ) (tk : Tok)
    (root : Option Tok) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (pl : PlainPart (shapeOf L t) (annOf L t))
    {k : Blk lam K → Tok → St lam K L α} {k' : Blk lam K → Tok → Lp lam K L β} {n : ℕ}
    {Γ : Cx lam K L} (has : Bool) (hs : root.isSome = has)
    (h : ∀ bl tl, n ≤ tl →
      Late post (tl + 1) (Γ.set tk (OracleName.fb t) (cloFb K t i hd has 0 pl)) (k bl tl) (k' bl tl)) :
    Late post n Γ (fbT t i tk [] root hd hinj pl k)
      (fbL t tk root.toList ⟨Finset.univ, Finset.univ_nonempty⟩ k') := by
  subst hs
  cases root <;> exact Late.marked h

/-- what the context knows of the tree over a component, if the component has one -/
def TreeKO (Γ : Cx lam K L) (n n' depth : ℕ) (leaf : ℕ → Body L) (tr : Option TTree) : Prop :=
  ∀ x, tr = some x → TreeK Γ n n' depth leaf x

/-- what the context knows of the trees over a component with a list of trees (ds: the depths, in
the order in which the trees are made; `leaf j`: the leaves of tree number j): there are as many
trees as depths, and `TreeK` holds of tree number j at depth number j and the leaves `leaf j`; the
bounds n and n' are the same for all trees -/
def TreesKO (Γ : Cx lam K L) (n n' : ℕ) : List ℕ → (ℕ → ℕ → Body L) → List TTree → Prop
  | [], _, [] => True
  | d :: ds, leaf, tr :: trs =>
    TreeK Γ n n' d (leaf 0) tr ∧ TreesKO Γ n n' ds (fun j => leaf (j + 1)) trs
  | _, _, _ => False

/-- as many trees as depths -/
theorem TreesKO.length_eq {Γ : Cx lam K L} {n n' : ℕ} :
    ∀ {ds : List ℕ} {leaf : ℕ → ℕ → Body L} {trs : List TTree},
      TreesKO Γ n n' ds leaf trs → trs.length = ds.length
  | [], _, [], _ => rfl
  | _ :: _, _, _ :: _, h => congrArg (· + 1) (TreesKO.length_eq h.2)
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- the knowledge of a tree survives wider bounds and every context that agrees with Γ below the
upper bound -/
theorem TreeK.frame {Γ Γ' : Cx lam K L} {n n' m m' depth : ℕ} {leaf : ℕ → Body L} {tr : TTree}
    (h : TreeK Γ n n' depth leaf tr) (h1 : m ≤ n) (h2 : n' ≤ m') (e : ∀ u, u < n' → Γ' u = Γ u) :
    TreeK Γ' m m' depth leaf tr :=
  ⟨h.sized, fun j hj =>
      ⟨(h.salts j hj).1.congr (e _ (h.salts j hj).2.2), h1.trans (h.salts j hj).2.1,
        Nat.lt_of_lt_of_le (h.salts j hj).2.2 h2⟩,
    fun u hu =>
      ⟨h1.trans (h.digs u hu).1, Nat.lt_of_lt_of_le (h.digs u hu).2.1 h2,
        (h.digs u hu).2.2.congr (e u (h.digs u hu).2.1)⟩⟩

theorem TreesKO.frame {Γ Γ' : Cx lam K L} {n n' m m' : ℕ} (h1 : m ≤ n) (h2 : n' ≤ m')
    (e : ∀ u, u < n' → Γ' u = Γ u) :
    ∀ {ds : List ℕ} {leaf : ℕ → ℕ → Body L} {trs : List TTree},
      TreesKO Γ n n' ds leaf trs → TreesKO Γ' m m' ds leaf trs
  | [], _, [], _ => trivial
  | _ :: _, _, _ :: _, h => ⟨h.1.frame h1 h2 e, TreesKO.frame h1 h2 e h.2⟩
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- the tree over a component, if it has one, under `hF`: related if the continuations are, at every
tree that may come, with what the context knows of it -/
theorem late_withTree {α β : Type} {post : ℕ → Cx lam K L → α → β → Prop} (sMT : ℕ) (has : Bool)
    (depth : ℕ) (leaf : ℕ → Body L) {k : Option TTree → St lam K L α}
    {k' : Option TTree → Lp lam K L β} {n : ℕ} {Γ : Cx lam K L} (hF : Fut n Γ)
    (h : ∀ (nt : ℕ) (Γt : Cx lam K L) (tr : Option TTree), tr.isSome = has → n ≤ nt → Fut nt Γt →
      (∀ u, u < n → Γt u = Γ u) → TreeKO Γt n nt depth leaf tr → Late post nt Γt (k tr) (k' tr)) :
    Late post n Γ (withTree sMT has depth leaf k) (withTreeL sMT has depth k') := by
  cases has with
  | true =>
    refine Late.bind (late_commitT sMT depth leaf hF) fun nt Γt tr tr' h1 => ?_
    obtain ⟨rfl, a1, hFt, frt, hT⟩ := h1
    exact h nt Γt (some tr) rfl a1 hFt frt fun x hx => by obtain rfl := Option.some.inj hx; exact hT
  | false => exact h n Γ none rfl le_rfl hF (fun _ _ => rfl) fun x hx => absurd hx (by simp)

/-- the trees over a component with a list of trees, under `Fut n Γ`: related if the continuations
are, at all trees that may come, with what the context knows of them -/
theorem late_withTrees {α β : Type} {post : ℕ → Cx lam K L → α → β → Prop} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) {k : List TTree → St lam K L α}
      {k' : List TTree → Lp lam K L β} {n : ℕ} {Γ : Cx lam K L}, Fut n Γ →
      (∀ (nt : ℕ) (Γt : Cx lam K L) (trs : List TTree), trs.length = ds.length → n ≤ nt →
        Fut nt Γt → (∀ u, u < n → Γt u = Γ u) → TreesKO Γt n nt ds leaf trs →
        Late post nt Γt (k trs) (k' trs)) →
      Late post n Γ (withTrees sMT ds leaf k) (withTreesL sMT ds k')
  | [], _, _, _, n, Γ, hF, h => h n Γ [] rfl le_rfl hF (fun _ _ => rfl) trivial
  | d :: ds, leaf, _, _, _, _, hF, h =>
    Late.bind (late_commitT sMT d (leaf 0) hF) fun n1 Γ1 tr tr' h1 => by
      obtain ⟨rfl, a1, hF1, fr1, hT1⟩ := h1
      exact late_withTrees sMT ds (fun j => leaf (j + 1)) hF1 fun nt Γt trs hl a2 hFt fr2 hT2 =>
        h nt Γt (tr :: trs) (congrArg (· + 1) hl) (a1.trans a2) hFt
          (fun u hu => (fr2 u (Nat.lt_of_lt_of_le hu a1)).trans (fr1 u hu))
          ⟨hT1.frame le_rfl a2 fr2, hT2.frame a1 le_rfl fun _ _ => rfl⟩

/-- the accumulator after a local round -/
def updLo {Y : Type} (acc : SlotAcc lam K Y) (tr : Option TTree) (nc : Option ℕ) (dd : List Tok)
    (bl : Blk lam K) (tl : Tok) : SlotAcc lam K Y :=
  { acc with
    tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [tr], toks := acc.toks ++ [tl],
    nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead }

section Slot
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem late_slotLo {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (m : r.Msg) (k : r.Chal → Strat s Unit) (acc : SlotAcc lam K Y) {n : ℕ}
    {Γ : Cx lam K L} (hF : Fut n Γ) :
    Late (fun n' Γ' x y =>
        ∃ (tr : Option TTree) (nc : Option ℕ) (dd : List Tok) (bl : Blk lam K)
            (tl nt : ℕ) (Γt : Cx lam K L),
          x = (k (w.chal bl), updLo acc tr nc dd bl tl) ∧
          y = (none, updLo acc tr nc dd bl tl) ∧
          n ≤ nt ∧ nt ≤ tl ∧ n' = tl + 1 ∧ Fut nt Γt ∧
          (∀ u, u < n → Γt u = Γ u) ∧
          TreeKO Γt n nt w.depthJ (bodyAt w.posAtJ emb m.1) tr ∧
          Kept w.grJ nc dd ∧
          (∀ u ∈ dd, nt ≤ u ∧ u < tl) ∧
          Γ' = setFb w.grJ t [curOf ph acc] i (hdOf (L := L) cms (acc.x.bind xin) i ph) w.hasJ
              (rtOf ph) plJ (a.plain m.2).2 (nc.getD 0) Γt)
      n Γ (slotLo sMT t cms xin a w emb plJ i ph ((m, k), acc))
      (skSlotLo sMT t w ph ((none : Option (Rho (r :: s))), acc)) := by
  rw [slotLo, skSlotLo]
  refine late_withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1)
    hF fun nt Γt tr hs a1 hFt frt hT => ?_
  refine late_fbSlotG w w.grJ t i cms (acc.x.bind xin) ph acc (tr.map TTree.root) plJ _ w.hasJ
    (by rw [Option.isSome_map, hs]) fun nc dd bl tl hK htl hdd => Late.pure ?_
  exact ⟨tr, nc, dd, bl, tl, nt, Γt, rfl, rfl, a1, htl, rfl, hFt, frt, hT, hK, hdd, rfl⟩

/-- the accumulator after the slot's part of the joining round -/
def updJoin {Y : Type} (acc : SlotAcc lam K Y) (tr : Option TTree) (c : Tok) : SlotAcc lam K Y :=
  { acc with c := c, trees := acc.trees ++ [tr], toks := acc.toks ++ [c] }

theorem late_slotJoin {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (m : r.Msg) (k : r.Chal → Strat s Unit) (acc : SlotAcc lam K Y) {n : ℕ}
    {Γ : Cx lam K L} (hF : Fut n Γ) :
    Late (fun n' Γ' x y =>
        ∃ (tr : Option TTree) (c nt : ℕ) (Γt : Cx lam K L), x = ((m, k), updJoin acc tr c) ∧
          y = (none, updJoin acc tr c) ∧ n ≤ nt ∧ nt ≤ c ∧ n' = c + 1 ∧ Fut nt Γt ∧
          (∀ u, u < n → Γt u = Γ u) ∧ TreeKO Γt n nt w.depthJ (bodyAt w.posAtJ emb m.1) tr ∧
          Γ' = Γt.set acc.tk (OracleName.g t) (cloG K t i w.hasJ (plJ (a.plain m.2).2)))
      n Γ (slotJoin sMT t a w emb plJ i ((m, k), acc))
      (skSlotJoin sMT t w ((none : Option (Rho (r :: s))), acc)) := by
  rw [slotJoin, skSlotJoin]
  refine late_withTree sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1)
    hF fun nt Γt tr hs a1 hFt frt hT => ?_
  rw [← hs]
  cases tr <;> exact Late.marked fun _ c hc =>
      Late.pure ⟨_, c, nt, Γt, rfl, rfl, a1, hc, rfl, hFt, frt, hT, rfl⟩

end Slot

/-! ## The context that the release supplies -/

theorem setHd_ne (Pc : Cx lam K L) {l : List Tok} {u : Tok} (h : u ∉ l)
    (o : OracleName) (c : Clo (spec lam K L) o) : setHd Pc l o c u = Pc u := by
  cases l with
  | nil => rfl
  | cons b l => exact funext fun o' => Ctx.set_ne_tok Pc (fun e => h (by rw [e]; simp)) o c o'

theorem baseUp_setHd (Pc : Cx lam K L) {u : Tok} (h : BaseUp Pc u) (l : List Tok) {o : OracleName}
    (c : Clo (spec lam K L) o) (ho : ∀ v, (baseC : Cx lam K L) v o = none) :
    BaseUp (setHd Pc l o c) u := by
  cases l with
  | nil => exact h
  | cons b l => exact baseUp_set Pc h b c ho

theorem ctxB_ne (t : Tag) (cms : List (Dig lam)) (x : Option X) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (tj t0 : List Tok)
        (nJ n0 : List ℕ) (pls : Plains s) (Pc : Cx lam K L) (u : Tok),
      u ∉ tj → u ∉ t0 → ctxB t cms x s A W embP i ph tj t0 nJ n0 pls Pc u = Pc u
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, ph, tj, t0, nJ, n0, (pl, pls), Pc, u, hj, hs => by
      have htl : ∀ l : List Tok, u ∉ l → u ∉ l.tail := fun l hl hm => hl (List.mem_of_mem_tail hm)
      unfold ctxB
      cases a.kind with
      | lo =>
        simp only
        rw [ctxB_ne t cms x s A W _ _ _ _ _ _ _ _ _ u (htl tj hj) hs]
        cases ph <;> exact setFb_ne _ _ _ _ _ _ _ _ _ Pc hj
      | sh =>
        cases ph with
        | loc =>
          simp only
          rw [ctxB_ne t cms x s A W _ _ _ _ _ _ _ _ _ u (htl tj hj) (htl t0 hs),
            setFb_ne _ _ _ _ _ _ _ _ _ _ hs, setHd_ne _ hj]
        | shr tk0 =>
          simp only
          rw [ctxB_ne t cms x s A W _ _ _ _ _ _ _ _ _ u hj (htl t0 hs),
            setFb_ne _ _ _ _ _ _ _ _ _ Pc hs]
        | first => exact ctxB_ne t cms x s A W _ _ _ _ _ _ _ _ _ u hj hs
        | aft => exact ctxB_ne t cms x s A W _ _ _ _ _ _ _ _ _ u hj hs

theorem baseUp_ctxB (t : Tag) (cms : List (Dig lam)) (x : Option X) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
        (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (tj t0 : List Tok)
        (nJ n0 : List ℕ) (pls : Plains s) (Pc : Cx lam K L) (u : Tok),
      BaseUp Pc u → BaseUp (ctxB t cms x s A W embP i ph tj t0 nJ n0 pls Pc) u
  | [], _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | _ :: s, (a, A), (w, W), embP, i, ph, tj, t0, nJ, n0, (pl, pls), Pc, u, h => by
      unfold ctxB
      cases a.kind with
      | lo =>
        refine baseUp_ctxB t cms x s A W _ _ _ _ _ _ _ _ _ u ?_
        cases ph <;> exact baseUp_setFb _ _ _ _ _ _ _ _ _ Pc h _
      | sh =>
        cases ph with
        | loc =>
          exact baseUp_ctxB t cms x s A W _ _ _ _ _ _ _ _ _ u
            (baseUp_setFb _ _ _ _ _ _ _ _ _ _ (baseUp_setHd _ h _ _ fun _ => rfl) _)
        | shr tk0 =>
          exact baseUp_ctxB t cms x s A W _ _ _ _ _ _ _ _ _
            u (baseUp_setFb _ _ _ _ _ _ _ _ _ Pc h _)
        | first => exact baseUp_ctxB t cms x s A W _ _ _ _ _ _ _ _ _ u h
        | aft => exact baseUp_ctxB t cms x s A W _ _ _ _ _ _ _ _ _ u h

/-! ## What openings need -/

/-- what the context knows of a token tree, without bounds -/
structure OpenK (Γ : Cx lam K L) (depth : ℕ) (leaf : ℕ → Body L) (tr : TTree) : Prop where
  sized : Sized depth tr.levels
  salts : ∀ j, j < 2 ^ depth → KSalt Γ (leaf j) (tr.salts.getD j 0)
  digs : ∀ u ∈ tr.levels.flatten, Base Γ u

/-- What the context knows, without bounds, of the trees of a component with a list of trees: depths
and trees are paired in their order, the first pair has the number k, and `OpenK` holds of each
pair at the leaves of its number. Nothing is said of a tree beyond the last depth, nor of a depth
beyond the last tree. -/
def OpensK (Γ : Cx lam K L) (leaf : ℕ → ℕ → Body L) : ℕ → List ℕ → List TTree → Prop
  | k, d :: ds, tr :: trs => OpenK Γ d (leaf k) tr ∧ OpensK Γ leaf (k + 1) ds trs
  | _, _, _ => True

/-- no tree: nothing is asked, whatever the depths -/
theorem opensK_nil (Γ : Cx lam K L) (leaf : ℕ → ℕ → Body L) (k : ℕ) (ds : List ℕ) :
    OpensK Γ leaf k ds [] := by
  cases ds <;> trivial

/-- if there are no more trees than depths, only closures without data are recorded for the root of
each tree -/
theorem opensK_root {Γ : Cx lam K L} {leaf : ℕ → ℕ → Body L} :
    ∀ {k : ℕ} {ds : List ℕ} {trs : List TTree},
      OpensK Γ leaf k ds trs → trs.length ≤ ds.length → ∀ tr ∈ trs, Base Γ tr.root
  | _, _, [], _, _, _, hm => absurd hm (by simp)
  | _, [], _ :: _, _, hl, _, _ => absurd hl (by simp)
  | _, _ :: _, _ :: _, h, hl, tr, hm => by
    rcases List.mem_cons.1 hm with rfl | hm
    · exact h.1.digs _ (sized_root _ _ h.1.sized)
    · exact opensK_root h.2 (Nat.le_of_succ_le_succ hl) tr hm

/-- to count from k + 1 is to count from k at the leaves of the next tree -/
theorem opensK_succ (Γ : Cx lam K L) (leaf : ℕ → ℕ → Body L) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree),
      OpensK Γ leaf (k + 1) ds trs ↔ OpensK Γ (fun j => leaf (j + 1)) k ds trs
  | _, [], _ => Iff.rfl
  | _, _ :: _, [] => Iff.rfl
  | k, _ :: ds, _ :: trs => and_congr_right fun _ => opensK_succ Γ leaf (k + 1) ds trs

theorem TreeK.openK {Γ : Cx lam K L} {n n' depth : ℕ} {leaf : ℕ → Body L}
    {tr : TTree} (h : TreeK Γ n n' depth leaf tr) :
    OpenK Γ depth leaf tr := ⟨h.sized, fun j hj => (h.salts j hj).1, fun u hu => (h.digs u hu).2.2⟩

theorem TreesKO.opensK {Γ : Cx lam K L} {n n' : ℕ} :
    ∀ {ds : List ℕ} {leaf : ℕ → ℕ → Body L} {trs : List TTree},
      TreesKO Γ n n' ds leaf trs → OpensK Γ leaf 0 ds trs
  | [], _, [], _ => trivial
  | _ :: ds, leaf, _ :: trs, h =>
    ⟨h.1.openK, (opensK_succ Γ leaf 0 ds trs).2 (TreesKO.opensK h.2)⟩
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- the knowledge of a tree depends on the context only at the tokens between its bounds -/
theorem TreeK.congr {Γ Γ' : Cx lam K L} {n n' depth : ℕ} {leaf : ℕ → Body L} {tr : TTree}
    (h : TreeK Γ n n' depth leaf tr) (e : ∀ u, n ≤ u → n' > u → Γ' u = Γ u) :
    TreeK Γ' n n' depth leaf tr :=
  ⟨h.sized, fun j hj =>
      ⟨(h.salts j hj).1.congr (e _ (h.salts j hj).2.1 (h.salts j hj).2.2), (h.salts j hj).2⟩,
    fun u hu =>
      ⟨(h.digs u hu).1, (h.digs u hu).2.1,
        (h.digs u hu).2.2.congr (e u (h.digs u hu).1 (h.digs u hu).2.1)⟩⟩

theorem TreeK.mono {Γ : Cx lam K L} {n n' m m' depth : ℕ} {leaf : ℕ → Body L} {tr : TTree}
    (h : TreeK Γ n n' depth leaf tr) (h1 : m ≤ n) (h2 : n' ≤ m') : TreeK Γ m m' depth leaf tr :=
  ⟨h.sized, fun j hj =>
      ⟨(h.salts j hj).1,
        by have := (h.salts j hj).2.1; omega,
        by have := (h.salts j hj).2.2; omega⟩,
    fun u hu =>
      ⟨by have := (h.digs u hu).1; omega, by have := (h.digs u hu).2.1; omega, (h.digs u hu).2.2⟩⟩

/-- the knowledge of a tree survives everything that leaves its tokens alone but for closures
without data -/
theorem TreeK.fr {Γ Γ' : Cx lam K L} {n n' m depth : ℕ} {leaf : ℕ → Body L}
    {tr : TTree} {Act : List Tok} (h : TreeK Γ n n' depth leaf tr) (hF : Fr Act m Γ Γ')
    (hm : n' ≤ m) (hA : ∀ a ∈ Act, n > a ∨ n' ≤ a) :
    TreeK Γ' n n' depth leaf tr := by
  have hna : ∀ u, n ≤ u → n' > u → u ∉ Act :=
    fun u h1 h2 hm' => by rcases hA u hm' with h | h <;> omega
  exact ⟨h.sized,
    fun j hj =>
      ⟨(h.salts j hj).1.fr hF (by have := (h.salts j hj).2.2; omega)
        (hna _ (h.salts j hj).2.1 (h.salts j hj).2.2)
      (baseUp_set _ (baseUp_base _) _ _ fun _ => rfl), (h.salts j hj).2⟩,
    fun u hu => ⟨(h.digs u hu).1, (h.digs u hu).2.1,
      (h.digs u hu).2.2.fr hF (by have := (h.digs u hu).2.1; omega)
        (hna u (h.digs u hu).1 (h.digs u hu).2.1) (baseUp_base u)⟩⟩

theorem TreeKO.congr {Γ Γ' : Cx lam K L} {n n' depth : ℕ} {leaf : ℕ → Body L} {tr : Option TTree}
    (h : TreeKO Γ n n' depth leaf tr) (e : ∀ u, n ≤ u → n' > u → Γ' u = Γ u) :
    TreeKO Γ' n n' depth leaf tr :=
  fun x hx => (h x hx).congr e

theorem TreesKO.congr {Γ Γ' : Cx lam K L} {n n' : ℕ} (e : ∀ u, n ≤ u → n' > u → Γ' u = Γ u) :
    ∀ {ds : List ℕ} {leaf : ℕ → ℕ → Body L} {trs : List TTree},
      TreesKO Γ n n' ds leaf trs → TreesKO Γ' n n' ds leaf trs
  | [], _, [], _ => trivial
  | _ :: _, _, _ :: _, h => ⟨h.1.congr e, TreesKO.congr e h.2⟩
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

theorem TreeKO.fr {Γ Γ' : Cx lam K L} {n n' m depth : ℕ} {leaf : ℕ → Body L}
    {tr : Option TTree} {Act : List Tok} (h : TreeKO Γ n n' depth leaf tr) (hF : Fr Act m Γ Γ')
    (hm : n' ≤ m) (hA : ∀ a ∈ Act, n > a ∨ n' ≤ a) :
    TreeKO Γ' n n' depth leaf tr := fun x hx => (h x hx).fr hF hm hA

theorem TreesKO.fr {Γ Γ' : Cx lam K L} {n n' m : ℕ} {Act : List Tok} (hF : Fr Act m Γ Γ')
    (hm : n' ≤ m) (hA : ∀ a ∈ Act, n > a ∨ n' ≤ a) :
    ∀ {ds : List ℕ} {leaf : ℕ → ℕ → Body L} {trs : List TTree},
      TreesKO Γ n n' ds leaf trs → TreesKO Γ' n n' ds leaf trs
  | [], _, [], _ => trivial
  | _ :: _, _, _ :: _, h => ⟨h.1.fr hF hm hA, TreesKO.fr hF hm hA h.2⟩
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim

/-- the trees of a slot's transcript: in each round the tree over the shared component and the tree
over the slot's, where they were made -/
def TreesKB (Γ : Cx lam K L) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    Tr s → List (Option TTree) → List (Option TTree) → Prop
  | [], _, _, _, _, tjs, t0s => tjs = [] ∧ t0s = []
  | _ :: s, (_, A), (w, W), emb, (m, _, τ), tjs, t0s =>
      (∀ tr, t0s.headD none = some tr →
        OpenK Γ w.depth0 (bodyAt w.posAt0 (fun p => emb (.inl p)) m.1) tr) ∧
      (∀ tr, tjs.headD none = some tr →
        OpenK Γ w.depthJ (bodyAt w.posAtJ (fun p => emb (.inl p)) m.1) tr) ∧
      TreesKB Γ s A W (fun p => emb (.inr p)) τ tjs.tail t0s.tail

/-! ## A local round, in all slots -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- what is known of a slot at the end of a local round: Γ1 is the context then, Act' the active
tokens then -/
structure LoFact {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (ph : PhT) (n n1 : ℕ) (Γ1 : Cx lam K L) (Act' : List Tok)
    (z : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) : Prop where
  ex : ∃ (tr : Option TTree) (nc : Option ℕ) (dd : List Tok) (bl : Blk lam K) (tl lo hi : ℕ),
    z' = (z.1.2 (w.chal bl), updLo z.2 tr nc dd bl tl) ∧
    n ≤ tl ∧ n ≤ lo ∧ hi ≤ n1 ∧
    TreeKO Γ1 lo hi w.depthJ (bodyAt w.posAtJ emb z.1.1.1) tr ∧
    (∀ a' ∈ Act', lo > a' ∨ hi ≤ a') ∧
    Kept w.grJ nc dd ∧
    (∀ u ∈ dd, n ≤ u ∧ n1 > u ∧ u ∉ Act' ∧ Base Γ1 u) ∧
    ∀ P : Cx lam K L, BaseUp P (curOf ph z.2) →
      Cov (setFb w.grJ t [curOf ph z.2] i (hdOf (L := L) cms (z.2.x.bind xin) i ph) w.hasJ (rtOf ph)
          plJ (a.plain z.1.1.2).2 (nc.getD 0) (Ctx.empty _))
        (curOf ph z.2) P →
      Cov Γ1 (curOf ph z.2) P

theorem curOf_afterLo (ph : PhT) (acc : SlotAcc lam K Y) : curOf ph.afterLo acc = acc.tk := by
  cases ph <;> rfl

theorem late_eachLo {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (ph : PhT) (n₀ : ℕ) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (n : ℕ) (Γ : Cx lam K L), n₀ ≤ n → Fut n Γ →
      (zs.map fun z => curOf ph z.2).Pairwise (fun u v : ℕ => u < v) →
      (∀ z ∈ zs, n₀ > curOf ph z.2 ∧ Base Γ (curOf ph z.2)) →
      Late (fun n1 Γ1 xs ys =>
          ys = xs.map (fun x => ((none : Option (Rho s)), x.2)) ∧
          n ≤ n1 ∧ Fut n1 Γ1 ∧
          (∀ u, n > u → u ∉ zs.map (fun z => curOf ph z.2) → Γ1 u = Γ u) ∧
          (xs.map fun x => x.2.tk).Pairwise (fun u v : ℕ => u < v) ∧
          (∀ x ∈ xs, n ≤ x.2.tk ∧ n1 > x.2.tk ∧ Base Γ1 x.2.tk) ∧
          List.Forall₂ (LoFact t cms xin a w emb plJ i ph n n1 Γ1 (xs.map fun x => x.2.tk)) zs xs)
        n Γ (eachM (slotLo sMT t cms xin a w emb plJ i ph) zs)
        (eachL (skSlotLo sMT t w ph) (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)))
  | [], n, Γ, _, hF, _, _ =>
    Late.pure ⟨rfl, le_rfl, hF, fun _ _ _ => rfl, List.Pairwise.nil,
        fun x hx => absurd hx (by simp), List.Forall₂.nil⟩
  | ((m, k), acc) :: zs, n, Γ, hn0, hF, hpw, hz => by
      obtain ⟨hcur, hbase⟩ := hz ((m, k), acc) (by simp)
      rw [List.map_cons, List.pairwise_cons] at hpw
      obtain ⟨hlt, hpw'⟩ := hpw
      refine Late.bind (late_slotLo sMT t cms xin a w emb plJ i ph m k acc hF)
        fun n1 Γ1 x y h1 => ?_
      obtain ⟨tr, nc, dd, bl, tl, nt, Γt, rfl, rfl, a1, a2, rfl, hFt, frt, hT, hK, hdd, rfl⟩ := h1
      set cur := curOf ph acc with hcurdef
      set Γs := setFb w.grJ t [cur] i (hdOf (L := L) cms (acc.x.bind xin) i ph) w.hasJ (rtOf ph) plJ
        (a.plain m.2).2 (nc.getD 0) Γt with hΓs
      have hsne : ∀ v, v ≠ cur → Γs v = Γt v := fun v hv => setFb_ne_tok _ _ _ _ _ _ _ _ _ _ Γt hv
      have hF1 : Fut (tl + 1) Γs := fut_setFb _ _ _ _ _ _ _ _ _ _ hFt (by omega) (by omega)
      have hne : ∀ z ∈ zs, curOf ph z.2 ≠ cur := fun z hzm =>
        Nat.ne_of_gt (hlt _ (List.mem_map.2 ⟨z, hzm, rfl⟩))
      refine Late.bind
        (late_eachLo a w emb plJ i ph n₀ zs (tl + 1) _ (by omega) hF1 hpw' fun z hzm => ?_)
        fun n2 Γ2 xs ys h2 => Late.pure ?_
      · obtain ⟨c1, c2⟩ := hz z (by simp [hzm])
        exact ⟨c1, (c2.congr (frt _ (by omega))).congr (hsne _ (hne z hzm))⟩
      · obtain ⟨rfl, b1, hF2, fr2, hpw2, hx2, hall⟩ := h2
        have hcurnot : cur ∉ zs.map fun z => curOf ph z.2 := fun hm => by
          obtain ⟨z, hzm, e⟩ := List.mem_map.1 hm
          exact hne z hzm e
        have hold : ∀ u, tl + 1 > u → n₀ ≤ u → Γ2 u = Γs u := fun u h1 h2 =>
          fr2 u h1 fun hm => by
            obtain ⟨z, hzm, e⟩ := List.mem_map.1 hm
            have := (hz z (by simp [hzm])).1
            omega
        refine ⟨rfl, by omega, hF2, fun u hu hnot => ?_, ?_,
          fun x hx => ?_, List.Forall₂.cons ⟨?_⟩ ?_⟩
        · simp only [List.map_cons, List.mem_cons, not_or] at hnot
          rw [fr2 u (by omega) hnot.2]
          exact (hsne u hnot.1).trans (frt u hu)
        · rw [List.map_cons, List.pairwise_cons]
          refine ⟨fun v hv => ?_, hpw2⟩
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self tl) (hx2 x hx).1
        · rcases List.mem_cons.1 hx with rfl | hx
          · refine ⟨by show n ≤ tl; omega, by show n2 > tl; omega, ?_⟩
            show Base Γ2 tl
            refine Cov.congr (cov_of_none fun o => ?_) (hold tl (by omega) (by omega))
            rw [hsne tl (by omega)]
            exact hFt tl a2 o
          · obtain ⟨c1, c2, c3⟩ := hx2 x hx
            exact ⟨by omega, c2, c3⟩
        · refine ⟨tr, nc, dd, bl, tl, n, nt, rfl, by omega, le_rfl, by omega, ?_, fun a' ha' => ?_,
            hK, fun u hu => ?_, fun P hP hPc => ?_⟩
          · refine hT.congr fun u h1 h2 => ?_
            rw [hold u (by omega) (by omega)]
            exact hsne u (by omega)
          · rcases List.mem_cons.1 ha' with h | ha'
            · exact Or.inr (by rw [h]; exact a2)
            · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha'
              have := (hx2 x hx).1
              exact Or.inr (by omega)
          · have d1 : @LE.le ℕ _ nt u := (hdd u hu).1
            have d2 : @LT.lt ℕ _ u tl := (hdd u hu).2
            refine ⟨by omega, by omega, fun hm => ?_, ?_⟩
            · rcases List.mem_cons.1 hm with h | hm
              · have h' : @Eq ℕ u tl := h
                omega
              · obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
                have := (hx2 x hx).1
                have e' : @Eq ℕ x.2.tk u := e
                omega
            · refine Cov.congr (cov_of_none fun o => ?_) (hold u (by omega) (by omega))
              rw [hsne u (by omega)]
              exact hFt u d1 o
          · refine Cov.congr ?_ (fr2 cur (by omega) hcurnot)
            exact cov_setFb_of _ _ _ _ _ _ _ _ _ _
              (Base.cov (hbase.congr (frt cur (by omega))) hP) hPc
        · refine hall.imp fun z z' hf => ⟨?_⟩
          obtain ⟨tr', nc', dd', bl', tl', lo, hi, e, c0, c1, c2, c3, c4, c5, c6, c7⟩ := hf.ex
          refine ⟨tr', nc', dd', bl', tl', lo, hi, e, by omega, by omega, c2, c3,
            fun a' ha' => ?_, c5, fun u hu => ?_, c7⟩
          · rcases List.mem_cons.1 ha' with h | ha'
            · exact Or.inl (by rw [h]; show lo > tl; omega)
            · exact c4 a' ha'
          · obtain ⟨d1, d2, d3, d4⟩ := c6 u hu
            have d1' : @LE.le ℕ _ (tl + 1) u := d1
            refine ⟨by omega, d2, fun hm => ?_, d4⟩
            rcases List.mem_cons.1 hm with h | hm
            · have h' : @Eq ℕ u tl := h
              omega
            · exact d3 hm

end Rounds

/-! ## The joining round, in all slots -/

section Join
variable {Y : Type} (sMT : ℕ) (t : Tag)

structure JoinFact {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (n n1 : ℕ) (Γ1 : Cx lam K L) (Act' : List Tok) (z z' : SlotSt lam K Y (r :: s)) : Prop where
  ex : ∃ (tr : Option TTree) (c lo hi : ℕ), z' = (z.1, updJoin z.2 tr c) ∧ n ≤ c ∧ n1 > c ∧ n ≤ lo ∧
    hi ≤ n1 ∧ TreeKO Γ1 lo hi w.depthJ (bodyAt w.posAtJ emb z.1.1.1) tr ∧
    ∀ a' ∈ Act', lo > a' ∨ hi ≤ a'
  ret : ∀ P : Cx lam K L, BaseUp P z.2.tk →
    P z.2.tk (OracleName.g t) = some (cloG K t i w.hasJ (plJ (a.plain z.1.1.2).2)) → Cov Γ1 z.2.tk P

theorem late_joinM {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (n₀ : ℕ) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (n : ℕ) (Γ : Cx lam K L), n₀ ≤ n → Fut n Γ →
      (zs.map fun z => z.2.tk).Pairwise (fun u v : ℕ => u < v) →
      (∀ z ∈ zs, n₀ > z.2.tk ∧ Base Γ z.2.tk) →
      Late (fun n1 Γ1 o o' =>
          o'.1 = o.1.map (fun x => ((none : Option (Rho (r :: s))), x.2)) ∧
          o'.2 = o.2 ∧
          o.2 = o.1.map (fun x => x.2.c) ∧
          n ≤ n1 ∧ Fut n1 Γ1 ∧
          (∀ u, n > u → u ∉ zs.map (fun z => z.2.tk) → Γ1 u = Γ u) ∧
          (o.1.map fun x => x.2.c).Pairwise (fun u v : ℕ => u < v) ∧
          (∀ x ∈ o.1, n ≤ x.2.c ∧ n1 > x.2.c ∧ Base Γ1 x.2.c) ∧
          List.Forall₂ (JoinFact t a w emb plJ i n n1 Γ1 (o.1.map fun x => x.2.c)) zs o.1)
        n Γ (joinM sMT t a w emb plJ i zs)
        (skJoinM sMT t w (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)))
  | [], n, Γ, _, hF, _, _ =>
    Late.pure ⟨rfl, rfl, rfl, le_rfl, hF, fun _ _ _ => rfl, List.Pairwise.nil,
        fun x hx => absurd hx (by simp), List.Forall₂.nil⟩
  | ((m, k), acc) :: zs, n, Γ, hn0, hF, hpw, hz => by
      obtain ⟨hcur, hbase⟩ := hz ((m, k), acc) (by simp)
      rw [List.map_cons, List.pairwise_cons] at hpw
      obtain ⟨hlt, hpw'⟩ := hpw
      refine Late.bind (late_slotJoin sMT t a w emb plJ i m k acc hF) fun n1 Γ1 x y h1 => ?_
      obtain ⟨tr, c, nt, Γt, rfl, rfl, a1, a2, rfl, hFt, frt, hT, rfl⟩ := h1
      set cur : ℕ := acc.tk with hcurdef
      set clo := cloG K t i w.hasJ (plJ (a.plain m.2).2) with hclo
      have hcur' : n₀ > cur := hcur
      have hF1 : Fut (c + 1) (Γt.set cur (OracleName.g t) clo) := hFt.set (by omega) (by omega) _ _
      have hne : ∀ z ∈ zs, z.2.tk ≠ cur := fun z hzm =>
        Nat.ne_of_gt (hlt _ (List.mem_map.2 ⟨z, hzm, rfl⟩))
      refine Late.bind
        (late_joinM a w emb plJ i n₀ zs (c + 1) _ (by omega) hF1 hpw' fun z hzm => ?_)
        fun n2 Γ2 o o' h2 => Late.pure ?_
      · obtain ⟨c1, c2⟩ := hz z (by simp [hzm])
        exact ⟨c1, (c2.congr (frt _ (by omega))).set_ne (hne z hzm) _ _⟩
      · obtain ⟨e1, e2, e3, b1, hF2, fr2, hpw2, hx2, hall⟩ := h2
        have hcurnot : cur ∉ zs.map fun z => z.2.tk := fun hm => by
          obtain ⟨z, hzm, e⟩ := List.mem_map.1 hm
          exact hne z hzm e
        have hold : ∀ u : ℕ,
            c + 1 > u → n₀ ≤ u → Γ2 u = (Γt.set cur (OracleName.g t) clo) u := fun u h1 h2 =>
          fr2 u h1 fun hm => by
            obtain ⟨z, hzm, e⟩ := List.mem_map.1 hm
            have := (hz z (by simp [hzm])).1
            omega
        refine ⟨by show _ :: o'.1 = _; rw [e1]; rfl, by show _ :: o'.2 = _ :: o.2; rw [e2],
          by show _ :: o.2 = _; rw [e3]; rfl, by omega, hF2, fun u hu hnot => ?_, ?_,
          fun x hx => ?_, List.Forall₂.cons ⟨?_, ?_⟩ ?_⟩
        · simp only [List.map_cons, List.mem_cons, not_or] at hnot
          rw [fr2 u (by omega) hnot.2]
          exact (funext fun o => Ctx.set_ne_tok Γt hnot.1 _ _ o).trans (frt u hu)
        · show (c :: o.1.map fun x => x.2.c).Pairwise _
          rw [List.pairwise_cons]
          refine ⟨fun v hv => ?_, hpw2⟩
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hv
          exact Nat.lt_of_lt_of_le (Nat.lt_succ_self c) (hx2 x hx).1
        · rcases List.mem_cons.1 hx with rfl | hx
          · refine ⟨by show n ≤ c; omega, by show n2 > c; omega, ?_⟩
            show Base Γ2 c
            refine Cov.congr (cov_of_none fun o => ?_) (hold c (by omega) (by omega))
            rw [Ctx.set_ne_tok Γt (by omega : c ≠ cur)]
            exact hFt c a2 o
          · obtain ⟨c1, c2, c3⟩ := hx2 x hx
            exact ⟨by omega, c2, c3⟩
        · refine ⟨tr, c, n, nt, rfl, by omega, by omega, le_rfl, by omega, ?_, fun a' ha' => ?_⟩
          · refine hT.congr fun u h1 h2 => ?_
            rw [hold u (by omega) (by omega)]
            exact funext fun o => Ctx.set_ne_tok Γt (by omega : u ≠ cur) _ _ o
          · rcases List.mem_cons.1 ha' with h | ha'
            · exact Or.inr (by rw [h]; exact a2)
            · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha'
              have := (hx2 x hx).1
              exact Or.inr (by omega)
        · intro P hP hPc
          refine Cov.congr ?_ (fr2 cur (by omega) hcurnot)
          exact Cov.set (Base.cov (hbase.congr (frt cur (by omega))) hP) hPc
        · refine hall.imp fun z z' hf => ⟨?_, hf.ret⟩
          obtain ⟨tr', c', lo, hi, e, c0, c00, c1, c2, c3, c4⟩ := hf.ex
          refine ⟨tr', c', lo, hi, e, by omega, c00, by omega, c2, c3, fun a' ha' => ?_⟩
          rcases List.mem_cons.1 ha' with h | ha'
          · exact Or.inl (by rw [h]; show lo > c; omega)
          · exact c4 a' ha'

end Join

/-! ## What is known of a slot at the end of the chains -/

theorem Cov.row {Γ P P' : Cx lam K L} {u : Tok} (h : Cov Γ u P') (e : P u = P' u) : Cov Γ u P :=
  fun o pt hp => by rw [e]; exact h o pt hp

theorem forall₂_comp {α β γ : Type} {R : α → β → Prop} {S : β → γ → Prop}
    {T : α → γ → Prop} (h : ∀ a b c, R a b → S b c → T a c) :
    ∀ {l1 : List α} {l2 : List β} {l3 : List γ},
      List.Forall₂ R l1 l2 → List.Forall₂ S l2 l3 → List.Forall₂ T l1 l3
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (forall₂_comp h t1 t2)

theorem shOf_lo {C : Type} : ∀ (k : Kind) (c c' : C), k = .lo → k.shOf c = k.shOf c'
  | .lo, _, _, _ => rfl

/-- in the phase `aft`, `ctxB` does not use the shared chain's tokens and numbers -/
theorem ctxB_aft (t : Tag) (cms : List (Dig lam)) (x : Option X) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (tj t0 t0' : List Tok) (nJ n0 n0' : List ℕ) (pls : Plains s) (Pc : Cx lam K L),
      ctxB t cms x s A W embP i .aft tj t0 nJ n0 pls Pc =
        ctxB t cms x s A W embP i .aft tj t0' nJ n0' pls Pc
  | [], _, _, _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, tj, t0, t0', nJ, n0, n0', (pl, pls), Pc => by
      unfold ctxB
      cases a.kind with
      | lo => exact ctxB_aft t cms x s A W _ _ _ _ _ _ _ _ _ _
      | sh => exact ctxB_aft t cms x s A W _ _ _ _ _ _ _ _ _ _

/-- `ctxB` does not use the token of the phase `shr` -/
theorem ctxB_shr (t : Tag) (cms : List (Dig lam)) (x : Option X) (b b' : Tok) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
        (i : ℕ) (tj t0 : List Tok) (nJ n0 : List ℕ) (pls : Plains s) (Pc : Cx lam K L),
      ctxB t cms x s A W embP i (.shr b) tj t0 nJ n0 pls Pc =
        ctxB t cms x s A W embP i (.shr b') tj t0 nJ n0 pls Pc
  | [], _, _, _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (a, A), (w, W), embP, i, tj, t0, nJ, n0, (pl, pls), Pc => by
      unfold ctxB
      cases a.kind <;> rfl

/-- the tokens of the shared chain that are still to be charged or made -/
def T0of (ph : PhT) (rq : Option TTree) (new0 : List Tok) : List Tok :=
  match ph with
  | .shr tk0 => tk0 :: new0
  | .aft => new0
  | _ => (rq.map TTree.root).toList ++ new0

section SlotK
variable {Y : Type} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- What is known of a slot at the end, seen from a round in the middle: z is the slot then, acc'
its accumulator at the end, T0 the shared tokens from then on, N0 the numbers of the final attempts
of the shared rounds from then on, ntr0 the shared trees from then on. nN: the numbers of the slot's
final attempts from then on, in the order of the rounds (the accumulator has the newest first); nD:
the chaining values of its attempts before the final ones: nothing but closures without data is
recorded for them. -/
def SlotK (Γ' : Cx lam K L) (n : ℕ) (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph : PhT) (S0 : SStrat s A) (T0 : List Tok) (N0 : List ℕ) (ntr0 : List (Option TTree))
    (z : SlotSt lam K Y s) (acc' : SlotAcc lam K Y) : Prop :=
  ∃ (nb : List (Blk lam K)) (ntr : List (Option TTree)) (new : List Tok)
      (nN : List ℕ) (nD : List Tok),
    acc'.x = z.2.x ∧
    acc'.blocks = z.2.blocks ++ nb ∧
    acc'.trees = z.2.trees ++ ntr ∧
    acc'.toks = z.2.toks ++ new ∧
    (∀ u ∈ new, n ≤ u) ∧
    acc'.nons = nN.reverse ++ z.2.nons ∧
    acc'.dead = nD ++ z.2.dead ∧
    (∀ u ∈ nD, n ≤ u ∧ Base Γ' u) ∧
    (∀ Pc : Cx lam K L, (∀ u, BaseUp Pc u) →
      ∀ u ∈ curOf ph z.2 :: new,
        Cov Γ' u (ctxB t cms (z.2.x.bind xin) s A W embP i ph (curOf ph z.2 :: new) T0 nN N0
            ((z.1.run (rhoOf s A W nb)).1).plains Pc)) ∧
    ∀ l, z.1 = S0.zip l →
      (∀ Pc : Cx lam K L, (∀ u, BaseUp Pc u) →
        ∀ u ∈ T0, Cov Γ' u
          (ctxB t cms (z.2.x.bind xin) s A W embP i ph (curOf ph z.2 :: new) T0 nN N0
            ((z.1.run (rhoOf s A W nb)).1).plains Pc)) ∧
      TreesKB Γ' s A W embS (z.1.run (rhoOf s A W nb)).1 ntr ntr0

end SlotK

/-! ## From a round and the rest to the whole: one slot -/

section Combine
variable {Y : Type} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem ctxB_lo (x : Option X) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (hk : a.kind = .lo)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (cur : Tok)
    (tj t0 : List Tok) (nJ n0 : List ℕ) (pl : r.Plain) (pls : Plains s) (Pc : Cx lam K L) :
    ctxB t cms x (r :: s) (a, A) (w, W) embP i ph (cur :: tj) t0 nJ n0 (pl, pls) Pc =
      ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) ph.afterLo tj t0 (restN w.grJ nJ) n0 pls
        (setFb w.grJ t [cur] i (hdOf (L := L) cms x i ph) w.hasJ (rtOf ph)
          (fun α => embP (.inl (.inr α))) (a.plain pl).2 (nJ.headD 0) Pc) := by
  conv_lhs => unfold ctxB
  simp only [hk]
  cases ph <;> rfl

theorem slotK_lo {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .lo)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) {n n1 : ℕ} {Γ1 Γ' : Cx lam K L} {Act1 T0 T0' : List Tok}
    {N0 N0' : List ℕ} {ntr0 : List (Option TTree)} {z : SlotSt lam K Y (r :: s)}
    {z' : SlotSt lam K Y s} {acc' : SlotAcc lam K Y}
    (hf : LoFact t cms xin a w (fun p => embS (.inl p))
      (fun α => embP (.inl (.inr α))) i ph n n1 Γ1 Act1 z z')
    (hS : SlotK t cms xin Γ' n1 s A W (fun p => embS (.inr p)) (fun q => embP (.inr q)) (i + 1)
      ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) T0' N0' ntr0 z' acc')
    (hFr : Fr Act1 n1 Γ1 Γ') (hn : n ≤ n1) (hcur : n > curOf ph z.2)
    (hAct : ∀ a' ∈ Act1, n ≤ a') (hcT : curOf ph z.2 ∉ T0)
    (hctx : ∀ tj nJ pls (Pc : Cx lam K L),
      ctxB t cms (z.2.x.bind xin) s A W (fun q => embP (.inr q)) (i + 1)
          ph.afterLo tj T0 nJ N0 pls Pc =
        ctxB t cms (z.2.x.bind xin) s A W (fun q => embP (.inr q)) (i + 1)
          ph.afterLo tj T0' nJ N0' pls Pc)
    (hT : ∀ u ∈ T0, u ∈ T0' ∨ Base Γ' u) :
    SlotK t cms xin Γ' n (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) T0 N0
      (none :: ntr0) z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨tr, nc, dd, bl, tl, lo, hi, rfl, c0, c1, c2, hTr, hA, hK, hdd, hret⟩ := hf.ex
  obtain ⟨nb, ntr, new, nN, nD, e1, e2, e3, e4, hnew, e5, e6, hnD, C1, C23⟩ := hS
  have hcurtl : curOf ph.afterLo (updLo acc tr nc dd bl tl) = tl := curOf_afterLo ph _
  rw [hcurtl] at C1 C23
  have hx : (updLo acc tr nc dd bl tl).x = acc.x := rfl
  rw [hx] at C1 C23
  have hcur' : n > curOf ph acc := hcur
  have hnotnew : curOf ph acc ∉ tl :: new := fun hm => by
    rcases List.mem_cons.1 hm with h | h
    · have h' : (curOf ph acc : ℕ) = tl := h
      omega
    · have := hnew _ h; omega
  have hbu : ∀ (Pc : Cx lam K L), (∀ u, BaseUp Pc u) →
      ∀ u, BaseUp
        (setFb w.grJ t [curOf ph acc] i (hdOf (L := L) cms (acc.x.bind xin) i ph) w.hasJ (rtOf ph)
          (fun α => embP (.inl (.inr α))) (a.plain m.2).2 (nc.getD 0) Pc) u :=
    fun Pc hPc u => baseUp_setFb _ _ _ _ _ _ _ _ _ Pc (hPc u) _
  have hlo : ∀ (Pc : Cx lam K L) pls,
      ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i ph (curOf ph acc :: tl :: new) T0
          (nc.toList ++ nN) N0 (m.2, pls) Pc =
        ctxB t cms (acc.x.bind xin) s A W (fun z => embP (.inr z)) (i + 1) ph.afterLo
          (tl :: new) T0 nN N0 pls
          (setFb w.grJ t [curOf ph acc] i (hdOf (L := L) cms (acc.x.bind xin) i ph) w.hasJ (rtOf ph)
            (fun α => embP (.inl (.inr α))) (a.plain m.2).2 (nc.getD 0) Pc) := fun Pc pls => by
    rw [ctxB_lo t cms _ a A w W hk, restN_kept _ hK.1, setFb_kept _ _ _ _ _ _ _ _ hK.1]
  have hzip : ∀ l, ((m, k) : Strat (r :: s) Unit) =
        SStrat.zip (s := r :: s) (A := (a, A)) (m0, k0) l →
      ∃ l', k (w.chal bl) = (k0 (a.kind.shOf (w.chal (blk0 lam K)))).zip l' := by
    rintro ⟨mj, kj⟩ hl
    have hl' : (m, k) = (a.join m0 mj, fun c => SStrat.zip (k0 (a.kind.shOf c)) (kj c)) := hl
    refine ⟨kj (w.chal bl), ?_⟩
    rw [(Prod.mk.inj hl').2]
    show (k0 (a.kind.shOf (w.chal bl))).zip (kj (w.chal bl)) = _
    rw [shOf_lo a.kind (w.chal bl) (w.chal (blk0 lam K)) hk]
  refine ⟨bl :: nb, tr :: ntr, tl :: new, nc.toList ++ nN, nD ++ dd, e1, by rw [e2]; simp [updLo],
    by rw [e3]; simp [updLo], by rw [e4]; simp [updLo], fun u hu => ?_,
    by rw [e5, List.reverse_append, toList_reverse]; simp [updLo], by rw [e6]; simp [updLo],
    fun u hu => ?_, fun Pc hPc u hu => ?_,
    fun l hl => ⟨fun Pc hPc u hu => ?_, fun tr' h => absurd h (by simp), fun tr' h => ?_, ?_⟩⟩
  · rcases List.mem_cons.1 hu with h | h
    · rw [h]; exact c0
    · have := hnew u h; omega
  · rcases List.mem_append.1 hu with h | h
    · exact ⟨hn.trans (hnD u h).1, (hnD u h).2⟩
    · obtain ⟨d1, d2, d3, d4⟩ := hdd u h
      exact ⟨d1, Cov.fr d4 hFr d2 d3 (baseUp_base u)⟩
  · show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i ph (curOf ph acc :: tl :: new) T0
        (nc.toList ++ nN) N0 (m.2, ((k (w.chal bl)).run (rhoOf s A W nb)).1.plains) Pc)
    rw [hlo]
    rcases List.mem_cons.1 hu with h | h
    · rw [h]
      refine Cov.row ?_ (ctxB_ne t cms _ s A W _ _ _ _ _ _ _ _ _ _ hnotnew hcT)
      refine Cov.fr (hret _ (hbu Pc hPc _) (cov_setFb _ _ _ _ _ _ _ _ _ _ Pc [])) hFr (by omega)
        (fun hm => ?_) (hbu Pc hPc _)
      have := hAct _ hm
      omega
    · rw [hctx]
      exact C1 _ (hbu Pc hPc) u h
  · show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i ph (curOf ph acc :: tl :: new) T0
        (nc.toList ++ nN) N0 (m.2, ((k (w.chal bl)).run (rhoOf s A W nb)).1.plains) Pc)
    rw [hlo]
    rcases hT u hu with h | h
    · obtain ⟨l', hl'⟩ := hzip l hl
      rw [hctx]
      exact (C23 l' hl').1 _ (hbu Pc hPc) u h
    · exact Base.cov h (baseUp_ctxB t cms _ s A W _ _ _ _ _ _ _ _ _ u (hbu Pc hPc u))
  · exact (hTr.fr hFr c2 hA tr' h).openK
  · obtain ⟨l', hl'⟩ := hzip l hl
    exact (C23 l' hl').2

end Combine

section Combine2
variable {Y : Type} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem bodyAt_shared {r : Round} (a : RAnn r) (hco : a.Coherent) (w : WireRB lam K r a)
    (hw : w.OKG) (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0) (mj mj' : a.Mj) :
    bodyAt w.posAt0 emb (a.join m0 mj).1 = bodyAt w.posAt0 emb (a.join m0 mj').1 := by
  funext l
  unfold bodyAt
  cases h : w.posAt0 l with
  | none => rfl
  | some p =>
    simp only
    rw [hco.rd_shared m0 mj mj' p (hw.place_posAt0 l p h).1]

theorem ctxB_sh (x : Option X) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (tk0 b : Tok)
    (tj t0 : List Tok) (nJ n0 : List ℕ) (pl : r.Plain) (pls : Plains s) (Pc : Cx lam K L) :
    ctxB t cms x (r :: s) (a, A) (w, W) embP i (.shr tk0) tj (tk0 :: t0) nJ n0 (pl, pls) Pc =
      ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) (.shr b) tj t0 nJ (restN w.gr0 n0) pls
        (setFb w.gr0 t [tk0] i (fun _ => Head.f5) w.has0 0 (fun α => embP (.inl (.inl α)))
          (a.plain pl).1 (n0.headD 0) Pc) := by
  conv_lhs => unfold ctxB
  simp only [hk]
  exact ctxB_shr t cms x 0 b s A W _ _ _ _ _ _ _ _

theorem ctxB_skip (x : Option X) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT)
    (hph : ph = .first ∨ ph = .aft) (tj t0 : List Tok) (nJ n0 : List ℕ) (pl : r.Plain)
    (pls : Plains s) (Pc : Cx lam K L) :
    ctxB t cms x (r :: s) (a, A) (w, W) embP i ph tj t0 nJ n0 (pl, pls) Pc =
      ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) ph tj t0 nJ n0 pls Pc := by
  conv_lhs => unfold ctxB
  rcases hph with rfl | rfl <;> simp only [hk]

theorem zip_step {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) (m : r.Msg) (k : r.Chal → Strat s Unit)
    (l : LStrat (r :: s) (a, A))
    (hl : ((m, k) : Strat (r :: s) Unit) = SStrat.zip (s := r :: s) (A := (a, A)) (m0, k0) l)
    (c : r.Chal) :
    m = a.join m0 l.1 ∧ k c = (k0 (a.kind.shOf c)).zip (l.2 c) := by
  obtain ⟨mj, kj⟩ := l
  have hl' : (m, k) = (a.join m0 mj, fun c => SStrat.zip (k0 (a.kind.shOf c)) (kj c)) := hl
  exact ⟨(Prod.mk.inj hl').1, by rw [(Prod.mk.inj hl').2]⟩

theorem slotK_shr {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh) (hco : a.Coherent) (hw : w.OKG)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (tk0 : ℕ) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) {n n2 n3 n4 tl : ℕ} {Γ4 Γ' : Cx lam K L}
    {Act2 new0 : List Tok} {N0 : List ℕ} {nc0 : Option ℕ} {ntr0 : List (Option TTree)}
    {tr0 : Option TTree} {bl : Blk lam K} {z : SlotSt lam K Y (r :: s)}
    {acc' : SlotAcc lam K Y} (hK0 : nc0.isSome = w.gr0.isSome)
    (hS : SlotK t cms xin Γ' n4 s A W (fun p => embS (.inr p)) (fun q => embP (.inr q)) (i + 1)
      (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (tl :: new0) N0 ntr0 (hear w bl false z) acc')
    (hFr : Fr Act2 n4 Γ4 Γ') (hn : n ≤ n4) (h34 : n3 ≤ n4)
    (hTr0 : TreeKO Γ4 n2 n3 w.depth0
      (bodyAt w.posAt0 (fun p => embS (.inl p)) (a.join m0 (a.split (r.dOrc, r.dPlain)).2).1) tr0)
    (hA0 : ∀ a' ∈ Act2, n2 > a' ∨ n3 ≤ a')
    (hret : ∀ P : Cx lam K L, BaseUp P tk0 →
      Cov (setFb w.gr0 t [tk0] i (fun _ => Head.f5) w.has0 0 (fun α => embP (.inl (.inl α)))
          (a.pl0 m0) (nc0.getD 0) (Ctx.empty _))
        tk0 P → Cov Γ4 tk0 P)
    (htk : n > tk0) (htkA : tk0 ∉ Act2) (hc : z.2.c ≠ tk0) (hnew0 : ∀ u ∈ tl :: new0, n ≤ u) :
    SlotK t cms xin Γ' n (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) (tk0 :: tl :: new0)
      (nc0.toList ++ N0) (tr0 :: ntr0) z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨nb, ntr, new, nN, nD, e1, e2, e3, e4, hnew, e5, e6, hnD, C1, C23⟩ := hS
  have hbu : ∀ (Pc : Cx lam K L) (pl0 : a.P0), (∀ u, BaseUp Pc u) →
      ∀ u, BaseUp
        (setFb w.gr0 t [tk0] i (fun _ => Head.f5) w.has0 0
          (fun α => embP (.inl (.inl α))) pl0 (nc0.getD 0) Pc) u :=
    fun Pc _ hPc u => baseUp_setFb _ _ _ _ _ _ _ _ _ Pc (hPc u) _
  have hsh : ∀ (Pc : Cx lam K L) pls,
      ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i (.shr tk0) (acc.c :: new)
          (tk0 :: tl :: new0) nN (nc0.toList ++ N0) (m.2, pls) Pc =
        ctxB t cms (acc.x.bind xin) s A W (fun z => embP (.inr z)) (i + 1) (.shr tl)
          (acc.c :: new) (tl :: new0) nN N0 pls
          (setFb w.gr0 t [tk0] i (fun _ => Head.f5) w.has0 0 (fun α => embP (.inl (.inl α)))
            (a.plain m.2).1 (nc0.getD 0) Pc) := fun Pc pls => by
    rw [ctxB_sh t cms _ a A w W hk embP i tk0 tl, restN_kept _ hK0, setFb_kept _ _ _ _ _ _ _ _ hK0]
  refine ⟨bl :: nb, none :: ntr, new, nN, nD, e1, by rw [e2]; simp [hear], by rw [e3]; simp [hear],
    e4, fun u hu => by have := hnew u hu; omega,
    e5, e6, fun u hu => ⟨hn.trans (hnD u hu).1, (hnD u hu).2⟩,
    fun Pc hPc u hu =>
      ?_, fun l hl => ⟨fun Pc hPc u hu => ?_, fun tr' h => ?_, fun tr' h => absurd h (by simp), ?_⟩⟩
  · show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i (.shr tk0) (acc.c :: new)
        (tk0 :: tl :: new0) nN (nc0.toList ++ N0)
        (m.2, ((k (w.chal bl)).run (rhoOf s A W nb)).1.plains) Pc)
    rw [hsh]
    exact C1 _ (hbu Pc _ hPc) u hu
  · obtain ⟨hm, hkc⟩ := zip_step a A m0 k0 m k l hl (w.chal bl)
    show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i (.shr tk0) (acc.c :: new)
        (tk0 :: tl :: new0) nN (nc0.toList ++ N0)
        (m.2, ((k (w.chal bl)).run (rhoOf s A W nb)).1.plains) Pc)
    rw [hsh]
    rcases List.mem_cons.1 hu with h | h
    · rw [h]
      refine Cov.row ?_ (ctxB_ne t cms _ s A W _ _ _ _ _ _ _ _ _ _ (fun hm' => ?_) (fun hm' => ?_))
      · refine Cov.fr (hret _ (hbu Pc _ hPc _) ?_) hFr (by omega) htkA (hbu Pc _ hPc _)
        rw [hm, hco.plain_join]
        exact cov_setFb _ _ _ _ _ _ _ _ _ _ Pc []
      · rcases List.mem_cons.1 hm' with h' | h'
        · exact hc h'.symm
        · have := hnew _ h'; omega
      · have := hnew0 _ hm'; omega
    · exact (C23 _ hkc).1 _ (hbu Pc _ hPc) u h
  · obtain ⟨hm, -⟩ := zip_step a A m0 k0 m k l hl (w.chal bl)
    have := (hTr0.fr hFr h34 hA0 tr' h).openK
    rw [bodyAt_shared a hco w hw _ m0 _ l.1, ← hm] at this
    exact this
  · exact (C23 _ (zip_step a A m0 k0 m k l hl (w.chal bl)).2).2

theorem slotK_skip {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT)
    (hph : ph = .first ∨ ph = .aft) (m0 : a.M0) (k0 : a.kind.Sh r.Chal → SStrat s A) {n : ℕ}
    {Γ' : Cx lam K L} {T0 : List Tok} {N0 : List ℕ} {ntr0 : List (Option TTree)}
    {z : SlotSt lam K Y (r :: s)} {acc' : SlotAcc lam K Y}
    (hS : SlotK t cms xin Γ' n s A W (fun p => embS (.inr p)) (fun q => embP (.inr q)) (i + 1) ph
      (k0 (a.kind.shOf (w.chal (blk0 lam K)))) T0 N0 ntr0 (hear w (blk0 lam K) false z) acc') :
    SlotK t cms xin Γ' n (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) T0 N0
      (none :: ntr0) z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨nb, ntr, new, nN, nD, e1, e2, e3, e4, hnew, e5, e6, hnD, C1, C23⟩ := hS
  have hcu : curOf ph (hear w (blk0 lam K) false ((m, k), acc)).2 = curOf ph acc := by
    rcases hph with rfl | rfl <;> rfl
  rw [hcu] at C1 C23
  refine ⟨blk0 lam K :: nb, none :: ntr, new, nN, nD, e1, by rw [e2]; simp [hear],
    by rw [e3]; simp [hear], e4, hnew, e5, e6, hnD, fun Pc hPc u hu => ?_,
    fun l hl =>
      ⟨fun Pc hPc u hu => ?_, fun tr' h => absurd h (by simp), fun tr' h => absurd h (by simp), ?_⟩⟩
  · show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i ph (curOf ph acc :: new) T0 nN N0
        (m.2, ((k (w.chal (blk0 lam K))).run (rhoOf s A W nb)).1.plains) Pc)
    rw [ctxB_skip t cms _ a A w W hk embP i ph hph]
    exact C1 Pc hPc u hu
  · show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i ph (curOf ph acc :: new) T0 nN N0
        (m.2, ((k (w.chal (blk0 lam K))).run (rhoOf s A W nb)).1.plains) Pc)
    rw [ctxB_skip t cms _ a A w W hk embP i ph hph]
    exact (C23 _ (zip_step a A m0 k0 m k l hl _).2).1 Pc hPc u hu
  · exact (C23 _ (zip_step a A m0 k0 m k l hl _).2).2

end Combine2

section Combine3
variable {Y : Type} (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

theorem ctxB_join (x : Option X) {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s)
    (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (tk root b : Tok)
    (tj t0 : List Tok) (nJ n0 : List ℕ) (pl : r.Plain) (pls : Plains s) (Pc : Cx lam K L) :
    ctxB t cms x (r :: s) (a, A) (w, W) embP i .loc (tk :: tj) (root :: t0) nJ n0 (pl, pls) Pc =
      ctxB t cms x s A W (fun z => embP (.inr z)) (i + 1) (.shr b) tj t0 nJ (restN w.gr0 n0) pls
        (setFb w.gr0 t [root] i (fun _ => Head.f4 cms) w.has0 0 (fun α => embP (.inl (.inl α)))
          (a.plain pl).1 (n0.headD 0)
          (Pc.set tk (OracleName.g t) (cloG K t i w.hasJ (embP (.inl (.inr (a.plain pl).2)))))) := by
  conv_lhs => unfold ctxB
  simp only [hk]
  exact ctxB_shr t cms x 0 b s A W _ _ _ _ _ _ _ _

theorem slotK_join {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .sh) (hco : a.Coherent) (hw : w.OKG)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) {n n1 n2 n3 n4 tl root : ℕ} {Γ1 Γ4 Γ' : Cx lam K L}
    {cs new0 : List Tok} {N0 : List ℕ} {nc0 : Option ℕ} {ntr0 : List (Option TTree)}
    {tr0 : Option TTree} {bl : Blk lam K} {z z1 : SlotSt lam K Y (r :: s)} {acc' : SlotAcc lam K Y}
    (hK0 : nc0.isSome = w.gr0.isSome)
    (hf : JoinFact t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i n n1 Γ1 cs z z1)
    (hE14 : Ext n1 Γ1 Γ4)
    (hS : SlotK t cms xin Γ' n4 s A W (fun p => embS (.inr p)) (fun q => embP (.inr q)) (i + 1)
      (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (tl :: new0) N0 ntr0 (hear w bl true z1) acc')
    (hFr : Fr (cs ++ [tl]) n4 Γ4 Γ') (h23 : n2 ≤ n3) (h3t : n3 ≤ tl) (h4 : n4 = tl + 1)
    (hTr0 : TreeKO Γ4 n2 n3 w.depth0
      (bodyAt w.posAt0 (fun p => embS (.inl p)) (a.join m0 (a.split (r.dOrc, r.dPlain)).2).1) tr0)
    (hcs : ∀ a' ∈ cs, n ≤ a' ∧ n1 > a')
    (hretR : ∀ P : Cx lam K L, BaseUp P root →
      Cov (setFb w.gr0 t [root] i (fun _ => Head.f4 cms) w.has0 0 (fun α => embP (.inl (.inl α)))
          (a.pl0 m0) (nc0.getD 0) (Ctx.empty _))
        root P → Cov Γ4 root P)
    (hr1 : n1 ≤ root) (hr2 : n2 > root) (htk : n > z.2.tk) (hnew0 : ∀ u ∈ new0, n4 ≤ u) :
    SlotK t cms xin Γ' n (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) (root :: tl :: new0)
      (nc0.toList ++ N0) (tr0 :: ntr0) z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨tr, c, lo, hi, rfl, c0, c00, c1, c2, hTr, hA⟩ := hf.ex
  obtain ⟨nb, ntr, new, nN, nD, e1, e2, e3, e4, hnew, e5, e6, hnD, C1, C23⟩ := hS
  have htk' : n > acc.tk := htk
  have key : ∀ v : ℕ, acc.tk = v → n > v := fun v h => h ▸ htk'
  have hk1 : n1 > acc.tk := by omega
  have hk4 : n4 > acc.tk := by omega
  have hner : acc.tk ≠ root := fun h => by have := key _ h; omega
  have hbu : ∀ (Pc : Cx lam K L) (p1 : PlainPart (shapeOf L t) (annOf L t)) (p2 : a.P0),
      (∀ u, BaseUp Pc u) →
      ∀ u, BaseUp
        (setFb w.gr0 t [root] i (fun _ => Head.f4 cms) w.has0 0 (fun α => embP (.inl (.inl α))) p2
          (nc0.getD 0) (Pc.set acc.tk (OracleName.g t) (cloG K t i w.hasJ p1))) u :=
    fun Pc _ _ hPc u => baseUp_setFb _ _ _ _ _ _ _ _ _ _ (baseUp_set Pc (hPc u) _ _ fun _ => rfl) _
  have hjo : ∀ (Pc : Cx lam K L) pls,
      ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i .loc (acc.tk :: c :: new)
          (root :: tl :: new0) nN (nc0.toList ++ N0) (m.2, pls) Pc =
        ctxB t cms (acc.x.bind xin) s A W (fun z => embP (.inr z)) (i + 1) (.shr tl)
          (c :: new) (tl :: new0) nN N0 pls
          (setFb w.gr0 t [root] i (fun _ => Head.f4 cms) w.has0 0 (fun α => embP (.inl (.inl α)))
            (a.plain m.2).1 (nc0.getD 0)
            (Pc.set acc.tk (OracleName.g t)
              (cloG K t i w.hasJ (embP (.inl (.inr (a.plain m.2).2)))))) := fun Pc pls => by
    rw [ctxB_join t cms _ a A w W hk embP i acc.tk root tl,
      restN_kept _ hK0, setFb_kept _ _ _ _ _ _ _ _ hK0]
  have hn4 : n ≤ n4 := by omega
  have hrootA : root ∉ cs ++ [tl] := fun hm => by
    rcases List.mem_append.1 hm with h | h
    · have := (hcs _ h).2; omega
    · have : root = tl := List.mem_singleton.1 h
      omega
  have htkA : acc.tk ∉ cs ++ [tl] := fun hm => by
    rcases List.mem_append.1 hm with h | h
    · have := (hcs _ h).1; omega
    · have := key _ (List.mem_singleton.1 h)
      omega
  have hA2 : ∀ (x y : ℕ), (∀ a' ∈ cs, x > a' ∨ y ≤ a') → y ≤ tl →
      ∀ a' ∈ cs ++ [tl], x > a' ∨ y ≤ a' := fun x y h1 h2 a' ha' => by
    rcases List.mem_append.1 ha' with h | h
    · exact h1 a' h
    · rw [List.mem_singleton.1 h]; exact Or.inr h2
  refine ⟨bl :: nb, tr :: ntr, c :: new, nN, nD, e1, by rw [e2]; simp [hear, updJoin],
    by rw [e3]; simp [hear, updJoin], by rw [e4]; simp [hear, updJoin], fun u hu => ?_, e5, e6,
    fun u hu => ⟨hn4.trans (hnD u hu).1, (hnD u hu).2⟩, fun Pc hPc u hu => ?_,
    fun l hl => ⟨fun Pc hPc u hu => ?_, fun tr' h => ?_, fun tr' h => ?_, ?_⟩⟩
  · rcases List.mem_cons.1 hu with h | h
    · rw [h]; exact c0
    · have := hnew u h; omega
  · show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i .loc (acc.tk :: c :: new)
        (root :: tl :: new0) nN (nc0.toList ++ N0)
        (m.2, ((k (w.chal bl)).run (rhoOf s A W nb)).1.plains) Pc)
    rw [hjo]
    rcases List.mem_cons.1 hu with h | h
    · rw [h]
      refine Cov.row ?_ (ctxB_ne t cms _ s A W _ _ _ _ _ _ _ _ _ _ (fun hm' => ?_) (fun hm' => ?_))
      · refine Cov.fr (Cov.ext (hf.ret _ (hbu Pc _ _ hPc _) ?_) hE14 hk1 (hbu Pc _ _ hPc _))
          hFr hk4 htkA (hbu Pc _ _ hPc _)
        rw [setFb_ne_tok _ _ _ _ _ _ _ _ _ _ _ hner]
        exact Ctx.set_same _ _ _ _
      · rcases List.mem_cons.1 hm' with h' | h'
        · have := key _ h'
          omega
        · have h1 := hnew _ h'
          have h2 : n4 > acc.tk := hk4
          exact absurd h1 (Nat.not_le.2 h2)
      · rcases List.mem_cons.1 hm' with h' | h'
        · have := key _ h'
          omega
        · have h1 := hnew0 _ h'
          exact absurd h1 (Nat.not_le.2 hk4)
    · exact C1 _ (hbu Pc _ _ hPc) u h
  · obtain ⟨hm, hkc⟩ := zip_step a A m0 k0 m k l hl (w.chal bl)
    show Cov Γ' u
      (ctxB t cms (acc.x.bind xin) (r :: s) (a, A) (w, W) embP i .loc (acc.tk :: c :: new)
        (root :: tl :: new0) nN (nc0.toList ++ N0)
        (m.2, ((k (w.chal bl)).run (rhoOf s A W nb)).1.plains) Pc)
    rw [hjo]
    rcases List.mem_cons.1 hu with h | h
    · rw [h]
      refine Cov.row ?_ (ctxB_ne t cms _ s A W _ _ _ _ _ _ _ _ _ _ (fun hm' => ?_) (fun hm' => ?_))
      · refine Cov.fr (hretR _ (hbu Pc _ _ hPc _) ?_) hFr (by omega) hrootA (hbu Pc _ _ hPc _)
        rw [hm, hco.plain_join]
        exact cov_setFb _ _ _ _ _ _ _ _ _ _ _ []
      · rcases List.mem_cons.1 hm' with h' | h'
        · have h'' : root = c := h'
          omega
        · have := hnew _ h'; omega
      · rcases List.mem_cons.1 hm' with h' | h'
        · have h'' : root = tl := h'
          omega
        · have := hnew0 _ h'; omega
    · exact (C23 _ hkc).1 _ (hbu Pc _ _ hPc) u h
  · obtain ⟨hm, -⟩ := zip_step a A m0 k0 m k l hl (w.chal bl)
    have := (hTr0.fr hFr (by omega)
      (hA2 n2 n3 (fun a' ha' => Or.inl (by have := (hcs a' ha').2; omega)) h3t) tr' h).openK
    rw [bodyAt_shared a hco w hw _ m0 _ l.1, ← hm] at this
    exact this
  · exact ((hTr.fr (Fr.of_ext hE14 []) c2 (fun a' ha' => absurd ha' (by simp))).fr
      hFr (by omega) (hA2 lo hi hA (by omega)) tr' h).openK
  · exact (C23 _ (zip_step a A m0 k0 m k l hl (w.chal bl)).2).2

end Combine3

/-! ## The equations of chainT and skB, by the kind of the round and the phase -/

section Eqs
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)
  {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m0 : a.M0)
  (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0)

theorem chainT_lo (hk : a.kind = .lo) (ph : PhT) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      (eachM
        (slotLo sMT t cms xin a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        zs).bind fun zs' =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  conv_lhs => unfold chainT
  split <;> first | rfl | simp_all

theorem chainT_join (hk : a.kind = .sh) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0 =
      (joinM sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqT depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  conv_lhs => unfold chainT
  split <;> first | rfl | simp_all

theorem chainT_shr (hk : a.kind = .sh) (tk0 : Tok) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) zs a0
      = tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  conv_lhs => unfold chainT
  split <;> first | rfl | simp_all

theorem chainT_skip (hk : a.kind = .sh) (ph : PhT) (hph : ph = .first ∨ ph = .aft) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1)
        ph (k0 (a.kind.shOf (w.chal (blk0 lam K)))) (zs.map (hear w (blk0 lam K) false))
        { a0 with trees := a0.trees ++ [none] } := by
  conv_lhs => unfold chainT
  rcases hph with rfl | rfl <;> (split <;> first | rfl | simp_all)

end Eqs

section EqsL
variable {Y : Type} (sMT : ℕ) (t : Tag) (depthReq : ℕ) {r : Round} {s : Shape} (a : RAnn r)
  (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A) (f0 : Option (Rho (r :: s)))
  (zs : List (SlotSk lam K Y (r :: s))) (a0 : Acc0)

theorem skB_lo (hk : a.kind = .lo) (ph : PhT) :
    skB (L := L) sMT t depthReq (r :: s) (a, A) (w, W) ph f0 zs a0
      = (eachL (skSlotLo sMT t w ph) zs).bind fun zs' =>
          skB sMT t depthReq s A W ph.afterLo (f0.map Prod.snd) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  conv_lhs => unfold skB
  split <;> first | rfl | simp_all

theorem skB_join (hk : a.kind = .sh) :
    skB (L := L) sMT t depthReq (r :: s) (a, A) (w, W) .loc f0 zs a0
      = (skJoinM sMT t w zs).bind fun o =>
          (reqL depthReq o.2).bind fun rq =>
          withTreeL sMT w.has0 w.depth0 fun tr0 =>
          fbGL w w.gr0 (ansB w) t rq.root (tr0.map TTree.root).toList
              (f0.map Prod.fst) fun nc dd bl tl =>
          skB sMT t depthReq s A W (.shr tl) (f0.map Prod.snd) (o.1.map (hearL bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  conv_lhs => unfold skB
  split <;> first | rfl | simp_all

theorem skB_shr (hk : a.kind = .sh) (tk0 : Tok) :
    skB (L := L) sMT t depthReq (r :: s) (a, A) (w, W) (.shr tk0) f0 zs a0
      = withTreeL sMT w.has0 w.depth0 fun tr0 =>
          fbGL w w.gr0 (ansB w) t tk0 (tr0.map TTree.root).toList
              (f0.map Prod.fst) fun nc dd bl tl =>
          skB sMT t depthReq s A W (.shr tl) (f0.map Prod.snd) (zs.map (hearL bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  conv_lhs => unfold skB
  split <;> first | rfl | simp_all

theorem skB_skip (hk : a.kind = .sh) (ph : PhT) (hph : ph = .first ∨ ph = .aft) :
    skB (L := L) sMT t depthReq (r :: s) (a, A) (w, W) ph f0 zs a0 =
      skB sMT t depthReq s A W ph (f0.map Prod.snd) (zs.map (hearL (blk0 lam K) false))
        { a0 with trees := a0.trees ++ [none] } := by
  conv_lhs => unfold skB
  rcases hph with rfl | rfl <;> (split <;> first | rfl | simp_all)

end EqsL

/-! ## The statement for all chains -/

/-- there is a shared round -/
def HasSh : (s : Shape) → RoundSplits s → Prop
  | [], _ => False
  | _ :: s, (a, A) => a.kind = .sh ∨ HasSh s A

/-- the active tokens -/
def actL {Y : Type} {s : Shape} (ph : PhT) (zs : List (SlotSt lam K Y s)) : List ℕ :=
  zs.map (fun z => curOf ph z.2) ++ (match ph with
    | .shr tk0 => [tk0]
    | _ => [])

/-- what is known of the request tree: its digests but for the root have no closure with data -/
def ReqK (Γ' : Cx lam K L) (n depthReq : ℕ) (rq : TTree) : Prop :=
  Sized depthReq rq.levels ∧ n ≤ rq.root ∧ ∀ u ∈ rq.levels.flatten, u ≠ rq.root → Base Γ' u

def ReqPost (Γ' : Cx lam K L) (n depthReq : ℕ) (ph : PhT) (a0 a0' : Acc0) : Prop :=
  match ph with
  | .shr _ => a0'.req = a0.req
  | .aft => a0'.req = a0.req
  | _ => ∀ rq, a0'.req = some rq → ReqK Γ' n depthReq rq

section Stmt
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

def ChainPost (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (S0 : SStrat s A)
    (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (n : ℕ) (Γ : Cx lam K L) :
    ℕ → Cx lam K L → List (SlotAcc lam K Y) × Acc0 → List (SlotAcc lam K Y) × Acc0 → Prop :=
  fun n' Γ' out out' =>
    out' = out ∧ n ≤ n' ∧ Fut n' Γ' ∧
    Fr (actL ph zs) n Γ Γ' ∧
    ∃ (new0 : List Tok) (ntr0 : List (Option TTree)) (nN0 : List ℕ) (nD0 : List Tok),
      out.2.toks = a0.toks ++ new0 ∧
      out.2.trees = a0.trees ++ ntr0 ∧
      (∀ u ∈ new0, n ≤ u) ∧
      out.2.nons = nN0.reverse ++ a0.nons ∧
      out.2.dead = nD0 ++ a0.dead ∧
      (∀ u ∈ nD0, n ≤ u ∧ Base Γ' u) ∧
      ReqPost Γ' n depthReq ph a0 out.2 ∧
      List.Forall₂
        (SlotK t cms xin Γ' n s A W embS embP i ph S0 (T0of ph out.2.req new0) nN0 ntr0) zs out.1

/-- The statement for one shape: for all arguments, under five hypotheses: `Fut n Γ`; the active
tokens (`actL ph zs`) stand in increasing order; each of them is below n and has `Base Γ`; if there
is a shared round (`HasSh`), there are 2^depthReq slots; in the phases `first` and `loc`, `a0.req` =
none: then `chainT` and `skB` (on the same accumulators, with no challenges given) are related by
`Late`, with `ChainPost` at the end. -/
def ChainStmt (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) : Prop :=
  ∀ (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t))
      (i : ℕ) (ph : PhT) (S0 : SStrat s A) (zs : List (SlotSt lam K Y s)) (a0 : Acc0)
      (n : ℕ) (Γ : Cx lam K L),
    Fut n Γ → (actL ph zs).Pairwise (fun u v : ℕ => u < v) →
    (∀ a' ∈ actL ph zs, n > a' ∧ Base Γ a') → (HasSh s A → zs.length = 2 ^ depthReq) →
    (ph = .first ∨ ph = .loc → a0.req = none) →
    Late (ChainPost t cms xin depthReq s A W embS embP i ph S0 zs a0 n Γ) n Γ
      (chainT sMT t cms xin depthReq s A W embS embP i ph S0 zs a0)
      (skB sMT t depthReq s A W ph none (zs.map fun z => ((none : Option (Rho s)), z.2)) a0)

theorem chain_nil : ChainStmt (L := L) (K := K) sMT t cms xin depthReq [] PUnit.unit () := by
  intro embS embP i ph S0 zs a0 n Γ hF hpw hact _ hreq
  refine Late.pure
    ⟨by simp [List.map_map, Function.comp_def], le_rfl, hF, Fr.refl _ _ _, [], [], [], [],
      by simp, by simp, fun u hu => absurd hu (by simp), by simp, by simp,
      fun u hu => absurd hu (by simp), ?_, ?_⟩
  · cases ph with
    | first => intro rq h; rw [hreq (Or.inl rfl)] at h; exact absurd h (by simp)
    | loc => intro rq h; rw [hreq (Or.inr rfl)] at h; exact absurd h (by simp)
    | shr tk0 => rfl
    | aft => rfl
  · rw [List.forall₂_map_right_iff]
    refine List.forall₂_same.2 fun z hz =>
      ⟨[], [], [], [], [], rfl, by simp, by simp, by simp, fun u hu => absurd hu (by simp),
        by simp, by simp, fun u hu => absurd hu (by simp), fun Pc hPc u hu => ?_,
        fun l _ => ⟨fun Pc hPc u hu => ?_, rfl, rfl⟩⟩
    · rw [List.mem_singleton.1 hu]
      exact Base.cov (hact _ (List.mem_append.2 (Or.inl (List.mem_map.2 ⟨z, hz, rfl⟩)))).2 (hPc _)
    · cases ph with
      | first => simp [T0of, hreq (Or.inl rfl)] at hu
      | loc => simp [T0of, hreq (Or.inr rfl)] at hu
      | aft => simp [T0of] at hu
      | shr tk0 =>
        have : u = tk0 := by simpa [T0of] using hu
        rw [this]
        exact Base.cov (hact tk0 (List.mem_append.2 (Or.inr (by simp)))).2 (hPc _)

end Stmt

theorem forall₂_mem {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β},
      List.Forall₂ R l1 l2 → List.Forall₂ (fun a b => a ∈ l1 ∧ R a b) l1 l2
  | _, _, .nil => .nil
  | _, _, .cons h t =>
    .cons ⟨List.mem_cons_self, h⟩
      ((forall₂_mem t).imp fun _ _ hab => ⟨List.mem_cons_of_mem _ hab.1, hab.2⟩)

section Steps
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

theorem actL_afterLo {s : Shape} (ph : PhT) (xs : List (SlotSt lam K Y s)) :
    actL ph.afterLo xs = xs.map fun x => x.2.tk := by
  cases ph <;> simp [actL, PhT.afterLo, curOf]

theorem chain_lo {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
    (W : RoundsQueryLayout lam K s A) (hk : a.kind = .lo)
    (ih : ChainStmt (L := L) sMT t cms xin depthReq s A W)
    (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
    (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (m0 : a.M0)
    (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0) (n : ℕ)
    (Γ : Cx lam K L) (hF : Fut n Γ) (hpw : (actL ph zs).Pairwise (fun u v : ℕ => u < v))
    (hact : ∀ a' ∈ actL ph zs, n > a' ∧ Base Γ a') (hlen : HasSh s A → zs.length = 2 ^ depthReq)
    (hreq : ph = .first ∨ ph = .loc → a0.req = none) :
    Late (ChainPost t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 n Γ) n Γ
      (chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0)
      (skB sMT t depthReq (r :: s) (a, A) (w, W) ph none
        (zs.map fun z => ((none : Option (Rho (r :: s))), z.2)) a0) := by
  rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk,
    skB_lo sMT t depthReq a A w W none _ a0 hk]
  have hcm : ∀ z ∈ zs, curOf ph z.2 ∈ actL ph zs := fun z hz =>
    List.mem_append.2 (Or.inl (List.mem_map.2 ⟨z, hz, rfl⟩))
  refine Late.bind
    (late_eachLo sMT t cms xin a w _ _ i ph n zs n Γ le_rfl hF
      (List.pairwise_append.1 hpw).1 fun z hz => hact _ (hcm z hz))
    fun n1 Γ1 xs ys h1 => ?_
  obtain ⟨rfl, a1, hF1, fr1, hpw1, hx1, hall⟩ := h1
  have hA1 : ∀ a' ∈ actL ph.afterLo xs, n ≤ a' ∧ n1 > a' ∧ Base Γ1 a' := fun a' ha' => by
    rw [actL_afterLo] at ha'
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha'
    exact hx1 x hx
  refine Late.mono
    (ih (fun p => embS (.inr p)) (fun z => embP (.inr z)) (i + 1) ph.afterLo
      (k0 (a.kind.shOf (w.chal (blk0 lam K)))) xs { a0 with trees := a0.trees ++ [none] } n1 Γ1 hF1
      (by rw [actL_afterLo]; exact hpw1) (fun a' ha' => (hA1 a' ha').2)
      (fun h => by rw [← hall.length_eq]; exact hlen h)
      (fun h => hreq (by cases ph <;> simp_all [PhT.afterLo])))
    fun n' Γ' out out' hpost => ?_
  obtain ⟨e0, b1, hF', hFr', new0, ntr0, nN0, nD0, e1, e2, hn0, e3, e4, hD0, hrq, hall'⟩ := hpost
  have hFr01 : Fr (actL ph zs) n Γ Γ1 := fun u hu hua o pt hp => Or.inl (by
    rw [← fr1 u hu fun hm => hua (List.mem_append.2 (Or.inl hm))]; exact hp)
  refine ⟨e0, by omega, hF', hFr01.trans hFr' a1 (fun a' ha' => Or.inr (hA1 a' ha').1), new0,
    none :: ntr0, nN0, nD0, e1, by rw [e2]; simp, fun u hu => by have := hn0 u hu; omega, e3, e4,
    fun u hu => ⟨a1.trans (hD0 u hu).1, (hD0 u hu).2⟩, ?_, ?_⟩
  · cases ph with
    | first => exact fun rq h => ⟨(hrq rq h).1, by have := (hrq rq h).2.1; omega, (hrq rq h).2.2⟩
    | loc => exact fun rq h => ⟨(hrq rq h).1, by have := (hrq rq h).2.1; omega, (hrq rq h).2.2⟩
    | shr tk0 => exact hrq
    | aft => exact hrq
  · refine forall₂_comp (fun z z' acc' hzf hS => ?_) (forall₂_mem hall) hall'
    obtain ⟨hz, hf⟩ := hzf
    have hcur := (hact _ (hcm z hz)).1
    rw [actL_afterLo] at hFr'
    refine slotK_lo t cms xin a A w W hk embS embP i ph m0 k0 hf hS hFr' a1 hcur
      (fun a' ha' => by obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha'; exact (hx1 x hx).1) ?_ ?_ ?_
    · cases ph with
      | shr tk0 =>
        intro hm
        rcases List.mem_cons.1 hm with h | h
        · have := (List.pairwise_append.1 hpw).2.2 _ (List.mem_map.2 ⟨z, hz, rfl⟩) tk0 (by simp)
          omega
        · have := hn0 _ h; omega
      | aft => intro hm; have := hn0 _ hm; omega
      | first =>
        intro hm
        rcases List.mem_append.1 hm with h | h
        · cases hq : out.2.req with
          | none => rw [hq] at h; simp at h
          | some rq =>
            rw [hq] at h
            have h' : curOf .first z.2 = rq.root := by simpa using h
            have := (hrq rq hq).2.1
            omega
        · have := hn0 _ h; omega
      | loc =>
        intro hm
        rcases List.mem_append.1 hm with h | h
        · cases hq : out.2.req with
          | none => rw [hq] at h; simp at h
          | some rq =>
            rw [hq] at h
            have h' : curOf .loc z.2 = rq.root := by simpa using h
            have := (hrq rq hq).2.1
            omega
        · have := hn0 _ h; omega
    · cases ph with
      | shr tk0 => exact fun tj nJ pls Pc => ctxB_aft t cms _ s A W _ _ _ _ _ _ _ _ _ _
      | aft => exact fun _ _ _ _ => rfl
      | first => exact fun _ _ _ _ => rfl
      | loc => exact fun _ _ _ _ => rfl
    · cases ph with
      | shr tk0 =>
        intro u hu
        rcases List.mem_cons.1 hu with h | h
        · refine Or.inr ?_
          rw [h]
          have htk := hact tk0 (List.mem_append.2 (Or.inr (by simp)))
          have hnc : tk0 ∉ zs.map fun z => curOf (.shr tk0) z.2 := fun hm => by
            have := (List.pairwise_append.1 hpw).2.2 _ hm tk0 (by simp)
            omega
          refine Cov.fr (htk.2.congr (fr1 tk0 htk.1 hnc)) hFr' (by have := htk.1; omega)
            (fun hm => ?_) (baseUp_base _)
          obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
          have h3 : n ≤ tk0 := e ▸ (hx1 x hx).1
          have := htk.1
          omega
        · exact Or.inl h
      | aft => exact fun u hu => Or.inl hu
      | first => exact fun u hu => Or.inl hu
      | loc => exact fun u hu => Or.inl hu

end Steps

end Compile.Batch
