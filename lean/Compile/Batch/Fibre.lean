-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Fibre.lean: along the hash work of a batch (`skB`, Compile/Batch/Mirror.lean), under
the hypotheses of `sk_fibreB` (`RoundsQueryLayout.OKG`, `RoundSplits.FmtFrom`, two lengths: `fl.length = n`,
`accs.length = n`), uniform Fiat-Shamir answers are: verifier messages sampled first, then answers
sampled from their fibres (the answers that yield them, up to proof-of-work bits: `ansB`, `tryL`,
Compile/Batch/Mirror.lean). `sk_fibreB` states it as an equation between two distributions.

All statements on runs are for the run `Iv N₀ δ`.

Notation: `Iv N₀ δ Q w`: the run of Q under the renumbering of tokens (`virtL N₀ δ`,
Compile/Step1_defc_L.lean) from the state w; `N₀`, `δ`: natural numbers; `LS lam K L`:
`LSt (spec lam K L)` (Rom/DeferLate.lean): the state of the experiment beside the challenger's own;
`fl`: a `List Bool`: the flags of the slots; `mask fl l`: the values of the slots whose flag is
true; `first l`: the first value that is given; `drawV C n`: n independent uniform values;
`drawR s A n`: the verifier messages of the local transcripts of n slots; `SlotAcc`, `Acc0`
(Compile/Batch/Prover.lean): what a slot, what the shared part has accumulated; in `skB … f0 zs a0`
(Compile/Batch/Mirror.lean), f0: the challenges of a slot's transcript from which the shared ones
are taken, if they are given.

Terms: lean/GLOSSARY.md.
-/
import Compile.Batch.Mirror
import Compile.Batch.LoopLaw
import Compile.Batch.LoopBind
import Compile.Step1_defc_L
import Compile.Step1_defc_Prob
import Iop.BatchFmt
import Rom.Forget

noncomputable section

namespace Compile.Batch.Fibre
open Iop Rom Prob
open Compile.DefC
  (virtL virtL_bind run_bind fibre fibre_nonempty unif_eq_bind_fibre unif_prod_map_fst)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (N₀ δ : ℕ)

abbrev LS (lam K : ℕ) (L : BatchProtocol I X) : Type := LSt (spec lam K L)

/-- the run of Q under the renumbering of tokens (`virtL N₀ δ`, Compile/Step1_defc_L.lean) -/
def Iv {α : Type} (Q : Lp lam K L α) (w : LS lam K L) : PMF (α × LS lam K L) := (virtL N₀ δ Q).run w

theorem Iv_pure {α : Type} (a : α) (w : LS lam K L) :
    Iv N₀ δ (LStep.pure a : Lp lam K L α) w = PMF.pure (a, w) := rfl
theorem Iv_pure' {α : Type} (a : α) (w : LS lam K L) :
    Iv N₀ δ (pure a : Lp lam K L α) w = PMF.pure (a, w) := rfl

theorem Iv_bind {α β : Type} (Q : Lp lam K L α) (g : α → Lp lam K L β) (w : LS lam K L) :
    Iv N₀ δ (Q.bind g) w = (Iv N₀ δ Q w).bind fun y => Iv N₀ δ (g y.1) y.2 := by
  unfold Iv
  rw [virtL_bind, run_bind]

theorem Iv_bind' {α β : Type} (Q : Lp lam K L α) (g : α → Lp lam K L β) (w : LS lam K L) :
    Iv N₀ δ (Q >>= g) w = (Iv N₀ δ Q w).bind fun y => Iv N₀ δ (g y.1) y.2 := Iv_bind N₀ δ Q g w

/-! ## One Fiat-Shamir answer -/

section One
variable {r : Round} {a : RAnn r} (w : WireRB lam K r a)

theorem chal_fst_unif (hw : w.OKG) :
    (PMF.uniformOfFintype ((Fin K → Dig lam) × Dig lam)).map (fun x => w.chal x.1) =
      PMF.uniformOfFintype r.Chal := by
  have h0 : (PMF.uniformOfFintype (Fin K → Dig lam)).map w.chal = PMF.uniformOfFintype r.Chal :=
    hw.chal_unif
  rw [← h0, ← unif_prod_map_fst (β := Fin K → Dig lam) (γ := Dig lam), PMF.map_comp]
  rfl

open Classical in
theorem ansB_some (hw : w.OKG) (c : r.Chal) :
    ansB w (some c) =
      ⟨fibre (fun x : (Fin K → Dig lam) × Dig lam => w.chal x.1) c,
        fibre_nonempty _ (chal_fst_unif w hw) c⟩ := by
  have h : (Finset.univ.filter fun x : (Fin K → Dig lam) × Dig lam => w.chal x.1 = c).Nonempty :=
    fibre_nonempty (fun x : (Fin K → Dig lam) × Dig lam => w.chal x.1) (chal_fst_unif w hw) c
  show (if h : (Finset.univ.filter fun x : (Fin K → Dig lam) × Dig lam =>
          w.chal x.1 = c).Nonempty then
        (⟨_, h⟩ : ASet lam K)
      else ⟨Finset.univ, Finset.univ_nonempty⟩) = _
  rw [dif_pos h]
  rfl

/-- under `w.OKG`: uniform answers: a uniform verifier message, then an answer from its fibre -/
theorem ans_unif (hw : w.OKG) :
    PMF.uniformOfFinset (ansB w none).1 (ansB w none).2 =
      (PMF.uniformOfFintype r.Chal).bind fun c =>
        PMF.uniformOfFinset (ansB w (some c)).1 (ansB w (some c)).2 := by
  classical
  have h :=
    unif_eq_bind_fibre (fun x : (Fin K → Dig lam) × Dig lam => w.chal x.1) (chal_fst_unif w hw)
  have e : PMF.uniformOfFinset (ansB w none).1 (ansB w none).2 =
      PMF.uniformOfFintype ((Fin K → Dig lam) × Dig lam) := rfl
  rw [e, h]
  refine congrArg _ (funext fun c => ?_)
  rw [ansB_some w hw c]

theorem chal_of_mem (hw : w.OKG) (c : r.Chal) (x : (Fin K → Dig lam) × Dig lam)
    (hx : x ∈ (PMF.uniformOfFinset (ansB w (some c)).1 (ansB w (some c)).2).support) :
    w.chal x.1 = c := by
  classical
  rw [ansB_some w hw c, PMF.mem_support_uniformOfFinset_iff] at hx
  simpa [fibre] using hx

/-- what a Fiat-Shamir query does, whatever the set of answers -/
theorem Iv_fbL {β : Type} (t : Tag) (tk : Tok) (us : List Tok)
    (k : Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    ∃ G : (Fin K → Dig lam) × Dig lam → PMF (β × LS lam K L),
      ∀ A : ASet lam K, Iv N₀ δ (fbL t tk us A k) st = (PMF.uniformOfFinset A.1 A.2).bind G :=
  ⟨_, fun _ => rfl⟩

theorem fb_fibre {β : Type} (hw : w.OKG) (t : Tag) (tk : Tok) (us : List Tok)
    (k : Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    Iv N₀ δ (fbL t tk us (ansB w none) k) st =
      (PMF.uniformOfFintype r.Chal).bind fun c => Iv N₀ δ (fbL t tk us (ansB w (some c)) k) st := by
  obtain ⟨G, hG⟩ := Iv_fbL (L := L) N₀ δ t tk us k st
  simp only [hG]
  rw [ans_unif w hw, PMF.bind_bind]

end One

/-! ## A local round: all slots -/

/-- n independent uniform values -/
def drawV (C : Type) [Fintype C] [Nonempty C] : ℕ → PMF (List C)
  | 0 => PMF.pure []
  | n + 1 => (PMF.uniformOfFintype C).bind fun c => (drawV C n).map fun l => c :: l

theorem len_drawV (C : Type) [Fintype C] [Nonempty C] : ∀ n, ∀ l ∈ (drawV C n).support, l.length = n
  | 0, l, hl => by
    simp only [drawV, PMF.support_pure, Set.mem_singleton_iff] at hl
    rw [hl]; rfl
  | n + 1, l, hl => by
    simp only [drawV, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hl
    obtain ⟨c, -, l', hl', rfl⟩ := hl
    simp [len_drawV C n l' hl']

/-- the values of the slots whose flag is true -/
def mask {β : Type} (fl : List Bool) (l : List β) : List (Option β) :=
  List.zipWith (fun b x => if b then some x else none) fl l

theorem mask_cons {β : Type} (b : Bool) (fl : List Bool) (x : β) (l : List β) :
    mask (b :: fl) (x :: l) = (if b then some x else none) :: mask fl l := rfl

theorem len_mask {β : Type} (fl : List Bool) (l : List β) (h : fl.length = l.length) :
    (mask fl l).length = l.length := by
  simp [mask, h]

theorem mask_map {β γ : Type} (f : β → γ) :
    ∀ (fl : List Bool) (l : List β), (mask fl l).map (Option.map f) = mask fl (l.map f)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | b :: fl, x :: l => by
    rw [mask_cons, List.map_cons, List.map_cons, mask_cons, mask_map f fl l]
    cases b <;> rfl

/-- the first value that is given -/
def first {β : Type} (l : List (Option β)) : Option β := l.findSome? id

theorem first_map {β γ : Type} (f : β → γ) :
    ∀ l : List (Option β), (first l).map f = first (l.map (Option.map f))
  | [] => rfl
  | none :: l => first_map f l
  | some _ :: _ => rfl

theorem first_mask_replicate {β : Type} (c : β) :
    ∀ (fl : List Bool),
      first (mask fl (List.replicate fl.length c)) = if fl.any id then some c else none
  | [] => rfl
  | true :: fl => rfl
  | false :: fl => by
    have := first_mask_replicate c fl
    simpa [List.replicate_succ, mask_cons, first] using this

open Compile.DefC (lbind_assoc)

/-- the tree over a component, if it has one, as a separate program -/
def treeOptL (sMT : ℕ) (has : Bool) (depth : ℕ) : Lp lam K L (Option TTree) :=
  withTreeL sMT has depth LStep.pure

/-- the trees over a component with a list of trees (ds: the depths), as a separate program: it
makes them one after the other and returns them in this order -/
def treesL (sMT : ℕ) (ds : List ℕ) : Lp lam K L (List TTree) :=
  withTreesL sMT ds LStep.pure

theorem withTreeL_eq {β : Type} (sMT : ℕ) (has : Bool)
    (depth : ℕ) (k : Option TTree → Lp lam K L β) :
    withTreeL sMT has depth k = (treeOptL sMT has depth).bind k := by
  cases has with
  | true =>
    show (commitL sMT depth).bind _ = ((commitL sMT depth).bind _).bind k
    rw [lbind_assoc]
    rfl
  | false => rfl

/-- what follows `withTreesL` may be moved into its continuation -/
theorem withTreesL_bind {β γ : Type} (sMT : ℕ) :
    ∀ (ds : List ℕ) (k : List TTree → Lp lam K L β) (g : β → Lp lam K L γ),
      (withTreesL sMT ds k).bind g = withTreesL sMT ds fun trs => (k trs).bind g
  | [], _, _ => rfl
  | d :: ds, k, g => by
    show ((commitL sMT d).bind _).bind g = (commitL sMT d).bind _
    rw [lbind_assoc]
    exact congrArg _ (funext fun tr => withTreesL_bind sMT ds (fun trs => k (tr :: trs)) g)

theorem withTreesL_eq {β : Type} (sMT : ℕ) (ds : List ℕ) (k : List TTree → Lp lam K L β) :
    withTreesL sMT ds k = (treesL sMT ds).bind k :=
  (withTreesL_bind sMT ds LStep.pure k).symm

section Local
variable {Y : Type} (sMT : ℕ) (t : Tag) {r : Round} {a : RAnn r} (w : WireRB lam K r a) (ph : PhT)

/-- what a local round does to the accumulator of a slot; h: the verifier message, if it is given -/
def loAcc (h : Option r.Chal) (acc : SlotAcc lam K Y) : Lp lam K L (SlotAcc lam K Y) :=
  (treeOptL sMT w.hasJ w.depthJ).bind fun tr =>
  fbSlotGL w w.grJ (ansB w) t ph acc.tk acc.c (tr.map TTree.root) h fun nc dd bl tl =>
  LStep.pure { acc with
               tk := tl, blocks := acc.blocks ++ [bl], trees := acc.trees ++ [tr],
               toks := acc.toks ++ [tl], nons := nc.toList ++ acc.nons, dead := dd ++ acc.dead }

theorem skSlotLo_eq {s : Shape} (fo : Option (Rho (r :: s))) (acc : SlotAcc lam K Y) :
    skSlotLo (L := L) sMT t w ph (fo, acc) =
      (loAcc sMT t w ph (fo.map Prod.fst) acc).bind fun acc' =>
        LStep.pure (fo.map Prod.snd, acc') := by
  unfold loAcc
  rw [lbind_assoc, skSlotLo, withTreeL_eq]
  refine congrArg _ (funext fun tr => ?_)
  rw [fbSlotGL_bind]
  rfl

theorem fbSlot_fibre {β : Type} (hw : w.OKG) (tk c : Tok) (root : Option Tok)
    (k : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    Iv N₀ δ (fbSlotGL w w.grJ (ansB w) t ph tk c root none k) st =
      (PMF.uniformOfFintype r.Chal).bind fun ch =>
        Iv N₀ δ (fbSlotGL w w.grJ (ansB w) t ph tk c root (some ch) k) st := by
  cases ph <;> exact fbG_fibre I X lam K L N₀ δ r a w _ _ w.grJ hw hw.grJ_ok t _ _ k st

theorem lo_fibre (hw : w.OKG) (acc : SlotAcc lam K Y) (st : LS lam K L) :
    Iv N₀ δ (loAcc (L := L) sMT t w ph none acc) st
      = (PMF.uniformOfFintype r.Chal).bind fun c => Iv N₀ δ (loAcc sMT t w ph (some c) acc) st := by
  unfold loAcc
  simp only [Iv_bind, fbSlot_fibre N₀ δ t w ph hw]
  rw [PMF.bind_comm]

def eachLo : List (Option r.Chal × SlotAcc lam K Y) → Lp lam K L (List (SlotAcc lam K Y)) :=
  eachL fun z => loAcc sMT t w ph z.1 z.2

theorem eachL_nil {σ τ : Type} (f : σ → Lp lam K L τ) : eachL f [] = LStep.pure [] := rfl
theorem eachL_cons {σ τ : Type} (f : σ → Lp lam K L τ) (x : σ) (l : List σ) :
    eachL f (x :: l) = (f x).bind fun b => (eachL f l).bind fun r => LStep.pure (b :: r) := rfl

theorem each_skSlotLo {s : Shape} : ∀ zs : List (SlotSk lam K Y (r :: s)),
    eachL (skSlotLo (L := L) sMT t w ph) zs
      = (eachLo sMT t w ph (zs.map fun z => (z.1.map Prod.fst, z.2))).bind fun accs =>
          LStep.pure ((zs.map fun z => z.1.map Prod.snd).zip accs)
  | [] => rfl
  | (fo, acc) :: zs => by
    unfold eachLo at *
    rw [eachL_cons, each_skSlotLo zs, skSlotLo_eq, List.map_cons, eachL_cons]
    simp only [lbind_assoc]
    rfl

theorem len_eachL {σ τ : Type} (f : σ → Lp lam K L τ) :
    ∀ (l : List σ) (st : LS lam K L), ∀ y ∈ (Iv N₀ δ (eachL f l) st).support, y.1.length = l.length
  | [], st, y, hy => by
    rw [eachL_nil, Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy
    rw [hy]; rfl
  | x :: l, st, y, hy => by
    rw [eachL_cons] at hy
    simp only [Iv_bind, Iv_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨y1, -, y2, hy2, rfl⟩ := hy
    simp [len_eachL f l y1.2 y2 hy2]

theorem each_fibre (hw : w.OKG) :
    ∀ (accs : List (SlotAcc lam K Y)) (fl : List Bool), fl.length = accs.length →
      ∀ st : LS lam K L,
        Iv N₀ δ (eachLo (L := L) sMT t w ph ((List.replicate accs.length none).zip accs)) st =
          (drawV r.Chal accs.length).bind fun hs =>
            Iv N₀ δ (eachLo sMT t w ph ((mask fl hs).zip accs)) st
  | [], [], _, st => by
    simp only [drawV, List.length_nil, PMF.pure_bind]
    rfl
  | acc :: accs, b :: fl, hl, st => by
    have ih := each_fibre hw accs fl (by simpa using hl)
    unfold eachLo at *
    simp only [List.length_cons, List.replicate_succ, List.zip_cons_cons, eachL_cons, Iv_bind, ih,
      drawV, PMF.bind_bind, PMF.bind_map, Function.comp_def, mask_cons]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, PMF.bind_const]
      rw [PMF.bind_comm]
    | true =>
      simp only [if_true, lo_fibre N₀ δ sMT t w ph hw, PMF.bind_bind]
      refine congrArg _ (funext fun c => ?_)
      rw [PMF.bind_comm]

end Local

/-! ## Lists -/

theorem zipL1 {α β γ : Type} (f : α → γ) :
    ∀ (l : List α) (m : List β), (l.zip m).map (fun z => (f z.1, z.2)) = (l.map f).zip m
  | [], _ => rfl
  | _ :: _, [] => rfl
  | x :: l, y :: m => by simp only [List.zip_cons_cons, List.map_cons, zipL1 f l m]

theorem zipL2 {α β γ : Type} (f : α → γ) :
    ∀ (l : List α) (m : List β), l.length = m.length → (l.zip m).map (fun z => f z.1) = l.map f
  | [], [], _ => rfl
  | x :: l, y :: m, h => by
    simp only [List.zip_cons_cons, List.map_cons, zipL2 f l m (by simpa using h)]

theorem map_rep_none {α β : Type} (f : α → β) (n : ℕ) :
    (List.replicate n (none : Option α)).map (Option.map f) = List.replicate n none := by
  simp

/-! ## The rounds of the hash work, on accumulators -/

section Rounds
variable {Y : Type} (sMT : ℕ) (t : Tag) (dR : ℕ)

def hearAcc (bl : Blk lam K) (noted : Bool) (acc : SlotAcc lam K Y) : SlotAcc lam K Y :=
  { acc with
    blocks := acc.blocks ++ [bl], trees := if noted then acc.trees else acc.trees ++ [none] }

theorem hear_zip {r : Round} {s : Shape} (bl : Blk lam K) (noted : Bool) :
    ∀ (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y)),
      (fos.zip accs).map (hearL bl noted) =
        (fos.map (Option.map Prod.snd)).zip (accs.map (hearAcc bl noted))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | fo :: fos, acc :: accs => by
    simp only [List.zip_cons_cons, List.map_cons, hear_zip bl noted fos accs]
    rfl

variable {r : Round} {a : RAnn r} (w : WireRB lam K r a)

def joAcc (acc : SlotAcc lam K Y) : Lp lam K L (SlotAcc lam K Y) :=
  (treeOptL sMT w.hasJ w.depthJ).bind fun tr =>
  gL t acc.tk (tr.map TTree.root) fun c =>
  LStep.pure { acc with c := c, trees := acc.trees ++ [tr], toks := acc.toks ++ [c] }

theorem skSlotJoin_eq {s : Shape} (fo : Option (Rho (r :: s))) (acc : SlotAcc lam K Y) :
    skSlotJoin (L := L) sMT t w (fo, acc) =
      (joAcc sMT t w acc).bind fun acc' => LStep.pure (fo, acc') := by
  unfold joAcc
  rw [lbind_assoc, skSlotJoin, withTreeL_eq]
  rfl

def joinAccs : List (SlotAcc lam K Y) → Lp lam K L (List (SlotAcc lam K Y) × List Tok)
  | [] => LStep.pure ([], [])
  | acc :: l =>
    (joAcc sMT t w acc).bind fun x => (joinAccs l).bind fun o => LStep.pure (x :: o.1, x.c :: o.2)

theorem skJoinM_zip {s : Shape} :
    ∀ (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y)), fos.length =
        accs.length →
      skJoinM (L := L) sMT t w (fos.zip accs) =
        (joinAccs sMT t w accs).bind fun o => LStep.pure (fos.zip o.1, o.2)
  | [], [], _ => rfl
  | fo :: fos, acc :: accs, h => by
    have ih := skJoinM_zip fos accs (by simpa using h)
    rw [List.zip_cons_cons]
    show (skSlotJoin sMT t w (fo, acc)).bind (fun z' =>
        (skJoinM sMT t w (fos.zip accs)).bind fun o => LStep.pure (z' :: o.1, z'.2.c :: o.2)) = _
    rw [ih, skSlotJoin_eq]
    show _ = ((joAcc sMT t w acc).bind fun x =>
        (joinAccs sMT t w accs).bind fun o => LStep.pure (x :: o.1, x.c :: o.2)).bind _
    simp only [lbind_assoc]
    rfl

theorem len_joinAccs :
    ∀ (l : List (SlotAcc lam K Y)) (st : LS lam K L),
      ∀ y ∈ (Iv N₀ δ (joinAccs (L := L) sMT t w l) st).support, y.1.1.length = l.length
  | [], st, y, hy => by
    have : y = (([], []), st) := by simpa [joinAccs, Iv_pure] using hy
    rw [this]
  | x :: l, st, y, hy => by
    simp only [joinAccs, Iv_bind, Iv_pure, PMF.mem_support_bind_iff,
      PMF.support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨y1, -, y2, hy2, rfl⟩ := hy
    simp [len_joinAccs l y1.2 y2 hy2]

variable {s : Shape} {A : RoundSplits s} (W : RoundsQueryLayout lam K s A)

theorem skB_lo (hk : a.kind = .lo) (ph : PhT) (f0 : Option (Rho (r :: s)))
    (zs : List (SlotSk lam K Y (r :: s))) (a0 : Acc0) :
    skB (L := L) sMT t dR (r :: s) (a, A) (w, W) ph f0 zs a0 =
      (eachL (skSlotLo sMT t w ph) zs).bind fun zs' =>
          skB sMT t dR s A W ph.afterLo (f0.map Prod.snd) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

theorem skB_join (hk : a.kind = .sh) (f0 : Option (Rho (r :: s)))
    (zs : List (SlotSk lam K Y (r :: s))) (a0 : Acc0) :
    skB (L := L) sMT t dR (r :: s) (a, A) (w, W) .loc f0 zs a0 = (skJoinM sMT t w zs).bind fun o =>
          (reqL dR o.2).bind fun rq =>
          (treeOptL sMT w.has0 w.depth0).bind fun tr0 =>
          fbGL w w.gr0 (ansB w) t rq.root (tr0.map TTree.root).toList
              (f0.map Prod.fst) fun nc dd bl tl =>
          skB sMT t dR s A W (.shr tl) (f0.map Prod.snd) (o.1.map (hearL bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  simp only [← withTreeL_eq]
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

theorem skB_shr (hk : a.kind = .sh) (tk0 : Tok) (f0 : Option (Rho (r :: s)))
    (zs : List (SlotSk lam K Y (r :: s))) (a0 : Acc0) :
    skB (L := L) sMT t dR (r :: s) (a, A) (w, W) (.shr tk0) f0 zs a0 =
      (treeOptL sMT w.has0 w.depth0).bind fun tr0 =>
          fbGL w w.gr0 (ansB w) t tk0 (tr0.map TTree.root).toList
              (f0.map Prod.fst) fun nc dd bl tl =>
          skB sMT t dR s A W (.shr tl) (f0.map Prod.snd) (zs.map (hearL bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  rw [← withTreeL_eq]
  obtain ⟨kind, M0, Mj, sp, P0, Pj, pl0, plj, pln, own⟩ := a
  dsimp only at hk
  subst hk
  rfl

/-- the local round, on accumulators -/
theorem Iv_skB_lo (hk : a.kind = .lo) (ph : PhT) (f0 : Option (Rho (r :: s)))
    (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y))
    (hl : fos.length = accs.length) (a0 : Acc0) (st : LS lam K L) :
    Iv N₀ δ (skB (L := L) sMT t dR (r :: s) (a, A) (w, W) ph f0 (fos.zip accs) a0) st =
      (Iv N₀ δ (eachLo sMT t w ph ((fos.map (Option.map Prod.fst)).zip accs)) st).bind fun y =>
          Iv N₀ δ (skB sMT t dR s A W ph.afterLo (f0.map Prod.snd)
                ((fos.map (Option.map Prod.snd)).zip y.1) { a0 with trees := a0.trees ++ [none] })
              y.2 := by
  have e1 : (fos.zip accs).map (fun z => (z.1.map Prod.fst, z.2)) =
      (fos.map (Option.map Prod.fst)).zip accs := zipL1 _ fos accs
  have e2 : (fos.zip accs).map (fun z => z.1.map Prod.snd) = fos.map (Option.map Prod.snd) :=
    zipL2 _ fos accs hl
  rw [skB_lo sMT t dR w W hk, each_skSlotLo, e1, e2]
  simp only [Iv_bind, Iv_pure, PMF.bind_bind, PMF.pure_bind]

theorem Iv_skB_lo' (hk : a.kind = .lo) (ph : PhT) (f0 : Option (Rho (r :: s)))
    (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y))
    (hl : fos.length = accs.length) (a0 : Acc0) (st : LS lam K L) (hsL : List (Option r.Chal))
    (tsL : List (Option (Rho s))) (f0' : Option (Rho s)) (e1 : fos.map (Option.map Prod.fst) = hsL)
    (e2 : fos.map (Option.map Prod.snd) = tsL) (e3 : f0.map Prod.snd = f0') :
    Iv N₀ δ (skB (L := L) sMT t dR (r :: s) (a, A) (w, W) ph f0 (fos.zip accs) a0) st =
      (Iv N₀ δ (eachLo sMT t w ph (hsL.zip accs)) st).bind fun y =>
          Iv N₀ δ (skB sMT t dR s A W ph.afterLo f0' (tsL.zip y.1)
                { a0 with trees := a0.trees ++ [none] }) y.2 := by
  subst e1 e2 e3
  exact Iv_skB_lo N₀ δ sMT t dR w W hk ph f0 fos accs hl a0 st

/-- what comes before the Fiat-Shamir query of the joining round -/
def preJ (accs : List (SlotAcc lam K Y)) :
    Lp lam K L ((List (SlotAcc lam K Y) × List Tok) × TTree × Option TTree) :=
  (joinAccs sMT t w accs).bind fun o =>
    (reqL dR o.2).bind fun rq =>
      (treeOptL sMT w.has0 w.depth0).bind fun tr0 => LStep.pure (o, rq, tr0)

theorem len_preJ (accs : List (SlotAcc lam K Y)) (st : LS lam K L) :
    ∀ z ∈ (Iv N₀ δ (preJ (L := L) sMT t dR w accs) st).support, z.1.1.1.length = accs.length := by
  intro z hz
  simp only [preJ, Iv_bind, Iv_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hz
  obtain ⟨y1, h1, y2, -, y3, -, rfl⟩ := hz
  exact len_joinAccs N₀ δ sMT t w accs st y1 h1

theorem Iv_skB_join (hk : a.kind = .sh) (f0 : Option (Rho (r :: s)))
    (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y))
    (hl : fos.length = accs.length) (a0 : Acc0) (st : LS lam K L) :
    Iv N₀ δ (skB (L := L) sMT t dR (r :: s) (a, A) (w, W) .loc f0 (fos.zip accs) a0) st =
      (Iv N₀ δ (preJ sMT t dR w accs) st).bind fun z =>
          Iv N₀ δ (fbGL w w.gr0 (ansB w) t z.1.2.1.root (z.1.2.2.map TTree.root).toList
                (f0.map Prod.fst) fun nc dd bl tl =>
                  skB sMT t dR s A W (.shr tl) (f0.map Prod.snd)
                    ((fos.map (Option.map Prod.snd)).zip (z.1.1.1.map (hearAcc bl true)))
                    { trees := a0.trees ++ [z.1.2.2], toks := a0.toks ++ [tl], req := some z.1.2.1,
                      nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }) z.2 := by
  rw [skB_join sMT t dR w W hk, skJoinM_zip sMT t w fos accs hl]
  simp only [preJ, Iv_bind, Iv_pure, PMF.bind_bind, PMF.pure_bind, hear_zip]

theorem Iv_skB_shr (hk : a.kind = .sh) (tk0 : Tok) (f0 : Option (Rho (r :: s)))
    (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y))
    (a0 : Acc0) (st : LS lam K L) :
    Iv N₀ δ (skB (L := L) sMT t dR (r :: s) (a, A) (w, W) (.shr tk0) f0 (fos.zip accs) a0) st =
      (Iv N₀ δ (treeOptL sMT w.has0 w.depth0) st).bind fun z =>
          Iv N₀ δ (fbGL w w.gr0 (ansB w) t tk0 (z.1.map TTree.root).toList
                (f0.map Prod.fst) fun nc dd bl tl =>
                  skB sMT t dR s A W (.shr tl) (f0.map Prod.snd)
                    ((fos.map (Option.map Prod.snd)).zip (accs.map (hearAcc bl false)))
                    { a0 with
                      trees := a0.trees ++ [z.1], toks := a0.toks ++ [tl],
                      nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }) z.2 := by
  rw [skB_shr sMT t dR w W hk]
  simp only [Iv_bind, hear_zip]

theorem Iv_skB_join' (hk : a.kind = .sh) (f0 : Option (Rho (r :: s)))
    (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y))
    (hl : fos.length = accs.length) (a0 : Acc0) (st : LS lam K L) (pc : Option r.Chal)
    (tsL : List (Option (Rho s))) (f0' : Option (Rho s)) (e1 : f0.map Prod.fst = pc)
    (e2 : fos.map (Option.map Prod.snd) = tsL) (e3 : f0.map Prod.snd = f0') :
    Iv N₀ δ (skB (L := L) sMT t dR (r :: s) (a, A) (w, W) .loc f0 (fos.zip accs) a0) st =
      (Iv N₀ δ (preJ sMT t dR w accs) st).bind fun z =>
          Iv N₀ δ (fbGL w w.gr0 (ansB w) t z.1.2.1.root
                (z.1.2.2.map TTree.root).toList pc fun nc dd bl tl =>
                  skB sMT t dR s A W (.shr tl) f0' (tsL.zip (z.1.1.1.map (hearAcc bl true)))
                    { trees := a0.trees ++ [z.1.2.2], toks := a0.toks ++ [tl], req := some z.1.2.1,
                      nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }) z.2 := by
  subst e1 e2 e3
  exact Iv_skB_join N₀ δ sMT t dR w W hk f0 fos accs hl a0 st

theorem Iv_skB_shr' (hk : a.kind = .sh) (tk0 : Tok) (f0 : Option (Rho (r :: s)))
    (fos : List (Option (Rho (r :: s)))) (accs : List (SlotAcc lam K Y)) (a0 : Acc0)
    (st : LS lam K L) (pc : Option r.Chal) (tsL : List (Option (Rho s)))
    (f0' : Option (Rho s)) (e1 : f0.map Prod.fst = pc)
    (e2 : fos.map (Option.map Prod.snd) = tsL) (e3 : f0.map Prod.snd = f0') :
    Iv N₀ δ (skB (L := L) sMT t dR (r :: s) (a, A) (w, W) (.shr tk0) f0 (fos.zip accs) a0) st =
      (Iv N₀ δ (treeOptL sMT w.has0 w.depth0) st).bind fun z =>
          Iv N₀ δ (fbGL w w.gr0 (ansB w) t tk0 (z.1.map TTree.root).toList pc fun nc dd bl tl =>
                skB sMT t dR s A W (.shr tl) f0' (tsL.zip (accs.map (hearAcc bl false)))
                  { a0 with
                    trees := a0.trees ++ [z.1], toks := a0.toks ++ [tl],
                    nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }) z.2 := by
  subst e1 e2 e3
  exact Iv_skB_shr N₀ δ sMT t dR w W hk tk0 f0 fos accs a0 st

end Rounds

/-! ## A shared Fiat-Shamir query, with what follows it -/

/-- the state after a Fiat-Shamir query -/
def aftFb (st : LS lam K L) (t : Tag) (tk : Tok)
    (us : List Tok) (x : (spec lam K L).Rng (OracleName.fb t)) : LS lam K L :=
  { st with
    vals := st.vals ++ [List.ofFn ((split lam K L).split (OracleName.fb t) x).2],
    evs := st.evs ++
        [⟨OracleName.fb t, x, Life2.up N₀ δ tk, us.map (Life2.up N₀ δ), st.vals.length, false⟩] }

theorem Iv_fbL_eq {β : Type} (t : Tag) (tk : Tok) (us : List Tok) (A : ASet lam K)
    (k : Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    Iv N₀ δ (fbL t tk us A k) st = (PMF.uniformOfFinset A.1 A.2).bind fun x =>
      Iv N₀ δ (k ((split lam K L).split (OracleName.fb t) x).1 (st.vals.length - δ))
          (aftFb N₀ δ st t tk us x) := rfl

theorem fb_step {β τ : Type} {r : Round} {a : RAnn r} (w : WireRB lam K r a) (hw : w.OKG) (t : Tag)
    (tk : Tok) (us : List Tok) (D : PMF τ) (k₀ : Blk lam K → Tok → Lp lam K L β)
    (k₁ : τ → Blk lam K → Tok → Lp lam K L β)
    (h : ∀ bl tl st', Iv N₀ δ (k₀ bl tl) st' = D.bind fun ts => Iv N₀ δ (k₁ ts bl tl) st')
    (p : Bool) (st : LS lam K L) :
    Iv N₀ δ (fbL t tk us (ansB w none) k₀) st =
      (PMF.uniformOfFintype r.Chal).bind fun c => D.bind fun ts =>
          Iv N₀ δ (fbL t tk us (ansB w (if p then some c else none)) (k₁ ts)) st := by
  have e : ∀ c : r.Chal,
      (D.bind fun ts => Iv N₀ δ (fbL t tk us (ansB w (if p then some c else none)) (k₁ ts)) st) =
        Iv N₀ δ (fbL t tk us (ansB w (if p then some c else none)) k₀) st := by
    intro c
    simp only [Iv_fbL_eq, h]
    rw [PMF.bind_comm]
  simp only [e]
  cases p with
  | true => simpa using fb_fibre N₀ δ w hw t tk us k₀ st
  | false => simp only [Bool.false_eq_true, if_false, PMF.bind_const]

/-! ### The same with proof-of-work bits -/

section StepG
variable {β τ : Type} {r : Round} {a : RAnn r} (w : WireRB lam K r a) {P : Type}

theorem Iv_ite {α : Type} (c : Bool) (A B : Lp lam K L α) (st : LS lam K L) :
    Iv N₀ δ (if c then A else B) st = if c then Iv N₀ δ A st else Iv N₀ δ B st := by
  cases c <;> rfl

/-- the distribution of the answer of one attempt -/
def ansLaw (g : GrW r.Chal P) (h : Option r.Chal) (last : Bool) :
    PMF ((Fin K → Dig lam) × Dig lam) :=
  match h with
  | none => PMF.uniformOfFintype _
  | some c => (PMF.uniformOfFintype (Fin (2 ^ g.b - 1 + 1))).bind fun y =>
      PMF.uniformOfFinset (if last || decide (zBits g.b y = fun _ => false) then
            ansB w (some (g.set (zBits g.b y) c))
          else ansT w g (zBits g.b y)).1
        (if last || decide (zBits g.b y = fun _ => false) then ansB w (some (g.set (zBits g.b y) c))
          else ansT w g (zBits g.b y)).2

/-- the state after an attempt at a ghost name -/
def aftFbw (st : LS lam K L) (t : Tag) (j : ℕ) (tk : Tok)
    (us : List Tok) (x : (spec lam K L).Rng (OracleName.fbw t j)) : LS lam K L :=
  { st with
    vals := st.vals ++ [List.ofFn ((split lam K L).split (OracleName.fbw t j) x).2],
    evs := st.evs ++
        [⟨OracleName.fbw t j, x, Life2.up N₀ δ tk, us.map (Life2.up N₀ δ), st.vals.length, false⟩] }

theorem Iv_tryW (g : GrW r.Chal P) (h : Option r.Chal) (last : Bool) (t : Tag) (j : ℕ) (tk : Tok)
    (us : List Tok) (k : Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    Iv N₀ δ (tryL w g (ansB w) h last fun A => fbLw t j tk us A k) st =
      (ansLaw w g h last).bind fun x =>
        Iv N₀ δ (k ((split lam K L).split (OracleName.fbw t j) x).1 (st.vals.length - δ))
            (aftFbw N₀ δ st t j tk us x) := by
  cases h with
  | none => rfl
  | some c => exact (PMF.bind_bind _ _ _).symm

theorem Iv_tryF (g : GrW r.Chal P) (h : Option r.Chal) (last : Bool) (t : Tag) (tk : Tok)
    (us : List Tok) (k : Blk lam K → Tok → Lp lam K L β) (st : LS lam K L) :
    Iv N₀ δ (tryL w g (ansB w) h last fun A => fbL t tk us A k) st =
      (ansLaw w g h last).bind fun x =>
        Iv N₀ δ (k ((split lam K L).split (OracleName.fb t) x).1 (st.vals.length - δ))
            (aftFb N₀ δ st t tk us x) := by
  cases h with
  | none => rfl
  | some c => exact (PMF.bind_bind _ _ _).symm

variable (D : PMF τ) (t : Tag) (tk : Tok) (us : List Tok) (h' : Option r.Chal)

theorem bind_ite (c : Bool) {γ : Type} (f g : τ → PMF γ) :
    (D.bind fun ts => if c then f ts else g ts) = if c then D.bind f else D.bind g := by
  cases c <;> rfl

/-- a sample on which only what follows the search depends may be made before the search -/
theorem fbWL_push (g : GrW r.Chal P) (k₀ : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β)
    (k₁ : τ → ℕ → List Tok → Blk lam K → Tok → Lp lam K L β)
    (h : ∀ m dd bl tl st',
      Iv N₀ δ (k₀ m dd bl tl) st' = D.bind fun ts => Iv N₀ δ (k₁ ts m dd bl tl) st') :
    ∀ (n j : ℕ) (dd : List Tok) (st : LS lam K L),
      Iv N₀ δ (fbWL w g (ansB w) t tk us h' k₀ n j dd) st =
        D.bind fun ts => Iv N₀ δ (fbWL w g (ansB w) t tk us h' (k₁ ts) n j dd) st
  | 0, j, dd, st => by
      simp only [fbWL, Iv_tryW, h]
      rw [PMF.bind_comm]
  | n + 1, j, dd, st => by
      simp only [fbWL, Iv_tryW, Iv_ite, h, fbWL_push g k₀ k₁ h n]
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun x => ?_)
      rw [bind_ite]

theorem fbGL_push (gr : Option (GrW r.Chal P))
    (k₀ : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β)
    (k₁ : τ → Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β)
    (h : ∀ nc dd bl tl st',
      Iv N₀ δ (k₀ nc dd bl tl) st' = D.bind fun ts => Iv N₀ δ (k₁ ts nc dd bl tl) st')
    (st : LS lam K L) :
    Iv N₀ δ (fbGL w gr (ansB w) t tk us h' k₀) st =
      D.bind fun ts => Iv N₀ δ (fbGL w gr (ansB w) t tk us h' (k₁ ts)) st := by
  cases gr with
  | none =>
      simp only [fbGL, Iv_fbL_eq, h]
      rw [PMF.bind_comm]
  | some g =>
      simp only [fbGL, fbTGL]
      cases g.more with
      | zero =>
          simp only [Iv_tryF, h]
          rw [PMF.bind_comm]
      | succ n =>
          simp only [Iv_tryF, Iv_ite, h,
            fbWL_push N₀ δ w D t tk us h' g (fun m => k₀ (some m)) (fun ts m => k₁ ts (some m))
              (fun m => h (some m)) n]
          rw [PMF.bind_comm]
          refine congrArg _ (funext fun x => ?_)
          rw [bind_ite]

theorem fbG_step (hw : w.OKG) (gr : Option (GrW r.Chal P)) (hgr : ∀ g, gr = some g → g.OK)
    (k₀ : Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β)
    (k₁ : τ → Option ℕ → List Tok → Blk lam K → Tok → Lp lam K L β)
    (h : ∀ nc dd bl tl st',
      Iv N₀ δ (k₀ nc dd bl tl) st' = D.bind fun ts => Iv N₀ δ (k₁ ts nc dd bl tl) st')
    (p : Bool) (st : LS lam K L) :
    Iv N₀ δ (fbGL w gr (ansB w) t tk us none k₀) st =
      (PMF.uniformOfFintype r.Chal).bind fun c =>
        D.bind fun ts =>
            Iv N₀ δ (fbGL w gr (ansB w) t tk us (if p then some c else none) (k₁ ts)) st := by
  simp only [← fbGL_push N₀ δ w D t tk us _ gr k₀ k₁ h st]
  cases p with
  | true => exact fbG_fibre I X lam K L N₀ δ r a w P β gr hw hgr t tk us k₀ st
  | false => simp only [Bool.false_eq_true, if_false, PMF.bind_const]

end StepG

/-! ## The verifier messages of all slots, as lists -/

/-- the verifier messages of one round, as the slots see them: independent in a local round, one for
all in a shared round -/
def headsOf {r : Round} (a : RAnn r) (n : ℕ) : PMF (List r.Chal) :=
  match a.kind with
  | .lo => drawV r.Chal n
  | .sh => (PMF.uniformOfFintype r.Chal).map (List.replicate n)

/-- the verifier messages of the local transcripts of n slots -/
def drawR : (s : Shape) → RoundSplits s → ℕ → PMF (List (Rho s))
  | [], _, n => PMF.pure (List.replicate n ())
  | r :: s, (a, A), n =>
    (headsOf a n).bind fun hs => (drawR s A n).map fun ts => (hs.zip ts : List (r.Chal × Rho s))

theorem len_headsOf {r : Round} (a : RAnn r) (n : ℕ) :
    ∀ l ∈ (headsOf a n).support, l.length = n := by
  intro l hl
  unfold headsOf at hl
  cases hk : a.kind with
  | lo => rw [hk] at hl; exact len_drawV _ n l hl
  | sh =>
    rw [hk] at hl
    simp only [PMF.mem_support_map_iff] at hl
    obtain ⟨c, -, rfl⟩ := hl
    simp

theorem len_drawR : ∀ (s : Shape) (A : RoundSplits s) (n : ℕ), ∀ l ∈ (drawR s A n).support, l.length = n
  | [], _, n, l, hl => by
    have hl' : l ∈ (PMF.pure (List.replicate n ()) : PMF (List (Rho []))).support := hl
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hl'
    rw [hl']; simp
  | r :: s, (a, A), n, l, hl => by
    have hl' : l ∈
        ((headsOf a n).bind fun hs =>
          (drawR s A n).map fun ts => (hs.zip ts : List (r.Chal × Rho s))).support := hl
    obtain ⟨hs, hhs, h2⟩ := (PMF.mem_support_bind_iff _ _ _).1 hl'
    obtain ⟨ts, hts, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 h2
    show (List.zip hs ts).length = n
    rw [List.length_zip, len_headsOf a n hs hhs, len_drawR s A n ts hts, Nat.min_self]

def toF : PhT → FPhase
  | .first => .first
  | .loc => .loc
  | .shr _ => .shr
  | .aft => .aft

theorem toF_afterLo (ph : PhT) : toF ph.afterLo = (toF ph).afterLo := by cases ph <;> rfl

section Main
variable {Y : Type} (sMT : ℕ) (t : Tag) (dR : ℕ)

/-- what is given to the slots in a round and after it, from the lists of heads and tails -/
theorem given_fst {r : Round} {s : Shape} (fl : List Bool) (hs : List r.Chal)
    (ts : List (Rho s)) (h : hs.length = ts.length) :
    (mask fl (hs.zip ts : List (Rho (r :: s)))).map (Option.map Prod.fst) = mask fl hs := by
  have := mask_map (Prod.fst : r.Chal × Rho s → r.Chal) fl (hs.zip ts)
  rw [List.map_fst_zip (le_of_eq h)] at this
  exact this

theorem given_snd {r : Round} {s : Shape} (fl : List Bool) (hs : List r.Chal)
    (ts : List (Rho s)) (h : hs.length = ts.length) :
    (mask fl (hs.zip ts : List (Rho (r :: s)))).map (Option.map Prod.snd) = mask fl ts := by
  have := mask_map (Prod.snd : r.Chal × Rho s → Rho s) fl (hs.zip ts)
  rw [List.map_snd_zip (le_of_eq h.symm)] at this
  exact this

/-- Under the hypotheses below: uniform answers in all chains are: the verifier messages of all
slots sampled first; then, in the chains of the slots with flag true and (if there is such a slot)
in the shared chain, answers from their fibres (up to proof-of-work bits), and uniform answers in
the other chains. -/
theorem sk_fibreB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A), RoundsQueryLayout.OKG s A W →
      ∀ ph : PhT, RoundSplits.FmtFrom s A (toF ph) →
        ∀ (n : ℕ) (fl : List Bool), fl.length = n →
          ∀ accs : List (SlotAcc lam K Y), accs.length = n →
            ∀ (a0 : Acc0) (st : LS lam K L),
              Iv N₀ δ (skB (L := L) sMT t dR s A W ph none ((List.replicate n none).zip accs) a0)
                  st =
                (drawR s A n).bind fun rs =>
                  Iv N₀ δ (skB sMT t dR s A W ph (first (mask fl rs)) ((mask fl rs).zip accs) a0) st
  | [], _, _, _, ph, _, n, fl, hfl, accs, hac, a0, st => by
    simp only [drawR, PMF.pure_bind]
    have e1 : ((List.replicate n (none : Option (Rho []))).zip accs).map Prod.snd = accs :=
      List.map_snd_zip (by simp [hac])
    have e2 : ((mask fl (List.replicate n (() : Rho []))).zip accs).map Prod.snd = accs :=
      List.map_snd_zip (by rw [len_mask _ _ (by simp [hfl])]; simp [hac])
    show Iv N₀ δ (pure (_, a0)) st = Iv N₀ δ (pure (_, a0)) st
    rw [e1]
    exact congrArg (fun l => Iv N₀ δ (pure (l, a0) : Lp lam K L _) st) e2.symm
  | r :: s, (a, A), (w, W), hW, ph, hF, n, fl, hfl, accs, hac, a0, st => by
    have hrep1 : (List.replicate n (none : Option (Rho (r :: s)))).map (Option.map Prod.fst) =
        List.replicate n none :=
      map_rep_none (α := r.Chal × Rho s) Prod.fst n
    have hrep2 : (List.replicate n (none : Option (Rho (r :: s)))).map (Option.map Prod.snd) =
        List.replicate n none :=
      map_rep_none (α := r.Chal × Rho s) Prod.snd n
    have hlen0 : (List.replicate n (none : Option (Rho (r :: s)))).length = accs.length := by
      simp [hac]
    cases hk : a.kind with
    | lo =>
      have hF' : RoundSplits.FmtFrom s A (toF ph.afterLo) := by
        rw [toF_afterLo]
        have : a.NoShared ∧ RoundSplits.FmtFrom s A (toF ph).afterLo := by
          simpa only [RoundSplits.FmtFrom, hk] using hF
        exact this.2
      -- the left side
      rw [Iv_skB_lo N₀ δ sMT t dR w W hk ph none _ accs hlen0, hrep1, hrep2]
      have hL : ∀ y ∈
              (Iv N₀ δ (eachLo (L := L) sMT t w ph ((List.replicate n none).zip accs)) st).support,
            Iv N₀ δ (skB sMT t dR s A W ph.afterLo
                  (Option.map Prod.snd (none : Option (Rho (r :: s))))
                  ((List.replicate n none).zip y.1) { a0 with trees := a0.trees ++ [none] }) y.2 =
              (drawR s A n).bind fun ts =>
                Iv N₀ δ (skB sMT t dR s A W ph.afterLo (first (mask fl ts)) ((mask fl ts).zip y.1)
                      { a0 with trees := a0.trees ++ [none] }) y.2 := by
        intro y hy
        have hy' : y.1.length = n := by
          have := len_eachL N₀ δ _ _ st y hy
          simpa [hac] using this
        exact sk_fibreB s A W hW.2 ph.afterLo hF' n fl hfl y.1 hy' _ y.2
      rw [bind_congr_support _ hL]
      subst hac
      rw [each_fibre N₀ δ sMT t w ph hW.1 accs fl hfl st, PMF.bind_bind]
      -- the right side
      have hh : headsOf a accs.length = drawV r.Chal accs.length := by unfold headsOf; rw [hk]
      simp only [drawR, hh, PMF.bind_bind, PMF.bind_map, Function.comp_def]
      refine bind_congr_support _ fun hs hhs => ?_
      rw [PMF.bind_comm]
      refine bind_congr_support _ fun ts hts => ?_
      have hlh := len_drawV _ _ hs hhs
      have hlt := len_drawR s A _ ts hts
      have hl2 : (mask fl (hs.zip ts : List (Rho (r :: s)))).length = accs.length := by
        rw [len_mask _ _ (by simp [hfl, hlh, hlt])]; simp [hlh, hlt]
      exact (Iv_skB_lo' N₀ δ sMT t dR w W hk ph (first (mask fl (hs.zip ts : List (Rho (r :: s)))))
        (mask fl (hs.zip ts : List (Rho (r :: s)))) accs hl2 a0 st (mask fl hs) (mask fl ts)
        (first (mask fl ts)) (given_fst fl hs ts (hlh.trans hlt.symm))
        (given_snd fl hs ts (hlh.trans hlt.symm))
        ((first_map _ _).trans (congrArg first (given_snd fl hs ts (hlh.trans hlt.symm))))).symm
    | sh =>
      subst hfl
      have hh : headsOf a fl.length =
          (PMF.uniformOfFintype r.Chal).map (List.replicate fl.length) := by
        unfold headsOf; rw [hk]
      have hR : ∀ G : List (r.Chal × Rho s) → PMF ((List (SlotAcc lam K Y) × Acc0) × LS lam K L),
          ((headsOf a fl.length).bind fun hs =>
              (drawR s A fl.length).map fun ts => (hs.zip ts : List (r.Chal × Rho s))).bind G =
            (PMF.uniformOfFintype r.Chal).bind fun c =>
              (drawR s A fl.length).bind fun ts => G ((List.replicate fl.length c).zip ts) := by
        intro G
        rw [hh, PMF.bind_bind, PMF.bind_map]
        simp only [PMF.bind_map, Function.comp_def]
      -- what is given in this round and after it
      have hpc : ∀ (c : r.Chal) (ts : List (Rho s)), ts.length = fl.length →
          (first (mask fl ((List.replicate fl.length c).zip ts : List (Rho (r :: s))))).map Prod.fst
            = if fl.any id then some c else none := by
        intro c ts hts
        exact ((first_map _ _).trans (congrArg first (given_fst fl _ ts (by simp [hts])))).trans
          (first_mask_replicate c fl)
      have hts2 : ∀ (c : r.Chal) (ts : List (Rho s)), ts.length = fl.length →
          (mask fl ((List.replicate fl.length c).zip ts : List (Rho (r :: s)))).map
              (Option.map Prod.snd) = mask fl ts :=
        fun c ts hts => given_snd fl _ ts (by simp [hts])
      have hf2 : ∀ (c : r.Chal) (ts : List (Rho s)), ts.length = fl.length →
          (first
              (mask fl ((List.replicate fl.length c).zip ts : List (Rho (r :: s))))).map Prod.snd =
            first (mask fl ts) :=
        fun c ts hts => (first_map _ _).trans (congrArg first (hts2 c ts hts))
      have hl2 : ∀ (c : r.Chal) (ts : List (Rho s)), ts.length = fl.length →
          (mask fl ((List.replicate fl.length c).zip ts : List (Rho (r :: s)))).length =
            accs.length := by
        intro c ts hts
        rw [len_mask _ _ (by simp [hts])]; simp [hts, hac]
      refine Eq.trans ?_ (hR _).symm
      cases ph with
      | first => simp [RoundSplits.FmtFrom, hk, toF] at hF
      | aft => simp [RoundSplits.FmtFrom, hk, toF] at hF
      | loc =>
        have hF' : RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toF] using hF
        rw [Iv_skB_join' N₀ δ sMT t dR w W hk none _ accs hlen0 a0 st none
            (List.replicate fl.length none) none rfl hrep2 rfl]
        have hL : ∀ z ∈ (Iv N₀ δ (preJ (L := L) sMT t dR w accs) st).support, _ = _ := fun z hz =>
          fbG_step N₀ δ w (drawR s A fl.length) t z.1.2.1.root (z.1.2.2.map TTree.root).toList
            hW.1 w.gr0 hW.1.gr0_ok _
            (fun ts nc dd bl tl =>
              skB sMT t dR s A W (.shr tl) (first (mask fl ts))
                ((mask fl ts).zip (z.1.1.1.map (hearAcc bl true)))
                { trees := a0.trees ++ [z.1.2.2], toks := a0.toks ++ [tl], req := some z.1.2.1,
                  nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead })
            (fun nc dd bl tl st' =>
              sk_fibreB s A W hW.2 (.shr tl) hF' fl.length fl rfl _
                (by rw [List.length_map, len_preJ N₀ δ sMT t dR w accs st z hz, hac]) _ st')
            (fl.any id) z.2
        rw [bind_congr_support _ hL, PMF.bind_comm]
        refine congrArg _ (funext fun c => ?_)
        rw [PMF.bind_comm]
        refine bind_congr_support _ fun ts hts => ?_
        have hlt := len_drawR s A _ ts hts
        exact (Iv_skB_join' N₀ δ sMT t dR w W hk _ _ accs (hl2 c ts hlt) a0 st _ _ _ (hpc c ts hlt)
          (hts2 c ts hlt) (hf2 c ts hlt)).symm
      | shr tk0 =>
        have hF' : RoundSplits.FmtFrom s A .shr := by
          have : a.NoSlot ∧ RoundSplits.FmtFrom s A .shr := by simpa only [RoundSplits.FmtFrom, hk, toF] using hF
          exact this.2
        rw [Iv_skB_shr' N₀ δ sMT t dR w W hk tk0 none _ accs a0 st none
            (List.replicate fl.length none) none rfl hrep2 rfl]
        have hL : ∀ z : Option TTree × LS lam K L, _ = _ := fun z =>
          fbG_step N₀ δ w (drawR s A fl.length) t tk0 (z.1.map TTree.root).toList
            hW.1 w.gr0 hW.1.gr0_ok _
            (fun ts nc dd bl tl =>
              skB sMT t dR s A W (.shr tl) (first (mask fl ts))
                ((mask fl ts).zip (accs.map (hearAcc bl false)))
                { a0 with
                  trees := a0.trees ++ [z.1], toks := a0.toks ++ [tl],
                  nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead })
            (fun nc dd bl tl st' =>
              sk_fibreB s A W hW.2 (.shr tl) hF' fl.length fl rfl _
                (by rw [List.length_map, hac]) _ st')
            (fl.any id) z.2
        simp only [hL]
        rw [PMF.bind_comm]
        refine congrArg _ (funext fun c => ?_)
        rw [PMF.bind_comm]
        refine bind_congr_support _ fun ts hts => ?_
        have hlt := len_drawR s A _ ts hts
        exact (Iv_skB_shr' N₀ δ sMT t dR w W hk tk0 _ _ accs a0 st _ _ _ (hpc c ts hlt)
          (hts2 c ts hlt) (hf2 c ts hlt)).symm

end Main

end Compile.Batch.Fibre
