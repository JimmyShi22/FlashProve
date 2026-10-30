-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLazyFin.lean: the compiled prover `proveBU` needs, of the trees over the encoded
index, only their roots and the openings that it shows. (not all hypotheses are named here: see
`erase_proveBU`) For the lazy prover (Compile/Batch/SeedLazyDefs.lean). (Words of this library:
lean/GLOSSARY.md.)

A token program runs on a store of secret strings; a token is a position in it (`erase`: the program
as an oracle algorithm on such a store).

  Part 1  the values of `openE` (Compile/Batch/TokTree.lean) and `opensExtB`
          (Compile/Batch/Prover.lean), which only read the store, do not change when the store
          grows, if all tokens of the trees are below its length (`SaltsLt`, `TreesLt`)
  Part 2  under that condition on vs0: on every store that extends vs0, `finishSlot` and `finishAll`
          are `finishSlotG` and `finishAllG` with the openings read from vs0; likewise `proveBU` on
          the trees is `proveBUG` on their roots and on the openings read from the store at the
          start
  Part 3  if there are 2^depthReq slots, `proveBUG`, which holds no outside token, does not look at
          the numbers of its tokens (`Compile.Seed.Par`); so, if what follows sees only its result,
          it may run on the empty store
  Part 4  the proof strings are made without coins, and without a query to a ghost name
  Part 5  under fixed oracle functions (`det`: every sample is 0), if, for every position p, the
          opening that is made when needed (`opL` at the leaf of p) has the salt and path of
          `opn p`, whose symbol is the external string's at p, the proof strings made with such
          openings are those of `finishAllG`

Limits: nothing on how an opening is made (Compile/Batch/SeedLazyLeaf.lean), distributions or cost.
-/
import Compile.Batch.SeedLazyDefs
import Compile.Batch.SeedParU
import Compile.Batch.RealQTree

noncomputable section

open Rom Iop ZKCP

namespace Compile.Batch
namespace Seed

open Life2 (up viewVals)
open Compile.Seed (Par All SaltsLt all_prefix upTree Sh ORel)
open List (Forall₂)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-! ## Part 1. The openings in the external strings, as values -/

theorem all_bind_congr {S : OSpec} {α β : Type} {Q : α → Prop} {c : OComp S α} (h : All Q c)
    {f f' : α → OComp S β} (hf : ∀ a, Q a → f a = f' a) : c.bind f = c.bind f' := by
  induction c with
  | pure a => exact hf a h
  | query o q k ih => exact congrArg (Rom.OComp.query o q) (funext fun r => ih r (h r))
  | sample n k ih => exact congrArg (Rom.OComp.sample n) (funext fun r => ih r (h r))

theorem all_bind_congr' {S : OSpec} {α β : Type} {Q : α → Prop} {c c' : OComp S α} (e : c = c')
    (h : All Q c') {f f' : α → OComp S β} (hf : ∀ a, Q a → f a = f' a) : c.bind f = c'.bind f' := by
  subst e
  exact all_bind_congr h hf

/-- the opening of leaf j of a tree over an encoded index, read from the store vs
-/
def openEV {σ : Type} (t : TreeH lam) (vs : List Bits) (j : ℕ) (a : σ) : Opening lam σ :=
  ⟨a, strOf vs (t.salts.getD j none), pathOf t.levels j⟩

theorem erase_openE {σ : Type} (t : TreeH lam) (j : ℕ) (a : σ) (vs : List Bits) :
    erase (openE (K := K) (L := L) t j a) vs = .pure (openEV t vs j a, vs) := by
  unfold openE openEV
  generalize t.salts.getD j none = x
  cases x with
  | none => rfl
  | some y => rfl

theorem strOf_getD_prefix {vs0 vs : List Bits} (h : vs0 <+: vs) {l : List (Option (Tok × Tok))}
    (hl : SaltsLt vs0.length l) (j : ℕ) :
    strOf vs (l.getD j none) = strOf vs0 (l.getD j none) := by
  rw [List.getD_eq_getElem?_getD]
  cases e : l[j]? with
  | none => rfl
  | some x =>
    cases x with
    | none => rfl
    | some y => exact getD_of_prefix h (hl y (List.mem_of_getElem? e)).1

theorem openEV_prefix {σ : Type} {vs0 vs : List Bits} (h : vs0 <+: vs) {t : TreeH lam}
    (hl : SaltsLt vs0.length t.salts) (j : ℕ) (a : σ) :
    openEV t vs j a = openEV t vs0 j a := by
  unfold openEV
  rw [strOf_getD_prefix h hl]

variable {E : ExtSpec}

/-- the field ext of a proof string: the openings opn at the read positions; the recursion of
opensExtB -/
def extV (we : WireE E) (opn : E.Pos → Opening lam E.Sym) (isRead : E.Pos → Bool) :
    List E.Pos → ExtF lam E
  | [] => fun _ => none
  | p :: ps =>
    if isRead p then @Function.update _ _ we.dec (extV we opn isRead ps) p (some (opn p))
    else extV we opn isRead ps

theorem extV_cons (we : WireE E) (opn : E.Pos → Opening lam E.Sym) (isRead : E.Pos → Bool)
    (p : E.Pos) (ps : List E.Pos) :
    extV we opn isRead (p :: ps) =
      if isRead p then @Function.update _ _ we.dec (extV we opn isRead ps) p (some (opn p))
      else extV we opn isRead ps := rfl

/-- the opening of position p, read from the trees and the store -/
def opnOf (we : WireE E) (y : E.Str) (trees : List (TreeH lam)) (vs : List Bits) (p : E.Pos) :
    Opening lam E.Sym :=
  openEV (trees.getD (we.which p) ⟨[], []⟩) vs (we.leaf p) (E.rd y p)

theorem erase_opensExtB (we : WireE E) (y : E.Str) (trees : List (TreeH lam))
    (isRead : E.Pos → Bool) (vs : List Bits) :
    ∀ ps : List E.Pos, erase (opensExtB (K := K) (L := L) we y trees isRead ps) vs =
      .pure (extV we (opnOf we y trees vs) isRead ps, vs)
  | [] => rfl
  | p :: ps => by
    have e : opensExtB (K := K) (L := L) we y trees isRead (p :: ps) = (opensExtB we y trees isRead ps).bind fun f =>
        if isRead p then
          (openE (trees.getD (we.which p) ⟨[], []⟩) (we.leaf p) (E.rd y p)).bind
            fun op => Step.pure (@Function.update _ _ we.dec f p (some op)) else Step.pure f := rfl
    rw [e, erase_bind, erase_opensExtB we y trees isRead vs ps]
    show erase (if isRead p then _ else _) vs = _
    rw [extV_cons]
    by_cases hr : isRead p = true
    · rw [if_pos hr, if_pos hr, erase_bind, erase_openE]
      rfl
    · rw [if_neg hr, if_neg hr]
      rfl

/-- all tokens of the trees are below b -/
def TreesLt (b : ℕ) (trees : List (TreeH lam)) : Prop := ∀ t ∈ trees, SaltsLt b t.salts

theorem opnOf_prefix (we : WireE E) (y : E.Str) {trees : List (TreeH lam)} {vs0 vs : List Bits}
    (h : vs0 <+: vs) (hl : TreesLt vs0.length trees) :
    opnOf we y trees vs = opnOf we y trees vs0 := by
  funext p
  refine openEV_prefix h ?_ _ _
  rw [List.getD_eq_getElem?_getD]
  cases e : trees[we.which p]? with
  | none => exact fun y hy => absurd hy List.not_mem_nil
  | some t => exact hl t (List.mem_of_getElem? e)

/-- what the field ext of a proof string is, for each set of read positions -/
def extOf (we : WireE E) (y : E.Str) (trees : List (TreeH lam)) (vs : List Bits) :
    (E.Pos → Bool) → ExtF lam E :=
  fun isRead => extV we (opnOf we y trees vs) isRead we.all

/-! ## Part 2. The program without the tokens of the trees over the encoded index -/

section Prove
variable (sMT sFS : ℕ) (t : Tag) {Y : Type} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt)
  (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ)
  (trees : List (TreeH lam)) (w : Wt)

theorem erase_finishSlot {vs0 vs : List Bits} (hp : vs0 <+: vs) (hl : TreesLt vs0.length trees)
    (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    erase (finishSlot (L := L) Q H wq wp trees w c0 a0 j x cj acc) vs =
      erase (finishSlotG Q H wq wp w (extOf wq.ext (H.ext w) trees vs0) c0 a0 j x cj acc) vs := by
  unfold finishSlot finishSlotG
  dsimp only
  split_ifs with hw
  · rfl
  · rw [erase_reveal, erase_reveal, erase_bind, erase_bind]
    refine all_bind_congr (all_prefix _ vs) fun o ho => ?_
    rw [erase_bind, erase_opensExtB, opnOf_prefix wq.ext (H.ext w) (hp.trans ho) hl]
    rfl

theorem erase_finishAll {vs0 : List Bits} (hl : TreesLt vs0.length trees) (fl : ℕ → Bool)
    (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits), vs0 <+: vs →
      erase (finishAll (L := L) Q H wq wp trees w fl c0 a0 j zs) vs =
        erase (finishAllG Q H wq wp w (extOf wq.ext (H.ext w) trees vs0) fl c0 a0 j zs) vs
  | _, [], _, _ => rfl
  | j, acc :: zs, vs, hp => by
    unfold finishAll finishAllG slotG
    rw [erase_bind, erase_bind]
    refine all_bind_congr' ?_ (all_prefix _ vs) fun o ho => ?_
    · cases acc.x with
      | none => rfl
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · exact erase_finishSlot Q H wq wp trees w hp hl c0 a0 j x cj acc
        · rfl
    · rw [erase_bind, erase_bind, erase_finishAll hl fl c0 a0 (j + 1) zs o.2 (hp.trans ho)]

/-- The compiled prover, given the roots and the openings: all chains, then the proof strings. -/
def proveBUG (cms : List (Dig lam)) (ext : (E.Pos → Bool) → ExtF lam E)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    St lam K L (List (Option (OneProtocolProof lam Q))) :=
  (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs).bind fun y =>
    finishAllG Q H wq wp w ext fl y.1 y.2.2 0 y.2.1

theorem erase_proveBU_split (fl : ℕ → Bool) (xs : List (Option Y)) (vs : List Bits) :
    erase (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs =
      (erase (chainsU sMT sFS t Q H wq wp embS embP xin depthReq (trees.map TreeH.root) w xs)
          vs).bind
        fun o => erase (finishAll Q H wq wp trees w fl o.1.1 o.1.2.2 0 o.1.2.1) o.2 := by
  unfold proveBU chainsU
  simp only [erase_bind, OComp.bind_assoc]
  rfl

/-- Under `TreesLt`: proveBU on the trees is proveBUG on their roots and on the openings read from
the store at the start. -/
theorem erase_proveBU (fl : ℕ → Bool) (xs : List (Option Y))
    {vs : List Bits} (hl : TreesLt vs.length trees) :
    erase (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs) vs =
      erase (proveBUG sMT sFS t Q H wq wp embS embP xin depthReq w (trees.map TreeH.root)
          (extOf wq.ext (H.ext w) trees vs) fl xs) vs := by
  unfold proveBUG
  rw [erase_proveBU_split, erase_bind]
  exact all_bind_congr (all_prefix _ vs) fun o ho =>
    erase_finishAll Q H wq wp trees w hl fl _ _ 0 _ o.2 ho

/-! ## Part 3. On the empty store -/

variable {N₀ δ : ℕ} (ext : (E.Pos → Bool) → ExtF lam E)

theorem par_finishSlotG {depthReq : ℕ} (c0 : H.Coin0) {a0 : Acc0}
    (h0 : Good0 depthReq (depths0 Q.loc.shape Q.ann wq.sh) a0) {j : ℕ} (hj : j < 2 ^ depthReq)
    (x : Y) (cj : H.Coin) (b : Bool) {acc : SlotAcc lam K (Y × H.Coin)}
    (hg : GoodAcc (depthsJ Q.loc.shape Q.ann wq.sh) acc) :
    Par N₀ δ Eq (finishSlotG (L := L) Q H wq wp w ext c0 (upAcc0 N₀ δ a0) j x cj (upAcc N₀ δ b acc))
      (finishSlotG Q H wq wp w ext c0 a0 j x cj acc) := by
  have eR : rootToks (acc.trees.map (Option.map (upTT N₀ δ)))
        (a0.trees.map (Option.map (upTT N₀ δ))) =
      (rootToks acc.trees a0.trees).map (up N₀ δ) :=
    rootToks_up hg.1 h0.1
  have eP : ((a0.req.map (upTT N₀ δ)).map fun rq => pathOf rq.levels j).getD [] =
      ((a0.req.map fun rq => pathOf rq.levels j).getD []).map (up N₀ δ) := by
    cases hq : a0.req with
    | none => rfl
    | some rq => exact pathOf_map _ (h0.2 rq hq) hj
  have eA : ((a0.req.map (upTT N₀ δ)).map fun rq => ancOf rq.levels j).getD [] =
      ((a0.req.map fun rq => ancOf rq.levels j).getD []).map (up N₀ δ) := by
    cases hq : a0.req with
    | none => rfl
    | some rq => exact ancOf_map _ (h0.2 rq hq) hj
  have eT : ((a0.req.map (upTT N₀ δ)).map TTree.root).toList =
      ((a0.req.map TTree.root).toList).map (up N₀ δ) :=
    toList_root_up h0.2
  unfold finishSlotG
  dsimp only [upAcc, upAcc0]
  rw [eR, eP, eA, eT, headD_up hg.2]
  simp only [List.length_map]
  split_ifs with hw
  · exact Par.pure rfl
  · refine Par.reveal' (by simp only [List.map_cons, List.map_append]) fun vs => ?_
    refine Par.bind (par_opensB Q.loc.shape Q.ann wq.sh _ acc.trees a0.trees _ hg.1 h0.1)
      fun f f' h => ?_
    subst h
    exact Par.pure rfl

theorem par_finishAllG {depthReq : ℕ} (fl : ℕ → Bool) (c0 : H.Coin0) {a0 : Acc0}
    (h0 : Good0 depthReq (depths0 Q.loc.shape Q.ann wq.sh) a0) :
    ∀ (j : ℕ) {l l' : List (SlotAcc lam K (Y × H.Coin))},
      Forall₂ (RelFin N₀ δ (depthsJ Q.loc.shape Q.ann wq.sh)) l l' → j + l'.length ≤ 2 ^ depthReq →
      Par N₀ δ Eq (finishAllG (L := L) Q H wq wp w ext fl c0 (upAcc0 N₀ δ a0) j l)
        (finishAllG Q H wq wp w ext fl c0 a0 j l')
  | _, _, _, .nil, _ => Par.pure rfl
  | j, _, _, @Forall₂.cons _ _ _ acc acc' l l' h1 h2, hl => by
    simp only [List.length_cons] at hl
    unfold finishAllG slotG
    refine Par.bind (r := Eq) ?_ fun π π' h => ?_
    · rw [h1.1]
      cases hx : acc'.x with
      | none => exact Par.pure rfl
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · obtain ⟨b, rfl, hg⟩ := h1.2 (by rw [hx]; exact fun e => by cases e)
          exact par_finishSlotG Q H wq wp w ext c0 h0 (by omega) x cj b hg
        · exact Par.pure rfl
    · subst h
      refine Par.bind (par_finishAllG fl c0 h0 (j + 1) h2 (by omega)) fun r r' h => ?_
      subst h
      exact Par.pure rfl

/-- proveBUG does not look at the numbers of its tokens, if the number of slots is 2^depthReq. -/
theorem par_proveBUG (cms : List (Dig lam)) (fl : ℕ → Bool)
    (xs : List (Option Y)) (hx : xs.length = 2 ^ depthReq) :
    Par N₀ δ Eq (proveBUG sMT sFS t Q H wq wp embS embP xin depthReq w cms ext fl xs)
      (proveBUG sMT sFS t Q H wq wp embS embP xin depthReq w cms ext fl xs) := by
  unfold proveBUG chainsU
  refine Par.bind
    (r := fun o o' =>
        o.1 = o'.1 ∧
        Forall₂ (RelFin N₀ δ (depthsJ Q.loc.shape Q.ann wq.sh)) o.2.1 o'.2.1 ∧
        o'.2.1.length = 2 ^ depthReq ∧
        o.2.2 = upAcc0 N₀ δ o'.2.2 ∧
        Good0 depthReq (depths0 Q.loc.shape Q.ann wq.sh) o'.2.2)
    ?_ fun o o' ho => ?_
  · refine Par.bind (par_drawT wp.coin0) fun c0 c0' h => ?_
    subst h
    refine Par.bind
      (par_eachM (r := Eq) (fun x x' h => by subst h; exact par_initSlotU sFS Q H wp w c0 x)
        (List.forall₂_same.2 fun _ _ => rfl))
      fun zs zs' hz => ?_
    refine Par.bind
      (par_chainTU sMT t cms (fun x : Y × H.Coin => xin x.1) depthReq Q.loc.shape Q.ann wq.sh embS
        embP 0 .first .first (H.strat0 w c0) zs zs' ⟨[], [], none, [], []⟩ ⟨[], [], none, [], []⟩ []
        [] rfl rfl hz.1 (hz.2.trans hx) ⟨.nil, fun _ e => by cases e⟩)
      fun o o' ho => ?_
    exact Par.pure ⟨rfl, ho⟩
  · obtain ⟨h0, h1, h2, h3, h4⟩ := ho
    rw [h0, h3]
    exact par_finishAllG Q H wq wp w ext fl o'.1 h4 0 h1 (by omega)

/-- So, if the number of slots is 2^depthReq, it may be run on the empty store, if what follows sees
only its result (k o.1). -/
theorem proveBUG_empty {γ : Type} (cms : List (Dig lam)) (fl : ℕ → Bool) (xs : List (Option Y))
    (hx : xs.length = 2 ^ depthReq) (vs : List Bits)
    (k : List (Option (OneProtocolProof lam Q)) → TypedOracleComputation lam K L γ) :
    (erase (proveBUG sMT sFS t Q H wq wp embS embP xin depthReq w cms ext fl xs) vs).bind
        (fun o => k o.1) =
      (erase (proveBUG sMT sFS t Q H wq wp embS embP xin depthReq w cms ext fl xs) []).bind
        fun o => k o.1 := by
  have h := par_proveBUG (N₀ := 0) (δ := vs.length) sMT sFS t Q H wq wp embS embP xin depthReq w ext
    cms fl xs hx vs (by omega)
  have e : viewVals 0 vs.length vs = [] := by simp [viewVals]
  rw [e] at h
  exact h.bind_eq fun a b hab => congrArg k hab.1

/-! ## Part 4. The proof strings are made without coins, and without a query to a ghost name -/

theorem nog_openT {σ : Type} (t : TTree) (j : ℕ) (a : σ) :
    NoGT (openT (lam := lam) (K := K) (L := L) t j a) := fun _ => trivial

theorem nog_opensComp {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (o : r.Orc)
    (tr : TTree) (isRead : r.Pos → Bool) (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ js : List ℕ, NoGT (opensComp (K := K) (L := L) dec posAt o tr isRead f js)
  | [] => trivial
  | j :: js => (nog_opensComp dec posAt o tr isRead f js).bind fun f' => by
      show NoGT (match posAt j with
        | some p =>
          if isRead p then
            (openT tr j (r.rd o p)).bind fun op =>
              Step.pure (@Function.update _ _ dec f' p (some op)) else Step.pure f'
        | none => Step.pure f')
      cases posAt j with
      | none => exact trivial
      | some p =>
        show NoGT (if isRead p then _ else _)
        cases isRead p
        · exact trivial
        · exact (nog_openT tr j _).bind fun _ => trivial

theorem nog_opensOpt {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (o : r.Orc) (tr : Option TTree) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    NoGT (opensOpt (K := K) (L := L) dec posAt depth o tr isRead f) := by
  cases tr with
  | none => exact trivial
  | some tr => exact nog_opensComp dec posAt o tr isRead f _

/-- Opening the positions read in the trees of one component, from tree number k on, queries no
ghost name. The depths and the trees are two lists of any lengths: where either list ends, nothing
more is opened. -/
theorem nog_opensTrees {r : Round} (dec : DecidableEq r.Pos) (posAt : ℕ → ℕ → Option r.Pos)
    (o : r.Orc) (isRead : r.Pos → Bool) :
    ∀ (k : ℕ) (ds : List ℕ) (trs : List TTree)
      (f : (p : r.Pos) → Option (Opening lam (r.Sym p))),
      NoGT (opensTrees (K := K) (L := L) dec posAt o isRead k ds trs f)
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | k, _ :: ds, tr :: trs, f =>
    (nog_opensTrees dec posAt o isRead (k + 1) ds trs f).bind fun f' =>
      nog_opensComp dec (posAt k) o tr isRead f' _

theorem nog_opensB :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (τ : Tr s)
        (tjs t0s : List (Option TTree)) (isRead : OPos s → Bool),
      NoGT (opensB (L := L) s A W τ tjs t0s isRead)
  | [], _, _, _, _, _, _ => trivial
  | _ :: s, (_, A), (_, W), (_, _, τ), tjs, t0s, _ =>
      (nog_opensOpt _ _ _ _ _ _ _).bind fun _ =>
        (nog_opensOpt _ _ _ _ _ _ _).bind fun _ =>
          (nog_opensB s A W τ tjs.tail t0s.tail _).bind fun _ => trivial

/-- The program that makes one slot's proof string queries no ghost name. -/
theorem nog_finishSlotG (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    NoGT (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · exact trivial
  · exact fun vs => (nog_opensB _ _ _ _ _ _ _).bind fun f => trivial

theorem nog_finishAllG (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      NoGT (finishAllG (L := L) Q H wq wp w ext fl c0 a0 j zs)
  | _, [] => trivial
  | j, acc :: zs => by
      unfold finishAllG slotG
      refine NoGT.bind ?_ fun π => (nog_finishAllG fl c0 a0 (j + 1) zs).bind fun r => trivial
      cases acc.x with
      | none => exact trivial
      | some y =>
        obtain ⟨x, cj⟩ := y
        show NoGT (if fl j then _ else _)
        cases fl j
        · exact trivial
        · exact nog_finishSlotG Q H wq wp w ext c0 a0 j x cj acc

/-- so, in what the scheme runs, the ghost names are written back (`realQ`) in the chains alone -/
theorem eraseR_proveBUG (cms : List (Dig lam)) (fl : ℕ → Bool)
    (xs : List (Option Y)) (vs : List Bits) :
    eraseR (proveBUG sMT sFS t Q H wq wp embS embP xin depthReq w cms ext fl xs) vs =
      (eraseR (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs) vs).bind
        fun o => erase (finishAllG Q H wq wp w ext fl o.1.1 o.1.2.2 0 o.1.2.1) o.2 := by
  unfold proveBUG
  rw [eraseR_bind]
  exact congrArg _ (funext fun o => eraseR_of_noGT (nog_finishAllG Q H wq wp w ext fl _ _ 0 _) o.2)

theorem sh_finishSlotG (μ : ℕ → ℕ) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) :
    Sh (S := spec lam K L) (sp := split lam K L) OracleName.other μ 0
      (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) := by
  unfold finishSlotG
  dsimp only
  split_ifs
  · exact .pure _
  · exact .reveal _ fun vs => (sh_opensB μ _ _ _ _ _ _ _).bind0 fun f => .pure _

theorem sh_finishAllG (μ : ℕ → ℕ) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))),
      Sh (S := spec lam K L) (sp := split lam K L) OracleName.other μ 0
        (finishAllG (L := L) Q H wq wp w ext fl c0 a0 j zs)
  | _, [] => .pure _
  | j, acc :: zs => by
      unfold finishAllG slotG
      refine Sh.bind0 ?_ fun π => (sh_finishAllG μ fl c0 a0 (j + 1) zs).bind0 fun r => .pure _
      cases acc.x with
      | none => exact .pure _
      | some y =>
        obtain ⟨x, cj⟩ := y
        show Sh _ μ 0 (if fl j then _ else _)
        cases fl j
        · exact .pure _
        · exact sh_finishSlotG Q H wq wp w ext μ c0 a0 j x cj acc

theorem noCoin_finishSlotG (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y) (cj : H.Coin)
    (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    (erase (finishSlotG (L := L) Q H wq wp w ext c0 a0 j x cj acc) vs).NoCoin :=
  noCoin_erase (sh_finishSlotG Q H wq wp w ext _ c0 a0 j x cj acc) vs

theorem noCoin_finishAllG (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits) :
    (erase (finishAllG (L := L) Q H wq wp w ext fl c0 a0 j zs) vs).NoCoin :=
  noCoin_erase (sh_finishAllG Q H wq wp w ext _ fl c0 a0 j zs) vs

/-! ## Part 5. Openings that are made when they are needed -/

variable (opL : ℕ → TypedOracleComputation lam K L (Option (Bits × List (Dig lam))))

theorem noCoin_opensExtL (hn : ∀ q, (opL q).NoCoin) (we : WireE E)
    (y : E.Str) (isRead : E.Pos → Bool) :
    ∀ ps, (opensExtL we y opL isRead ps).NoCoin
  | [] => trivial
  | p :: ps => OComp.NoCoin.bind (noCoin_opensExtL hn we y isRead ps) fun of => by
      cases of with
      | none => exact trivial
      | some f =>
        show (if isRead p then _ else _ : TypedOracleComputation lam K L _).NoCoin
        split_ifs
        · exact OComp.NoCoin.bind (hn _) fun _ => trivial
        · exact trivial

theorem det_opensExtL (g : Fam (spec lam K L)) (we : WireE E) (y : E.Str)
    (opn : E.Pos → Opening lam E.Sym)
    (ho : ∀ p, (opL (we.leaf p)).det g = some ((opn p).salt, (opn p).path))
    (hs : ∀ p, (opn p).sym = E.rd y p) (isRead : E.Pos → Bool) :
    ∀ ps, (opensExtL we y opL isRead ps).det g = some (extV we opn isRead ps)
  | [] => rfl
  | p :: ps => by
    unfold opensExtL extV
    rw [OComp.det_bind, det_opensExtL g we y opn ho hs isRead ps]
    dsimp only
    split_ifs
    · rw [OComp.det_bind, ho p, ← hs p]
      rfl
    · rfl

theorem noCoin_finishSlotL (hn : ∀ q, (opL q).NoCoin) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc vs).NoCoin := by
  unfold finishSlotL
  dsimp only
  split_ifs
  · exact trivial
  · refine OComp.NoCoin.bind (noCoin_opensExtL opL hn _ _ _ _) fun og => ?_
    cases og with
    | none => exact trivial
    | some gx =>
      exact OComp.NoCoin.bind
        (noCoin_finishSlotG Q H wq wp w _ c0 a0 j x cj acc vs) fun _ => trivial

theorem noCoin_finishAllL (hn : ∀ q, (opL q).NoCoin) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits),
      (finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs vs).NoCoin
  | _, [], _ => trivial
  | j, acc :: zs, vs => by
    unfold finishAllL slotL
    refine OComp.NoCoin.bind ?_ fun o1 => ?_
    · cases acc.x with
      | none => exact trivial
      | some xc =>
        obtain ⟨x, cj⟩ := xc
        dsimp only
        split_ifs
        · exact noCoin_finishSlotL Q H wq wp w opL hn c0 a0 j x cj acc vs
        · exact trivial
    · cases o1 with
      | none => exact trivial
      | some o =>
        exact OComp.NoCoin.bind (noCoin_finishAllL hn fl c0 a0 (j + 1) zs o.2) fun _ => trivial

variable (g : Fam (spec lam K L)) (opn : E.Pos → Opening lam E.Sym)

theorem det_finishSlotL (ho : ∀ p, (opL (wq.ext.leaf p)).det g = some ((opn p).salt, (opn p).path))
    (hs : ∀ p, (opn p).sym = E.rd (H.ext w) p) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ) (x : Y)
    (cj : H.Coin) (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    (finishSlotL (L := L) Q H wq wp w opL c0 a0 j x cj acc vs).det g =
      some ((erase
          (finishSlotG Q H wq wp w
            (fun isRead => extV wq.ext opn isRead wq.ext.all) c0 a0 j x cj acc) vs).det g) := by
  unfold finishSlotL
  dsimp only
  split_ifs with hw
  · unfold finishSlotG
    dsimp only
    rw [if_pos hw]
    rfl
  · rw [OComp.det_bind, det_opensExtL opL g wq.ext (H.ext w) opn ho hs]
    dsimp only
    rw [OComp.det_bind]
    rfl

theorem det_slotL (ho : ∀ p, (opL (wq.ext.leaf p)).det g = some ((opn p).salt, (opn p).path))
    (hs : ∀ p, (opn p).sym = E.rd (H.ext w) p) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) (j : ℕ)
    (acc : SlotAcc lam K (Y × H.Coin)) (vs : List Bits) :
    (slotL (L := L) Q H wq wp w opL fl c0 a0 j acc vs).det g =
      some ((erase
          (slotG Q H wq wp w (fun isRead => extV wq.ext opn isRead wq.ext.all) fl c0 a0 j acc)
          vs).det g) := by
  unfold slotL slotG
  cases acc.x with
  | none => rfl
  | some xc =>
    obtain ⟨x, cj⟩ := xc
    dsimp only
    split_ifs
    · exact det_finishSlotL Q H wq wp w opL g opn ho hs c0 a0 j x cj acc vs
    · rfl

theorem det_finishAllL (ho : ∀ p, (opL (wq.ext.leaf p)).det g = some ((opn p).salt, (opn p).path))
    (hs : ∀ p, (opn p).sym = E.rd (H.ext w) p) (fl : ℕ → Bool) (c0 : H.Coin0) (a0 : Acc0) :
    ∀ (j : ℕ) (zs : List (SlotAcc lam K (Y × H.Coin))) (vs : List Bits),
      (finishAllL (L := L) Q H wq wp w opL fl c0 a0 j zs vs).det g =
        some ((erase
            (finishAllG Q H wq wp w (fun isRead => extV wq.ext opn isRead wq.ext.all) fl c0 a0 j zs)
            vs).det g)
  | _, [], _ => rfl
  | j, acc :: zs, vs => by
    unfold finishAllL finishAllG
    rw [OComp.det_bind, erase_bind, OComp.det_bind, det_slotL Q H wq wp w opL g opn ho hs]
    dsimp only
    rw [OComp.det_bind, det_finishAllL ho hs fl c0 a0 (j + 1) zs, erase_bind, OComp.det_bind]
    rfl

end Prove

end Seed
end Compile.Batch
