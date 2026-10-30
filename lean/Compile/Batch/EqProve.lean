-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/EqProve.lean: proof of `Spec.eqProveB` (Compile/Batch/SpecEqProve.lean): under
`RoundsQueryLayout.OKG`, `GrFitP`, `wp.OK`, `Fmt`, one execution of the honest program (`proveBL`, a program of
`LStep`, Rom/DeferLate.lean) has the distribution of a session of the batch IOP, then the
reduction's subroutine (`proveBW`, Compile/Batch/Mirror.lean).

  1  Both programs begin with one salt for each slot, whatever they hold; the honest prover's coins
     are sampled first.
  2  The hash work (`skB`, Compile/Batch/Mirror.lean) does not depend on what the slots hold
     (`Fibre.skB_reZ`), and uniform answers are: verifier messages first, then answers from their
     fibres (`Fibre.sk_fibreB`; fibres: the head of Compile/Batch/Fibre.lean).
  3  In every run the hash blocks of a slot yield the messages given to it, except for the
     proof-of-work bits (`Fibre.supp_skB`); by the hypothesis `GrFitP` nothing that is made at the
     end depends on these; so both programs finish alike.
  4  `core`, and the session: uniform ρ and coins, taken as lists (`Fibre.map_slots_unif`,
     `map_finRange_unif_pi`).
-/
import Compile.Batch.SpecEqProve
import Compile.Batch.FibreSupp
import Compile.Batch.FibreProb

noncomputable section

namespace Compile.Batch.Fibre
open Iop Rom Prob
open Compile.DefC (virtL lbind_assoc)

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (N₀ δ : ℕ)

/-! ## 1. Coins and salts -/

theorem Iv_drawL_bind {β γ : Type} [Fintype β] [Nonempty β] (e : Enum β) (he : e.OK)
    (g : β → Lp lam K L γ) (st : LS lam K L) :
    Iv N₀ δ ((drawL e).bind g) st = (unif β).bind fun b => Iv N₀ δ (g b) st := by
  show (unif (Fin (e.n + 1))).bind (fun r => Iv N₀ δ (g (e.e r)) st) = _
  rw [← map_unif_equiv (Equiv.ofBijective e.e he), PMF.bind_map]
  rfl

theorem eachL_map {σ σ' τ : Type} (f : σ' → Lp lam K L τ) (g : σ → σ') :
    ∀ l : List σ, eachL (fun a => f (g a)) l = eachL f (l.map g)
  | [] => rfl
  | a :: l => by rw [List.map_cons, eachL_cons, eachL_cons, eachL_map f g l]

variable (sFS : ℕ)

/-- a slot at its start: a salt; z: the verifier messages given to it, and what it holds -/
def initP {Z : Type} {s : Shape} (z : Option (Rho s) × Option Z) : Lp lam K L (SlotSk lam K Z s) :=
  LStep.fresh sFS fun salt => LStep.pure (z.1, ⟨z.2, salt, 0, [], [], [salt], [], []⟩)

/-- n slots at their start, holding nothing -/
def baseL (n : ℕ) : Lp lam K L (List (SlotAcc lam K PUnit)) :=
  eachL (fun _ : Unit =>
      LStep.fresh sFS fun salt => LStep.pure ⟨none, salt, 0, [], [], [salt], [], []⟩)
    (List.replicate n ())

/-- entry number j of a list of contents -/
def pOf {Z : Type} (ps : List (Option Z)) : ℕ → Option Z := fun j => ps.getD j none

theorem each_initP {Z : Type} {s : Shape} :
    ∀ l : List (Option (Rho s) × Option Z), eachL (initP (lam := lam) (K := K) (L := L) sFS) l =
      (baseL sFS l.length).bind fun bs =>
        LStep.pure ((l.map Prod.fst).zip (reX (pOf (l.map Prod.snd)) bs))
  | [] => rfl
  | z :: l => by
    unfold baseL
    rw [eachL_cons, each_initP l, List.length_cons, List.replicate_succ, eachL_cons]
    unfold baseL
    simp only [lbind_assoc]
    rfl

theorem blocks_baseL :
    ∀ (n : ℕ) (st : LS lam K L),
      ∀ y ∈ (Iv N₀ δ (baseL (L := L) sFS n) st).support, y.1.length = n ∧ ∀ b ∈ y.1, b.blocks = []
  | 0, st, y, hy => by
    have hy' : y ∈ (Iv N₀ δ (LStep.pure [] : Lp lam K L (List (SlotAcc lam K PUnit))) st).support :=
      hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy'
    rw [hy']
    exact ⟨rfl, fun b hb => by cases hb⟩
  | n + 1, st, y, hy => by
    unfold baseL at hy
    rw [List.replicate_succ, eachL_cons, Iv_bind] at hy
    obtain ⟨y1, h1, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    rw [Iv_bind] at hy
    obtain ⟨y2, h2, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at hy
    obtain ⟨l2, b2⟩ := blocks_baseL n y1.2 y2 h2
    have h1' : y1 ∈
        ((PMF.uniformOfFintype (Fin sFS → Bool)).bind fun u =>
          Iv N₀ δ (LStep.pure
                ⟨none, st.vals.length - δ, 0, [], [], [st.vals.length - δ],
                  [], []⟩ : Lp lam K L (SlotAcc lam K PUnit)) _).support := h1
    obtain ⟨u, -, h1'⟩ := (PMF.mem_support_bind_iff _ _ _).1 h1'
    rw [Iv_pure, PMF.support_pure, Set.mem_singleton_iff] at h1'
    rw [hy]
    refine ⟨by simp [l2], fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · rw [h1']
    · exact b2 b hb

section Prove
variable (sMT : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type}
  (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
  (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
  (embE : E.Sym → Body L) (depthReq : ℕ) (trees : List (TreeH lam))

/-- what the honest prover's slots hold: the instance and the coins of the slot -/
def psL (xs : List (Option Y)) (cs : List H.Coin) : List (Option (Y × H.Coin)) :=
  List.zipWith (fun x c => x.map fun x => (x, c)) xs cs

/-- If `wp.coin.OK`: the coins of the slots are sampled first. -/
theorem Iv_each_initL (hp : wp.coin.OK) :
    ∀ (xs : List (Option Y)) (st : LS lam K L),
      Iv N₀ δ (eachL (initL (lam := lam) (K := K) (L := L) sFS Q H wp) xs) st =
        (drawV H.Coin xs.length).bind fun cs =>
          Iv N₀ δ (eachL (initP sFS) ((psL Q H xs cs).map fun p => (none, p))) st
  | [], st => by
    simp only [List.length_nil, drawV, PMF.pure_bind]
    rfl
  | x :: xs, st => by
    rw [eachL_cons]
    show Iv N₀ δ
        (((drawL wp.coin).bind fun cj => initP sFS (none, x.map fun x => (x, cj))).bind
          fun b => (eachL (initL sFS Q H wp) xs).bind fun r => LStep.pure (b :: r)) st = _
    rw [lbind_assoc, Iv_drawL_bind N₀ δ _ hp]
    simp only [List.length_cons, drawV, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    refine congrArg _ (funext fun c => ?_)
    have e : ∀ cs : List H.Coin,
        (psL Q H (x :: xs) (c :: cs)).map (fun p => ((none : Option (Rho Q.loc.shape)), p)) =
          (none, x.map fun x => (x, c)) :: (psL Q H xs cs).map fun p => (none, p) := fun _ => rfl
    simp only [e, eachL_cons, Iv_bind, Iv_each_initL hp xs, PMF.bind_bind]
    rw [PMF.bind_comm]

/-! ## 3. Both programs finish alike (under the hypotheses of `finish_eq`) -/

open Classical in
/-- the output of the session for one slot: `none`, or the disclosed view -/
def outp (w : Wt) (c0 : H.Coin0) (x : Y) (c : H.Coin) (ρ : Rho Q.loc.shape) :
    Option (DView Q.loc) :=
  if ρ ∈ H.one.withheld w x then none
  else some (Q.loc.dview x (H.ext w) ((H.one.strat w x (c0, c)).run ρ).1)

/-! ### Under `GrFitP`: nothing of what is made at the end depends on the proof-of-work bits -/

section Zero
variable {Q H wq} (hG : GrFitP H wq) {ρ₁ ρ₂ : Rho Q.loc.shape}
  (hz : RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ₁ = RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ₂)
include hG hz

theorem wh_zero (w : Wt) (x : Y) : ρ₁ ∈ H.one.withheld w x ↔ ρ₂ ∈ H.one.withheld w x := by
  rw [hG.wh w x ρ₁, hG.wh w x ρ₂, hz]

theorem reads_zero (x : Y) (pl : Plains Q.loc.shape) :
    Q.loc.reads x ρ₁ pl = Q.loc.reads x ρ₂ pl := by
  rw [hG.reads x ρ₁ pl, hG.reads x ρ₂ pl, hz]

theorem extReads_zero (x : Y) : Q.loc.extReads x ρ₁ = Q.loc.extReads x ρ₂ := by
  rw [hG.extReads x ρ₁, hG.extReads x ρ₂, hz]

/-- the disclosed view of the honest run -/
theorem dview_zero (w : Wt) (x : Y) (c : H.one.Coin) :
    Q.loc.dview x (H.ext w) ((H.one.strat w x c).run ρ₁).1 =
      Q.loc.dview x (H.ext w) ((H.one.strat w x c).run ρ₂).1 := by
  have p1 : ((H.one.strat w x c).run ρ₁).1.plains = ((H.one.strat w x c).run ρ₂).1.plains := by
    rw [(hG.run w x c ρ₁).1, (hG.run w x c ρ₂).1, hz]
  have r1 : ∀ p,
      ((H.one.strat w x c).run ρ₁).1.read p = ((H.one.strat w x c).run ρ₂).1.read p := fun p => by
    rw [(hG.run w x c ρ₁).2 p, (hG.run w x c ρ₂).2 p, hz]
  have q1 : ((H.one.strat w x c).run ρ₁).1.rho = ρ₁ := Strat.rho_run _ _
  have q2 : ((H.one.strat w x c).run ρ₂).1.rho = ρ₂ := Strat.rho_run _ _
  have e1 : Q.loc.reads x ρ₁ = Q.loc.reads x ρ₂ := funext (reads_zero hG hz x)
  have e2 := extReads_zero hG hz x
  unfold InteractiveOracleProof.dview InteractiveOracleProof.extAns
  rw [q1, q2, p1, e1, e2]
  simp only [r1]

end Zero

/-- under `GrFitP`: the proof string is made alike from verifier randomness that differs in
proof-of-work bits only -/
theorem finishBL_zero (hG : GrFitP H wq) {ρ₁ ρ₂ : Rho Q.loc.shape}
    (hz : RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ₁ = RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh ρ₂)
    {Z : Type} (x : Y) (dv : DView Q.loc) (a0 : Acc0) (j : ℕ) (acc : SlotAcc lam K Z) :
    finishBL (L := L) t Q wq embS embP xin embE trees x ρ₁ dv a0 j acc =
      finishBL t Q wq embS embP xin embE trees x ρ₂ dv a0 j acc := by
  have e1 : Q.loc.reads x ρ₁ = Q.loc.reads x ρ₂ := funext (reads_zero hG hz x)
  have e2 := extReads_zero hG hz x
  unfold finishBL
  rw [e1, e2]

section Slots
variable {N : ℕ} (w : Wt) (fl : ℕ → Bool) (c0 : H.Coin0) (x : Fin N → Option Y)
  (c : Fin N → H.Coin) (ρs : Fin N → Rho Q.loc.shape)

/-- the verifier messages given to slot j; what it holds for the honest prover; what it holds for
the reduction -/
def foF (j : Fin N) : Option (Rho Q.loc.shape) :=
  if fl j.val && (x j).isSome then some (ρs j) else none
def pLF (j : Fin N) : Option (Y × H.Coin) := (x j).map fun xj => (xj, c j)
def pWF (j : Fin N) : Option (Own Q) :=
  if fl j.val then (x j).map fun xj => (xj, ρs j, outp Q H w c0 xj (c j) (ρs j)) else none

theorem finish_eq (hG : GrFitP H wq) (a0 : Acc0) :
    ∀ (l : List (Fin N)) (j₀ : ℕ), l.map Fin.val = List.range' j₀ l.length →
      ∀ bs outs : List (SlotAcc lam K PUnit), (∀ b ∈ bs, b.blocks = []) →
        All3 (Yields Q.loc.shape Q.ann wq.sh) (l.map (foF Q fl x ρs)) bs outs →
        finishAllL (L := L) t Q H wq wp embS embP xin embE trees w fl c0 a0 j₀
            (reX (pOf (l.map (pLF Q H x c))) outs) =
          finishAllW t Q wq embS embP xin embE trees a0 j₀
            (reX (pOf (l.map (pWF Q H w fl c0 x c ρs))) outs)
  | [], _, _, [], [], _, _ => rfl
  | a :: l, j₀, hl, b :: bs, o :: outs, hb, h3 => by
    have hv : a.val = j₀ ∧ l.map Fin.val = List.range' (j₀ + 1) l.length := by
      rw [List.map_cons, List.length_cons, List.range'_succ] at hl
      exact ⟨(List.cons.inj hl).1, (List.cons.inj hl).2⟩
    have ih := finish_eq hG a0 l (j₀ + 1) hv.2 bs outs
      (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')) h3.2
    show (_ : Lp lam K L (Option (OneProtocolProof lam Q))).bind (fun π =>
                    (finishAllL t Q H wq wp embS embP xin embE trees w fl c0 a0 (j₀ + 1)
                        (reX (pOf (l.map (pLF Q H x c))) outs)).bind
                      fun r => pure (π :: r)) =
      (_ : Lp lam K L (Option (OneProtocolProof lam Q))).bind (fun π =>
                    (finishAllW t Q wq embS embP xin embE trees a0 (j₀ + 1)
                        (reX (pOf (l.map (pWF Q H w fl c0 x c ρs))) outs)).bind
                      fun r => pure (π :: r))
    rw [ih]
    refine congrArg (fun P : Lp lam K L (Option (OneProtocolProof lam Q)) => P.bind _) ?_
    -- the slot a
    show (match pLF Q H x c a with
        | some (xx, cj) =>
            if fl j₀ then
              haveI := wp.decW w xx (rhoOf Q.loc.shape Q.ann wq.sh o.blocks)
              if rhoOf Q.loc.shape Q.ann wq.sh o.blocks ∈ H.one.withheld w xx then pure none
              else
                finishBL t Q wq embS embP xin embE trees xx (rhoOf Q.loc.shape Q.ann wq.sh o.blocks)
                  (Q.loc.dview xx (H.ext w)
                    ((H.one.strat w xx (c0, cj)).run (rhoOf Q.loc.shape Q.ann wq.sh o.blocks)).1)
                  a0 j₀ (setX (pLF Q H x c a) o)
            else pure none
        | none => (pure none : Lp lam K L (Option (OneProtocolProof lam Q))))
      = (match pWF Q H w fl c0 x c ρs a with
        | some (xx, ρ, some dv) =>
          finishBL t Q wq embS embP xin embE trees xx ρ dv a0 j₀ (setX (pWF Q H w fl c0 x c ρs a) o)
        | _ => pure none)
    unfold pLF pWF
    rw [hv.1]
    cases hx : x a with
    | none => cases fl j₀ <;> rfl
    | some xa =>
      cases hf : fl j₀ with
      | false => rfl
      | true =>
        have hfo : foF Q fl x ρs a = some (ρs a) := by
          unfold foF
          rw [hv.1, hf, hx]
          rfl
        obtain ⟨bls, e1, e2⟩ := h3.1.2 (ρs a) hfo
        have hr : RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh (rhoOf Q.loc.shape Q.ann wq.sh o.blocks) =
            RoundsQueryLayout.zero Q.loc.shape Q.ann wq.sh (ρs a) := by
          rw [e1, hb b List.mem_cons_self, List.nil_append, e2]
        simp only [Option.map_some, if_true]
        unfold outp
        by_cases hw : ρs a ∈ H.one.withheld w xa
        · have hw' : rhoOf Q.loc.shape Q.ann wq.sh o.blocks ∈ H.one.withheld w xa :=
            (wh_zero hG hr w xa).2 hw
          rw [if_pos hw, if_pos hw']
        · have hw' : ¬ rhoOf Q.loc.shape Q.ann wq.sh o.blocks ∈ H.one.withheld w xa := fun h =>
            hw ((wh_zero hG hr w xa).1 h)
          rw [if_neg hw, if_neg hw', dview_zero hG hr w xa (c0, c a),
            finishBL_zero t Q H wq embS embP xin embE trees hG hr]
          rfl
  | [], _, _, [], _ :: _, _, h3 => h3.elim
  | [], _, _, _ :: _, _, _, h3 => h3.elim
  | _ :: _, _, _, [], _, _, h3 => h3.elim
  | _ :: _, _, _, _ :: _, [], _, h3 => h3.elim

/-! ## 4. The two programs, written out -/

theorem zipWith_map_map {ι α β γ : Type} (f : α → β → γ) (g : ι → α) (h : ι → β) : ∀ l : List ι,
    List.zipWith f (l.map g) (l.map h) = l.map fun a => f (g a) (h a)
  | [] => rfl
  | a :: l => by simp only [List.map_cons, List.zipWith_cons_cons, zipWith_map_map f g h l]

theorem bind_congr_supp {γ τ : Type} {p : PMF γ}
    {g g' : γ → PMF τ} (h : ∀ a ∈ p.support, g a = g' a) : p.bind g = p.bind g' := by
  refine PMF.ext fun b => ?_
  rw [PMF.bind_apply, PMF.bind_apply]
  refine tsum_congr fun a => ?_
  by_cases ha : p a = 0
  · rw [ha, zero_mul, zero_mul]
  · rw [h a ((p.mem_support_iff a).2 ha)]

theorem map_val_finRange (N : ℕ) :
    (List.finRange N).map Fin.val = List.range' 0 (List.finRange N).length := by
  rw [List.length_finRange, ← List.range_eq_range']
  exact List.map_coe_finRange_eq_range

theorem rho_pWF (j : Fin N) :
    (pWF Q H w fl c0 x c ρs j).map (fun z => z.2.1) = foF Q fl x ρs j := by
  unfold pWF foF
  cases fl j.val <;> cases x j <;> rfl

/-- the honest prover: coins, salts, hash work with uniform answers, the proof strings -/
theorem Iv_proveBL (hp : wp.OK) (st : LS lam K L) :
    Iv N₀ δ (proveBL (L := L) sMT sFS t Q H wq wp embS embP xin embE depthReq trees w
          fl ((List.finRange N).map x)) st =
      (unif H.Coin0).bind fun c0 =>
        (unif (Fin N → H.Coin)).bind fun c => (Iv N₀ δ (baseL sFS N) st).bind fun b =>
          (Iv N₀ δ (skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first none
                ((List.replicate N none).zip b.1) ⟨[], [], none, [], []⟩)
              b.2).bind fun o =>
            Iv N₀ δ (finishAllL t Q H wq wp embS embP xin embE trees w fl c0 o.1.2 0
                  (reX (pOf ((List.finRange N).map (pLF Q H x c))) o.1.1)) o.2 := by
  unfold proveBL
  rw [Iv_drawL_bind N₀ δ _ hp.coin0]
  refine congrArg _ (funext fun c0 => ?_)
  rw [Iv_bind, Iv_each_initL N₀ δ sFS Q H wp hp.coin, List.length_map, List.length_finRange,
    ← map_finRange_unif_pi, PMF.bind_map, PMF.bind_bind]
  refine congrArg _ (funext fun c => ?_)
  have e1 : psL Q H ((List.finRange N).map x) ((List.finRange N).map c) =
      (List.finRange N).map (pLF Q H x c) :=
    zipWith_map_map _ x c _
  have e2 : (((List.finRange N).map (pLF Q H x c)).map fun p =>
        ((none : Option (Rho Q.loc.shape)), p)).length = N := by simp
  have e3 : (((List.finRange N).map (pLF Q H x c)).map fun p =>
        ((none : Option (Rho Q.loc.shape)), p)).map Prod.fst =
      List.replicate N none := by
    rw [List.map_map, List.map_map]
    show (List.finRange N).map (fun _ => none) = _
    rw [List.map_const', List.length_finRange]
  have e4 : (((List.finRange N).map (pLF Q H x c)).map fun p =>
        ((none : Option (Rho Q.loc.shape)), p)).map Prod.snd =
      (List.finRange N).map (pLF Q H x c) := by
    rw [List.map_map]
    exact List.map_id _
  show (Iv N₀ δ
      (eachL (initP sFS)
        ((psL Q H ((List.finRange N).map x) ((List.finRange N).map c)).map fun p => (none, p)))
      st).bind _ = _
  rw [e1, each_initP, e2, e3, e4, Iv_bind, PMF.bind_bind]
  refine congrArg _ (funext fun b => ?_)
  rw [Iv_pure, PMF.pure_bind]
  show Iv N₀ δ
      ((skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first none
        ((List.replicate N none).zip (reX (pOf ((List.finRange N).map (pLF Q H x c))) b.1))
        ⟨[], [], none, [], []⟩).bind _) b.2 = _
  rw [zip_reX, skB_reZ, lbind_assoc, Iv_bind]
  rfl

/-- the reduction's subroutine: salts, hash work with the given messages, the proof strings -/
theorem Iv_proveBW (st : LS lam K L) :
    Iv N₀ δ (proveBW (L := L) sMT sFS t Q wq embS embP xin embE depthReq trees
          ((List.finRange N).map (pWF Q H w fl c0 x c ρs))) st =
      (Iv N₀ δ (baseL sFS N) st).bind fun b =>
          (Iv N₀ δ (skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first
                (first ((List.finRange N).map (foF Q fl x ρs)))
                (((List.finRange N).map (foF Q fl x ρs)).zip b.1) ⟨[], [], none, [], []⟩)
              b.2).bind fun o =>
            Iv N₀ δ (finishAllW t Q wq embS embP xin embE trees o.1.2 0
                  (reX (pOf ((List.finRange N).map (pWF Q H w fl c0 x c ρs))) o.1.1)) o.2 := by
  unfold proveBW
  have e0 : eachL (initW (lam := lam) (K := K) (L := L) sFS Q)
        ((List.finRange N).map (pWF Q H w fl c0 x c ρs)) =
      eachL (initP sFS)
        (((List.finRange N).map (pWF Q H w fl c0 x c ρs)).map fun o =>
          (o.map fun z => z.2.1, o)) := by
    have hW : initW (lam := lam) (K := K) (L := L) sFS Q =
        fun o : Option (Own Q) =>
          initP sFS ((fun o : Option (Own Q) => (o.map fun z => z.2.1, o)) o) := rfl
    rw [hW]
    exact eachL_map _ _ _
  have e2 : (((List.finRange N).map (pWF Q H w fl c0 x c ρs)).map fun o =>
        (o.map fun z => z.2.1, o)).length = N := by simp
  have e3 : (((List.finRange N).map (pWF Q H w fl c0 x c ρs)).map fun o =>
        (o.map fun z => z.2.1, o)).map Prod.fst =
      (List.finRange N).map (foF Q fl x ρs) := by
    rw [List.map_map, List.map_map]
    exact List.map_congr_left fun j _ => rho_pWF Q H w fl c0 x c ρs j
  have e4 : (((List.finRange N).map (pWF Q H w fl c0 x c ρs)).map fun o =>
        (o.map fun z => z.2.1, o)).map Prod.snd =
      (List.finRange N).map (pWF Q H w fl c0 x c ρs) := by
    rw [List.map_map]
    exact List.map_id _
  have e5 : (((List.finRange N).map (pWF Q H w fl c0 x c ρs)).findSome? fun o =>
        o.map fun z => z.2.1) =
      first ((List.finRange N).map (foF Q fl x ρs)) := by
    unfold first
    rw [List.findSome?_map, List.findSome?_map]
    exact congrArg (fun f => List.findSome? f (List.finRange N))
      (funext fun j => rho_pWF Q H w fl c0 x c ρs j)
  rw [e0, e5, each_initP, e2, e3, e4, lbind_assoc, Iv_bind]
  refine congrArg _ (funext fun b => ?_)
  show Iv N₀ δ
      ((skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first
        (first ((List.finRange N).map (foF Q fl x ρs)))
        (((List.finRange N).map (foF Q fl x ρs)).zip
          (reX (pOf ((List.finRange N).map (pWF Q H w fl c0 x c ρs))) b.1))
        ⟨[], [], none, [], []⟩).bind _) b.2 = _
  rw [zip_reX, skB_reZ, lbind_assoc, Iv_bind]
  rfl

/-- Under the hypotheses below: the statement with coins and verifier messages written out. -/
theorem core (hW : RoundsQueryLayout.OKG Q.loc.shape Q.ann wq.sh) (hG : GrFitP H wq) (hp : wp.OK)
    (hF : Q.ann.Fmt) (st : LS lam K L) :
    Iv N₀ δ (proveBL (L := L) sMT sFS t Q H wq wp embS embP xin embE depthReq trees w
          fl ((List.finRange N).map x)) st =
      (unif H.Coin0).bind fun c0 =>
        (unif (Fin N → H.Coin)).bind fun c => (unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
          Iv N₀ δ (proveBW sMT sFS t Q wq embS embP xin embE depthReq trees
            ((List.finRange N).map (pWF Q H w fl c0 x c fun j => ρ.slot j))) st := by
  rw [Iv_proveBL N₀ δ sFS sMT t Q H wq wp embS embP xin embE depthReq trees w fl x hp st]
  refine congrArg _ (funext fun c0 => congrArg _ (funext fun c => ?_))
  simp only [Iv_proveBW]
  rw [PMF.bind_comm (unif (BRho N Q.loc.shape Q.ann))]
  refine bind_congr_supp fun b hb => ?_
  obtain ⟨lb, bb⟩ := blocks_baseL N₀ δ sFS N st b hb
  have lfl : ((List.finRange N).map fun j : Fin N => fl j.val && (x j).isSome).length = N := by simp
  rw [sk_fibreB N₀ δ sMT t depthReq Q.loc.shape Q.ann wq.sh hW .first hF N _ lfl b.1 lb
        ⟨[], [], none, [], []⟩ b.2,
    ← map_slots_unif, PMF.bind_map, PMF.bind_bind]
  refine congrArg _ (funext fun ρ => ?_)
  have em : mask ((List.finRange N).map fun j : Fin N => fl j.val && (x j).isSome)
        ((List.finRange N).map fun j => ρ.slot j) =
      (List.finRange N).map (foF Q fl x fun j => ρ.slot j) :=
    zipWith_map_map _ _ _ _
  have hmem : ((List.finRange N).map fun j => ρ.slot j) ∈ (drawR Q.loc.shape Q.ann N).support := by
    rw [← map_slots_unif]
    exact (PMF.mem_support_map_iff _ _ _).2 ⟨ρ, PMF.mem_support_uniformOfFintype ρ, rfl⟩
  have hcoh := cohG_drawR Q.loc.shape Q.ann N
    ((List.finRange N).map fun j : Fin N => fl j.val && (x j).isSome) _ hmem
  rw [em] at hcoh
  show (Iv N₀ δ
      (skB sMT t depthReq Q.loc.shape Q.ann wq.sh .first
        (first (mask ((List.finRange N).map fun j : Fin N => fl j.val && (x j).isSome)
            ((List.finRange N).map fun j => ρ.slot j)))
        ((mask ((List.finRange N).map fun j : Fin N => fl j.val && (x j).isSome)
          ((List.finRange N).map fun j => ρ.slot j)).zip b.1)
        ⟨[], [], none, [], []⟩) b.2).bind _ = _
  rw [em]
  refine bind_congr_supp fun o ho => ?_
  have l2 : ((List.finRange N).map (foF Q fl x fun j => ρ.slot j)).length = b.1.length := by
    rw [List.length_map, List.length_finRange, lb]
  rw [finish_eq t Q H wq wp embS embP xin embE trees w fl c0 x c (fun j => ρ.slot j) hG o.1.2
      (List.finRange N) 0 (map_val_finRange N) b.1 o.1.1 bb
      (supp_skB N₀ δ sMT t depthReq Q.loc.shape Q.ann wq.sh hW .first hF _ _ b.1 l2 hcoh _ _ o ho)]

open Classical in
/-- what the reduction is told, from the session's return -/
theorem osOf_eq (ρ : BRho N Q.loc.shape Q.ann) :
    osOf x (ownSlots x fl) ((fun j : ownSlots x fl => ρ.slot j.1), fun j : ownSlots x fl =>
      match x j with
      | none => none
      | some xj =>
        if ρ.slot j.1 ∈ H.one.withheld w xj then none
        else some (Q.loc.dview xj (H.ext w) ((H.one.strat w xj (c0, c j)).run (ρ.slot j.1)).1))
      = (List.finRange N).map (pWF Q H w fl c0 x c fun j => ρ.slot j) := by
  unfold osOf
  refine List.map_congr_left fun j _ => ?_
  unfold pWF outp
  have hJ : j ∈ ownSlots x fl ↔ fl j.val = true ∧ (x j).isSome = true := by simp [ownSlots]
  cases hx : x j with
  | none =>
    have hn : j ∉ ownSlots x fl := fun h => by have := (hJ.1 h).2; rw [hx] at this; cases this
    rw [dif_neg hn]
    cases fl j.val <;> rfl
  | some xj =>
    cases hf : fl j.val with
    | false =>
      have hn : j ∉ ownSlots x fl := fun h => by have := (hJ.1 h).1; rw [hf] at this; cases this
      rw [dif_neg hn]
      rfl
    | true =>
      have hy : j ∈ ownSlots x fl := hJ.2 ⟨hf, by rw [hx]; rfl⟩
      rw [dif_pos hy]
      simp only [hx, Option.map_some, if_true]

end Slots

end Prove

end Compile.Batch.Fibre

namespace Compile.Batch
open Iop Rom Prob Compile.Batch.Fibre
open Compile.BatchLife (bsess)

/-- Under `RoundsQueryLayout.OKG`, `GrFitP`, `wp.OK`, `Fmt`: one execution is a session of the batch IOP, then
the reduction's subroutine (`Spec.eqProveB`). -/
theorem eqProveB : Spec.eqProveB := by
  intro I X lam K L sMT sFS t Y E Q Wt H wq wp embS embP xin embE depthReq trees N₀
    δ N w fl x st hW hG hp hF
  have h := core N₀ δ sFS sMT t Q H wq wp embS embP xin embE depthReq trees w fl x hW hG hp hF st
  refine Eq.trans h ?_
  unfold bsess BatchHonestProver.output
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, unif_prod, prod]
  have e1 : ∀ c0 : H.Coin0,
      ((unif (Fin N → H.Coin)).bind fun c => (unif (BRho N Q.loc.shape Q.ann)).bind fun ρ =>
        Iv N₀ δ (proveBW (L := L) sMT sFS t Q wq embS embP xin embE depthReq trees
          ((List.finRange N).map (pWF Q H w fl c0 x c fun j => ρ.slot j))) st)
      = (unif (BRho N Q.loc.shape Q.ann)).bind fun ρ => (unif (Fin N → H.Coin)).bind fun c =>
        Iv N₀ δ (proveBW sMT sFS t Q wq embS embP xin embE depthReq trees
              ((List.finRange N).map (pWF Q H w fl c0 x c fun j => ρ.slot j))) st :=
          fun c0 => PMF.bind_comm _ _ _
  simp only [e1]
  rw [PMF.bind_comm (unif H.Coin0)]
  refine congrArg _ (funext fun ρ => congrArg _ (funext fun c0 => congrArg _ (funext fun c => ?_)))
  exact congrArg
    (fun os => Iv N₀ δ (proveBW (L := L) sMT sFS t Q wq embS embP xin embE depthReq trees os) st)
    (osOf_eq Q H w fl c0 x c ρ).symm

end Compile.Batch
