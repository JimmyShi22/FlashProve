-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeepsLater.lean: `K05_keepsW_all_any`
(Johnson/Desc/First/Att/K05KeepsAny.lean: the law of the kind K5 in the form for the table of
joints, at any base, the join's tie a letter) with more in the hand of whoever shows what is asked
of the relation behind the kind.

Why. `BillsAllJ` asks, of the relation behind the kind, a later ledger G' and `GatheredAllJ` there,
from "the seat has laid (h, G)" and `Said` alone. It does not say how G stands to the ledger F at
the entry of the kind. But the join's tie `K3Join` is drawn from what the lookup left in F:
`k3join_of_left` (Johnson/Desc/First/Att/K05Left.lean) asks `Stays` F G' and G'.ns = F.ns. At the
hearing's own return `hear_said` (Johnson/Desc/First/Att/K5SaidAll.lean) proves `Stays` F G and
`room_behind` (Johnson/Desc/First/Att/K05Room.lean) gives G.ns = F.ns; `RowTopSays`
(Johnson/Desc/First/Att/K05RowTop.lean) holds neither.

Definitions, statements and proofs.
Main names:
  `LaysBack seat`: the seat reads back, as the ledger, the ledger that it has laid.
  `gatheredAllJ_mono`: `GatheredAllJ` is monotone in the tie, at the one world at which it asks it.
  `BillsLaterJ`: `BillsAllJ` with three premises more: seat.ledger (recA a) = some F, `Stays` F G
    and G.ns = F.ns. The tie may depend on the statement a.
  `K05_keepsW_later_any`: the law under `BillsLaterJ`, `LaysBack` and `Room` with slotsOf (script
    p.own) + k free slots. The premise on the tie is asked at the statements with "on", at a ledger
    G' in which what lay in the ledger at the entry stays, with its number of slots, in the world of
    G'.
The proof follows that of `K05_keepsW_all_any`; new are the lines that draw `Stays` F G and G.ns =
F.ns from a yes of `decide` (`decide_lays`, Johnson/Desc/First/Att/K5Shape.lean).
Limits: those of Johnson/Desc/First/Att/K05KeepsAny.lean, and `LaysBack`. No premise is shown in
this file or in what it imports, and no member is shown. The statement holds for nothing where "on"
holds of no statement, where R' holds of no witness or where out returns nothing. The letter yOf
stands in no premise and not in the conclusion. No soundness of the protocol is claimed. Nothing on
completeness or hiding.

-/
import Johnson.Desc.First.Att.K05KeepsAny
import Johnson.Desc.First.Att.K05Room

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (recOf)
open K5Law (PlanLaw)
open Cb.Pv.Att.End (EndLay JoinLay NameJ)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel

variable {M0 Mg X : Type}

/-- The seat reads back, as the ledger, the ledger that it has laid. -/
def LaysBack {St : Type} (seat : Seat St) : Prop :=
  ∀ (s : St) (h : Heard) (G : Fork) (s' : St), seat.lay s h G = some s' → seat.ledger s' = some G

/-- GatheredAllJ is monotone in the tie, at the one world at which it asks it. -/
theorem gatheredAllJ_mono (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) {J₂ : Type} [Fintype J₂] [DecidableEq J₂]
    (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Jn Jn' : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    {zx : Array E} {zk : Array (Array E)} {entry : ℕ → ℕ → ℕ → Cb.Gl.E} {G : Fork} {h : Heard} {L : Lists} {x0 : X} {m : Mg}
    (hJ : ∀ gL, Jn x0 gL (G.worldOf Reading.gl (Λ.maskOf m) entry) m → Jn' x0 gL (G.worldOf Reading.gl (Λ.maskOf m) entry) m)
    (hga : GatheredAllJ P0 Λ ns N rows S lid cf fs Ly Jn zx zk entry G h L x0 m) :
    GatheredAllJ P0 Λ ns N rows S lid cf fs Ly Jn' zx zk entry G h L x0 m := by
  intro nz du dt d1 d2 d3 d4
  obtain ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, M, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hk, hx, hv, hJ0,
    rest⟩ := hga nz du dt d1 d2 d3 d4
  exact ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, M, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hk, hx, hv,
    hJ gL hJ0, rest⟩

/-- What is asked of the relation behind the kind, the payer holding how the ledger behind the
hearing stands to the ledger at the kind's entry. The tie may depend on the statement. -/
def BillsLaterJ {St Aa Bb W : Type} (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ)
    (S : Attention.Shape) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) {J₂ : Type} [Fintype J₂]
    [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Jn : Aa → X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (seat : Seat St) (x : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (zx : Aa → Array E)
    (zk : Aa → Array (Array E)) (on : Aa → Prop) (part : W → Mg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), on a → R' b w → ∀ (F G : Fork) (h : Heard) (L : Lists),
    seat.ledger (recA a) = some F → seat.lay (recA a) h G = some (recB b) → Said x h G L →
    Stays F G → G.ns = F.ns →
    ∃ (G' : Fork) (entry : ℕ → ℕ → ℕ → Cb.Gl.E), Stays G G' ∧ Sized G' ∧ G'.ns = G.ns ∧
      GatheredAllJ P0 Λ ns N rows S lid cf fs Ly (Jn a) (zx a) (zk a) entry G' h L (x0 a) (part w)

open Classical in
/-- **The kind's law in the form for the table of joints, at any base, the payer of the bill holding
the ledger at the kind's entry.** -/
theorem K05_keepsW_later_any {St Aa Bb W : Type} {P0 : OwnPar Cb.Gl.E M0 X} {cellJ0 : AttSeg.Raw → P0.J}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (B : BaseIs P0 A.S A.fs cellJ0)
    (hok : planOkAll cf A.S A.fs = true) (Λ0 : Lin P0 Mg) (seat : Seat St) (hlb : LaysBack seat) (p : Par)
    (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D A.S.ls A.S.cf.lmS)
    (Jn : Aa → X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hJn : ∀ a, on a → ∀ (F G' : Fork) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (m : Mg) (gL : Forest.Heard),
      seat.ledger (recA a) = some F → Stays F G' → G'.ns = F.ns →
      Jn a (x0 a) gL (G'.worldOf Reading.gl (Λ0.maskOf m) entry) m → ∀ kv,
      Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl (G'.worldOf Reading.gl (Λ0.maskOf m) entry)) =
        Cb.Pv.Att.End.joinVal ((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).q (x0 a)) kv (((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).ce (x0 a)).val ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).msg m)))
    (k : ℕ) (hroom : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Room F ns0 k0 (slotsOf (script p.own) + k))
    (hk3 : ∀ a, on a → K3Pts A.fs (zx a) (zy a) (zk a) (P0.zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = A.S.cf.sh.getD 0 0)
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsLaterJ P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 A.S.ls A.S.cf.lmS j0) Jn
      seat p.own recA recB x0 zx zk on part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  have hid := (OnBytes.Road.L5.plan_shape hA).1
  have PA := plan_all hid hok
  have PL := PA.law
  obtain ⟨_, _, u1, u2, wl, _, _, U⟩ := PA.units
  have h01 := OnBytes.Road.L5.callsFit_a01 PL.fit
  have e := (K5Law.place_scores PL.place).symm.trans U.sco
  simp only [List.cons.injEq, and_true] at e
  have hrec : p.own = recOf (closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)) A.own.rows :=
    hp.trans (rec_of_plan hA PL.place (OnBytes.Road.Rows.norm_of_hid hid)
      (Nat.le_of_succ_le (OnBytes.Road.Rows.sizes_of_hid hid).lnT) U _ B.D B.npl B.kap)
  refine Reduction.keepsW_of_pinned part mOf (fun m => ?_) pin
  refine Reduction.Leads.conseq (K05_row_any_plan B hid hok Λ0 seat p ns0 k0 Q0 j0 A.own.rows hrec Ex ds out recA recB x0 yOf
    (fun _ => m) zx zy zk on
    (fun a ha F hF => ⟨(hroom a ha F hF).sized, (hroom a ha F hF).ns, (hroom a ha F hF).next⟩) hk3 hyes hpass hd he hscl)
    (fun _ h => h) fun a τ b ha hout hq => ⟨hon' a τ b ha hout, fun w hw hR => ?_⟩
  obtain ⟨F, G, h, L, q1, q2, q3, q4⟩ := hq
  -- the hearing's own return: how G stands to the ledger at the entry
  obtain ⟨_, F1, h1, G1, l1, hh, l2⟩ := (decide_lays seat p _ _ _).1 (hyes a τ b ha hout).1
  have eF : F = F1 := Option.some.inj (q1.symm.trans l1)
  have eG : G = G1 := Option.some.inj ((hlb _ _ _ _ q2).symm.trans (hlb _ _ _ _ l2))
  subst eF eG
  have RF := hroom a ha F q1
  obtain ⟨_, _, _, _, _, _, st⟩ := hear_said hh RF.sized
  have hns : G.ns = F.ns := (room_behind hh RF).ns.trans RF.ns.symm
  obtain ⟨G', entry, g1, g2, g3, g4⟩ := hb a b w ha hR F G h L q1 q2 q3 st hns
  subst hw
  refine q4 G' entry g1 g2 g3 (gatheredTop_of_all P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) B.kap A.own.rows hid PL B.D B.C (qW := 2) (qM := 1)
    (qD := 1)
    (fun w' hw' => by
      rw [U.sWl] at hw'
      rw [← Option.some.inj hw', B.D, B.C]
      exact U.w3)
    (by rw [e.1, B.D, B.C]; exact unitIs_m1 h01 U.m2) (by rw [e.2, B.D, B.C]; exact unitIs_d1 h01 U.d2) rfl rfl
    (fun j => by
      have := (Cb.Pv.Att.End.mem_allNames P0.D A.S.ls A.S.cf.lmS).1 j.2
      rw [B.D] at this
      exact this) (hk3 a ha) (said_congr hrec (q3.mono g1))
    (gatheredAll_of_J P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs _ (meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0)
      (fun x0' gL W' m' => Jn a x0' gL W' m' ∧ W' = G'.worldOf Reading.gl (Λ0.maskOf (part w)) entry ∧ x0' = x0 a ∧ m' = part w)
      (fun gL W' hJ kv => by
        obtain ⟨j1, rfl, _, _⟩ := hJ
        exact hJn a ha F G' entry (part w) gL q1 (st.trans g1) (g3.trans hns) j1 kv)
      (gatheredAllJ_mono P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs _ (Jn a) _
        (fun gL hJ => ⟨hJ, rfl, rfl, rfl⟩) g4)))

end VerifiableInference.Desc.First.Att.P
