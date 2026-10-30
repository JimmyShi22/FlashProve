-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeepsAny.lean: K05_keepsW_all (Att/K05KeepsAll.lean) at any base (BaseIs,
Att/K05RowAny.lean: kap = 4; the sizes are
the shape's; the calls are callsOf fs; two plane messages; the cells are read at given places), with
the join's tie as a letter
(Att/K05GatheredJ.lean). That the tables are true stays a premise (AttAt and CellsTie inside
GatheredAllJ), in the form in which the
smallness test's kind can give it.

Main names:
  `BillsAllJ`: what is asked of the relation R' behind the kind, at the statements with "on": a
    later ledger and entries of the vector
    of tables at which GatheredAllJ holds.
  `K05_keepsW_all_any`: KeepsW on on' (Todo at the world's part) R' (bearErr …).

Premises: Attention.plan's return; BaseIs; p.own = A.own; planOkAll = true; hscl; hJn (Jn gives hjv
at meantQ … Q0). At each statement
with "on": Room at the ledger in front; K3Pts. The seam; the written rounds are Plain with the
kind's entries; BillsAllJ; on' holds for
certain of what the piece puts out; the pin. None is shown in this file or in what it imports. That
GatheredAllJ is ever met at a view
that the verifier accepts is not shown. planOkAll is evaluated in no file of this tree.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowAny
import Johnson.Desc.First.Att.K05GatheredJ

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

/-- What is asked of the relation behind the kind. -/
def BillsAllJ {St Aa Bb W : Type} (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ)
    (S : Attention.Shape) (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) {J₂ : Type} [Fintype J₂]
    [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (seat : Seat St) (x : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X) (zx : Aa → Array E)
    (zk : Aa → Array (Array E)) (on : Aa → Prop) (part : W → Mg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), on a → R' b w → ∀ (G : Fork) (h : Heard) (L : Lists),
    seat.lay (recA a) h G = some (recB b) → Said x h G L →
    ∃ (G' : Fork) (entry : ℕ → ℕ → ℕ → Cb.Gl.E), Stays G G' ∧ Sized G' ∧ G'.ns = G.ns ∧
      GatheredAllJ P0 Λ ns N rows S lid cf fs Ly Jn (zx a) (zk a) entry G' h L (x0 a) (part w)

open Classical in
/-- **The kind's law in the form for the table of joints, at any base, the join's tie a letter**:
that the tables are true stays
a premise, in the form in which the smallness test's kind can give it. -/
theorem K05_keepsW_all_any {St Aa Bb W : Type} {P0 : OwnPar Cb.Gl.E M0 X} {cellJ0 : AttSeg.Raw → P0.J}
    {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg} {A : Attention.Plan}
    (hA : Attention.plan settings i cf = Except.ok A) (B : BaseIs P0 A.S A.fs cellJ0)
    (hok : planOkAll cf A.S A.fs = true) (Λ0 : Lin P0 Mg) (seat : Seat St) (p : Par) (hp : p.own = A.own) (ns0 k0 : ℕ)
    (Q0 : JoinLay (closedOf P0 Λ0 ns0 (numsPlan p.own k0))) (j0 : NameJ P0.D A.S.ls A.S.cf.lmS)
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    (hJn : ∀ x0 m gL W, Jn x0 gL W m → ∀ kv,
      Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl W) =
        Cb.Pv.Att.End.joinVal ((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).q x0) kv (((meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0).ce x0).val ((closedOf P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).msg m)))
    (Ex : ExtSpec) (ds : List RDT) (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (kr : ℕ) (hroom : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Room F ns0 k0 kr)
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
    (hb : BillsAllJ P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs (endLay P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) cellJ0 A.S.ls A.S.cf.lmS j0) Jn
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
  obtain ⟨_, G, h, L, _, q2, q3, q4⟩ := hq
  obtain ⟨G', entry, g1, g2, g3, g4⟩ := hb a b w ha hR G h L q2 q3
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
    (gatheredAll_of_J P0 (meantLin P0 Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) A.own.rows A.S settings.lidb cf A.fs _ (meantQ P0 Λ0 ns0 (numsPlan p.own k0) Q0) Jn (hJn (x0 a) (part w)) g4))

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_all_any
