-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05KeepsTop.lean: K05_row_plan (Att/K05RowBase.lean) in the form for the
table of joints
(Johnson/Desc/Plain/Pinned.lean: keepsW_of_pinned).

Main names:
  `BillsTop`: what is asked of the relation R' behind the kind: R' b w gives, for every (h, G) that
    the seat has laid into b with
    Said, a later ledger (Stays, Sized, as many slots) and entries of the vector of tables at which
      GatheredTop holds, at the
    world's part "part w".
  `K05_keepsW_plan`: KeepsW on on' (Todo at the world's part) R' (bearErr …).

Premises more than K05_row_plan's: BillsTop; on' holds for certain of what the piece puts out; the
pin (R' b w fixes part w as
mOf a). None is shown in this file or in what it imports.
No soundness of the protocol is claimed: the seam and the premises named are not shown.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05RowBase
import Johnson.Desc.Plain.Pinned

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (recOf)
open K5Law (PlanLaw)
open Cb.Pv.Att.End (EndLay JoinLay NameJ)
open OnBytes.Slice OnBytes.Flat OnBytes.Maker Run Fo.Peel
open Cb.Pv.Tail (Size JCell)

variable {M0 Mg X : Type}

/-- What is asked of the relation behind the kind. -/
def BillsTop {St Aa Bb W : Type} (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ)
    (S : Attention.Shape) {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂)
    (Q : JoinLay (closedOf P0 Λ ns N)) (seat : Seat St) (x : Params.AttentionRounds) (recA : Aa → St) (recB : Bb → St)
    (x0 : Aa → X) (zk : Aa → Array (Array E)) (part : W → Mg) (R' : Bb → W → Prop) : Prop :=
  ∀ (a : Aa) (b : Bb) (w : W), R' b w → ∀ (G : Fork) (h : Heard) (L : Lists), seat.lay (recA a) h G = some (recB b) →
    Said x h G L → ∃ (G' : Fork) (entry : ℕ → ℕ → ℕ → Cb.Gl.E), Stays G G' ∧ Sized G' ∧ G'.ns = G.ns ∧
      GatheredTop P0 Λ ns N rows S Ly Q (zk a) entry G' h L (x0 a) (part w)

open Classical in
/-- **The kind's law in the form for the table of joints.** -/
theorem K05_keepsW_plan {St Aa Bb W : Type} {s : Size} {S : Attention.Shape} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (pl : ℕ → ℕ → ℕ → JCell s) (zOf : X → ℕ → Cb.Gl.E)
    (Λ0 : Lin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Mg) (seat : Seat St) (p : Par) (ns0 k0 : ℕ) (Q0 : JoinLay (closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0)))
    (j0 : NameJ (OnBytes.Road.L5.dimOf S) S.ls S.cf.lmS) (rows : ℕ) (hU : unitsOk S fs = true)
    (hrec : p.own = recOf (closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)) rows) (Ex : ExtSpec) (ds : List RDT)
    (out : Aa → Tr (uLT (ckP .two) ds) → Option Bb) (recA : Aa → St) (recB : Bb → St) (x0 : Aa → X)
    (yOf : Aa → Ex.Str) (zx zy : Aa → Array E) (zk : Aa → Array (Array E)) (on : Aa → Prop)
    (hon : ∀ a, on a → ∀ F, seat.ledger (recA a) = some F → Sized F ∧ F.ns = ns0 ∧ F.next = k0)
    (hk3 : ∀ a, on a → K3Pts fs (zx a) (zy a) (zk a) (zOf (x0 a)))
    (hyes : ∀ a τ b, on a → out a τ = some b →
      decide seat p (recA a) ((rvT (ckP .two) ds τ).map noDigest) = .ok (recB b) ∧
        roundsFit (rounds p) ((rvT (ckP .two) ds τ).map noDigest) = true ∧
        ∀ r ∈ (rvT (ckP .two) ds τ).map noDigest, ∀ x ∈ r.drawn.elems, Fmt.Fld.two.okE x = true)
    (hpass : ∀ a τ b, out a τ = some b → passT (ckP .two) ds (rhoT (ckP .two) ds τ) = true)
    (hd : ∀ d ∈ ds, Plain (toRD d)) (he : ds.map (·.entry) = (rounds p).map (·.entry))
    (hscl : (Q0.scl.κ 0).sh = S.cf.sh.getD 0 0)
    (part : W → Mg) (mOf : Aa → Mg) (on' : Bb → Prop) (R' : Bb → W → Prop)
    (hon' : ∀ a τ b, on a → out a τ = some b → on' b)
    (hb : BillsTop (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) rows S
      (endLay (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0) (cellAt S pl) S.ls S.cf.lmS j0) (meantQ (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0)
      seat p.own recA recB x0 zk part R')
    (pin : ∀ a τ b w, on a → out a τ = some b → R' b w → part w = mOf a) :
    (⟨uLT (ckP .two) ds, out⟩ : Reduction Aa Bb).KeepsW on on'
      (fun a w => ((closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.Todo (x0 a) (part w)) R'
      (bearErr ds _ (((closedOf (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) (meantLin (baseOf (K := Cb.Gl.E) (X := X) S pl (OnBytes.Road.L5.callsOf fs) 2 zOf) Λ0 ns0 (numsPlan p.own k0) Q0) ns0 (numsPlan p.own k0)).own (theMeans Cb.Gl.E _ _ _)).ch.eps Ex)) := by
  refine Reduction.keepsW_of_pinned part mOf (fun m => ?_) pin
  refine Reduction.Leads.conseq (K05_row_plan hid PL pl zOf Λ0 seat p ns0 k0 Q0 j0 rows hU hrec Ex ds out recA recB x0 yOf
    (fun _ => m) zx zy zk on hon hk3 hyes hpass hd he hscl) (fun _ h => h)
    fun a τ b ha hout hq => ⟨hon' a τ b ha hout, fun w hw hR => ?_⟩
  obtain ⟨_, G, h, L, _, q2, q3, q4⟩ := hq
  obtain ⟨G', entry, g1, g2, g3, g4⟩ := hb a b w hR G h L q2 q3
  subst hw
  exact q4 G' entry g1 g2 g3 g4

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.K05_keepsW_plan
