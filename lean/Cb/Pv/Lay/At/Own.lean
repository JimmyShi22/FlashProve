-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Own.lean: all stages of the own rounds of a layers' sub-proof that is not the first
(LayV, LayVO: Cb/Pv/Lay/OwnAll.lean) at a value, with the law seam proved, the weights' stretch
still a letter. The law rides is trivial here: nothing is carried from the start to the weights.

Main names:
  `aH1`, `aH2`: the names of the never-sent vectors among the batched sumcheck's revealed maps;
    `ia_cases`: the first side has no other piece but the form part.
  `tailPt`: g coordinates of a point from a place on.
  `OwnPar`: over the letters of Cb/Pv/Lay/At/Mid.lean: the orders and masks of the two gated layers.
  `fp`: the letters of Cb/Pv/Lay/At/Foot.lean. `st5`, `st6`: the states of the two gated layers,
    read off the batched sumcheck's output.
  `ev_H1`, `ev_H2`: the gated layer's input claim, and the routed stretch's claims, give the batched
    sumcheck's rows on the never-sent vectors' end values.
  `WPart`: the weights' stretch as a letter with one law: its claims give the batched sumcheck's
    rows on the weight claims' end values (its value: Cb/Pv/Lay/At/OwnW.lean).
  `ow4`: what of the batched sumcheck's output claims is owed at the end: the first row and the rows
    on the two sides' form parts.
  `out_of`: the law seam, on an output.
  `layV`, `layVO`: the records. `layVO_pT`: what is claimed before the first round.
  `layVO_knowAt`: knowledge soundness of the chain at these letters.

Limits: that the programs' records are these is not said here. The value covers norms of five limbs,
the panel of the attention's output read from cells, and a plan with terms, routed experts and both
joins; no other. The identity that the selector's entries sum to 1 is no claim of this chain. "The
drawn coefficient of the terms' sumcheck is not 0" stands in the chain's last claim
(Cb/Pv/Lay/OwnAll.lean). The late panels, and what follows them, read the lookup's point off the
state of the terms' output; that this is the first statement's point at a statement that the chain
puts out is not shown here. The rows on the two gated layers' end values hold the extensions over
the padded features too: they are the programs' only if rd m c = 0 at every name c that is not
valid, or if the numbers of hidden units are powers of 2. That the choices of the coefficients left
out are lawful, so that the chain's verifier puts a statement out at all, is not shown here. Nothing
is said on an honest prover, on completeness or on hiding.


-/
import Cb.Pv.Lay.At.Mid
import Cb.Pv.Lay.At.Foot

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers Cb.Pv.Att
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Pan pans lF lFe zpos Hh1t hhU dJ)

noncomputable section

/-! ### Names and points -/

section Names
variable (D : Dim)

theorem memD : Pan.D ∈ pans D := by simp [pans]

theorem memDr (i : Fin D.ne) : Pan.Dr i ∈ pans D := by
  simp [pans, i.isLt]

/-- The vector of the gated products; of the routed gated products of layer 2 i + 1. -/
def aH1 : IA D := .inr ⟨⟨Pan.D, memD D⟩, ⟨0, Nat.one_pos⟩⟩
def aH2 (i : Fin D.ne) : IA D := .inr ⟨⟨Pan.Dr i, memDr D i⟩, ⟨0, Nat.one_pos⟩⟩

/-- The pieces of the first side. -/
theorem ia_cases (a : IA D) : a = .inl () ∨ a = aH1 D ∨ ∃ i, a = aH2 D i := by
  rcases a with _ | ⟨⟨p, hp⟩, c⟩
  · exact Or.inl rfl
  · have hc := c.isLt
    cases p with
    | D =>
      refine Or.inr (Or.inl ?_)
      have e : c = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.1 hc)
      rw [e]
      rfl
    | Dr l =>
      have hl : l < D.ne := by
        simpa [pans] using hp
      refine Or.inr (Or.inr ⟨⟨l, hl⟩, ?_⟩)
      have e : c = ⟨0, Nat.one_pos⟩ := Fin.ext (Nat.lt_one_iff.1 hc)
      rw [e]
      rfl
    | _ => exact absurd hc (Nat.not_lt_zero _)

theorem wid_D : Pan.D.wid D = D.lL + lF D := by
  show Nat.clog 2 (2 ^ D.lL) + Nat.clog 2 D.f = _
  rw [Nat.clog_pow 2 D.lL (by norm_num)]
  rfl

end Names

section Pts
variable {E : Type} [Field E]

/-- g coordinates of a point, from the place off on. -/
def tailPt (g off : ℕ) (ζ : ℕ → E) : Fin g → E := fun i => ζ (off + i)

theorem ext_tailPt (g off : ℕ) (v ζ : ℕ → E) :
    Blocks.ext g v (Blocks.nat (tailPt g off ζ)) = extAt g off v ζ := by
  unfold Blocks.ext extAt
  refine sum_congr rfl fun y _ => ?_
  rw [eqN_congr' (off := 0) (off' := off) (a := Blocks.nat (tailPt g off ζ)) (a' := ζ)
    (fun t ht => by
      rw [Nat.zero_add]
      unfold Blocks.nat tailPt
      rw [dif_pos ht]) y]

end Pts

/-! ### What stays free -/

/-- The letters of the two gated layers that stay free, beside At/Mid.lean's. -/
structure OwnPar (E : Type) [Field E] [Fintype E] [scl : Scl] (M X : Type)
    extends MidPar E M X where
  e5 : Fin (D.lL + lF D + D.lT) ≃ Fin (D.lL + lF D + D.lT)
  e6 : Fin (D.lL - 1 + (lFe D + D.lT)) ≃ Fin (D.lL - 1 + (lFe D + D.lT))
  w5 : PIdx (ldPartFmt E (D.lL + lF D + D.lT) (fun _ => 2) ++ [pDummy E 2]) → J
  c5 : Bool → J
  w6 : PIdx (ldPartFmt E (D.lL - 1 + (lFe D + D.lT)) (fun _ => 2) ++ [pDummy E 2]) → J
  c6 : Bool → J

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type}

namespace OwnPar
variable (P : OwnPar E M X)

/-- The batched sumcheck; its outputs. -/
abbrev In : InnL E := P.ip.inn
abbrev O4 : Type := P.In.toSum.T.par.Out

/-- The letters of the two gated layers. -/
@[reducible] def fp : FootPar0 E where
  D := P.D
  J := P.J
  rd := P.rd
  e5 := P.e5
  e6 := P.e6
  nH1 := P.cI (.inl (aH1 P.D))
  nH2 := fun i => P.cI (.inl (aH2 P.D i))
  w5 := P.w5
  c5 := P.c5
  w6 := P.w6
  c6 := P.c6

/-- The batched sumcheck's out point, and the further variable's challenge. -/
def zeta (o : P.O4) : ℕ → E := Blocks.nat (P.In.Kp.outPt P.In.Mk o)
def be4 (o : P.O4) : E := P.In.Kp.outB P.In.Mk o

/-- The states of the two gated layers, read off the batched sumcheck's output. -/
def st5 (o : P.O4) : St5 E P.D where
  pt := tailPt (P.D.lL + lF P.D) (kS P.D - (P.D.lL + lF P.D)) (P.zeta o)
  zt := fun j => zpos P.D o.st.z j
  be := P.be4 o
  v := o.vals (.inl (aH1 P.D))

def st6 (o : P.O4) : St6 E P.D where
  pt := tailPt (lFe P.D) (kS P.D - lFe P.D) (P.zeta o)
  rt := P.tp.tm.Kp.outPt P.tp.tm.Mk o.st.o3
  be := P.be4 o
  v := fun i => o.vals (.inl (aH2 P.D i))

/-- **The gated layer's input claim gives the row on the end value of the gated products.** -/
theorem ev_H1 (o : P.O4) (m : P.J → E) (h : P.fp.gp.Sg (P.st5 o) m) :
    P.In.toSum.T.par.EHolds o m (.inl (aH1 P.D)) := by
  rw [P.In.ev_iff]
  have h1 := (P.fp.gp_sg (P.st5 o) m).1 h
  have e1 : Blocks.ext (P.D.lL + lF P.D) (Hh1t P.D (P.rd m) (Blocks.nat (P.st5 o).zt))
      (Blocks.nat (P.st5 o).pt) =
      extAt (Pan.D.wid P.D) (kS P.D - Pan.D.wid P.D) (Hh1t P.D (P.rd m) (zpos P.D o.st.z))
        (P.zeta o) := by
    rw [wid_D]
    show Blocks.ext _ _ (Blocks.nat (tailPt _ _ (P.zeta o))) = _
    rw [ext_tailPt]
    refine extAt_congr (fun Y _ => ?_) _
    unfold Inst.Model.FFSeg.Hh1t Inst.Model.FFSeg.hhU
    refine ext_pt (fun j hj => ?_) _
    unfold Blocks.nat
    rw [dif_pos hj]
    rfl
  rw [e1] at h1
  exact h1

/-- **The routed stretch's claims give the rows on the end values of the routed gated products.** -/
theorem ev_H2 (o : P.O4) (m : P.J → E) (i : Fin P.D.ne)
    (h : P.fp.rt.val (P.st6 o) m i = P.fp.rt.sh i (P.st6 o)) :
    P.In.toSum.T.par.EHolds o m (.inl (aH2 P.D i)) := by
  rw [P.In.ev_iff]
  rw [P.fp.rt_val] at h
  have e1 : Blocks.ext (lFe P.D)
      (fun j => hhU P.D (P.rd m) (2 * i.val + 1) (P.D.fe + j) (Blocks.nat (P.st6 o).rt))
      (Blocks.nat (P.st6 o).pt) =
      extAt (lFe P.D) (kS P.D - lFe P.D)
        (fun j => hhU P.D (P.rd m) (2 * i.val + 1) (P.D.fe + j) (P.ip.rt o.st)) (P.zeta o) := by
    show Blocks.ext _ _ (Blocks.nat (tailPt _ _ (P.zeta o))) = _
    rw [ext_tailPt]
    rfl
  rw [e1] at h
  exact h

/-- The weights' stretch, as a letter with one law. -/
structure WPart where
  Wt : WeightsL E
  st7 : P.O4 → Wt.St
  rd7 : M → Wt.J → E
  /-- its claims give the rows on the weight claims' end values -/
  law : ∀ o m, (∀ a, Wt.val (st7 o) (rd7 m) a = Wt.sh a (st7 o)) →
    ∀ i, P.In.toSum.T.par.EHolds o (P.msg m) (.inr (.inr i))

/-- What of the batched sumcheck's output claims is owed at the end. -/
def ow4 (o : P.O4) (m : M) : Prop :=
  P.In.toSum.T.par.UHolds o (P.msg m) ∧ P.In.toSum.T.par.EHolds o (P.msg m) (.inl (.inl ())) ∧
    P.In.toSum.T.par.EHolds o (P.msg m) (.inr (.inl ()))

/-- **The law seam, on an output.** -/
theorem out_of (W : P.WPart) (o : P.O4) (m : M) (h0 : P.ow4 o m)
    (h5 : P.fp.gp.Sg (P.st5 o) (P.msg m))
    (h6 : ∀ i, P.fp.rt.val (P.st6 o) (P.msg m) i = P.fp.rt.sh i (P.st6 o))
    (h7 : ∀ a, W.Wt.val (W.st7 o) (W.rd7 m) a = W.Wt.sh a (W.st7 o)) :
    P.In.toSum.T.par.OutHolds o (P.msg m) := by
  refine ⟨h0.1, fun a => ?_⟩
  rcases a with a | b
  · rcases ia_cases P.D a with rfl | rfl | ⟨i, rfl⟩
    · exact h0.2.1
    · exact P.ev_H1 o (P.msg m) h5
    · exact P.ev_H2 o (P.msg m) i (h6 i)
  · rcases b with _ | i
    · exact h0.2.2
    · exact W.law o m h7 i

/-! ### A sub-proof that is not the first -/

/-- The statements behind the token point. -/
abbrev XT : Type := X × (Fin P.D.lT → E)

/-- The stages up to the batched sumcheck. -/
abbrev midL : Mid E M P.XT := P.mid (X' := P.XT) Prod.fst Prod.snd fun _ _ => True

/-- All stages behind the token point. -/
def layV (W : P.WPart) : LayV E M P.XT where
  toMid := P.midL
  Ft :=
    { Gp := P.fp.gp
      st5 := fun b => P.st5 b.2
      rd5 := P.msg
      Rt := P.fp.rt
      st6 := fun b => P.st6 b.2
      rd6 := P.msg
      Wt := W.Wt
      st7 := fun b => W.st7 b.2
      rd7 := W.rd7 }
  ow4 := fun b m => P.ow4 b.2 m
  seam := fun b m h0 h5 h6 h7 => P.out_of W b.2 m h0 h5 h6 h7
  rides := fun _ _ _ => trivial

/-- The own rounds of a sub-proof that is not the first. -/
def layVO (W : P.WPart) : LayVO E M X where
  gT := P.D.lT
  K := ℕ × Fin P.D.nNu
  d := fun _ m k => dJ P.D (P.rd (P.msg m)) k.1 k.2
  Q := fun x m => P.jg x (P.tS x m) m = 0
  V := P.layV W
  atPt := fun x p m h =>
    ⟨(P.fore_atPt (X' := P.XT) Prod.fst Prod.snd (fun _ _ => True) (x, p) m h).1,
      (P.fore_atPt (X' := P.XT) Prod.fst Prod.snd (fun _ _ => True) (x, p) m h).2.1⟩

/-- What is claimed before the first round: all 17 identities of every norm at every position, and
the lookup's join at the true sum of the terms. -/
theorem layVO_pT (W : P.WPart) (x : X) (m : M) :
    (P.layVO W).pT x m ↔
      (∀ k : ℕ × Fin P.D.nNu, ∀ Y < 2 ^ P.D.lT, dJ P.D (P.rd (P.msg m)) k.1 k.2 Y = 0) ∧
        P.jg x (P.tS x m) m = 0 := Iff.rfl

/-- **Knowledge soundness of the own rounds at the value.** -/
theorem layVO_knowAt (W : P.WPart) {Kc X0 Wp : Type} (Ex : ExtSpec)
    (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0) (Dn : X → M → Prop) :
    KnowAt ((P.layVO W).toOwn.ch.R Ex) (jt A0 pr fun x m => Dn x m ∧ (P.layVO W).pT x m)
      (jt A0 (fun e => pr ((P.layVO W).toOwn.ch.back e)) ((P.layVO W).toOwn.ch.Last Dn))
      (fun _ _ _ wp => wp) ((P.layVO W).toOwn.ch.eps Ex) :=
  (P.layVO W).knowAt Ex A0 pr Dn

end OwnPar
end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.OwnPar.ev_H1
#print axioms Cb.Pv.Lay.At.OwnPar.ev_H2
#print axioms Cb.Pv.Lay.At.OwnPar.out_of
#print axioms Cb.Pv.Lay.At.OwnPar.layVO_knowAt
