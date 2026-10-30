-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackAtPub.lean: the port of the batched sumcheck's two form parts
(Johnson/Road/K4/StackPort.lean) with its premises on the verifier's side paid from the library's
public record of a layer sub-proof, Pub34 (Johnson/Road/Rows/LayerEnds34.lean), on true reads.

  `stack_port_pub34`: let X be a record Pub34, Wo a world in which every table of the reads holds
    what it says of the matrices Mm (ReadsTrue), and in which the record's two claims on the sides'
    hidden end values (sideClaims) are worth 0. Let P be parameters of the typed batched sumcheck,
    o one of its outputs and m typed entries, tied to the record: the table of scales, the sizes,
    the tables and the first layer are the record's; the cells P.rd m are the cells of Mm; the
    output's state holds what the verifier has heard (StackTies); the rounds are as many; the
    output's point reads as the record's challenges turned round; the hidden value under each of
    the two slots is what the output shows less its factor times the mask entry. Then the two forms
    rowF of the typed ledger stackCl (Cb/Pv/Lay/End/StackA.lean) are worth 0, at any late entries.
Limits. The ties are premises on letters: that the typed chain's value at a run of K4's text meets
them is not shown here. A record is a premise (Johnson/Road/K4/PubOfHearTied.lean makes one), and so
is ReadsTrue. The sumcheck's own first output row is not spoken of. An implication in one world: no
draw, nothing on soundness or on hiding.


-/
import Johnson.Road.K4.StackPort
import Johnson.Road.K4.StackPub34

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (World)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell)
open Cb.Pv.Lay.At (InnPar0 kS)
open Cb.Pv.Lay.End (rowF)
open Blocks (Form)

variable {K : Type} [Field K] [Fintype K]

/-- **The port at a record Pub34, on true reads.** -/
theorem stack_port_pub34 [scl : Scl] (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K)
    (hRd : X.ReadsTrue Wo Mm) (hS : ∀ f ∈ X.sideClaims, f.value X.ρ Wo = 0)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (P : InnPar0 K) [DecidableEq P.J]
    {J₂ : Type} [DecidableEq J₂] [Fintype J₂]
    (hrd : ∀ (a b : K) (m m' : P.J → K) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (hD : X.D = P.D) (htb : X.tb = P.tb) (hL0 : X.c.v.g * X.c.v.y.Lam = P.L0)
    (o : P.inn.toSum.T.par.Out) {m : P.J → K} (u : J₂ → K)
    (hcells : cellsOf P.D (cellsAt X.p.v.y Mm) = P.rd m)
    (T : StackTies P o.st X.ρ X.p.v.y X.p.shownT X.om (zOf X.ρ X.H.fo.zx X.H.fo.zy)
      (pt X.ρ X.c.rt))
    (hk : X.lam = kS P.D)
    (hpt : ∀ j, j < kS P.D → Blocks.nat (P.inn.Kp.outPt P.inn.Mk o) j =
      X.ρ.val (X.c.rs.getD (kS P.D - 1 - j) zeroE))
    (hA : Wo.slot X.sA0 = o.vals (.inl (.inl ())) -
      P.inn.Kp.outB P.inn.Mk o * m (P.cI (.inl (.inl ()))))
    (hB : Wo.slot X.sB0 = o.vals (.inr (.inl ())) -
      P.inn.Kp.outB P.inn.Mk o * m (P.cI (.inr (.inl ())))) :
    Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o (.inl (.inl ()))) = 0 ∧
      Form.val (Sum.elim m u) (rowF P (J₂ := J₂) o (.inr (.inl ()))) = 0 := by
  have S := sigFits_of_pub34 X Wo Mm hRd
  rw [← hscl, hD, htb, hL0, hcells] at S
  have hst := X.hst
  have hlam := X.hlam
  have hrs := X.hrs
  rw [hk] at hst hlam hrs
  exact stack_port hrd o u S T (ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS) X.hp X.hcl X.hom hlam hrs hst
    hpt hA hB (hS _ (by simp [Rows.Pub34.sideClaims])) (hS _ (by simp [Rows.Pub34.sideClaims]))

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stack_port_pub34
