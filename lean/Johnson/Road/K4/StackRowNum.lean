-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowNum.lean: (D4) of the fourth stage at a hearing (d4_of_led4,
Johnson/Road/K4/StackRow.lean) with its premises on numbers paid: the numbering of the batched
sumcheck's end values is num4 (Johnson/Road/K4/Num4.lean) over the numbering numK of the weight
panels' pieces (Johnson/Road/K4/NumPieces.lean), and the verifier numbers its weight claims so
(placed_v0, Johnson/Road/K4/WalkV0.lean).

Main names:
  `panA_virt`: the number of the value of a never-sent vector is 1 plus the vector's number.
  `ncl_of_led`: the plan's number of the panels' weight claims is the number of the pieces: the text
    tests its counter against the plan (hearStack_public, OnBytes/Desc/First/K4/StackPublic.lean).
  `d4_of_led_num`: (D4) at a hearing.
Limits. PREMISES: those of d4_of_led4 but for its four clauses on the fourth stage's numbering,
v0Of, F0 and hlt; in their place: that the fourth stage's numbering is num4 at numK, and that the
plan has at least as many weight claims as the panels have pieces (hNCL: ncl_of_led pays it). One
direction: from returns. Nothing on soundness.


-/
import Johnson.Road.K4.StackRow
import Johnson.Road.K4.Num4
import Johnson.Road.K4.WalkV0
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc
open OnBytes.Model (World Fork Psc Level Tsc WsShape WsClaim)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard ClaimEnv nEndT callsTS)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR)
open OnBytes.Desc.First.K4 (hearStack_public)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Pan pans)

/-- The number of the value of a never-sent vector, by its panel, is 1 plus the vector's number. -/
theorem panA_virt {D : Dim} (i : Σ p : {p : Pan // p ∈ pans D}, Fin (cntA p.1)) :
    panA i.1.1 = 1 + (virtOf i.1.1).getD 0 := by
  obtain ⟨⟨p, hp⟩, c⟩ := i
  cases p with
  | D => rfl
  | Dr l =>
    show 2 + l = 1 + (1 + l)
    omega
  | _ => exact c.elim0

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **The plan's number of the panels' weight claims is the number of the pieces.** -/
theorem ncl_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    {shownT : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    {D : Dim} {z : ℕ → Cb.Gl.E} {Wo : World Cb.Gl.E} {c : ClaimEnv}
    {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {lk L0 : ℕ}
    {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E} {low zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (S : SigFits gl Wo (envOfHear P o shownT) c h pc s D lk L0 cc t low z zh ζ tb)
    (hTS : callsTS P = some [0, 1, 2, 5]) {cl : List WsClaim}
    (hcl : c.weightClaims [0, 1, 2, 5] = some cl) : nWK D = hp.NCL - 0 := by
  obtain ⟨tT', shownT', TS, pn', _, _, _, _, _, _, _, _, -, q1, q2, q3, q4, -, q6, -⟩ :=
    hearStack_public Ld.c4
  have e0 := Option.some.inj (q1.symm.trans Ld.kTT)
  have e1 := congrArg Tsc.sEnd e0
  have eT : tT'.sEnd = tT.sEnd := e1
  rw [eT] at q2
  obtain rfl : shownT = shownT' := Option.some.inj (hsh.symm.trans q2)
  obtain rfl : [0, 1, 2, 5] = TS := Option.some.inj (hTS.symm.trans q3)
  exact (placed_v0 q4 (placed_fields S rfl q4 hcl)).2.symm.trans (beq_iff_eq.mp q6)

variable {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF Pf) R)

/-- **(D4) of the fourth stage at a hearing**, with the numbers paid. -/
theorem d4_of_led_num (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (hc : (k4Tail W' P hp t0 nz a).d4.Claim ((k4Tail W' P hp t0 nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 p3) (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4)
    (k3 : (tailF Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q)
    (n4 : ∀ q : IA Pf.D ⊕ IB Pf.D, W'.w4.num q = num4 Pf.D (numK Pf.D) q)
    (hNCL : nWK Pf.D ≤ hp.NCL - 0)
    (hyv : o.v.y = P.y) (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    {shownT : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    {z : ℕ → Cb.Gl.E} (hz0 : ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st.z = z)
    (hz3 : Pf.ip.zP ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2.st .QK = z)
    {Wo : World Cb.Gl.E} {c : ClaimEnv} {h : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    {s : WsShape} {lk L0 : ℕ} {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E}
    {low zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (S : SigFits gl Wo (envOfHear P o shownT) c h pc s Pf.D lk L0 cc t low z zh ζ tb)
    (hTS : callsTS P = some [0, 1, 2, 5]) {cl : List WsClaim}
    (hcl : c.weightClaims [0, 1, 2, 5] = some cl) (hrs : kS Pf.D ≤ o.K.rs.size) :
    Pf.ip.inn.Sm.pol a.st4
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2)
        (k4Tail W' P hp t0 nz a).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs) :=
  d4_of_led4 Pf W' Ld nz a x hc O3 O4 k3 k4 n3 (v0Of Pf.D) (n4 _)
    (fun i => (n4 _).trans (panA_virt i))
    ((n4 _).trans (by
      show 2 + Pf.D.ne = 1 + (1 + P.y.LamM)
      rw [hLM]
      omega))
    (fun p i => (n4 _).trans (by
      show 2 + (1 + Pf.D.ne) + ((numK Pf.D).symm ⟨p, i⟩).val = _
      rw [numK_val, hLM]))
    (fun p i => Nat.lt_of_lt_of_le (offIn_lt (cntB Pf.D) (pans Pf.D) p.1 i p.2 i.2) hNCL)
    hyv hNN hLM hNE hEnd hsh hz0 hz3 S hTS hcl hrs
    (fun pn' hp' => (placed_v0 hp' (placed_fields S rfl hp' hcl)).1)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.panA_virt
#print axioms OnBytes.Road.K4.ncl_of_led
#print axioms OnBytes.Road.K4.d4_of_led_num
