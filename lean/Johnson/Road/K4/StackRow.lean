-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRow.lean: the own claim of the batched sumcheck of a layers' sub-proof, at a
hearing of the text of the layers' own rounds in a group that is not the first: where the row that
the text holds for that sumcheck is worth 0, the form in which the library's ledger writes the
sumcheck's first output claim is worth 0.

Johnson/Road/K4/OwnRows.lean (stgT_rowUp) holds a record's row form against the ledger's form at a
stage's own typed output, under four conditions (D1) to (D4). Here (D3) and (D4) are shown for the
fourth stage. (D3): the stage has no kept map, and the text hands the empty form to its row. (D4):
the library's summand on the stage's end values is the product As Bs that the verifier computes
(d4_inn, Johnson/Road/K4/StackRowD4.lean), where the end values by name are the words that the round
of the end values sent, by number (hearStack_words, OnBytes/Desc/First/K4/StackWords.lean).

Main names:
  `psc_stackVals`: the words of the round of the end values, in the two ways of writing.
  `virt_lt`: the number of a never-sent vector is below 1 + ne.
  `envOfHear`: the panels' environment that the text of the batched sumcheck makes.
  `d4_of_led4`: (D4) at a hearing. `u4_of_led`: the ledger's form is worth 0.
Limits. PREMISES, NONE SHOWN HERE: Led7; the fourth stage's claim; OutIs at the third and fourth
stages; the numbers of the rounds; the numberings of the end values of the third and fourth stages,
the fourth's in four clauses; v0Of, the number of each weight panel's first claim, a letter with the
premises that it is the verifier's (F0) and stays below the plan's number of claims; SigFits at the
panels' environment that the text makes; the calls of the second walk; the weight claims' list; four
sizes; the two clauses on the lookup's point; as many challenges as rounds; StgFits, the lawful
pick, the target, (D1) and (D2) at the fourth stage. One direction: from returns. Nothing on
soundness.


-/
import Johnson.Road.K4.OwnRows
import Johnson.Road.K4.PointsOfLed
import Johnson.Road.K4.StackRowD4
import OnBytes.Desc.First.K4.StackWords
import OnBytes.Desc.First.K4.BatchLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Psc Level Tsc Aff WsShape WsClaim powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard SBlk Panels PanelEnv ClaimEnv nEndT callsTS stubO
  panelsA panelsT placePanels)
open OnBytes.Tie.Pv.Lay (OutIs StgFits)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR pscT sentOf tapeEps plainWs)
open OnBytes.Desc.First.K4 (stackVals stackRec stack_heard hearStack_words drop_drop' powers_val)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Pan pans)

/-- The words of the round of the end values of the batched sumcheck: its call begins one round in
front of the stage's tape. -/
theorem psc_stackVals (n lamS : ℕ) (t : Tape) : (pscT n lamS (t.drop 1)).v = stackVals lamS t := by
  have dv : (t.drop 1).drop (lamS + 2) = t.drop (lamS + 3) := by
    rw [drop_drop']
    congr 1
    omega
  show sentOf ((t.drop 1).drop (lamS + 2)) = sentOf (t.drop (lamS + 3))
  rw [dv]

/-- The number of the never-sent vector of a panel of the library's list is below 1 + ne. -/
theorem virt_lt {D : Dim} {pn : Pan} (hp : pn ∈ pans D) : (virtOf pn).getD 0 < 1 + D.ne := by
  cases pn with
  | Dr l =>
    have := dr_lt hp
    show 1 + l < 1 + D.ne
    omega
  | _ => exact Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_add_right 1 D.ne)

/-- The panels' environment that the text of the batched sumcheck makes: shownT: what the second
token sumcheck has shown. -/
abbrev envOfHear (P : Pub) (o : Own) (shownT : Array E) : PanelEnv :=
  { v := o.v, e := o.H.fo.e, shownT := shownT, zt := o.H.ztF, stubO := stubO P.y }

section Led

variable [scl : Scl] {M X : Type} (Pf : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF Pf) R)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **(D4) of the fourth stage at a hearing**: the library's summand on the stage's end values, at
the stage's own end point, is the verifier's product As Bs, read. -/
theorem d4_of_led4 (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (hc : (k4Tail W' P hp t0 nz a).d4.Claim ((k4Tail W' P hp t0 nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (k4Tail W' P hp t0 nz a).d3 p3) (O4 : OutIs gl (k4Tail W' P hp t0 nz a).d4 p4)
    (k3 : (tailF Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q) (v0Of : Pan → ℕ)
    (nA0 : W'.w4.num (Sum.inl (Sum.inl ()) : IA Pf.D ⊕ IB Pf.D) = 0)
    (nA : ∀ i : (Σ p : {p : Pan // p ∈ pans Pf.D}, Fin (cntA p.1)),
      W'.w4.num (Sum.inl (Sum.inr i) : IA Pf.D ⊕ IB Pf.D) = 1 + (virtOf i.1.1).getD 0)
    (nB0 : W'.w4.num (Sum.inr (Sum.inl ()) : IA Pf.D ⊕ IB Pf.D) = 1 + (1 + P.y.LamM))
    (nB : ∀ (p : {p : Pan // p ∈ pans Pf.D}) (i : Fin (cntB Pf.D p.1)),
      W'.w4.num (Sum.inr (Sum.inr ⟨p, i⟩) : IA Pf.D ⊕ IB Pf.D) =
        2 + (1 + P.y.LamM) + (v0Of p.1 + i))
    (hlt : ∀ (p : {p : Pan // p ∈ pans Pf.D}) (i : Fin (cntB Pf.D p.1)),
      v0Of p.1 + i < hp.NCL - 0)
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
    (hcl : c.weightClaims [0, 1, 2, 5] = some cl) (hrs : kS Pf.D ≤ o.K.rs.size)
    (F0 : ∀ pn' : Panels, panelsT (envOfHear P o shownT) [0, 1, 2, 5]
        (panelsA (envOfHear P o shownT) {}) = some pn' →
      List.Forall₂ (fun (b : SBlk) (pn : Pan) => pn.weight = true → b.v0 = some (v0Of pn))
        (placePanels pn'.bl).1.toList (pans Pf.D)) :
    Pf.ip.inn.Sm.pol a.st4
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2)
        (k4Tail W' P hp t0 nz a).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs) := by
  obtain ⟨tT', shownT', TS, pn', Hh, V, shA, shB, q1, q2, q3, q4, q5, wA, wH, wB, wV⟩ :=
    hearStack_words Ld.s2 Ld.c4
  have e0 := Option.some.inj (q1.symm.trans Ld.kTT)
  have e1 := congrArg Tsc.sEnd e0
  have eT : tT'.sEnd = tT.sEnd := e1
  rw [eT] at q2
  obtain rfl : shownT = shownT' := Option.some.inj (hsh.symm.trans q2)
  obtain rfl : [0, 1, 2, 5] = TS := Option.some.inj (hTS.symm.trans q3)
  rw [← k4, ← hyv] at q5
  have hom : gl.val ((powers (tapeEps ((ksOf P hp).tc4 (t0.drop 1))) 2).getD 0 zeroE) = 1 := by
    rw [powers_val gl _ (n := 2) (s := 0) (by omega), pow_zero]
  have T : StackTies Pf.ip a.st4 gl o.v.y shownT
      (powers (tapeEps ((ksOf P hp).tc4 (t0.drop 1))) 2) z (pt gl tT.r) :=
    stackTies_of_led Pf W' Ld nz a x hc O3 k3 n3 (by rw [hyv]; exact hNN) (by rw [hyv]; exact hLM)
      (by rw [hyv]; exact hNE) hEnd hsh rfl hz0 hz3
  have FE := placed_fields S rfl q4 hcl
  have FW := (placed_sides S (fun _ _ => 0)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩)
    rfl q4 hcl hom q5).imp fun _ _ k => (⟨k.bw, k.bwy⟩ : _ ∧ _)
  have hvq : ∀ q, (k4Tail W' P hp t0 nz a).d4.v q =
      gl.val ((stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop 1))).getD (W'.w4.num q) zeroE) :=
    fun q => by
      show gl.val ((pscT _ hp.lamS (((ksOf P hp).tc4 (t0.drop 1)).drop 1)).v.getD
        (W'.w4.num q) zeroE) = _
      rw [psc_stackVals]
  exact d4_inn T hom (by rw [hyv]; exact hNE) FE FW q5 hrs _
    (hpt_of_led Pf W' Ld nz a x O4 k4) v0Of (F0 pn' q4) _
    (by rw [hvq, nA0, wA])
    (fun i => by
      rw [hvq, nA i]
      exact congrArg gl.val (wH _ (by rw [hLM]; exact virt_lt i.1.2)).symm)
    (by rw [hvq, nB0, wB])
    (fun p i => by
      rw [hvq, nB p i]
      exact congrArg gl.val (wV _ (hlt p i)).symm) Wo

/-- **The ledger's form of the batched sumcheck's first output claim is worth 0**, where the row
that the text holds for that sumcheck is worth 0 in the world W2. hD4: (D4), as d4_of_led4 concludes
it. -/
theorem u4_of_led (Ld : Led7 P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (nz : NzT (tailF Pf) (ksOf P hp) (t0.drop 1)) (a : Adds7 (tailF Pf)) (x : Pf.XT)
    (hD4 : Pf.ip.inn.Sm.pol a.st4
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2)
        (k4Tail W' P hp t0 nz a).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs))
    (hn : (tailF Pf).s4.n = 0)
    (ht : a.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1))).target)
    (f : StgFits gl (tailF Pf).s4 a.st4 (plainWs hp.lamS) hp.lamS 2)
    (hF : ∀ st, HFixs.OK _ ((tailF Pf).s4.F st)) (Ex : ExtSpec) (y : Ex.Str)
    (W2 : World Cb.Gl.E) (hrow : o.K.rowS.value gl W2 = 0) (m : M)
    (D1 : (tailF Pf).s4.L.T.par.W a.st4 (Pf.msg m) =
      OnBytes.Road.Hd.place W2.slot ((tailF Pf).s4.L.T.par.vars a.st4)
        (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1))).first)
    (D2 : (tailF Pf).s4.L.T.par.inc a.st4 (Pf.msg m) =
      gl.val (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1))).target -
        (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1))).start.value gl W2)
    {J₂ : Type} [Fintype J₂] (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (Pf.msg m) w)
      (upForm (J₂ := J₂) (Cb.Sub.formU Pf.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
        ((tailF Pf).b4 ((k4Tail W' P hp t0 nz a).z7 x)).2)) = 0 := by
  have hr : ((stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop 1))).rowForm
      (mulE o.K.fin.As o.K.fin.Bs) {}).value gl W2 = 0 := by
    rw [← (stack_heard Ld.c4).2.2.2.1]
    exact hrow
  exact (stgT_rowUp W'.w4.num hp.lamS (((ksOf P hp).tc4 (t0.drop 1)).drop 1) nz.b4 a.st4 a.t4 hn
    (stack_recAt Ld.c4) ht f hF Ex y W2 (mulE o.K.fin.As o.K.fin.Bs) {} (Pf.msg m) D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show PEmpty from b).elim)
    hD4 (fun _ b _ _ => PEmpty.elim b) (fun _ _ b _ => PEmpty.elim b) w).1 hr

end Led

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.psc_stackVals
#print axioms OnBytes.Road.K4.virt_lt
#print axioms OnBytes.Road.K4.d4_of_led4
#print axioms OnBytes.Road.K4.u4_of_led
