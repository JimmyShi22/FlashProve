-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackRowFirst.lean: THE FIRST GROUP's twin of StackRow.lean and StackRowNum.lean:
the batched sumcheck's own row at a hearing of K4's text, for the first group's chain: from the
record LedG (Johnson/Road/K4/OwnLedgersG.lean), which stands in every group.

The statements and proofs are those of the two files, turned to the first group's letters
(Johnson/Road/K4/AtFirst.lean says which) by a program and compiled; each name bears an F. One
number turns with them: K4's text hears hp.NCL - (if (g == 0) = true then 1 else 0) weight claims
in the batched sumcheck: in the first group one fewer than the plan's number; the one more is the
embedding's.

Main names: `d4_of_led4F` (the typed summand at the end values is the verifier's As · Bs, read) ·
`u4_of_ledF` (eight_of_ledF's premise u4) · `ncl_of_ledF` (nWK D is the number of weight claims
that the text hears) · `d4_of_led_numF` (the first with the numbering's premises gone).
Limits. As the two files'. Identities on public numbers and given values, and one implication in a
given world: nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StackRowNum
import Johnson.Road.K4.OfLedFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading World Fork Psc Level Tsc Aff WsShape WsClaim powers)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard SBlk Panels PanelEnv ClaimEnv nEndT callsTS stubO
  panelsA panelsT placePanels)
open OnBytes.Tie.Pv.Lay (OutIs StgFits)
open OnBytes.Desc.First.P1 (gl NzT Adds7 TailM TailR tailT pscT sentOf tapeEps plainWs)
open OnBytes.Desc.First.K4 (stackVals stackRec stack_heard hearStack_words hearStack_public
  drop_drop' powers_val k0)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Pan pans)

section LedF

variable [scl : Scl] {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)
  {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own} {F G : Fork}
  {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 :
      Tape}

/-- **(D4) of the fourth stage at a hearing**: the library's summand on the stage's end values, at
the stage's own end point, is the verifier's product As Bs, read. -/
theorem d4_of_led4F (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim ((tailT W' (ksOf P hp) (t0.drop (k0
        g)) nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3) (O4 : OutIs gl (tailT W'
        (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q) (v0Of : Pan → ℕ)
    (nA0 : W'.w4.num (Sum.inl (Sum.inl ()) : IA Pf.D ⊕ IB Pf.D) = 0)
    (nA : ∀ i : (Σ p : {p : Pan // p ∈ pans Pf.D}, Fin (cntA p.1)),
      W'.w4.num (Sum.inl (Sum.inr i) : IA Pf.D ⊕ IB Pf.D) = 1 + (virtOf i.1.1).getD 0)
    (nB0 : W'.w4.num (Sum.inr (Sum.inl ()) : IA Pf.D ⊕ IB Pf.D) = 1 + (1 + P.y.LamM))
    (nB : ∀ (p : {p : Pan // p ∈ pans Pf.D}) (i : Fin (cntB Pf.D p.1)),
      W'.w4.num (Sum.inr (Sum.inr ⟨p, i⟩) : IA Pf.D ⊕ IB Pf.D) =
        2 + (1 + P.y.LamM) + (v0Of p.1 + i))
    (hlt : ∀ (p : {p : Pan // p ∈ pans Pf.D}) (i : Fin (cntB Pf.D p.1)),
      v0Of p.1 + i < hp.NCL - (if (g == 0) = true then 1 else 0))
    (hyv : o.v.y = P.y) (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    {shownT : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    {z : ℕ → Cb.Gl.E} (hz0 : ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7
        x)).2.st.z = z)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st .QK =
        z)
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
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz
            a).z7 x)).2)
        (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.v =
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
  have hom : gl.val ((powers (tapeEps ((ksOf P hp).tc4 (t0.drop (k0 g)))) 2).getD 0 zeroE) = 1 := by
    rw [powers_val gl _ (n := 2) (s := 0) (by omega), pow_zero]
  have T : StackTies Pf.ip a.st4 gl o.v.y shownT
      (powers (tapeEps ((ksOf P hp).tc4 (t0.drop (k0 g)))) 2) z (pt gl tT.r) :=
    stackTies_of_ledF Pf W' Ld nz a x hc O3 k3 n3 (by rw [hyv]; exact hNN) (by rw [hyv]; exact hLM)
      (by rw [hyv]; exact hNE) hEnd hsh rfl hz0 hz3
  have FE := placed_fields S rfl q4 hcl
  have FW := (placed_sides S (fun _ _ => 0)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0,
      fun _ _ => 0, fun _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0, fun _ _ _ => 0⟩)
    rfl q4 hcl hom q5).imp fun _ _ k => (⟨k.bw, k.bwy⟩ : _ ∧ _)
  have hvq : ∀ q, (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.v q =
      gl.val ((stackVals hp.lamS ((ksOf P hp).tc4 (t0.drop (k0 g)))).getD (W'.w4.num q) zeroE) :=
    fun q => by
      show gl.val ((pscT _ hp.lamS (((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1)).v.getD
        (W'.w4.num q) zeroE) = _
      rw [psc_stackVals]
  exact d4_inn T hom (by rw [hyv]; exact hNE) FE FW q5 hrs _
    (hpt_of_ledF Pf W' Ld nz a x O4 k4) v0Of (F0 pn' q4) _
    (by rw [hvq, nA0, wA])
    (fun i => by
      rw [hvq, nA i]
      exact congrArg gl.val (wH _ (by rw [hLM]; exact virt_lt i.1.2)).symm)
    (by rw [hvq, nB0, wB])
    (fun p i => by
      rw [hvq, nB p i]
      exact congrArg gl.val (wV _ (hlt p i)).symm) Wo

/-- **The ledger's form of the batched sumcheck's first output claim is worth 0**, where the row
that the text holds for that sumcheck is worth 0 in the world W2. hD4: (D4), as d4_of_led4F
    concludes
it. -/
theorem u4_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hD4 : Pf.ip.inn.Sm.pol a.st4
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz
            a).z7 x)).2)
        (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs))
    (hn : (tailW Pf).s4.n = 0)
    (ht : a.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g)))).target)
    (f : StgFits gl (tailW Pf).s4 a.st4 (plainWs hp.lamS) hp.lamS 2)
    (hF : ∀ st, HFixs.OK _ ((tailW Pf).s4.F st)) (Ex : ExtSpec) (y : Ex.Str)
    (W2 : World Cb.Gl.E) (hrow : o.K.rowS.value gl W2 = 0) (m : M)
    (D1 : (tailW Pf).s4.L.T.par.W a.st4 (Pf.msg m) =
      OnBytes.Road.Hd.place W2.slot ((tailW Pf).s4.L.T.par.vars a.st4)
        (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g)))).first)
    (D2 : (tailW Pf).s4.L.T.par.inc a.st4 (Pf.msg m) =
      gl.val (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g)))).target -
        (stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g)))).start.value gl W2)
    {J₂ : Type} [Fintype J₂] (w : J₂ → Cb.Gl.E) :
    Blocks.Form.val (Sum.elim (Pf.msg m) w)
      (upForm (J₂ := J₂) (Cb.Sub.formU Pf.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
        ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2)) = 0 := by
  have hr : ((stackRec o.v o.H hp.lamS G2 ((ksOf P hp).tc4 (t0.drop (k0 g)))).rowForm
      (mulE o.K.fin.As o.K.fin.Bs) {}).value gl W2 = 0 := by
    rw [← (stack_heard Ld.c4).2.2.2.1]
    exact hrow
  exact (stgT_rowUp W'.w4.num hp.lamS (((ksOf P hp).tc4 (t0.drop (k0 g))).drop 1) nz.b4 a.st4 a.t4
      hn
    (stack_recAt Ld.c4) ht f hF Ex y W2 (mulE o.K.fin.As o.K.fin.Bs) {} (Pf.msg m) D1 D2
    (by
      rw [Aff.value_empty]
      exact Finset.sum_eq_zero fun b _ => (show PEmpty from b).elim)
    hD4 (fun _ b _ _ => PEmpty.elim b) (fun _ _ b _ => PEmpty.elim b) w).1 hr

end LedF

section NumF

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape} {H1 : Heard} {hd2 : Level} {tT : Tsc}
  {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}

/-- **The plan's number of the panels' weight claims is the number of the pieces.** -/
theorem ncl_of_ledF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    {shownT : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    {D : Dim} {z : ℕ → Cb.Gl.E} {Wo : World Cb.Gl.E} {c : ClaimEnv}
    {h : OnBytes.Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {lk L0 : ℕ}
    {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E} {low zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (S : SigFits gl Wo (envOfHear P o shownT) c h pc s D lk L0 cc t low z zh ζ tb)
    (hTS : callsTS P = some [0, 1, 2, 5]) {cl : List WsClaim}
    (hcl : c.weightClaims [0, 1, 2, 5] = some cl) : nWK D = hp.NCL - (if (g == 0) = true then 1 else
        0) := by
  obtain ⟨tT', shownT', TS, pn', _, _, _, _, _, _, _, _, -, q1, q2, q3, q4, -, q6, -⟩ :=
    hearStack_public Ld.c4
  have e0 := Option.some.inj (q1.symm.trans Ld.kTT)
  have e1 := congrArg Tsc.sEnd e0
  have eT : tT'.sEnd = tT.sEnd := e1
  rw [eT] at q2
  obtain rfl : shownT = shownT' := Option.some.inj (hsh.symm.trans q2)
  obtain rfl : [0, 1, 2, 5] = TS := Option.some.inj (hTS.symm.trans q3)
  exact (placed_v0 q4 (placed_fields S rfl q4 hcl)).2.symm.trans (beq_iff_eq.mp q6)

variable {M X : Type} (Pf : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW Pf) R)

/-- **(D4) of the fourth stage at a hearing**, with the numbers paid. -/
theorem d4_of_led_numF (Ld : LedG P hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    (nz : NzT (tailW Pf) (ksOf P hp) (t0.drop (k0 g))) (a : Adds7 (tailW Pf)) (x : Pf.ofp.fs.X3)
    (hc : (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.Claim ((tailT W' (ksOf P hp) (t0.drop (k0
        g)) nz a).y4 x)) {p3 p4 : Psc}
    (O3 : OutIs gl (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d3 p3) (O4 : OutIs gl (tailT W'
        (ksOf P hp) (t0.drop (k0 g)) nz a).d4 p4)
    (k3 : (tailW Pf).s3.L.S.k = P.y.h.lt) (k4 : kS Pf.D = hp.lamS)
    (n3 : ∀ q : ShA Pf.D, W'.w3.num q = numA Pf.D q)
    (n4 : ∀ q : IA Pf.D ⊕ IB Pf.D, W'.w4.num q = num4 Pf.D (numK Pf.D) q)
    (hNCL : nWK Pf.D ≤ hp.NCL - (if (g == 0) = true then 1 else 0))
    (hyv : o.v.y = P.y) (hNN : P.y.NN * P.y.Lam = Pf.D.nNu) (hLM : P.y.LamM = Pf.D.ne)
    (hNE : P.y.h.NE = Pf.D.nx) (hEnd : Pf.D.nNu + Pf.D.ne + Pf.D.ne * Pf.D.nx ≤ nEndT P.y)
    {shownT : Array E}
    (hsh : ((Array.range (nEndT P.y)).mapM fun i => G2.shown (tT.sEnd + i)) = some shownT)
    {z : ℕ → Cb.Gl.E} (hz0 : ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7
        x)).2.st.z = z)
    (hz3 : Pf.ip.zP ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).z7 x)).2.st .QK =
        z)
    {Wo : World Cb.Gl.E} {c : ClaimEnv} {h : OnBytes.Model.Layer.Shape} {pc : List (List String)}
    {s : WsShape} {lk L0 : ℕ} {cc : Cells Cb.Gl.E} {t : Cell → Cb.Gl.E}
    {low zh ζ : ℕ → Cb.Gl.E} {tb : Tables}
    (S : SigFits gl Wo (envOfHear P o shownT) c h pc s Pf.D lk L0 cc t low z zh ζ tb)
    (hTS : callsTS P = some [0, 1, 2, 5]) {cl : List WsClaim}
    (hcl : c.weightClaims [0, 1, 2, 5] = some cl) (hrs : kS Pf.D ≤ o.K.rs.size) :
    Pf.ip.inn.Sm.pol a.st4
        (Pf.ip.inn.Kp.outPt Pf.ip.inn.Mk ((tailW Pf).b4 ((tailT W' (ksOf P hp) (t0.drop (k0 g)) nz
            a).z7 x)).2)
        (tailT W' (ksOf P hp) (t0.drop (k0 g)) nz a).d4.v =
      gl.val (mulE o.K.fin.As o.K.fin.Bs) :=
  d4_of_led4F Pf W' Ld nz a x hc O3 O4 k3 k4 n3 (v0Of Pf.D) (n4 _)
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

end NumF

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.d4_of_led4F
#print axioms OnBytes.Road.K4.u4_of_ledF
#print axioms OnBytes.Road.K4.ncl_of_ledF
#print axioms OnBytes.Road.K4.d4_of_led_numF
