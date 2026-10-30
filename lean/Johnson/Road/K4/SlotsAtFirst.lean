-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotsAtFirst.lean: THE FIRST GROUP's twin of the typed part of
Johnson/Road/K4/SlotsAt.lean: the clauses "the hidden value under a slot is what was shown less the
challenge times the mask entry" of the ports' dictionaries, at the library's own names and records
of the first group's chain, in the world of every ledger later than the call that laid the slot.

The first group's chain has its own letters: the parameters FullFPar, the chain behind the three
points tailW P, the norms' record eAtF. Its first six stages are written as a later group's. What is
general in SlotsAt.lean (the algebra, the tape's side, one stage) is imported. The statements and
proofs here are that file's, turned to these letters by a program and compiled; each name bears an
F.

Main names: `eAt_shLF` … `eAt_shPF`, `tAt_shF`, `tAt_bF`, `gAt_shL5F` … `gAt_b6F` (what the records
read, by definition) · `sqL_atF`, `sqR_atF`, `g5L_atF`, `g5R_atF`, `g6L_atF`, `g6R_atF` ·
`slot2_atF`, `slotW_atF`, `slotP_atF` · `batCl_atF` · `slotT_atF` · `stack_atF`.
Limits. As SlotsAt.lean's: OutIs of the stage; that the call returns on the stage's own tape, from a
ledger with arrays of the right sizes; that the ledger Hl is later; the numbering of the end values;
how many values the call lays; that y at the mask entry's name is the mask at the slot's number: all
premises. One direction. Nothing on soundness.


-/
import Johnson.Road.K4.SlotsAt
import Cb.Pv.Lay.End.LayFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading Fork Psc Level Aff)
open OnBytes.Model.Layer (Pub Env Heard HeardStack)
open OnBytes.PscRun (Sized hideRun_ok)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 tailT TailM TailR sentOf levelIn_heard)
open OnBytes.Desc.First.K4 (hearStack engFl)
open Inst.Model.FFSeg (Dim)
open Inst.Model (Scl)

/-! ## What the library's records read of a last statement -/

section Reads

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : OwnFPar E' M X)
  (W : P.WFPart) (e : (tailFst P W).s7.Nx) (zt : ℕ → E')

theorem eAt_shLF : (eAtF P W e zt).shL = ((tailFst P W).b1 e).2.vals false := rfl
theorem eAt_shRF : (eAtF P W e zt).shR = ((tailFst P W).b1 e).2.vals true := rfl
theorem eAt_b1F : (eAtF P W e zt).β1 =
    (tailFst P W).s1.L.Q.outB (tailFst P W).s1.L.M ((tailFst P W).b1 e).2 := rfl

theorem eAt_sh2F (n : ℕ) : (eAtF P W e zt).sh2 n =
    if h : n < P.D.nNu * 4 then ((tailFst P W).b2 e).2.vals (finProdFinEquiv.symm ⟨n, h⟩) else 0 :=
  rfl
theorem eAt_b2F : (eAtF P W e zt).β2 =
    (tailFst P W).s2.L.Q.outB (tailFst P W).s2.L.M ((tailFst P W).b2 e).2 := rfl
theorem eAt_shClF : (eAtF P W e zt).shCl = @id (Fin 1 → E') ((tailFst P W).b2 e).1.2 0 := rfl
theorem eAt_shWF (n : ℕ) : (eAtF P W e zt).shW n =
    if h : n < P.D.nNu * 9 then ((tailFst P W).b1 e).1.1.1.1.2 ⟨n, h⟩ else 0 := rfl
theorem eAt_shPF (n : ℕ) : (eAtF P W e zt).shP n =
    if h : n < P.D.nNu * 7 then ((tailFst P W).b2 e).1.1.1.2 ⟨n, h⟩ else 0 := rfl

end Reads

section ReadsF

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : FullFPar E' M X)
  (e : (tailW P).s7.Nx)

theorem tAt_shF (n : ℕ) : (termsEAt P.tp ((tailW P).b3 e).2).sh n =
    pick P.D ((tailW P).b3 e).2.vals 0 n := rfl
theorem tAt_bF : (termsEAt P.tp ((tailW P).b3 e).2).β =
    (tailW P).s3.L.Q.outB (tailW P).s3.L.M ((tailW P).b3 e).2 := rfl

theorem gAt_shL5F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).shL5 =
    ((tailW P).b5 e).2.vals false := rfl
theorem gAt_shR5F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).shR5 =
    ((tailW P).b5 e).2.vals true := rfl
theorem gAt_b5F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).β5 =
    (tailW P).s5.L.Q.outB (tailW P).s5.L.M ((tailW P).b5 e).2 := rfl
theorem gAt_shL6F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).shL6 =
    ((tailW P).b6 e).2.vals false := rfl
theorem gAt_shR6F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).shR6 =
    ((tailW P).b6 e).2.vals true := rfl
theorem gAt_b6F : (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2).β6 =
    (tailW P).s6.L.Q.outB (tailW P).s6.L.M ((tailW P).b6 e).2 := rfl

end ReadsF

/-! ## The six clauses of the three product layers -/

section Clauses

variable [scl : Scl] {M X : Type} (P : FullFPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailW P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailW P) k t) (a : Adds7 (tailW P)) (x : P.ofp.fs.X3)
  (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {J₂ : Type}

/-- FrontDict.sqL: the left end value of the product layer of the squares. -/
theorem sqL_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d1 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k1 rho C order F (k.tc1 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w1.num false = 0) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((namesAt P.ofp.nr U).mL) = mask L.sL) :
    (Hl.worldOf gl mask entry).slot L.sL =
      (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).shL -
        (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).β1 *
          y ((namesAt P.ofp.nr U).mL) := by
  have s := stgT_level_slot W'.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1 O mask entry hF h lH
    false (e := 0) (by omega) hnum
  rw [eAt_shLF, eAt_b1F, hy]
  exact s

/-- FrontDict.sqR: the right end value. -/
theorem sqR_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d1 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k1 rho C order F (k.tc1 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w1.num true = 1) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((namesAt P.ofp.nr U).mR) = mask L.sR) :
    (Hl.worldOf gl mask entry).slot L.sR =
      (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).shR -
        (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).β1 *
          y ((namesAt P.ofp.nr U).mR) := by
  have s := stgT_level_slot W'.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1 O mask entry hF h lH
    true (e := 1) (by omega) hnum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard h
  rw [eAt_shRF, eAt_b1F, hy, hsR]
  exact s

/-- FrontDict.g5L: the left end value of the first product layer of the gated products. -/
theorem g5L_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d5 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k5 rho C order F (k.tc5 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w5.num false = 0)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mL5) = mask L.sL) :
    (Hl.worldOf gl mask entry).slot L.sL =
      (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).shL5 -
        (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).β5 *
          y ((gNamesAt P.fp U).mL5) := by
  have s := stgT_level_slot W'.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5 O mask entry hF h lH
    false (e := 0) (by omega) hnum
  rw [gAt_shL5F, gAt_b5F, hy]
  exact s

/-- FrontDict.g5R: its right end value. -/
theorem g5R_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d5 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k5 rho C order F (k.tc5 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w5.num true = 1)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mR5) = mask L.sR) :
    (Hl.worldOf gl mask entry).slot L.sR =
      (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).shR5 -
        (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).β5 *
          y ((gNamesAt P.fp U).mR5) := by
  have s := stgT_level_slot W'.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5 O mask entry hF h lH
    true (e := 1) (by omega) hnum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard h
  rw [gAt_shR5F, gAt_b5F, hy, hsR]
  exact s

/-- FrontDict.g6L: the left end value of the second product layer. -/
theorem g6L_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d6 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k6 rho C order F (k.tc6 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w6.num false = 0)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mL6) = mask L.sL) :
    (Hl.worldOf gl mask entry).slot L.sL =
      (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).shL6 -
        (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).β6 *
          y ((gNamesAt P.fp U).mL6) := by
  have s := stgT_level_slot W'.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6 O mask entry hF h lH
    false (e := 0) (by omega) hnum
  rw [gAt_shL6F, gAt_b6F, hy]
  exact s

/-- FrontDict.g6R: its right end value. -/
theorem g6R_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d6 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k6 rho C order F (k.tc6 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w6.num true = 1)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mR6) = mask L.sR) :
    (Hl.worldOf gl mask entry).slot L.sR =
      (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).shR6 -
        (gatedEAt P.fp ((tailW P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailW P).b6 ((tailT W' k t nz a).z7 x)).2).β6 *
          y ((gNamesAt P.fp U).mR6) := by
  have s := stgT_level_slot W'.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6 O mask entry hF h lH
    true (e := 1) (by omega) hnum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard h
  rw [gAt_shR6F, gAt_b6F, hy, hsR]
  exact s

/-- LedDict.slot2: the end values of the token sumcheck of the row products. nn: how many end values
the call lays. -/
theorem slot2_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d2 p) {Pt : Array E} {nn dY : ℕ}
    {F G : Fork} {u : Tape} {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : Fl.tscIn Pt k.k2 nn dY F ((k.tcP t).drop 1) = some (o, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnn : 4 * P.D.nNu ≤ nn)
    (hnum : ∀ q : Fin P.D.nNu × Fin 4, W'.w2.num q = (finProdFinEquiv q : ℕ)) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 4 * P.D.nNu → y ((namesAt P.ofp.nr U).m2 n) = mask (o.sEnd + n)) :
    ∀ n, n < 4 * P.D.nNu → (Hl.worldOf gl mask entry).slot (o.sEnd + n) =
      (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).sh2 n -
        (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).β2 *
          y ((namesAt P.ofp.nr U).m2 n) := by
  intro n hn
  have hn' : n < P.D.nNu * 4 := by omega
  have s := stgT_slot W'.w2.num k.k2 ((k.tcP t).drop 1) nz.b2 a.st2 a.t2 O
    (finProdFinEquiv.symm ⟨n, hn'⟩) (e := n) (by rw [hnum, Equiv.apply_symm_apply])
    (tsc_slot gl mask entry hF h lH (by omega))
  rw [eAt_sh2F, dif_pos hn', eAt_b2F, hy n hn]
  exact s

/-- FrontDict.batCl: the claimed sum of the token sumcheck of the row products. -/
theorem batCl_atF {Pt : Array E} {nn dY : ℕ} {F G : Fork} {u : Tape} {o : OnBytes.Model.Tsc}
    (hF : Sized F) (h : Fl.tscIn Pt k.k2 nn dY F ((k.tcP t).drop 1) = some (o, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E) (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : y ((namesAt P.ofp.nr U).mCl) = mask F.next) :
    (Hl.worldOf gl mask entry).slot o.sCl =
      (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).shCl - y ((namesAt P.ofp.nr U).mCl) := by
  rw [eAt_shClF, hy, tsc_cl gl mask entry hF h lH]
  rfl

/-- LedDict.slotW: the sums' scalars. The run that lays them: the words that the tape's first round
sent, under the factor 1. -/
theorem slotW_atF {F G : Fork} {first : ℕ} {vW : Array E} (hF : Sized F)
    (h : F.hideRun first vW oneE = some G) (hv : vW.toList = sentOf t)
    (hsz : 9 * P.D.nNu ≤ vW.size) {Hl : Fork} (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 9 * P.D.nNu → y ((namesAt P.ofp.nr U).mW n) = mask (first + n)) :
    ∀ n, n < 9 * P.D.nNu → (Hl.worldOf gl mask entry).slot (first + n) =
      (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).shW n -
        y ((namesAt P.ofp.nr U).mW n) := by
  intro n hn
  have hn' : n < P.D.nNu * 9 := by omega
  rw [eAt_shWF, dif_pos hn', hy n hn, run_slot gl mask entry hF h lH (i := n) (by omega), hv,
    gl.one, one_mul]
  rfl

/-- LedDict.slotP: the products' scalars: as slotW_atF, on the tape from the products' round on. -/
theorem slotP_atF {F G : Fork} {first : ℕ} {vP : Array E} (hF : Sized F)
    (h : F.hideRun first vP oneE = some G) (hv : vP.toList = sentOf (k.tcP t))
    (hsz : 7 * P.D.nNu ≤ vP.size) {Hl : Fork} (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 7 * P.D.nNu → y ((namesAt P.ofp.nr U).mP n) = mask (first + n)) :
    ∀ n, n < 7 * P.D.nNu → (Hl.worldOf gl mask entry).slot (first + n) =
      (eAtF P.ofp P.wfPart ((tailT W' k t nz a).z7 x) zt).shP n -
        y ((namesAt P.ofp.nr U).mP n) := by
  intro n hn
  have hn' : n < P.D.nNu * 7 := by omega
  rw [eAt_shPF, dif_pos hn', hy n hn, run_slot gl mask entry hF h lH (i := n) (by omega), hv,
    gl.one, one_mul]
  rfl

/-- TermsDict.slot: the end values of the sumcheck of the terms. -/
theorem slotT_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d3 p) {Pt : Array E} {nn dY : ℕ}
    {F G : Fork} {u : Tape} {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : Fl.tscIn Pt k.k3 nn dY F (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o, G, u))
    {Hl : Fork} (lH : Fo.Later G Hl) (hnn : P.D.nNu + P.D.ne + P.D.ne * P.D.nx ≤ nn)
    (hnum : ∀ q : ShA P.D, W'.w3.num q = numA P.D q) (U : TermsReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < P.D.nNu + P.D.ne + P.D.ne * P.D.nx →
      y ((namesT P.tp U).mT n) = mask (o.sEnd + n)) :
    ∀ n, n < P.D.nNu + P.D.ne + P.D.ne * P.D.nx →
      (Hl.worldOf gl mask entry).slot (o.sEnd + n) =
        (termsEAt P.tp ((tailW P).b3 ((tailT W' k t nz a).z7 x)).2).sh n -
          (termsEAt P.tp ((tailW P).b3 ((tailT W' k t nz a).z7 x)).2).β *
            y ((namesT P.tp U).mT n) := by
  intro n hn
  obtain ⟨q, rfl⟩ := numA_surj hn
  have s := stgT_slot W'.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 a.st3 a.t3 O q
    (hnum q) (tsc_slot gl mask entry hF h lH (by omega))
  rw [tAt_shF, pick_num, tAt_bF, hy _ hn]
  exact s

/-- The premises hA and hB of stack_port: end value q of the batched sumcheck, number e. μ: what the
messages hold at the mask entry's name. -/
theorem stack_atF {p : Psc} (O : OutIs gl (tailT W' k t nz a).d4 p) {Pp : Pub} {v : Env} {H : Heard}
    {NCLp : ℕ} {F G : Fork} {u : Tape} {S : HeardStack} (hF : Sized F)
    (h : hearStack engFl Pp v H k.k4 NCLp F (k.tc4 t) = some (S, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (q : IA P.D ⊕ IB P.D) {e : ℕ} (he : e < 2 + (1 + Pp.y.LamM) + NCLp)
    (hnum : W'.w4.num q = e) {μ : Cb.Gl.E} (hμ : μ = mask (S.sA0 + e)) :
    (Hl.worldOf gl mask entry).slot (S.sA0 + e) =
      ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2.vals q -
        P.ip.inn.Kp.outB P.ip.inn.Mk ((tailW P).b4 ((tailT W' k t nz a).z7 x)).2 * μ := by
  have s := stgT_slot W'.w4.num k.k4 ((k.tc4 t).drop 1) nz.b4 a.st4 a.t4 O q hnum
    (stack_slot gl mask entry hF h lH he)
  rw [hμ]
  exact s

end Clauses

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.eAt_shLF
#print axioms OnBytes.Road.K4.eAt_shRF
#print axioms OnBytes.Road.K4.eAt_b1F
#print axioms OnBytes.Road.K4.eAt_sh2F
#print axioms OnBytes.Road.K4.eAt_b2F
#print axioms OnBytes.Road.K4.eAt_shClF
#print axioms OnBytes.Road.K4.eAt_shWF
#print axioms OnBytes.Road.K4.eAt_shPF
#print axioms OnBytes.Road.K4.tAt_shF
#print axioms OnBytes.Road.K4.tAt_bF
#print axioms OnBytes.Road.K4.gAt_shL5F
#print axioms OnBytes.Road.K4.gAt_shR5F
#print axioms OnBytes.Road.K4.gAt_b5F
#print axioms OnBytes.Road.K4.gAt_shL6F
#print axioms OnBytes.Road.K4.gAt_shR6F
#print axioms OnBytes.Road.K4.gAt_b6F
#print axioms OnBytes.Road.K4.sqL_atF
#print axioms OnBytes.Road.K4.sqR_atF
#print axioms OnBytes.Road.K4.g5L_atF
#print axioms OnBytes.Road.K4.g5R_atF
#print axioms OnBytes.Road.K4.g6L_atF
#print axioms OnBytes.Road.K4.g6R_atF
#print axioms OnBytes.Road.K4.slot2_atF
#print axioms OnBytes.Road.K4.batCl_atF
#print axioms OnBytes.Road.K4.slotW_atF
#print axioms OnBytes.Road.K4.slotP_atF
#print axioms OnBytes.Road.K4.slotT_atF
#print axioms OnBytes.Road.K4.stack_atF
