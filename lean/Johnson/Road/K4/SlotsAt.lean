-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/SlotsAt.lean: the clauses "the hidden value under a slot is what was shown less the
challenge times the mask entry" of the ports' dictionaries, at the library's own names and records,
in the world of every ledger later than the call that laid the slot: the six clauses of the three
product layers, the two token sumchecks' end values, the claimed sum of the first, the sums' and the
products' scalars, and the end values of the batched sumcheck.

The dictionary FrontDict (Johnson/Road/K4/ValuesOfClaims.lean) asks W.slot s = sh - β * y (name) for
each end value. Four facts meet in such a clause: what a later ledger's world holds under the slot
and what that ledger shows there (level_world, level_shown, tsc_world, tsc_shown,
OnBytes/Desc/First/P1/Heard.lean; stack_heard, OnBytes/Desc/First/K4/StackEnded.lean); that
the typed output of the chain's stage is the tape's words, read (OutIs,
OnBytes/Tie/Pv/Lay/HearTieL.lean; stgT, tailT, OnBytes/Desc/First/P1/TailTape.lean); what the
library's records read of the chain's last statement (eAt, termsEAt, gatedEAt); and that the mask
entry's name is worth the mask at the slot's number.

Main names:
  `slot_at`: the algebra.
  `run_slot`, `level_slot`, `tsc_slot`, `tsc_cl`, `stack_slot`: the tape's side: under a slot, in
    every later ledger's world.
  `stgT_slot`, `stgT_level_slot`: with the typed output of a stage whose data are read off the same
    tape.
  `eAt_shL` … `eAt_shP`, `tAt_sh`, `tAt_b`, `gAt_shL5` … `gAt_b6`: what the library's records read
    of a last statement: each by definition. `numA_surj`: every number in range is an end value's.
  `sqL_at`, `sqR_at`, `g5L_at`, `g5R_at`, `g6L_at`, `g6R_at` (FrontDict); `slot2_at`, `slotW_at`,
    `slotP_at` (LedDict); `batCl_at` (FrontDict.batCl); `slotT_at` (TermsDict.slot); `stack_at` (the
    premises hA, hB of stack_port, Johnson/Road/K4/StackPort.lean): the clauses, at the letters P
    of the library's chain, the data tailT read off a tape, and any entries y.
Limits. PREMISES, EACH A TIE BETWEEN TWO TEXTS' LETTERS, NONE SHOWN HERE: OutIs of the stage; that
the call returns on the stage's own tape, from a ledger with arrays of the right sizes; that the
ledger Hl is later; the numbering of the end values; how many values the call lays; that y at the
mask entry's name is the mask at the slot's number. One direction. Nothing on soundness.


-/
import OnBytes.Desc.First.P1.Heard
import OnBytes.Desc.First.P1.HeardPsc
import OnBytes.Desc.First.K4.StackEnded
import OnBytes.Desc.First.K4.NormsTape
import OnBytes.Desc.First.P1.TailTape
import OnBytes.Desc.First.P1.TailParts
import OnBytes.Tie.Pv.Lay.HearTieL
import Cb.Pv.Lay.End.LayAll

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
open OnBytes.Tie.Pv.Lay.Eng (StgH TailH)
open OnBytes.Desc.First.P1 (gl Ks NzT Adds7 tailT TailM TailR pscT stgT sentOf level_world
  level_shown levelIn_heard tsc_world tsc_shown tscIn_heard tscVals tscY roundAt slot_worldOf
  array_getD_toList tapeMu tapeMu_eq)
open OnBytes.Desc.First.K4 (hearStack engFl stack_heard stackVals stackY drop_drop')
open Inst.Model.FFSeg (Dim)
open Inst.Model (Scl)

/-! ## The algebra, and the tape's side -/

/-- From "what is shown is the hidden value plus the challenge times the mask entry". -/
theorem slot_at {K : Type} [Field K] {w v sh β β' μ mk : K} (h1 : v = w + β' * mk) (h2 : sh = v)
    (h3 : β = β') (h4 : μ = mk) : w = sh - β * μ := by
  rw [h2, h3, h4, h1]
  ring

/-- Under the slot of end value e of a product layer, in the world of every later ledger: the word
that the tape's values round sent, read, is the hidden value plus the further challenge times the
mask entry. -/
theorem level_slot {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    {mu : ℕ} {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork} {t u : Tape} {L : Level}
    (hF : Sized F) (h : Fl.levelIn mu rho C order F t = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) {e : ℕ} (he : e < 2) :
    ρ.val ((pscT 0 mu t).v.getD e zeroE) =
      (Hl.worldOf ρ mask entry).slot (L.sL + e) + ρ.val (pscT 0 mu t).beta * mask (L.sL + e) := by
  have a := ((level_world ρ mask entry hF h).2.2.2 Hl lH).2.1 e he
  rw [level_shown hF h Hl lH e he] at a
  exact a

/-- A run of values v, laid from the slot first on under the factor f: in the world of every later
ledger the hidden value under slot first + i is entry i, read, less the factor times the mask
entry. -/
theorem run_slot {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    {F G Hl : Fork} {first : ℕ} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun first v f = some G) (lH : Fo.Later G Hl) {i : ℕ} (hi : i < v.size) :
    (Hl.worldOf ρ mask entry).slot (first + i) =
      ρ.val (v.toList.getD i zeroE) - ρ.val f * mask (first + i) := by
  obtain ⟨_, _, hin, _⟩ := hideRun_ok F G first v f hF h
  have q := hin i hi
  have r := lH.keep (first + i) q.2.2.1
  rw [slot_worldOf, r.2.1, r.2.2, q.2.2.2.1, q.2.2.2.2, array_getD_toList]

/-- Under the slot of end value e of a token sumcheck: as level_slot. -/
theorem tsc_slot {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    {Pt : Array E} {lt nn dY : ℕ} {F G : Fork} {t u : Tape} {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : Fl.tscIn Pt lt nn dY F t = some (o, G, u)) {Hl : Fork} (lH : Fo.Later G Hl) {e : ℕ}
    (he : e < nn) :
    ρ.val ((pscT 0 lt t).v.getD e zeroE) =
      (Hl.worldOf ρ mask entry).slot (o.sEnd + e) +
        ρ.val (pscT 0 lt t).beta * mask (o.sEnd + e) := by
  have hl : (Pt.toList.take lt).length = lt := by
    rw [List.length_take, Array.length_toList]
    exact Nat.min_eq_left (tscIn_heard h).1
  have a := ((tsc_world ρ mask entry hF h).2.2.2.2.2.2.2 Hl lH).2 e he
  rw [tsc_shown hF h Hl lH e he] at a
  unfold tscVals tscY at a
  rw [hl] at a
  exact a

/-- Under the slot of a token sumcheck's claimed sum: the first word that its first round sent,
read, less the mask entry. -/
theorem tsc_cl {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    {Pt : Array E} {lt nn dY : ℕ} {F G : Fork} {t u : Tape} {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : Fl.tscIn Pt lt nn dY F t = some (o, G, u)) {Hl : Fork} (lH : Fo.Later G Hl) :
    (Hl.worldOf ρ mask entry).slot o.sCl = ρ.val ((sentOf t).getD 0 zeroE) - mask F.next := by
  rw [((tsc_world ρ mask entry hF h).2.2.2.2.2.2.2 Hl lH).1]
  show ρ.val (tapeMu t) - mask F.next = _
  rw [tapeMu_eq]

/-- Under the slot of end value i of the batched sumcheck. Its call begins one round in front of the
stage's tape. -/
theorem stack_slot {K : Type} [Field K] (ρ : Reading K) (mask : ℕ → K) (entry : ℕ → ℕ → ℕ → K)
    {Pp : Pub} {v : Env} {H : Heard} {lamS NCLp : ℕ} {F G : Fork} {t u : Tape} {S : HeardStack}
    (hF : Sized F) (h : hearStack engFl Pp v H lamS NCLp F t = some (S, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) {i : ℕ} (hi : i < 2 + (1 + Pp.y.LamM) + NCLp) :
    ρ.val ((pscT 0 lamS (t.drop 1)).v.getD i zeroE) =
      (Hl.worldOf ρ mask entry).slot (S.sA0 + i) +
        ρ.val (pscT 0 lamS (t.drop 1)).beta * mask (S.sA0 + i) := by
  obtain ⟨_, _, _, _, _, vals, G1, hl, hs, hG1, hG⟩ := stack_heard h
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lamS + 2 + (2 + (1 + Pp.y.LamM) + NCLp) } :
      Fork) := hF
  obtain ⟨_, hS1, _, _⟩ := hideRun_ok _ G1 _ _ _ hF' hG1
  have s := run_slot ρ mask entry hF' hG1 ((Fo.hideRun_later hS1 hG).trans lH) (i := i)
    (by rw [hs]; exact hi)
  have dv : (t.drop 1).drop (lamS + 2) = t.drop (lamS + 3) := by
    rw [drop_drop']
    congr 1
    omega
  have dy : (t.drop 1).drop (lamS + 1) = t.drop (lamS + 2) := by
    rw [drop_drop']
    congr 1
    omega
  have ev : (pscT 0 lamS (t.drop 1)).v = stackVals lamS t := by
    show sentOf ((t.drop 1).drop (lamS + 2)) = sentOf (t.drop (lamS + 3))
    rw [dv]
  have eb : (pscT 0 lamS (t.drop 1)).beta = (stackY lamS t).2.2 := by
    show (roundAt (OnBytes.Psc.Weight.atZero 1) ((t.drop 1).drop (lamS + 1))).2.2 = _
    rw [dy]
    rfl
  rw [ev, eb, s, hl]
  ring

/-- One end value against the typed output of a stage whose data are read off a tape. a: the end
value's typed name; e: its number; s: the tape's side. -/
theorem stgT_slot {M X : Type} {S : Stg Cb.Gl.E M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {p : Psc}
    (O : OutIs gl (stgT num k t hβ st tg) p) (a : S.L.S.A) {e : ℕ} (hnum : num a = e)
    {w mk : Cb.Gl.E}
    (s : gl.val ((pscT 0 k t).v.getD e zeroE) = w + gl.val (pscT 0 k t).beta * mk) :
    w = (stgT num k t hβ st tg).out.vals a -
      S.L.Q.outB S.L.M (stgT num k t hβ st tg).out * mk := by
  have hv : (stgT num k t hβ st tg).v a = gl.val ((pscT 0 k t).v.getD e zeroE) := by
    show gl.val ((sentOf (t.drop (k + 2))).getD (num a) zeroE) =
      gl.val ((sentOf (t.drop (k + 2))).getD e zeroE)
    rw [hnum]
  have hb : gl.val (stgT num k t hβ st tg).H.beta = gl.val (pscT 0 k t).beta := rfl
  exact slot_at s ((congrFun O.vals a).trans hv) (O.last.trans hb) rfl

/-- Every number below the number of the terms' end values is the number of one. -/
theorem numA_surj {D : Dim} {n : ℕ} (hn : n < D.nNu + D.ne + D.ne * D.nx) :
    ∃ q : ShA D, numA D q = n := by
  by_cases h1 : n < D.nNu
  · exact ⟨.inl ⟨n, h1⟩, rfl⟩
  by_cases h2 : n - D.nNu < D.ne
  · exact ⟨.inr (.inl ⟨n - D.nNu, h2⟩), by
      show D.nNu + (n - D.nNu) = n
      omega⟩
  have hr : n - D.nNu - D.ne < D.nx * D.ne := by
    rw [Nat.mul_comm]
    omega
  have hx : 0 < D.nx := by
    rcases Nat.eq_zero_or_pos D.nx with h0 | h0
    · rw [h0, Nat.zero_mul] at hr
      omega
    · exact h0
  refine ⟨.inr (.inr (⟨(n - D.nNu - D.ne) / D.nx, Nat.div_lt_of_lt_mul hr⟩,
    ⟨(n - D.nNu - D.ne) % D.nx, Nat.mod_lt _ hx⟩)), ?_⟩
  show D.nNu + D.ne + (n - D.nNu - D.ne) / D.nx * D.nx + (n - D.nNu - D.ne) % D.nx = n
  have e := Nat.div_add_mod' (n - D.nNu - D.ne) D.nx
  omega

/-- The same against the typed output of a stage whose data are read off the layer's tape. a: the
end value's typed name; e: its number. -/
theorem stgT_level_slot {M X : Type} {S : Stg Cb.Gl.E M X} (num : S.L.S.A → ℕ) (k : ℕ) (t : Tape)
    (hβ : gl.val (pscT S.n k t).beta ≠ 0) (st : S.L.St) (tg : E) {p : Psc}
    (O : OutIs gl (stgT num k t hβ st tg) p) (mask : ℕ → Cb.Gl.E)
    (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {rho : Array E} {C : Aff} {order : List ℕ} {F G : Fork}
    {u : Tape} {L : Level} (hF : Sized F) (h : Fl.levelIn k rho C order F t = some (L, G, u))
    {Hl : Fork} (lH : Fo.Later G Hl) (a : S.L.S.A) {e : ℕ} (he : e < 2) (hnum : num a = e) :
    (Hl.worldOf gl mask entry).slot (L.sL + e) =
      (stgT num k t hβ st tg).out.vals a -
        S.L.Q.outB S.L.M (stgT num k t hβ st tg).out * mask (L.sL + e) := by
  have s := level_slot gl mask entry hF h lH he
  have hv : (stgT num k t hβ st tg).v a = gl.val ((pscT 0 k t).v.getD e zeroE) := by
    show gl.val ((sentOf (t.drop (k + 2))).getD (num a) zeroE) =
      gl.val ((sentOf (t.drop (k + 2))).getD e zeroE)
    rw [hnum]
  have hb : gl.val (stgT num k t hβ st tg).H.beta = gl.val (pscT 0 k t).beta := rfl
  exact slot_at s ((congrFun O.vals a).trans hv) (O.last.trans hb) rfl

/-! ## What the library's records read of a last statement -/

section Reads

variable {E' : Type} [Field E'] [Fintype E'] [scl : Scl] {M X : Type} (P : OwnPar E' M X)
  (W : P.WPart) (e : (tailAt P W).s7.Nx) (zt : ℕ → E')

theorem eAt_shL : (eAt P W e zt).shL = ((tailAt P W).b1 e).2.vals false := rfl
theorem eAt_shR : (eAt P W e zt).shR = ((tailAt P W).b1 e).2.vals true := rfl
theorem eAt_b1 : (eAt P W e zt).β1 =
    (tailAt P W).s1.L.Q.outB (tailAt P W).s1.L.M ((tailAt P W).b1 e).2 := rfl

theorem eAt_sh2 (n : ℕ) : (eAt P W e zt).sh2 n =
    if h : n < P.D.nNu * 4 then ((tailAt P W).b2 e).2.vals (finProdFinEquiv.symm ⟨n, h⟩) else 0 :=
  rfl
theorem eAt_b2 : (eAt P W e zt).β2 =
    (tailAt P W).s2.L.Q.outB (tailAt P W).s2.L.M ((tailAt P W).b2 e).2 := rfl
theorem eAt_shCl : (eAt P W e zt).shCl = @id (Fin 1 → E') ((tailAt P W).b2 e).1.2 0 := rfl
theorem eAt_shW (n : ℕ) : (eAt P W e zt).shW n =
    if h : n < P.D.nNu * 9 then ((tailAt P W).b1 e).1.1.1.1.2 ⟨n, h⟩ else 0 := rfl
theorem eAt_shP (n : ℕ) : (eAt P W e zt).shP n =
    if h : n < P.D.nNu * 7 then ((tailAt P W).b2 e).1.1.1.2 ⟨n, h⟩ else 0 := rfl

theorem tAt_sh (n : ℕ) : (termsEAt P.tp ((tailAt P W).b3 e).2).sh n =
    pick P.D ((tailAt P W).b3 e).2.vals 0 n := rfl
theorem tAt_b : (termsEAt P.tp ((tailAt P W).b3 e).2).β =
    (tailAt P W).s3.L.Q.outB (tailAt P W).s3.L.M ((tailAt P W).b3 e).2 := rfl

theorem gAt_shL5 : (gatedEAt P.fp ((tailAt P W).b5 e).2 ((tailAt P W).b6 e).2).shL5 =
    ((tailAt P W).b5 e).2.vals false := rfl
theorem gAt_shR5 : (gatedEAt P.fp ((tailAt P W).b5 e).2 ((tailAt P W).b6 e).2).shR5 =
    ((tailAt P W).b5 e).2.vals true := rfl
theorem gAt_b5 : (gatedEAt P.fp ((tailAt P W).b5 e).2 ((tailAt P W).b6 e).2).β5 =
    (tailAt P W).s5.L.Q.outB (tailAt P W).s5.L.M ((tailAt P W).b5 e).2 := rfl
theorem gAt_shL6 : (gatedEAt P.fp ((tailAt P W).b5 e).2 ((tailAt P W).b6 e).2).shL6 =
    ((tailAt P W).b6 e).2.vals false := rfl
theorem gAt_shR6 : (gatedEAt P.fp ((tailAt P W).b5 e).2 ((tailAt P W).b6 e).2).shR6 =
    ((tailAt P W).b6 e).2.vals true := rfl
theorem gAt_b6 : (gatedEAt P.fp ((tailAt P W).b5 e).2 ((tailAt P W).b6 e).2).β6 =
    (tailAt P W).s6.L.Q.outB (tailAt P W).s6.L.M ((tailAt P W).b6 e).2 := rfl

end Reads

/-! ## The six clauses of the three product layers -/

section Clauses

variable [scl : Scl] {M X : Type} (P : FullPar Cb.Gl.E M X) {R : TailR} (W' : TailM (tailF P) R)
  (k : Ks) (t : Tape) (nz : NzT (tailF P) k t) (a : Adds7 (tailF P)) (x : P.XT)
  (mask : ℕ → Cb.Gl.E) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) {J₂ : Type}

/-- FrontDict.sqL: the left end value of the product layer of the squares. -/
theorem sqL_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d1 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k1 rho C order F (k.tc1 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w1.num false = 0) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((namesAt P.nr U).mL) = mask L.sL) :
    (Hl.worldOf gl mask entry).slot L.sL =
      (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).shL -
        (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).β1 *
          y ((namesAt P.nr U).mL) := by
  have s := stgT_level_slot W'.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1 O mask entry hF h lH
    false (e := 0) (by omega) hnum
  rw [eAt_shL, eAt_b1, hy]
  exact s

/-- FrontDict.sqR: the right end value. -/
theorem sqR_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d1 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k1 rho C order F (k.tc1 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w1.num true = 1) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((namesAt P.nr U).mR) = mask L.sR) :
    (Hl.worldOf gl mask entry).slot L.sR =
      (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).shR -
        (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).β1 *
          y ((namesAt P.nr U).mR) := by
  have s := stgT_level_slot W'.w1.num k.k1 (k.tc1 t) nz.b1 a.st1 a.t1 O mask entry hF h lH
    true (e := 1) (by omega) hnum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard h
  rw [eAt_shR, eAt_b1, hy, hsR]
  exact s

/-- FrontDict.g5L: the left end value of the first product layer of the gated products. -/
theorem g5L_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d5 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k5 rho C order F (k.tc5 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w5.num false = 0)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mL5) = mask L.sL) :
    (Hl.worldOf gl mask entry).slot L.sL =
      (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).shL5 -
        (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).β5 *
          y ((gNamesAt P.fp U).mL5) := by
  have s := stgT_level_slot W'.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5 O mask entry hF h lH
    false (e := 0) (by omega) hnum
  rw [gAt_shL5, gAt_b5, hy]
  exact s

/-- FrontDict.g5R: its right end value. -/
theorem g5R_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d5 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k5 rho C order F (k.tc5 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w5.num true = 1)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mR5) = mask L.sR) :
    (Hl.worldOf gl mask entry).slot L.sR =
      (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).shR5 -
        (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).β5 *
          y ((gNamesAt P.fp U).mR5) := by
  have s := stgT_level_slot W'.w5.num k.k5 (k.tc5 t) nz.b5 a.st5 a.t5 O mask entry hF h lH
    true (e := 1) (by omega) hnum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard h
  rw [gAt_shR5, gAt_b5, hy, hsR]
  exact s

/-- FrontDict.g6L: the left end value of the second product layer. -/
theorem g6L_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d6 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k6 rho C order F (k.tc6 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w6.num false = 0)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mL6) = mask L.sL) :
    (Hl.worldOf gl mask entry).slot L.sL =
      (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).shL6 -
        (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).β6 *
          y ((gNamesAt P.fp U).mL6) := by
  have s := stgT_level_slot W'.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6 O mask entry hF h lH
    false (e := 0) (by omega) hnum
  rw [gAt_shL6, gAt_b6, hy]
  exact s

/-- FrontDict.g6R: its right end value. -/
theorem g6R_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d6 p) {rho : Array E} {C : Aff}
    {order : List ℕ} {F G : Fork} {u : Tape} {L : Level} (hF : Sized F)
    (h : Fl.levelIn k.k6 rho C order F (k.tc6 t) = some (L, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnum : W'.w6.num true = 1)
    (U : GatedReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E) (hy : y ((gNamesAt P.fp U).mR6) = mask L.sR) :
    (Hl.worldOf gl mask entry).slot L.sR =
      (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).shR6 -
        (gatedEAt P.fp ((tailF P).b5 ((tailT W' k t nz a).z7 x)).2
        ((tailF P).b6 ((tailT W' k t nz a).z7 x)).2).β6 *
          y ((gNamesAt P.fp U).mR6) := by
  have s := stgT_level_slot W'.w6.num k.k6 (k.tc6 t) nz.b6 a.st6 a.t6 O mask entry hF h lH
    true (e := 1) (by omega) hnum
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsR, _⟩ := levelIn_heard h
  rw [gAt_shR6, gAt_b6, hy, hsR]
  exact s

/-- LedDict.slot2: the end values of the token sumcheck of the row products. nn: how many end values
the call lays. -/
theorem slot2_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d2 p) {Pt : Array E} {nn dY : ℕ}
    {F G : Fork} {u : Tape} {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : Fl.tscIn Pt k.k2 nn dY F ((k.tcP t).drop 1) = some (o, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (hnn : 4 * P.D.nNu ≤ nn)
    (hnum : ∀ q : Fin P.D.nNu × Fin 4, W'.w2.num q = (finProdFinEquiv q : ℕ)) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 4 * P.D.nNu → y ((namesAt P.nr U).m2 n) = mask (o.sEnd + n)) :
    ∀ n, n < 4 * P.D.nNu → (Hl.worldOf gl mask entry).slot (o.sEnd + n) =
      (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).sh2 n -
        (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).β2 *
          y ((namesAt P.nr U).m2 n) := by
  intro n hn
  have hn' : n < P.D.nNu * 4 := by omega
  have s := stgT_slot W'.w2.num k.k2 ((k.tcP t).drop 1) nz.b2 a.st2 a.t2 O
    (finProdFinEquiv.symm ⟨n, hn'⟩) (e := n) (by rw [hnum, Equiv.apply_symm_apply])
    (tsc_slot gl mask entry hF h lH (by omega))
  rw [eAt_sh2, dif_pos hn', eAt_b2, hy n hn]
  exact s

/-- FrontDict.batCl: the claimed sum of the token sumcheck of the row products. -/
theorem batCl_at {Pt : Array E} {nn dY : ℕ} {F G : Fork} {u : Tape} {o : OnBytes.Model.Tsc}
    (hF : Sized F) (h : Fl.tscIn Pt k.k2 nn dY F ((k.tcP t).drop 1) = some (o, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E) (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : y ((namesAt P.nr U).mCl) = mask F.next) :
    (Hl.worldOf gl mask entry).slot o.sCl =
      (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).shCl - y ((namesAt P.nr U).mCl) := by
  rw [eAt_shCl, hy, tsc_cl gl mask entry hF h lH]
  rfl

/-- LedDict.slotW: the sums' scalars. The run that lays them: the words that the tape's first round
sent, under the factor 1. -/
theorem slotW_at {F G : Fork} {first : ℕ} {vW : Array E} (hF : Sized F)
    (h : F.hideRun first vW oneE = some G) (hv : vW.toList = sentOf t)
    (hsz : 9 * P.D.nNu ≤ vW.size) {Hl : Fork} (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 9 * P.D.nNu → y ((namesAt P.nr U).mW n) = mask (first + n)) :
    ∀ n, n < 9 * P.D.nNu → (Hl.worldOf gl mask entry).slot (first + n) =
      (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).shW n -
        y ((namesAt P.nr U).mW n) := by
  intro n hn
  have hn' : n < P.D.nNu * 9 := by omega
  rw [eAt_shW, dif_pos hn', hy n hn, run_slot gl mask entry hF h lH (i := n) (by omega), hv, gl.one,
    one_mul]
  rfl

/-- LedDict.slotP: the products' scalars: as slotW_at, on the tape from the products' round on. -/
theorem slotP_at {F G : Fork} {first : ℕ} {vP : Array E} (hF : Sized F)
    (h : F.hideRun first vP oneE = some G) (hv : vP.toList = sentOf (k.tcP t))
    (hsz : 7 * P.D.nNu ≤ vP.size) {Hl : Fork} (lH : Fo.Later G Hl) (zt : ℕ → Cb.Gl.E)
    (U : NormsReads J₂) (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < 7 * P.D.nNu → y ((namesAt P.nr U).mP n) = mask (first + n)) :
    ∀ n, n < 7 * P.D.nNu → (Hl.worldOf gl mask entry).slot (first + n) =
      (eAt P.toOwnPar P.wPart ((tailT W' k t nz a).z7 x) zt).shP n -
        y ((namesAt P.nr U).mP n) := by
  intro n hn
  have hn' : n < P.D.nNu * 7 := by omega
  rw [eAt_shP, dif_pos hn', hy n hn, run_slot gl mask entry hF h lH (i := n) (by omega), hv, gl.one,
    one_mul]
  rfl

/-- TermsDict.slot: the end values of the sumcheck of the terms. -/
theorem slotT_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d3 p) {Pt : Array E} {nn dY : ℕ}
    {F G : Fork} {u : Tape} {o : OnBytes.Model.Tsc} (hF : Sized F)
    (h : Fl.tscIn Pt k.k3 nn dY F (((k.tcP t).drop 1).drop (k.k2 + 3)) = some (o, G, u))
    {Hl : Fork} (lH : Fo.Later G Hl) (hnn : P.D.nNu + P.D.ne + P.D.ne * P.D.nx ≤ nn)
    (hnum : ∀ q : ShA P.D, W'.w3.num q = numA P.D q) (U : TermsReads J₂)
    (y : P.J ⊕ J₂ → Cb.Gl.E)
    (hy : ∀ n, n < P.D.nNu + P.D.ne + P.D.ne * P.D.nx →
      y ((namesT P.tp U).mT n) = mask (o.sEnd + n)) :
    ∀ n, n < P.D.nNu + P.D.ne + P.D.ne * P.D.nx →
      (Hl.worldOf gl mask entry).slot (o.sEnd + n) =
        (termsEAt P.tp ((tailF P).b3 ((tailT W' k t nz a).z7 x)).2).sh n -
          (termsEAt P.tp ((tailF P).b3 ((tailT W' k t nz a).z7 x)).2).β *
            y ((namesT P.tp U).mT n) := by
  intro n hn
  obtain ⟨q, rfl⟩ := numA_surj hn
  have s := stgT_slot W'.w3.num k.k3 (((k.tcP t).drop 1).drop (k.k2 + 3)) nz.b3 a.st3 a.t3 O q
    (hnum q) (tsc_slot gl mask entry hF h lH (by omega))
  rw [tAt_sh, pick_num, tAt_b, hy _ hn]
  exact s

/-- The premises hA and hB of stack_port: end value q of the batched sumcheck, number e. μ: what the
messages hold at the mask entry's name. -/
theorem stack_at {p : Psc} (O : OutIs gl (tailT W' k t nz a).d4 p) {Pp : Pub} {v : Env} {H : Heard}
    {NCLp : ℕ} {F G : Fork} {u : Tape} {S : HeardStack} (hF : Sized F)
    (h : hearStack engFl Pp v H k.k4 NCLp F (k.tc4 t) = some (S, G, u)) {Hl : Fork}
    (lH : Fo.Later G Hl) (q : IA P.D ⊕ IB P.D) {e : ℕ} (he : e < 2 + (1 + Pp.y.LamM) + NCLp)
    (hnum : W'.w4.num q = e) {μ : Cb.Gl.E} (hμ : μ = mask (S.sA0 + e)) :
    (Hl.worldOf gl mask entry).slot (S.sA0 + e) =
      ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2.vals q -
        P.ip.inn.Kp.outB P.ip.inn.Mk ((tailF P).b4 ((tailT W' k t nz a).z7 x)).2 * μ := by
  have s := stgT_slot W'.w4.num k.k4 ((k.tc4 t).drop 1) nz.b4 a.st4 a.t4 O q hnum
    (stack_slot gl mask entry hF h lH he)
  rw [hμ]
  exact s

end Clauses

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.slot_at
#print axioms OnBytes.Road.K4.run_slot
#print axioms OnBytes.Road.K4.level_slot
#print axioms OnBytes.Road.K4.tsc_slot
#print axioms OnBytes.Road.K4.tsc_cl
#print axioms OnBytes.Road.K4.stack_slot
#print axioms OnBytes.Road.K4.stgT_slot
#print axioms OnBytes.Road.K4.numA_surj
#print axioms OnBytes.Road.K4.stgT_level_slot
#print axioms OnBytes.Road.K4.eAt_shL
#print axioms OnBytes.Road.K4.eAt_shR
#print axioms OnBytes.Road.K4.eAt_b1
#print axioms OnBytes.Road.K4.eAt_sh2
#print axioms OnBytes.Road.K4.eAt_b2
#print axioms OnBytes.Road.K4.eAt_shCl
#print axioms OnBytes.Road.K4.eAt_shW
#print axioms OnBytes.Road.K4.eAt_shP
#print axioms OnBytes.Road.K4.tAt_sh
#print axioms OnBytes.Road.K4.tAt_b
#print axioms OnBytes.Road.K4.gAt_shL5
#print axioms OnBytes.Road.K4.gAt_shR5
#print axioms OnBytes.Road.K4.gAt_b5
#print axioms OnBytes.Road.K4.gAt_shL6
#print axioms OnBytes.Road.K4.gAt_shR6
#print axioms OnBytes.Road.K4.gAt_b6
#print axioms OnBytes.Road.K4.sqL_at
#print axioms OnBytes.Road.K4.sqR_at
#print axioms OnBytes.Road.K4.g5L_at
#print axioms OnBytes.Road.K4.g5R_at
#print axioms OnBytes.Road.K4.g6L_at
#print axioms OnBytes.Road.K4.g6R_at
#print axioms OnBytes.Road.K4.slot2_at
#print axioms OnBytes.Road.K4.batCl_at
#print axioms OnBytes.Road.K4.slotW_at
#print axioms OnBytes.Road.K4.slotP_at
#print axioms OnBytes.Road.K4.slotT_at
#print axioms OnBytes.Road.K4.stack_at
