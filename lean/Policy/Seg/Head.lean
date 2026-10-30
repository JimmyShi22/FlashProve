-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/Head.lean

The conditions of the head with the cost ledger (Policy/Rel/LedgerHead.lean) as families of
Cb/Req/ReqSpec.lean, over p = 2^64 - 2^32 + 1.

Definitions and three statements; the proofs are in Policy/Seg/HeadProofs.lean. `segHeadPol s pol`
has 9 families of keys and 21 of identities; `segHeadPolY s pol`, the last segment, has the identity
"y = 0 if e < 1,024" in front.
From the plain head's file Cm/TargetSegHead.lean come the 17 identities of the final normalisation,
the families NF, NFH, HD1, HD2, CNF and the plain margin. Written here: ROW on 120 bytes; HD0 with
the ledger's term in the margin; HE0, HE1; the ledger's identities (B4), (Z), (B2), (B3).
The policy's three numbers stand in (B4), (B2), (B3) alone: C in a public coefficient of (B4) and in
the affine form of the cell atom of (B2), θ and cap in public coefficients of (B2) and (B3).
HD0 is divided by 2^23 in the field and looked up in `R16`, where the relation has the key undivided
in 2^23 · [0, 2^16): it is the same condition (`LedgerHead.inLut_R23_iff`,
Policy/Rel/LedgerThirdDigit.lean), and the glued segment has at most four families of keys, not five.


Limits: definitions and statements only. Nothing on the request's form r < e, on bounds of cells, or
on protocols. That the definitions of Inst/Model/Head/, which the families mirror, are the programs'
has been compared by reading, not in Lean (the head of Inst/Model/Head/Trace.lean).
-/
import Policy.Rel.LedgerRel
import Policy.Seg.Dict
import Cm.TargetSegHeadY

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

noncomputable section

/-! ## Forms -/

/-- ex (3 cells of hf, + 8,421,505): the value looked up at the middle digit -/
def cEx (v i : ℕ) : CForm Gl.E := cK 8421505 + TS.cRd 3 fun l => TS.cHf (Head.fEx l v) i

/-- the n ledger bytes from byte a on, at position i, low byte first -/
def cHid (a n i : ℕ) : CForm Gl.E := lb256 (fun m => TS.cDv m i) a n

/-- d1 + 2^16 ex at the token v -/
def cHe (v i : ℕ) : CForm Gl.E := TS.cD1 v i + ((2 : Gl.E) ^ 16) • cEx v i

/-! ## Public tables -/

/-- ρ_i and ρC_i of the request, at the position of a vertex -/
def rhoP : XI → ℕ → Gl.E := fun x b => (((Cm.reqOf x).rho (vi b) : ℤ) : Gl.E)
def rhoCP : XI → ℕ → Gl.E := fun x b => (((Cm.reqOf x).rhoC (vi b) : ℤ) : Gl.E)
/-- ρC_i at the live vertices of a family on the vocabulary -/
def rhoCT : XI → ℕ → Gl.E := fun x b => if va 18 b < 202048 then rhoCP x b else 0
/-- ρ_i at the live vertices of HE1 -/
def rhoE1 : XI → ℕ → Gl.E := fun x b => if va 17 b < 70976 then rhoP x b else 0

/-! ## The keys -/

/-- The margin with the ledger's term: the mirror of `Head.mg`. -/
def mgPolEx : Ex1 XI Gl.E :=
  TS.mgEx + Ex.sc rhoCT (aff fun b => cHid 99 5 (vi b) + ((2 : Gl.E) ^ 37) • cHid 104 1 (vi b))

/-- The keys as expressions: the mirror of `LedgerHead.key`, but at HD0, where the key is divided by
2^23 in the field. -/
def keyExPol (np : NormPar) : Head.Fam → Ex1 XI Gl.E
  | .NF => TS.keyEx np .NF
  | .NFH => TS.keyEx np .NFH
  | .HD0 => ((2 : Gl.E) ^ 23)⁻¹ • (mgPolEx - ((2 : Gl.E) ^ 8) • TS.k1Ex - TS.k2Ex)
  | .HD1 => TS.k1Ex
  | .ROW => aff (TS.gd 7 120 fun n i => (((Ledger.mu n : ℤ) : Gl.E)) • TS.cDv n i)
  | .HD2 => TS.k2Ex
  | .HE0 => aff (TS.gd 17 131072 cHe) + (32896 : Gl.E) • Ex.pub rhoP
  | .HE1 =>
    aff (fun b =>
        if va 17 b < 70976 then cHe (131072 + va 17 b) (vi b) else cK (((FE.row 0 : ℤ) : Gl.E))) +
      (32896 : Gl.E) • Ex.pub rhoE1
  | .CNF => TS.keyEx np .CNF

/-- the number of variables for the index of a family -/
def vxPol : Head.Fam → ℕ
  | .NF => 13 | .NFH => 13 | .HD0 => 18 | .HD1 => 18 | .ROW => 7 | .HD2 => 18 | .HE0 => 17
  | .HE1 => 17 | .CNF => 13

/-- the logarithm of the number of rows of a family's table -/
def tabLogPol : Head.Fam → ℕ
  | .ROW => 8 | .HD2 => 8 | _ => 16

def keyFamPol (np : NormPar) (f : Head.Fam) : Fam XI Gl.E := Ex1.fam (vxPol f + 10) (keyExPol np f)

/-- the table of a family: that of Inst/Model/Head/Trace.lean: at HD0 the range table of width 16 -/
def keyTabPol (f : Head.Fam) : Tab Gl.F := tabOf (Head.tableOf f) (tabLogPol f)

def allFamPol : List Head.Fam := [.NF, .NFH, .HD0, .HD1, .ROW, .HD2, .HE0, .HE1, .CNF]

/-! ## The ledger's four identities -/

/-- `ex` at the inner vertex b' = i · 2^18 + v of a sum over the vocabulary; 0 at dead tokens -/
def exIn : ℕ → CForm Gl.E := fun b' =>
  if b' % 2 ^ 18 < 202048 then cEx (b' % 2 ^ 18) (b' / 2 ^ 18 % 2 ^ 10) else cK 0

/-- (B4) at position i: ρC_i (c_i + k_i - C): the mirror of `Head.dB4` -/
def jB4Ex (pol : AcceptancePolicy) : Ex1 XI Gl.E :=
  Ex.sc rhoCP
    (aff (fun b => cHid 99 5 (vi b) + cHid 110 5 (vi b)) - Ex.con ((pol.C : ℕ) : Gl.E))

/-- (Z) at position i: ρC_i (zs_i + Σ_v ex_i[v] - 2^24): the mirror of `Head.dZ` -/
def jZEx : Ex1 XI Gl.E :=
  Ex.sc rhoCP
    (aff (fun b => cHid 117 3 (vi b)) + sumA 10 18 (aff0 exIn) - Ex.con ((2 : Gl.E) ^ 24))

/-- (B2): Σ_i ρC_i (c_i + C b_i + u_i) - θ NB: the mirror of `Head.sB2` -/
def sB2Ex (pol : AcceptancePolicy) : Ex1 XI Gl.E :=
  sumA 0 10
      (Ex.sc rhoCP
        (aff0 fun b' =>
          cHid 99 5 (vi b') + ((pol.C : ℕ) : Gl.E) • cHid 104 1 (vi b') + cHid 105 5 (vi b'))) -
    Ex.pub fun x _ => ((pol.theta : ℕ) : Gl.E) * (((Cm.reqOf x).NB : ℕ) : Gl.E)

/-- (B3): Σ_i ρC_i (b_i + z_i) - cap [NB > 0]: the mirror of `Head.sB3` -/
def sB3Ex (pol : AcceptancePolicy) : Ex1 XI Gl.E :=
  sumA 0 10 (Ex.sc rhoCP (aff0 fun b' => cHid 104 1 (vi b') + cHid 115 2 (vi b'))) -
    Ex.pub fun x _ => if 0 < (Cm.reqOf x).NB then ((pol.cap : ℕ) : Gl.E) else 0

def jB4Fam (pol : AcceptancePolicy) : Fam XI Gl.E := Ex1.fam 10 (jB4Ex pol)
def jZFam : Fam XI Gl.E := Ex1.fam 10 jZEx
def sB2Fam (pol : AcceptancePolicy) : Fam XI Gl.E := Ex1.fam 0 (sB2Ex pol)
def sB3Fam (pol : AcceptancePolicy) : Fam XI Gl.E := Ex1.fam 0 (sB3Ex pol)

def ledgerIdn (pol : AcceptancePolicy) : List (Fam XI Gl.E) := [jB4Fam pol, jZFam, sB2Fam pol, sB3Fam pol]

/-! ## The segment -/

/-- The head's segment. -/
def segHeadPol (s : Cm.Scales) (pol : AcceptancePolicy) : SegSpec XI Gl.F Gl.E where
  rowsLog := Cm.Seg.rowsLog 24
  cols := Cm.Seg.cols 24
  idn := (List.range 17).map (TS.idnFam s.nf) ++ ledgerIdn pol
  keys := allFamPol.map fun f => (keyFamPol s.nf f, keyTabPol f)

/-- A segment with the identity "y = 0 if e < T" in front. -/
def withY (S : SegSpec XI Gl.F Gl.E) : SegSpec XI Gl.F Gl.E := { S with idn := TS.idY :: S.idn }

/-- The last segment. -/
def segHeadPolY (s : Cm.Scales) (pol : AcceptancePolicy) : SegSpec XI Gl.F Gl.E := withY (segHeadPol s pol)

end

/-! ## What is stated of it -/

/-- The head's clauses of `LedgerRel.Cond Gl.p`, but for the one on y, at integer cells t: every key
is an entry of its table, the 17 identities and the ledger's four are 0. -/
def HeadCl (np : NormPar) (pol : AcceptancePolicy) (W : Mat) (x : XI) (t : Head.Cells ℤ) : Prop :=
  (∀ f a i, a < Head.len f → i < Head.nT →
    Head.InLut (LedgerHead.tableOf f)
      (LedgerHead.key np (t.cast Gl.F) (Cm.TP.castH Gl.p W) (Head.Req.of pol x) f a i)) ∧
  (∀ i < Head.nT, ∀ k < 17, Head.N.idn np (t.cast Gl.F) i k = 0) ∧
  (∀ i < Head.nT,
    Head.dB4 (t.cast Gl.F) (Head.Req.of pol x) i = 0 ∧
    Head.dZ (t.cast Gl.F) (Head.Req.of pol x) i = 0) ∧
  (Head.sB2 (t.cast Gl.F) (Head.Req.of pol x) = 0 ∧ Head.sB3 (t.cast Gl.F) (Head.Req.of pol x) = 0)

namespace Spec

/-- States: every family of `segHeadPol s pol` is well formed at the format `TS.fmtRef`. -/
def headPol_wf : Prop := ∀ (s : Cm.Scales) (pol : AcceptancePolicy), (segHeadPol s pol).WF TS.fmtRef

/-- States: every place that `segHeadPol s pol` reads is one that the dictionary at `Hd.main` lets
the last segment read. -/
def headPol_places : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy), ∀ q ∈ (segHeadPol s pol).places, q ∈ reads Hd.main 24

/-- States: for integer matrices M of cells, an integer index matrix and integer cells t with
`ReadsAtMain t M`, the segment's conditions hold if and only if the head's clauses `HeadCl` hold at
t. -/
def headPol_holds_int : Prop :=
  ∀ (s : Cm.Scales) (pol : AcceptancePolicy) (x : XI) (Wz : Mat) (M : ℕ → ℕ → ℕ → ℤ) (t : Head.Cells ℤ),
    ReadsAtMain t M →
    ((segHeadPol s pol).Holds TS.fmtRef x (fun y c => ((Wz y c : ℤ) : Gl.F))
        (Partition.castM (E := Gl.E) M) ↔
      HeadCl s.nf pol Wz x t)

end Spec

end Policy
