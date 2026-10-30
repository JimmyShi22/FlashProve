-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Inner.lean: the parameters of the batched sumcheck of the inner products of a layers'
sub-proof (Cb/Pv/Lay/Inner.lean) at a value: the panels of the library's description of a group of
layers (Inst/Model/FF/Objects.lean).

The two long vectors hold the panels as blocks (Cb/Pv/Lay/At/PanPlace.lean). Each side is made of
pieces (Cb/Pv/Lay/At/Pieces.lean). First side: one piece for all that is a form in the cells; the
vector of the gated products, on the block of the panel D; for each layer with routed experts the
vector of its routed gated products, laid into the rows of the panel Dr under public factors that
hold the shown entries of the selector. Second side: one piece for all that is a form in the cells;
one piece for each row of a panel with weights and two factors; one for each panel with three
factors. On the panel D the call's and the rows' weights stand on the second side, so that the first
side holds the vector of the gated products itself.

Main names:
  `InnPar0`: what stays free beside the letters of Cb/Pv/Lay/At/Terms.lean.
  `IA`, `IB`: the names of the pieces. `sideA`, `sideB`: the two families of pieces.
  `InnPar0.par`, `InnPar0.inn`: the parameters. The state is St4 (Cb/Pv/Lay/At/Start.lean).
  `inn_hc`: the sum of the summand over the cube is the matrix products' side of the lookup's join
  plus the drawn element times the kept part of the sumcheck of the terms.
Limits: inn_hc asks that an expert has no more hidden units than a layer. That the programs'
vectors and factors are these is not said here. Nothing is said on an honest prover, on completeness
or on zero knowledge.


-/
import Cb.Pv.Lay.At.Terms
import Cb.Pv.Lay.At.Pieces
import Cb.Pv.Lay.At.InnerGeo
import Cb.Pv.Lay.At.Start
import Cb.Pv.Lay.At.Line
import Cb.Pv.Lay.End.Sig0

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Cb Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Pan Rd rdTrue pans offP lamS Sig0 Sig1 wc call hhU zpos Hh1t fSh)
open Cb.Pv.Lay.End.Sig (off_inside pans_nodup sum_om sig0_acc)

noncomputable section

/-! ### What stays free -/

/-- The letters of the batched sumcheck that stay free, beside those of the sumcheck of the
terms. -/
structure InnPar0 (E : Type) [Field E] [Fintype E] [scl : Scl] where
  /-- the letters of the sumcheck of the terms -/
  T : TermPar0 E
  /-- the affine side of the lookup's join as a form in the entries -/
  lnTg : (ℕ → E) → E
  lnInc : (ℕ → E) → T.J → E
  /-- the masks: the hiding polynomial's coefficients; the end values' -/
  wI : PIdx (ldPartFmt E (kS T.D) (fun _ => 2) ++ [pDummy E 2]) → T.J
  cI : IA T.D ⊕ IB T.D → T.J

variable {E : Type} [Field E] [Fintype E] [scl : Scl]

namespace InnPar0
variable (P : InnPar0 E)

abbrev D : Dim := P.T.D
abbrev tb : Tables := P.T.tb
abbrev L0 : ℕ := P.T.L0
abbrev J : Type := P.T.J
abbrev rd : (P.J → E) → Cell → E := P.T.rd
abbrev rw : (P.J → E) → ℕ → LW E := P.T.rw

/-- The sumcheck of the terms. -/
abbrev Y3 : PscPar E := P.T.tm.toSum.T.par

/-- The states. -/
abbrev St : Type := St4 E P.J P.Y3.Out

/-- The end point of the sumcheck of the terms. -/
def rt (st : P.St) : ℕ → E := Blocks.nat (P.T.tm.Kp.outPt P.T.tm.Mk st.o3)

/-- The lookup's point that a panel reads: an early panel the state's; a late one that of the output
of the sumcheck of the terms. -/
def zP (st : P.St) (p : Pan) : ℕ → E := if p.late then st.o3.st else st.z

/-- The record of the early panels: the contractions at the lookup's token point, with the honest
gated products. -/
def rE (st : P.St) (m : P.J → E) : Rd E :=
  rdTrue P.D (P.rd m) st.z (P.rt st) (fun l j => hhU P.D (P.rd m) l j (zpos P.D st.z)) fun _ _ => 0

/-- The record of the late panels: the contractions at the end point of the sumcheck of the terms,
with what it has shown. -/
def rL (st : P.St) (m : P.J → E) : Rd E :=
  recV P.D (recAt P.D (P.rd m) st.o3.st (P.rt st)) st.o3.vals

def rP (st : P.St) (m : P.J → E) (p : Pan) : Rd E := if p.late then P.rL st m else P.rE st m

/-- The two factors of an entry of a panel, the first with all weights. -/
def FA (st : P.St) (m : P.J → E) (p : Pan) (ρ ι : ℕ) : E :=
  p.om st.β * wc P.D (P.zP st p) (call p.fam) * p.wt P.D (P.zP st p) ρ * p.A P.D (P.rP st m p) ρ ι
def FB (st : P.St) (m : P.J → E) (p : Pan) (ρ ι : ℕ) : E :=
  p.B P.D (P.rP st m p) P.tb P.L0 (P.rw m) (P.zP st p) (P.rt st) ρ ι

/-- A shown entry of the selector. -/
def selV (st : P.St) (l e : ℕ) : E :=
  if h : l < P.D.ne ∧ e < P.D.nx then st.o3.vals (.inr (.inr (⟨l, h.1⟩, ⟨e, h.2⟩))) else 0

/-- The public factors of the pieces of the first side. -/
def κA (st : P.St) : Pan → ℕ → E
  | .Dr l', e => st.β * wc P.D st.o3.st (call .D) * (Pan.Dr l').wt P.D st.o3.st e * P.selV st l' e
  | _, _ => 1

/-- The vectors of the pieces of the first side. -/
def vA (st : P.St) (m : P.J → E) : Pan → ℕ → E
  | .D => Hh1t P.D (P.rd m) (zpos P.D st.z)
  | .Dr l' => fun j => hhU P.D (P.rd m) (2 * l' + 1) (P.D.fe + j) (P.rt st)
  | _ => fun _ => 0

/-- The public factors of the pieces of the second side. -/
def κB (st : P.St) : Pan → ℕ → E
  | .D, ρ => wc P.D st.z (call .D) * Pan.D.wt P.D st.z ρ
  | _, _ => 1

/-- The first long vector on a panel's block. -/
def VA (st : P.St) (m : P.J → E) (p : Pan) : ℕ → E :=
  if isVirt p then
    (if p.three then fun t => if t / 2 ^ p.wcol P.D < p.nr P.D then
        P.κA st p (t / 2 ^ p.wcol P.D) * P.vA st m p (t % 2 ^ p.wcol P.D) else 0
      else fun t => P.κA st p 0 * P.vA st m p t)
  else cellOf P.D p (P.FA st m p)

/-- The second long vector on a panel's block. -/
def VB (st : P.St) (m : P.J → E) (p : Pan) : ℕ → E :=
  cellOf P.D p fun ρ ι => P.κB st p ρ * P.FB st m p ρ ι

/-- A panel's block of a long vector. -/
def onP (V : Pan → ℕ → E) (p : Pan) (y : ℕ) : E := blk (p.wid P.D) (nP P.D p) (V p) y

/-- The first side. -/
def sideA : PSide E P.St P.J (kS P.D) where
  I := IA P.D
  g := Sum.elim (fun _ => kS P.D) fun i => if i.1.1.three then i.1.1.wcol P.D else i.1.1.wid P.D
  n0 := Sum.elim (fun _ => 0) fun i =>
    if i.1.1.three then nP P.D i.1.1 * 2 ^ wrow P.D i.1.1 else nP P.D i.1.1
  R := Sum.elim (fun _ => 1) fun i => if i.1.1.three then i.1.1.nr P.D else 1
  κ := Sum.elim (fun _ _ _ => 1) fun i st e => P.κA st i.1.1 e
  v := fun st m => Sum.elim
    (fun _ y => ((pans P.D).map fun p => if isVirt p then 0 else P.onP (P.VA st m) p y).sum)
    fun i => P.vA st m i.1.1
  hg := fun i => by
    rcases i with _ | ⟨⟨p, hp⟩, _⟩
    · exact le_refl _
    · have hp' : p ∈ pans P.D := hp
      have h := wid_le P.D hp'
      show (if p.three then p.wcol P.D else p.wid P.D) ≤ kS P.D
      rw [kS_eq]
      split_ifs
      · rw [wid_eq] at h
        omega
      · exact h
  hn := fun i => by
    rcases i with _ | ⟨⟨p, hp⟩, _⟩
    · show 0 + 1 ≤ 2 ^ (kS P.D - kS P.D)
      rw [Nat.sub_self]
      exact le_refl _
    · have hp' : p ∈ pans P.D := hp
      show (if p.three then nP P.D p * 2 ^ wrow P.D p else nP P.D p) +
          (if p.three then p.nr P.D else 1) ≤
        2 ^ (kS P.D - if p.three then p.wcol P.D else p.wid P.D)
      rw [kS_eq]
      split_ifs
      · exact rows_lt P.D hp'
      · exact nP_lt P.D hp'

/-- The second side. -/
def sideB : PSide E P.St P.J (kS P.D) where
  I := IB P.D
  g := Sum.elim (fun _ => kS P.D) fun i => if i.1.1.three then i.1.1.wid P.D else i.1.1.wcol P.D
  n0 := Sum.elim (fun _ => 0) fun i =>
    if i.1.1.three then nP P.D i.1.1 else nP P.D i.1.1 * 2 ^ wrow P.D i.1.1 + i.2
  R := fun _ => 1
  κ := Sum.elim (fun _ _ _ => 1) fun i st _ => if i.1.1.three then 1 else P.κB st i.1.1 i.2
  v := fun st m => Sum.elim
    (fun _ y => ((pans P.D).map fun p => if p.weight then 0 else P.onP (P.VB st m) p y).sum)
    fun i => if i.1.1.three then P.VB st m i.1.1
      else fun ι => if ι < i.1.1.nc P.D then P.FB st m i.1.1 i.2 ι else 0
  hg := fun i => by
    rcases i with _ | ⟨⟨p, hp⟩, _⟩
    · exact le_refl _
    · have hp' : p ∈ pans P.D := hp
      have h := wid_le P.D hp'
      show (if p.three then p.wid P.D else p.wcol P.D) ≤ kS P.D
      rw [kS_eq]
      split_ifs
      · exact h
      · rw [wid_eq] at h
        omega
  hn := fun i => by
    rcases i with _ | ⟨⟨p, hp⟩, e⟩
    · show 0 + 1 ≤ 2 ^ (kS P.D - kS P.D)
      rw [Nat.sub_self]
      exact le_refl _
    · have hp' : p ∈ pans P.D := hp
      show (if p.three then nP P.D p else nP P.D p * 2 ^ wrow P.D p + e) + 1 ≤
        2 ^ (kS P.D - if p.three then p.wid P.D else p.wcol P.D)
      rw [kS_eq]
      by_cases h3 : p.three = true
      · rw [if_pos h3, if_pos h3]
        exact nP_lt P.D hp'
      · rw [if_neg h3, if_neg h3]
        have he : (e : ℕ) < p.nr P.D := Nat.lt_of_lt_of_le e.isLt (cntB_le P.D h3)
        have := rows_lt P.D hp'
        omega

open Classical in
/-- The two sides, with the start form of Cb/Pv/Lay/At/Start.lean. -/
def par : InnPar E where
  J := P.J
  k := kS P.D
  St := P.St
  a := P.sideA.side
  b := P.sideB.side
  inc := startInc P.Y3 P.lnInc P.T.rT
  tg := startTg P.Y3 P.lnTg
  wAt := P.wI
  cAt := P.cI

/-- The parameters of the batched sumcheck, at the value. -/
def inn : InnL E := P.par.inn

end InnPar0

end
end Cb.Pv.Lay.At
