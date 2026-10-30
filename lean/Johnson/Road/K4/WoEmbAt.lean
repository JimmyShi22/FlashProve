-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/WoEmbAt.lean: THE PREMISE (HE) OF `woSaysF_at_ledG`
(Johnson/Road/K4/WoAtLedFirst.lean), AT A HEARING OF K4's TEXT IN THE FIRST GROUP: the pair that the
first group's typed merge adds (`tenEF`, Cb/Pv/Lay/End/FirstShare.lean), at the claims' state read
off the tape, and the embedding's claim as the hearing's text makes it (`claimE` at what was heard)
say the same of every matrix W. Two statements and their proofs.

  `tenEmb_claim_at`: `tenEmb_claim` (Johnson/Road/K4/TenEmbClaim.lean) at parameters, a number of
    column bits, two sizes and a vocabulary that are the library's reference ones and the layout's
    BY EQUATIONS, not by their text.
  `he_of_hear`: where the hearing returns in the first group: for every cE that `claimE` returns at
    o.H.ZE, o.H.tkh, P.V and P.tokv, and every W: `tval (tenEF Pf (aS7 …).1.1) (matOf W) = claimVal
    gl P.wsLay W cE`.

NO NEW ARGUMENT: `tenEmb_claim`; `aS7F_parts` (the claims' state is `st7F` at the first statement x:
its two points are x's, its tokens the value's at x); `emb_hear`, `emb_hear_sizes`
(Johnson/Road/K4/EmbHear.lean: the two arrays are what the tape's second and third round drew);
`nat_rd`, `pt_toArray` (EmbJoin.lean).

Limits. AT THE LIBRARY's REFERENCE PARAMETERS ALONE: hP: Pf.D.P = ppref; hkW: Pf.kW = kRef; hV: P.V
= ppref's vocabulary. PREMISES beside these: the hearing's return, in the first group; three sizes
of the value are the layout's (hls, hgB, hlt); x's two further points are the readings of what the
tape's second and third round drew (hxa, hxb); htok: THE VALUE's TOKENS AT x ARE THE PUBLIC RECORD's
ARRAY P.tokv on the 2 ^ lT positions; the layout of the weights is what `wsLayOf` returns at a shape
with the library's numbers; `EmbNums` (public numbers of the layers' layout). The tape t, k, nz and
g7 of the state are letters: of the state only what `st7F` lays off x is read. An identity on public
data and any matrix W: nothing on which matrix is committed, on whose tokens the array holds, on a
draw or on soundness.
-/
import Johnson.Road.K4.WoAtLedFirst
import Johnson.Road.K4.TenEmbClaim
import Johnson.Road.K4.EmbJoin
import Johnson.Road.K4.EmbHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Reading Fork WsShape WsClaim wsLayOf)
open OnBytes.Model.Layer (Pub HPlan2 Own ClaimEnv)
open OnBytes.Desc.First.K4 (hear engFl envOf)
open OnBytes.Desc.First.P1 (gl Ks NzT TailM TailR Tg7 aS7 drawnOf)
open OnBytes.Slice (GE)
open Inst.Model (Scl Params ppref)
open Inst.Model.Layout (kRef units off)
open Cb.Pv.Lay.At (tval tenEmb)
open Meaning.Emb (EmbNums)

/-- `tenEmb_claim` at letters that are the reference parameters and the layout's sizes by
equations. -/
theorem tenEmb_claim_at {K : Type} [Field K] (ρ : Reading K) (c : ClaimEnv) (s : WsShape)
    (pp : Params) (k lt ls V : ℕ) (hpp : pp = ppref) (hk' : k = kRef) (hlt : lt = c.v.y.h.lt)
    (hls : ls = c.v.y.ls) (hV : V = ppref.V) (Z : SizedW s pp)
    (hl : wsLayOf s true k = .ok c.wsLay) (N : EmbNums c.v.y) {ZE tkh : Array E}
    {tokv : Array ℕ} {cl : WsClaim} (hZ : ZE.size = c.v.y.ls + c.v.y.h.lt)
    (hk : tkh.size = c.v.y.lPd - c.v.y.ls) (h : c.claimE ZE tkh V tokv = some cl)
    {hh gB : ℕ} {pa pb : ℕ → K} {tok : ℕ → ℕ} (hgB : gB = c.v.y.lPd - c.v.y.ls)
    (hpa : ∀ j, j < ls + lt → pa j = pt ρ ZE j) (hpb : ∀ j, j < gB → pb j = pt ρ tkh j)
    (htok : ∀ p, p < 2 ^ lt → tok p = tokv.getD p 0)
    (hH : off k (units pp) (units pp).length ≤ hh) (W : ℕ → ℕ → K) :
    tval (tenEmb pp k hh lt ls gB pa pb tok) (Inst.Model.Layout.Tensor.matOf W) =
      claimVal ρ c.wsLay W cl := by
  subst hpp hk' hlt hls hV
  exact tenEmb_claim ρ c s Z hl N hZ hk h hgB hpa hpb htok hH W

variable [scl : Scl] {P : Pub} {hp : HPlan2} {g : ℕ} {fo : OnBytes.Model.Forest.Heard} {o : Own}
  {F G : Fork} {t0 u : Tape}
  {M X0 : Type} (Pf : FullFPar GE M X0) {R : TailR} (W' : TailM (tailW Pf) R)

/-- **The added pair and the embedding's claim say the same of every matrix, at a hearing in the
first group.** -/
theorem he_of_hear (h : hear engFl P hp g fo F t0 = some (o, G, u)) (hg : (g == 0) = true)
    (k : Ks) (t : Tape) (nz : NzT (tailW Pf) k t) (x : Pf.ofp.fs.X3) (g7 : Tg7)
    (hP : Pf.D.P = ppref) (hkW : Pf.kW = kRef) (hV : P.V = ppref.V)
    (hls : P.y.ls = Pf.ls) (hgB : P.y.lPd - P.y.ls = Pf.gB) (hlt : P.y.h.lt = Pf.D.lT)
    (hxa : x.1.2 = Johnson.L5.Layers.rd gl (Pf.ls + Pf.D.lT) (drawnOf (t0.drop 1)))
    (hxb : x.2 = Johnson.L5.Layers.rd gl Pf.gB (drawnOf ((t0.drop 1).drop 1)))
    (htok : ∀ p, p < 2 ^ Pf.D.lT → Pf.tok (Pf.ofp.fs.x0F x) p = P.tokv.getD p 0)
    {s : WsShape} (Z : SizedW s Pf.D.P) (hl : wsLayOf s true Pf.kW = .ok P.wsLay)
    (N : EmbNums P.y) (cE : WsClaim)
    (hE : (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE) (W : ℕ → ℕ → GE) :
    tval (tenEF Pf (aS7 W' k t nz x g7).1.1) (Inst.Model.Layout.Tensor.matOf W) =
      claimVal gl P.wsLay W cE := by
  obtain ⟨_, ey, aZ, _, aT, _⟩ := emb_hear hg h
  obtain ⟨sZ, sT⟩ := emb_hear_sizes hg h
  rw [(aS7F_parts Pf W' k t nz x g7).1]
  have ey' : (envOf P o).v.y = P.y := ey
  exact tenEmb_claim_at gl (envOf P o) s Pf.D.P Pf.kW Pf.D.lT Pf.ls P.V hP hkW
    (by rw [ey']; exact hlt.symm) (by rw [ey']; exact hls.symm) hV Z hl (by rw [ey']; exact N)
    (by rw [ey']; exact sZ) (by rw [ey']; exact sT) hE (by rw [ey']; exact hgB.symm)
    (fun j hj => by
      show Blocks.nat x.1.2 j = _
      rw [aZ, pt_toArray, hxa, nat_rd _ hj])
    (fun j hj => by
      show Blocks.nat x.2 j = _
      rw [aT, pt_toArray, hxb, nat_rd _ hj])
    htok Pf.hH W

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tenEmb_claim_at
#print axioms OnBytes.Road.K4.he_of_hear
