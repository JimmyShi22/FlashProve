-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/FirstShare.lean: in the first layers' sub-proof: what the pull-backs of the ledgers of
the claims on the gated products, on the stream that comes in and of the merge, with the pending
row, pay of what the chain of the sub-proof's own rounds owes at its end.

Cb/Pv/Lay/At/OwnFirstW.lean has the chain of the first sub-proof's own rounds at a value. This file
reads the letters of the claims off a last statement e of that chain and pays the fields o5, o6 and
lW, o7 of the chain's bill (Cb/Pv/Lay/End/Last.lean); its fields c5, c6, c7 are True at this chain.

Main definitions: tailW (the chain's letters: tailFst of Cb/Pv/Lay/End/NormsFirst.lean at these
letters), stF (what the weights' stretch reads, off e), tenEF, rhsF (the pair of the claim that the
first group adds, and the other side of its identity: the arguments of FullFPar.wf).
Main theorems: gated_share_first, weights_share_first.

Limits: as Cb/Pv/Lay/End/GatedShare.lean, EmbShare.lean and MergeShare.lean. The pending row is a
premise.


-/
import Cb.Pv.Lay.At.OwnFirstW
import Cb.Pv.Lay.End.Last
import Cb.Pv.Lay.End.EmbShare
import Cb.Pv.Lay.End.MergeShare
import Cb.Pv.Lay.End.NormsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End.Gated

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Arr lF lFe xS)

noncomputable section

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullFPar E M X)
  {Nm J₂ : Type} [Fintype J₂] [DecidableEq P.J] [DecidableEq J₂]

/-- The letters of the chain behind the three points. -/
abbrev tailW : LayTail E M P.ofp.fs.X3 := tailFst P.ofp P.wfPart

/-- The pair of the claim that the first group adds. -/
abbrev tenEF : St7 E P.wp0.n → (Fin P.wp0.h → E) × ((Fin P.wp0.k → Bool) → E) :=
  fun st => tenEmb P.D.P P.kW P.hW P.D.lT P.ls P.gB st.pa st.pb st.tok

/-- The other side of the first group's identity. -/
abbrev rhsF : St7 E P.wp0.n → (P.wp0.J → E) → E :=
  fun st m => P.ofp.fs.side (fun F i => xS P.D (P.rd m) 0 F i) st.pa st.pb

/-- What the weights' stretch reads, off a last statement. -/
def stF (e : (tailW P).s7.Nx) : St7 E P.nW :=
  (P.ofp.layVF P.wfPart).Ft.st7 ((P.ofp.layVF P.wfPart).Ft.b4 ((tailW P).xW e))

/-- The four fields of the chain's bill that belong to the two product layers; c5 and c6 are True at
this chain. -/
theorem gated_share_first (Y : LateLay Nm J₂) (ι : GatedNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (tailW P).s7.Nx) (m : M) (s : ℕ) (h1 : 1 ≤ P.D.lL) (hs1 : s ≤ lF P.D)
    (hs2 : s ≤ lFe P.D) (hfe : P.D.fe = 2 ^ lFe P.D)
    (hfm : ∀ x : GatedNm, x.InR P.D s → fm (ι x) = toAff (gatedFm P.rd P.D
      (gatedEAt P.fp ((tailW P).b5 e).2 ((tailW P).b6 e).2) s x))
    (hY : GoodNm Y ι P.D s)
    (h : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (gatedLedOf P.fp Y ι ((tailW P).b5 e).2 ((tailW P).b6 e).2 s)) (P.msg m)) :
    (tailW P).s5.Lc ((tailW P).b5 e).1.1 ((tailW P).b5 e).1.2 m ∧
      (tailW P).ow5 ((tailW P).b5 e) m ∧
      (tailW P).s6.Lc ((tailW P).b6 e).1.1 ((tailW P).b6 e).1.2 m ∧
      (tailW P).ow6 ((tailW P).b6 e) m := by
  obtain ⟨a5, a6⟩ := gated_pull P.fp P.hrd Y ι fm ((tailW P).b5 e).2 ((tailW P).b6 e).2 (P.msg m) s
    h1 hs1 hs2 hfe hfm hY h
  exact ⟨trivial, a5, trivial, a6⟩

/-- The three fields of the chain's bill that belong to the weights' round and the merge; c7 is True
at this chain. -/
theorem weights_share_first (Y : LateLay Nm J₂) (ι : EmbNm → Nm) (fm : Nm → TWhole.Aff E P.J)
    (e : (tailW P).s7.Nx) (m : M)
    (hfm : ∀ x, EmbIn P.nb x → fm (ι x) = toAff (embFm P.rd P.D (stF P e).pa P.ls x))
    (hY : ∀ l, l < Arr.x0.nCell → ∀ kh, kh < P.nb → Y.good (ι (.x0 l kh)))
    (hE : TWhole.Ledger.Holds (Cb.Sub.pullL (lateA Y fm)
      (embLedOf Y ι (((tailW P).y7 e).1.2 (0 : Fin 1)) P.mkE P.nb P.gB (stF P e).pb)) (P.msg m))
    (hM : TWhole.Ledger.Holds
      (Cb.Sub.pullL (lateA Y fm) (mergeLedF P.wp0 (tenEF P) (rhsF P) P.mkE e.2)) (P.msg m))
    (hP : Pending P.wp0 (rowWF P.wp0 (tenEF P) e.2.st.1.1 e.2.st.2
          ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2))
        ((noKept P.wf.L.Sm).outPt P.wf.L.Mk e.2) ((noKept P.wf.L.Sm).outB P.wf.L.Mk e.2)
        (e.2.vals ()) (P.msg m)) :
    (tailW P).lW ((tailW P).xW e) ((tailW P).y7 e).1.2 m ∧
      (tailW P).s7.Lc ((tailW P).y7 e) e.1.2 m ∧ (tailW P).s7.Out e m :=
  ⟨emb_pull P.rd P.hrd P.D Y ι fm _ P.mkE P.nb P.ls P.gB (stF P e).pa (stF P e).pb (P.msg m) hfm hY
      hE,
    trivial, merge_pull_first P.wp0 (tenEF P) (rhsF P) P.mkE (lateA Y fm) e.2 (P.msg m) hM hP⟩

end

end Cb.Pv.Lay.End.Gated
