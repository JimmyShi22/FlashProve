-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4IdnFirst.lean: IN THE FIRST GROUP THE ROAD's SENTENCE (J11) AT THE RECORD's TOKENS
GIVES THE CLAUSE `EmbField` (Johnson/Road/Rows/LayerTop.lean) AS THE TABLE OF JOINTS' ITEM ON THE
IDENTITIES OF SEGMENT 0 ASKS IT: at the request that is read back off the request file, at every
index that the decoded stored table holds. The first group's filling of K04's letter idn
(Johnson/Road/K4/CloseFillFirst.lean) holds (J11) (`Plan4F.J11`,
Johnson/Road/K4/ValueSaysFirst.lean): every entry of the stream that comes in is the entry of the
committed embedding's row of THE SEAT's token. Glue: `Idn.j11`'s value is a difference
(Inst/Model/FF/Trace.lean). No draw, no count.

  `emb_of_j11`: in the form of the later groups' `norm_of_idn`: at any integers Mz whose casts are
    the value's matrices, any request xx and any matrix Wi of integers, UNDER htok AND hW.
  `emb_at_request`: htok IS PAID: at the first chain's own seat, where the record's words are the
    request file's (hs) and `backReq` reads r off that file (hb): at xx := (putReq r tk).val, every
    tk (`tokv_tie`, Johnson/Road/K4/TokensAtState.lean).
  `wn_of_holds`: hW FROM THREE SMALLER LINES: a matrix that is mat inside the reference rows and
    columns and 0 outside (hWn), where mat spells M (hmat) and M holds the index i (`Holds`,
    Johnson/Flat/LedgerClaim.lean), is i.mat, cast.
  `ReqTies`: THREE TIES ON FOUR LETTERS OF THE TABLE's MEANING (reqB, reqW, req, put).
  `emb_at_table`: both laid in: from two conjuncts of "in order" (the record's words are reqW's;
    `backReq` reads something off reqB's bytes), `ReqTies`, hWn, hmat, `Holds M i`: `EmbField` at
    i.mat and (put (req a) tk).val.

HELD AGAINST, BY READING, NOT IMPORTED: other files' one term for the table's meaning:
there "in order" holds both conjuncts; the item
constr 0 idn asks `EmbField` at i.mat and (put (H.req a) _).val for every M and i with "the decoder
gives M" and `Holds M i`; the decoder is the stored table's pin's own, so that M is the witness's
cells. IN THAT TERM reqB, reqW, H.req AND put ARE FOUR FREE LETTERS: NOTHING THERE TIES THEM:
`ReqTies` SAYS WHAT THIS ROW WANTS OF WHOEVER FILLS THEM.

WHO COULD PAY WHAT STAYS. hWn: the value's committed matrix off a tuple is matAt inside its rows and
columns, 0 outside: a lemma on the value (`Plan4.Wn_msg`), in a file that is not imported
here. hmat: "matAt at the pinned part of w spells w's cells": by the seat's make, where the seat's
reader of the cells is the cells themselves. hM: as in the later groups. hscl, hlam: public.

Limits. K04_law IS NOT PROVED BY THIS. NO VALUE OF ALL PREMISES TOGETHER IS BUILT. That K4's block
leaves the record's words: another file of K4's. `NormField` in the first group is not treated here.
The reference sizes alone.
-/
import Johnson.Road.K4.CloseRefFirst
import Johnson.Road.K4.TokensAtState
import Johnson.Road.Rows.LayerTop
import Johnson.Desc.First.K4.SeatS
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Flat OnBytes.Road
open OnBytes.Model.Verify (Public layerShape words32)
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Road.Rows.Norms (castM EmbField)
open VerifiableInference.Desc.First (S)
open VerifiableInference.OnPublicFiles.Flat (Req GE)
open Inst.Model (Scl Mat ppref)
open Inst.Model.Layout (kRef hRef)

/-- **(J11) gives `EmbField`**, at any integers whose casts are the value's matrices, where the
section's table of scales is the record's and a group has four layers, UNDER htok (the seat's tokens
at the record s are xx's) AND hW (the value's committed matrix off t is Wi, cast). -/
theorem emb_of_j11 [scl : Scl] {M T : Type} (U : RefSeat M T) (X : Public) (p : Par)
    (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4) (t : M) (Mz : Mats ℤ)
    (hM : (U.atRecF X p).mats t = castM Mz) (s : T)
    (hJ : (U.atRecF X p).toLF.planF.J11 s t) (Wi : Mat) (xx : Cm.Seg.XI)
    (htok : (fun q => (U.L.tokv s).getD q 0) = Cm.Seg.tokX xx)
    (hW : (U.atRecF X p).toLF.planF.Wn ((U.atRecF X p).toLF.planF.toPlan4.msg t) =
      fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) :
    EmbField (layerShape X.P) X.layers.sc U.y p.g Mz Wi xx := by
  have hsc : scl = sclOf (layerShape X.P) X.layers.sc p.g 4 := by
    rw [hscl, ← hlam]
  intro j i hv
  obtain ⟨_, hj, hi⟩ := hv
  have h0 := hJ j hj i hi
  have hc : (U.atRecF X p).toLF.planF.toPlan4.cells t = _ :=
    (U.atRecF X p).cells_eqF t (fun _ _ _ hb => if_neg hb)
  have ht : (U.atRecF X p).toLF.planF.tok s i = Cm.Seg.tokX xx i := congrFun htok i
  rw [hc, hM, hW, ht] at h0
  subst hsc
  exact sub_eq_zero.2 h0

/-- **At the request that is read back off the request file**: htok is paid: at the first chain's
own seat, where the record's words are the file's (hs) and `backReq` reads r off it (hb). hW stays.
-/
theorem emb_at_request [scl : Scl] {M : Type} (U : RefSeat M S) (hU : U.L = seatS) (X : Public)
    (p : Par) (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4) (t : M) (Mz : Mats ℤ)
    (hM : (U.atRecF X p).mats t = castM Mz) (s : S)
    (hJ : (U.atRecF X p).toLF.planF.J11 s t) (Wi : Mat) {b : ByteArray} {r : Req}
    (hb : Meaning.backReq b = some r) (hs : s.req = words32 b) (tk : Fin ppref.V)
    (hW : (U.atRecF X p).toLF.planF.Wn ((U.atRecF X p).toLF.planF.toPlan4.msg t) =
      fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) :
    EmbField (layerShape X.P) X.layers.sc U.y p.g Mz Wi (putReq r tk).val :=
  emb_of_j11 U X p hscl hlam t Mz hM s hJ Wi _
    (by
      rw [hU]
      exact tokv_tie hb hs tk) hW

/-- **hW from three smaller lines**: a matrix that is mat inside the reference rows and columns and
0 outside (hWn), where mat spells M (hmat) and M holds the index i, is i.mat, cast. -/
theorem wn_of_holds {Wn' mat : ℕ → ℕ → Cb.Gl.E}
    (hWn : ∀ r c, Wn' r c = if r < hRef ∧ c < 2 ^ kRef then mat r c else 0)
    {Mc : Fin hRef → Fin (2 ^ kRef) → GE} {i : Cm.Idx}
    (hH : VerifiableInference.OnPublicFiles.Flat.Holds Mc i)
    (hmat : ∀ y c, mat y.val c.val = Mc y c) :
    Wn' = fun a b => ((i.mat a b : ℤ) : Cb.Gl.E) := by
  funext r c
  rw [hWn]
  by_cases h : r < hRef ∧ c < 2 ^ kRef
  · rw [if_pos h]
    exact (hmat ⟨r, h.1⟩ ⟨c, h.2⟩).trans (hH.1 ⟨r, h.1⟩ ⟨c, h.2⟩)
  · rw [if_neg h, hH.2 r c h, Int.cast_zero]

/-- **Three ties on four letters of the table's meaning**: the words are the bytes' words; the
request is what `backReq` reads off the bytes, where it reads something; put is `putReq`. -/
structure ReqTies {P : Type} (reqB : P → ByteArray) (reqW : P → Array UInt32)
    (req : P × S → Req) (put : Req → Fin ppref.V → Req) : Prop where
  words : ∀ z, reqW z = words32 (reqB z)
  back : ∀ a r, Meaning.backReq (reqB a.1) = some r → req a = r
  put : put = putReq

/-- **As the table's item on the identities of segment 0 asks it**: from the two conjuncts of "in
order" (h1, h2), `ReqTies`, hWn, hmat and `Holds Mc i`; hscl, hlam, hM, hU as above. -/
theorem emb_at_table [scl : Scl] {M P : Type} (U : RefSeat M S) (hU : U.L = seatS) (X : Public)
    (p : Par) (hscl : scl = sclX X p.g) (hlam : X.layers.y.Lam = 4) (t : M) (Mz : Mats ℤ)
    (hM : (U.atRecF X p).mats t = castM Mz) {reqB : P → ByteArray} {reqW : P → Array UInt32}
    {req : P × S → Req} {put : Req → Fin ppref.V → Req} (Tz : ReqTies reqB reqW req put)
    (a : P × S) (h1 : a.2.req = reqW a.1) (h2 : (Meaning.backReq (reqB a.1)).isSome = true)
    (hJ : (U.atRecF X p).toLF.planF.J11 a.2 t) (tk : Fin ppref.V)
    (hWn : ∀ r c, (U.atRecF X p).toLF.planF.Wn ((U.atRecF X p).toLF.planF.toPlan4.msg t) r c =
      if r < hRef ∧ c < 2 ^ kRef then U.matAt t r c else 0)
    {Mc : Fin hRef → Fin (2 ^ kRef) → GE} {i : Cm.Idx}
    (hH : VerifiableInference.OnPublicFiles.Flat.Holds Mc i)
    (hmat : ∀ y c, U.matAt t y.val c.val = Mc y c) :
    EmbField (layerShape X.P) X.layers.sc U.y p.g Mz i.mat (put (req a) tk).val := by
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 h2
  rw [Tz.put, Tz.back a r hr]
  exact emb_at_request U hU X p hscl hlam t Mz hM a.2 hJ i.mat hr (h1.trans (Tz.words a.1)) tk
    (wn_of_holds hWn hH hmat)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.emb_of_j11
#print axioms OnBytes.Road.K4.emb_at_request
#print axioms OnBytes.Road.K4.wn_of_holds
#print axioms OnBytes.Road.K4.emb_at_table
