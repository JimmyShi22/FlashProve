-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/RowKey.lean: CONDITIONAL: the row that the masked sumcheck "the
key at the index" of an attention segment leaves is worth 0 where the rounds heard are the honest
part's. Statements with their proofs, by calls alone. It is the twin, for the one summand that is no
sum of weighted products of two maps, of row_zero_products and row_zero_left
(Johnson/Desc/ProofFile/Honest/K5/Law/Rows.lean).

The verifier makes this row by leftKey (Johnson/Desc/First/Att/LeftP.lean): by leftKey_spec
(Att/K5LeftAll.lean) it is the form that the sumcheck leaves at the plain function keyFlat on what
the ledger shows under the end values' numbers. That function reads as the summand's formula
(keyFlat_formula_of, Johnson/Desc/K5/Honest/Law/KeyFlat.lean), the summand is tame at the shape's
numbers of coefficients (tame_sdOf, Johnson/Desc/K5/Honest/Law/TameSD.lean), and the common
statement on a row (row_zero) does the rest.

Main names:
  key_hS0          the plain function on what the ledger shows reads as the formula on what is sent
  row_zero_key     **the row is worth 0**, with what the ledger shows as a premise
  row_zero_leftKey   the same with that premise shown by shown_reads

ALL THREE ARE CONDITIONAL. The premises, and who is meant to show each:
  hS: at this state the job's summand is the text sdOf at the letters g, w', rho, om' with which the
    verifier makes its row: that the prover's two arrays are the verifier's is the caller's.
  hvs, he, hdY, hen: the call has the verifier's numbers (shape_sSD, TameSD.lean): public.
  hd, ha, hh: the rounds heard are the honest part's, played alone: the caller's.
  hm: the world has the hiding polynomial's coins under the sumcheck's own slots: the caller's.
  hsig: the claimed form is worth the summand's total (for the total: sSD_start,
    Johnson/Desc/K5/Honest/Law/ReadSD.lean): the caller's.
  hF, hl: the ledger in front is sized; the ledger at which the row is made is later: the caller's.
    hf: the verifier's leftKey returns the row at the ledger H: the caller's.
Limits. One sumcheck, played alone. Nothing says that a premise holds at any place.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Rows
import Johnson.Desc.K5.Honest.Law.TameSD
import Johnson.Desc.K5.Honest.Law.KeyFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork World)
open OnBytes.Slice (GE)
open OnBytes.Tie.Pv.Att (keyFlat)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call Heard hear ownSlots)
open VerifiableInference.Desc.First.Att.P (Geo chal leftKey leftKey_spec)
open ProofFile.Honest.SumLaw
open H2K5.Honest (Summand K5In sdOf sdDs tame_sdOf keyFlat_formula_of)

variable {V W X : Type}

/-- **The verifier's plain function on what the ledger shows reads as the summand's formula on what
is sent.** CONDITIONAL on: there is one challenge more than the summand has variables; under each
end value's number the ledger shows what reads as the value sent. -/
theorem key_hS0 (g : Geo) (w' : K5In) (rho om' : Array E) (h : Heard) (H : Fork) (m : List E)
    (hr : h.r.length = (sdOf g w' rho om').vars + 1)
    (hsh : ∀ j, j < g.Lam + g.NP * g.lt → Reading.gl.val (H.vp.getD (h.sEnd + j) zeroE) =
      shownVal Reading.gl (sdOf g w' rho om') h.r m j) :
    Reading.gl.val (keyFlat g.lt g.Lam g.HA g.NP (rho.extract 0 g.lt)
      (rho.extract g.lt (g.lt + g.lgk)) ((chal h).extract 0 g.lt)
      ((chal h).extract g.lt (g.lt + g.lgk)) ((chal h).extract (g.lt + g.lgk) (2 * g.lt + g.lgk))
      om' fun j => H.vp.getD (h.sEnd + j) zeroE) =
      (sdOf g w' rho om').formula Reading.gl (h.r.take (sdOf g w' rho om').vars)
        (shownVal Reading.gl (sdOf g w' rho om') h.r m) := by
  rw [← take_is_chal h _ hr]
  exact keyFlat_formula_of Reading.gl g w' rho om' _ _ _ hsh

/-- **The row that the sumcheck "the key at the index" leaves is worth 0**, in any world,
CONDITIONAL on the premises that the head lists. -/
theorem row_zero_key (name endName : String) (k : Call) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G H : Fork) (h : Heard)
    (Wd : World GE) (g : Geo) (w' : K5In) (rho om' : Array E) (f : Aff)
    (hS : S t.input (frontOf t seen) = sdOf g w' rho om')
    (hvs : k.vs = (sdDs g).map Var.plain) (he : k.ends = some e) (hdY : e.dY = g.lt + 1)
    (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots k.all → Wd.slot (h.first + i) = hidingCoin c i)
    (hsig : C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total)
    (hf : leftKey g H h rho om' = some f)
    (hsh : ∀ j, j < g.Lam + g.NP * g.lt → Reading.gl.val (H.vp.getD (h.sEnd + j) zeroE) =
      shownVal Reading.gl (S t.input (frontOf t seen)) h.r (endRun c) j) :
    f.value Reading.gl Wd = 0 := by
  have hT : (S t.input (frontOf t seen)).Tame Reading.gl (sdDs g) e.dY := by
    rw [hS, hdY]
    exact tame_sdOf Reading.gl g w' rho om'
  have hr := heard_r_vars (V := V) name endName k (sdDs g) e lead S c t seen dr rounds C F G h hvs
    he hT.vars hd ha hh
  rw [leftKey_spec hf]
  refine row_zero (V := V) name endName k (sdDs g) e lead S c t seen dr rounds C F G h _ Wd hvs he
    hT hd ha hh hm hsig ?_
  rw [hS] at hr hsh ⊢
  exact key_hS0 g w' rho om' h H (endRun c) hr hsh

/-- **The same, with what the ledger shows paid**: CONDITIONAL as row_zero_key but for its last
premise, and on: the call has the summand's number of end values; the ledger in front of the hearing
is sized; H, the ledger at which the verifier makes the row, is later than the one that the hearing
hands back. -/
theorem row_zero_leftKey (name endName : String) (k : Call) (e : Ends)
    (lead : W → Front X → List E) (S : W → Front X → Summand)
    (c : SumCoins name endName (jobOf k lead S)) (t : State W X) (seen : Seen)
    (dr : List Fmt.Drawn) (rounds : List Fmt.RoundView) (C : Aff) (F G H : Fork) (h : Heard)
    (Wd : World GE) (g : Geo) (w' : K5In) (rho om' : Array E) (f : Aff)
    (hS : S t.input (frontOf t seen) = sdOf g w' rho om')
    (hvs : k.vs = (sdDs g).map Var.plain) (he : k.ends = some e) (hdY : e.dY = g.lt + 1)
    (hen : e.n = g.Lam + g.NP * g.lt) (hd : drawsOk k dr = true)
    (ha : alone (sumPart (V := V) name endName (jobOf k lead S)) c t seen dr = some rounds)
    (hh : hear C k F rounds = some (h, G))
    (hm : ∀ i, i < ownSlots k.all → Wd.slot (h.first + i) = hidingCoin c i)
    (hsig : C.value Reading.gl Wd = Reading.gl.val (S t.input (frontOf t seen)).total)
    (hf : leftKey g H h rho om' = some f) (hF : OnBytes.PscRun.Sized F)
    (hl : OnBytes.PscRun.Later G H) :
    f.value Reading.gl Wd = 0 :=
  row_zero_key (V := V) name endName k e lead S c t seen dr rounds C F G H h Wd g w' rho om' f hS
    hvs he hdY hd ha hh hm hsig hf fun j hj =>
      shown_reads (V := V) name endName k (sdDs g) e lead S c t seen dr rounds C F G H h hvs he
        (by rw [hS]; exact H2K5.Honest.SD.ds_length g) (by rw [hS, hen]; rfl) hd ha hh hF hl j
        (by rw [hen]; exact hj)

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.key_hS0
#print axioms ProofFile.Honest.K5.row_zero_key
#print axioms ProofFile.Honest.K5.row_zero_leftKey
