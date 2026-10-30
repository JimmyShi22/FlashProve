-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MeansOrd.lean: K05_means (Att/K05Means.lean) CARRIED TO THE LETTERS IN
WHICH THE LIBRARY's att_ord_base (Johnson/Road/Rows/AttStartBase.lean) AND THE INTEGER MODEL's
CLAUSES TAKE IT: at the trace t' c := cellValS y (pl ‹the place of the name c›), y := the committed
symbols off the messages: which has the tie "ht" at EVERY name by its make.

Why. attCells (Johnson/Desc/First/Look/K3CallerAtt.lean) reads 0 at a name whose place lies outside
the sizes; t' reads some cell there. The two agree at the VALID names, where every valid name's
place lies within the sizes; and the library's relation of an attention segment reads valid names
only (Johnson/Road/Lane5AttValid.lean: idnVal_agree): that lemma is called, not typed anew.

Main names:
  `InsideA tl S`: every valid name's place lies within the sizes of the plan's record tl.
  `symsA`, `cellsBy pl`: the committed symbols y off the messages; the trace t'.
  `attCells_agree`: PlaceOK pl and InsideA give AgreeD (dimOf S) (attCells … m) (cellsBy … pl m).
  `K05_means_at`: Todo gives own1 and own2 AT t'. `K05_rider_means_at`: the lookup's base joint in
    front gives ridden AT t'.
  `K05_means_ord`: **so the integers behind the symbols are in order**: L5.AttOrd A.S (zsOf pl Mz),
    from: BaseAt y Mz ("the committed symbols are the packing of small integers": HERE IT IS SPENT),
    2 β ≤ 2^18, PlaceOK, InsideA, Todo at (x0, m), the lookup's base joint in front at m, and the
    keys' clause at t'.

Premises: those named. The keys' clause (every looked-up value at t' is an entry of its table) is
the lookup's kind's row, in att_ord_base's letters: it is a premise here, though the lookup's base
joint holds it in the lookup's own letters: that step is not made here.
Limits. Those of K05Means.lean. No (x0, m) with Todo is shown. InsideA and PlaceOK are conditions on
public data, evaluated nowhere here. That y is the reading of the symbols that the integer model's
map to its integers uses is not shown: two readings stand in two texts (K5's files'; the model's).
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Means
import Johnson.Road.Lane5AttValid
import Johnson.Road.Rows.AttStartBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.L5 (callsOf dimOf sclOf tbOf addrA)
open OnBytes.Road.L5.V (AgreeD idnVal_agree)
open OnBytes.Road.Rows (PlaceOK zsOf att_ord_base)
open Cb.Pv.Tail (JCell Syms BaseAt cellValS)
open VerifiableInference.OnPublicFiles (kLookupCR)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt AttOK attCells attRider szOf symAt
  sigListCalls seatCalls cellJ enCell msgAtt rawOf)

/-- Every valid name's place lies within the sizes. -/
def InsideA (tl : HTailF2) (S : Attention.Shape) : Prop :=
  ∀ c : Raw, c.Valid (dimOf S) → (addrA S c).1 < (szOf tl).NM ∧
    (addrA S c).2.2 < (szOf tl).k (addrA S c).1 ∧ (addrA S c).2.1 < (szOf tl).m (addrA S c).1

section
variable (x : VerifiableInference.Desc.First.Look.Place) (S : Attention.Shape) (tl : HTailF2)
  (D : Sent) (rad : OracleShape → Nat)

/-- The committed symbols, off the messages. -/
noncomputable def symsA (m : (attSg x D rad).Msg) : Syms Cb.Gl.E (szOf tl) :=
  symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl m

/-- The cells behind the symbols, by a map of places: at every name. -/
noncomputable def cellsBy (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (m : (attSg x D rad).Msg) :
    Raw → Cb.Gl.E :=
  fun c => cellValS (symsA x tl D rad m) (pl (addrA S c).1 (addrA S c).2.1 (addrA S c).2.2)

/-- **The caller's cells and the cells by a map of places agree at the valid names.** -/
theorem attCells_agree (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (hp : PlaceOK pl) (hin : InsideA tl S)
    (m : (attSg x D rad).Msg) :
    AgreeD (dimOf S) (attCells x S tl D rad m) (cellsBy x S tl D rad pl m) := by
  intro c hv
  obtain ⟨h1, h2, h3⟩ := hin c hv
  have e : cellJ (szOf tl) (addrA S c).1 (addrA S c).2.1 (addrA S c).2.2 =
      some (pl (addrA S c).1 (addrA S c).2.1 (addrA S c).2.2) := by
    unfold cellJ
    rw [dif_pos ⟨h1, h2, h3⟩]
    exact congrArg some (hp ⟨_, h1⟩ ⟨_, h2⟩ ⟨_, h3⟩).symm
  show msgAtt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl x.ns m
    ((cellJ (szOf tl) (addrA S c).1 (addrA S c).2.1 (addrA S c).2.2).map Sum.inr) = _
  rw [e]
  rfl

end

section Means
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **own1 and own2 at the trace that has the tie at every name.** -/
theorem K05_means_at {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg)
    (h : ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m)
    (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (hp : PlaceOK pl) (hin : InsideA tl A.S) :
    (∀ j b g i, (Idn.at1 j b g i).Valid (dimOf A.S) →
        idnVal (dimOf A.S) (cellsBy x A.S tl D rad pl m) (.at1 j b g i) = 0) ∧
      ∀ b g i, (Idn.at2 b g i).Valid (dimOf A.S) →
        idnVal (dimOf A.S) (cellsBy x A.S tl D rad pl m) (.at2 b g i) = 0 := by
  have M := K05_means x tl D rad Ex Wp α hA ns N x0 m h
  have G := attCells_agree x A.S tl D rad pl hp hin m
  exact ⟨fun j b g i hv => (idnVal_agree G hv).symm.trans (M.own1 j b g i hv),
    fun b g i hv => (idnVal_agree G hv).symm.trans (M.own2 b g i hv)⟩

/-- **ridden at that trace.** -/
theorem K05_rider_means_at {set : Params.Setting} {S : Attention.Shape}
    (H : AttOK set x S tl D rad) (a : Unit × Ex.Str) (w : (attSg x D rad).Msg × Wp)
    (h : ((kLookupCR [attRider x S tl D rad Ex Wp]).A (attRider x S tl D rad Ex Wp)).relR a w)
    (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (hp : PlaceOK pl) (hin : InsideA tl S) :
    ∀ b g i, (Idn.at3 b g i).Valid (dimOf S) →
      idnVal (dimOf S) (cellsBy x S tl D rad pl w.1) (.at3 b g i) = 0 := fun b g i hv =>
  (idnVal_agree (attCells_agree x S tl D rad pl hp hin w.1) hv).symm.trans
    (K05_rider_means x tl D rad Ex Wp H a w h b g i hv)

/-- **The attention link is in order at the integers behind the committed symbols.** -/
theorem K05_means_ord {set : Params.Setting} {settings : Model.Settings} {i : Attention.In}
    {cf : Attention.Cfg} {A : Attention.Plan} (hA : Attention.plan settings i cf = Except.ok A)
    (H : AttOK set x A.S tl D rad) (ns : ℕ) (N : Nums)
    (x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl))) (m : (attSg x D rad).Msg)
    (h : ((closedOf (attBase x A.S tl D rad) (attLin x A.S tl D rad Ex Wp α ns N) ns N).own (theMeans Cb.Gl.E _ _ _)).ch.Todo x0 m)
    (a : Unit × Ex.Str) (wp : Wp)
    (hL : ((kLookupCR [attRider x A.S tl D rad Ex Wp]).A (attRider x A.S tl D rad Ex Wp)).relR a
      (m, wp))
    (φ : Cb.Gl.F →+* Cb.Gl.E)
    {Mz : ∀ μ : Fin (szOf tl).NM, Fin ((szOf tl).k μ) → Fin ((szOf tl).m μ) → ℤ}
    (hB : BaseAt (symsA x tl D rad m) Mz) (h2 : 2 * ((szOf tl).beta : ℤ) ≤ 2 ^ 18)
    (pl : ℕ → ℕ → ℕ → JCell (szOf tl)) (hp : PlaceOK pl) (hin : InsideA tl A.S)
    (keys : ∀ (c : Fin 4) (X : ℕ), X < (dimOf A.S).used c →
      keyVec (scl := sclOf A.S) (dimOf A.S) (tbOf A.S) (cellsBy x A.S tl D rad pl m) c X ∈
        lutSet (lut (scl := sclOf A.S) (dimOf A.S) (tbOf A.S) c)) :
    OnBytes.Road.L5.AttOrd A.S (zsOf pl Mz) :=
  att_ord_base φ hB pl h2 (t := cellsBy x A.S tl D rad pl m) (fun _ => rfl)
    (K05_means_at x tl D rad Ex Wp α hA ns N x0 m h pl hp hin).1
    (K05_means_at x tl D rad Ex Wp α hA ns N x0 m h pl hp hin).2 keys
    (K05_rider_means_at x tl D rad Ex Wp H a (m, wp) hL pl hp hin)

end Means

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.attCells_agree
#print axioms VerifiableInference.Desc.First.Att.P.K05_means_at
#print axioms VerifiableInference.Desc.First.Att.P.K05_rider_means_at
#print axioms VerifiableInference.Desc.First.Att.P.K05_means_ord
