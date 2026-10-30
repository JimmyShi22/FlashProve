-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05DataMats.lean: kind K5: THE ONE TIE AT THE SEAM BETWEEN THE TABLE OF
JOINTS' READING OF THE WITNESS (the data: the arrays' cells and the segment's mask row: Bound,
Johnson/Desc/First/Batch/Law/Measure.lean) AND THE KIND's LAW's (a typed tuple of messages, read by
address: valAt, Johnson/Desc/First/Look/K3CallerBase.lean); and what follows from it: both clauses
of WorldTie (Johnson/Desc/First/Att/K05WorthAtTable.lean).

IS IT EMPTY HERE? NO MEMBER IS SHOWN. AddrTie is shown of no witness.

Main names:
  `dataByAddr arrayOf D`: the data, read by address: a mask entry is the mask row's; cell (t, r, c)
    is cell (r, c) of the array that the link's list names at t; 0 where it names none.
  `matsOfData tl arrayOf D`: the matrices off the data: matsOfMsg's text
    (Johnson/Desc/First/Att/K05CellsTie.lean) with the reader turned: a cell is the one unpacking
    (cellValS, Cb/Pv/Tail/InLink.lean) of the symbols, and symbol (matrix, row of symbols, column)
    is the data's cell at the matrix's symbol array.
  `AddrTie x tl D rad arrayOf m Dt fs`: the law's reading of the tuple m (0 where it fails) is the
    data's AT THE ADDRESSES THAT ARE READ, and at no other: (sym) the symbols of the matrices'
    symbol arrays, inside their sizes; (mask) the mask entries under the slots that the forms of fs
    name.
  `matsOfData_eq`: under AddrTie the two families of matrices are one.
  `worldTie_of_addrTie`: **WorldTie at the law's own mask and entry**, for forms whose entries all
    name row 0 of the array iU3, at every St with two equations: at1 keeps the mask row; at1's cell
    (0, i) of the array that the link's list names at iU3 is entryOf at the matrices off the data.
The three definitions dataByAddr · symOfData · matsOfData stand in a light file of their own, free of any kind
(Johnson/Desc/Sound/DataMats.lean; namespace VerifiableInference.Desc.Sound); this file imports it and exports the three names into its own
namespace: no file above turns.
Limits. A rule over letters. The list of tables funs and the number of columns K3 are letters: that
they are the law's is the caller's. The two equations on St are shown of no filling here.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05WorthAtTable
import Johnson.Desc.First.Att.K05CellsTie
import Johnson.Desc.Sound.DataMats

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road.Rows (Addr)
open Cb.Pv.Tail (JCell Syms cellValS)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated worldOwn dataQ)
open VerifiableInference.Desc.First.Look (Sent attSg JAtt msgAtt enCell cellJ sigListCalls seatCalls szOf
  symAt valAt)
open K5Law (entryOf)

export VerifiableInference.Desc.Sound (dataByAddr symOfData matsOfData)

/-- **The one tie**: the law's reading of the tuple of messages, by address, is the data's: AT THE
ADDRESSES THAT ARE READ, AND AT NO OTHER: the symbols of the matrices' symbol arrays, inside their
sizes; the mask entries under the slots that the forms of fs name. -/
structure AddrTie (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
    (rad : OracleShape → Nat) (arrayOf : Array (ℕ × String)) (m : (attSg x D rad).Msg)
    (Dt : Bound GQ) (fs : List Aff) : Prop where
  sym : ∀ (μ : Fin (szOf tl).NM) (i' : Fin (_root_.Alg.symRows ((szOf tl).m μ)))
    (c : Fin ((szOf tl).k μ)),
    (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m
      (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)).getD 0 =
      dataByAddr arrayOf Dt (.cell (tl.gtTree.getD μ.val 0) i'.val c.val)
  mask : ∀ f ∈ fs, ∀ y ∈ f.slots.toList,
    (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) m (.mask y.1)).getD 0 =
      dataByAddr arrayOf Dt (.mask y.1)

section
variable (x : VerifiableInference.Desc.First.Look.Place) (tl : HTailF2) (D : Sent)
  (rad : OracleShape → Nat)

/-- **Under the tie the two families of matrices are one.** -/
theorem matsOfData_eq {arrayOf : Array (ℕ × String)} {m : (attSg x D rad).Msg} {Dt : Bound GQ}
    {fs : List Aff} (T : AddrTie x tl D rad arrayOf m Dt fs) :
    matsOfMsg x tl D rad m = matsOfData tl arrayOf Dt := by
  have es : symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl m =
      symOfData tl arrayOf Dt := by
    funext μ i' c
    exact T.sym μ i' c
  funext a r c
  unfold matsOfMsg matsOfData enCell
  cases h : cellJ (szOf tl) a r c with
  | none => rfl
  | some j =>
    show cellValS (symAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link) tl m) j = _
    rw [es]

variable (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns tl)) → Cb.Gl.E)

/-- **Both clauses of WorldTie from the one tie.** -/
theorem worldTie_of_addrTie (S : Attention.Shape) (ns : ℕ) (N : Nums) (St : Stated)
    (own : List (ℕ × ℕ)) (s : First.S) (pt : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ)
    (m : (attSg x D rad).Msg) (iU3 K3 : ℕ) (funs : List HFun) (fs : List Aff)
    (T : AddrTie x tl D rad pt.L.arrayOf m (dataQ own pt rd) fs)
    (hmask : ∀ j, (St.at1 s (dataQ own pt rd)).mask j = (dataQ own pt rd).mask j)
    (hcell : ∀ b, pt.L.arrayOf[iU3]? = some b → ∀ i, (St.at1 s (dataQ own pt rd)).cell b.1 b.2 0 i =
      entryOf Reading.gl tl K3 (matsOfData tl pt.L.arrayOf (dataQ own pt rd)) funs 0 0 i)
    (hthere : (pt.L.arrayOf[iU3]?).isSome = true)
    (hents : ∀ f ∈ fs, ∀ y ∈ f.ents.toList, y.tree = iU3 ∧ y.row = 0) :
    WorldTie St own s pt rd ((attLin x S tl D rad Ex Wp α ns N).maskOf m)
      (entryOf Reading.gl tl K3 (matsOfMsg x tl D rad m) funs) fs := by
  refine ⟨fun f hf y hy => ?_, fun f hf y hy => ?_⟩
  · rw [hmask]
    exact (T.mask f hf y hy).symm
  · obtain ⟨e1, e2⟩ := hents f hf y hy
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 hthere
    rw [e1, e2, matsOfData_eq x tl D rad T]
    show (match pt.L.arrayOf[iU3]? with
      | some b => (St.at1 s (dataQ own pt rd)).cell b.1 b.2 0 y.idx
      | none => 0) = _
    rw [hb]
    exact hcell b hb y.idx

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.matsOfData_eq
#print axioms VerifiableInference.Desc.First.Att.P.worldTie_of_addrTie
