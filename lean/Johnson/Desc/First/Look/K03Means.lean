-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K03Means.lean: THE LOOKUP ON A LINK's CALLS: FROM THE RELATION THAT THE
KIND's LAW CONCLUDES IN FRONT OF ITS BLOCK TO FOUR CLAUSES OF THE MEANING's ROW: at an attention
link: every looked-up value is an entry of its table, and the denominator is the sum of the row's
weights; at a layers' link: the keys' clause and the one-hot clause. Statements and proofs. NO
SOUNDNESS OF ANY TEXT THAT RUNS IS CLAIMED.

Why. The end theorems on the lookup at the calls (K3AttGoodIn.lean, K3LayGoodIn.lean) conclude, in
front of the block, AttFront a w and LayFront a w: the witness's messages are pinned to the
statement, and AttSays | LaySays holds of them. The four clauses (K3CallerMeans.lean: attKey_at,
attRidden_at, layKey_at, layHot_at) start from the typed joint in front of the proved block. The two
meet: att_says and lay_says (K3CallerAtt.lean, K3CallerLay.lean) are equivalences.

Main names:
  att_relR, lay_relR: AttSays | LaySays of a tuple of messages gives the typed joint in front.
  K03_means_att: AttFront a w, with the named reading of the cells at the row's own hidden matrices
    and three premises on public data, gives AttKeyAt X W g and AttRiddenAt X W g.
  K03_means_lay: LayFront a w, with the two named readings, gives LayKeyAt X i W g and
    LayHotAt X i xi W g.

Limits. Those of K3CallerMeans.lean: the four clauses are typed there as the meaning's row types
them, held against that file's text by a program, not by Lean. The readings CellsAre, MatsAre and
WeightsAre, and AttOK, LayOK, TabsAre and the bound on the calls' sizes are premises. One group g.
Nothing on the output head's link, nothing on the digits' lookup.
On the readings (by report: a reading of the definitions).
(1) At the lists of integers that are unpacked from the caller's own symbols CellsAre and MatsAre
hold WITHOUT the smallness test: both sides unpack the same symbols by the same map, and both are 0
outside the record's sizes. What is asked there is that the caller's symbols are the symbols from
which the row's hidden values are read. Where the symbols pack nothing small the clauses then speak
of the 0 that both sides read: it is the smallness test's clause that ties them to what is
committed. (2) CellsAre and MatsAre are equations of FUNCTIONS, on all names and all (a, r, c),
valid or not: at another list they would bind its entries outside every size to 0. (3) WeightsAre
runs over EVERY l, where KeyField reads four layers: it can be given only by one who has the
committed weights equal to the index's matrix's casts on the whole table, and both 0 beyond it.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3AttGoodIn
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Desc.First.Look.K3CallerMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Clauses (Hid2 Idx2 AttKeyAt AttRiddenAt LayKeyAt LayHotAt)

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {set : Params.Setting} {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ}

/-- What AttSays says of a tuple of messages is the typed joint in front of the proved block. -/
theorem att_relR {A : Attention.Shape} (H : AttOK set x A tl D rad) (m : (attSg x D rad).Msg)
    (h : AttSays x A tl D rad m) :
    ((kLookupCR [attRider x A tl D rad extNone Unit]).A
      (attRider x A tl D rad extNone Unit)).relR ((), ()) (m, ()) :=
  (att_says extNone Unit H ((), ()) (m, ())).2 h

/-- **The two clauses at an attention link, from the relation in front.** -/
theorem K03_means_att (X : Verify.Public) (W : Hid2) (g : ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
    (H : AttOK set x (Road.Hd.shapeA X g) tl D rad) (a : S × Fr.E.Str)
    (w : Desc.Wit Cells Tok MsgT)
    (h : AttFront G x (Road.Hd.shapeA X g) tl D rad seatT arr smp a w)
    (hZ : CellsAre x (Road.Hd.shapeA X g) tl D rad (attMs x D rad seatT arr w) (W.MA g))
    (hT : TabsAre (Road.Hd.shapeA X g) x.fs)
    (hU : ∀ c : Fin 4, (Road.L5.dimOf (Road.Hd.shapeA X g)).used c ≤
      2 ^ Cb.LdLkp.Port.nOf x.fs c) :
    AttKeyAt X W g ∧ AttRiddenAt X W g :=
  ⟨attKey_at extNone Unit X W g H ((), ()) (attMs x D rad seatT arr w, ())
      (att_relR H _ h.2) hZ hT hU,
    attRidden_at extNone Unit X W g H ((), ()) (attMs x D rad seatT arr w, ())
      (att_relR H _ h.2) hZ⟩

variable {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}

/-- What LaySays says of a tuple of messages is the typed joint in front of the proved block. -/
theorem lay_relR (q : LayPub) (m : (laySg x D rad oW).Msg)
    (h : LaySays x q tl D rad oW wOf nr nc m) :
    ((kLookupCR [layRider x q tl D rad oW wOf nr nc extNone Unit]).A
      (layRider x q tl D rad oW wOf nr nc extNone Unit)).relR ((), ()) (m, ()) :=
  (lay_says extNone Unit ((), ()) (m, ())).2 h

/-- **The two clauses at a layers' link, from the relation in front.** -/
theorem K03_means_lay (X : Verify.Public) (i : Idx2) (xi : Cm.Seg.XI) (W : Hid2) (g : ℕ)
    (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
    (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
    (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
    (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (H : LayOK set x) (a : S × Fr.E.Str)
    (w : Desc.Wit Cells Tok MsgT)
    (h : LayFront G x (pubAt X g) tl D rad oW wOf nr nc seatT arr smp smpW strW msgW a w)
    (hM : MatsAre x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w) (W.MG g))
    (hW : WeightsAre x tl D rad oW wOf nr nc g (layMs x D rad oW seatT arr msgW w) i.mat) :
    LayKeyAt X i W g ∧ LayHotAt X i xi W g :=
  ⟨layKey_at extNone Unit X W g i H ((), ()) (layMs x D rad oW seatT arr msgW w, ())
      (lay_relR (pubAt X g) _ h.2) hM hW,
    layHot_at extNone Unit X W g i xi ((), ()) (layMs x D rad oW seatT arr msgW w, ())
      (lay_relR (pubAt X g) _ h.2) hM⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.K03_means_att
#print axioms VerifiableInference.OnPublicFiles.K03_means_lay
