-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/W/TwoReaders.lean: CONDITIONAL.

What is here. TWO OF THE LIBRARY's READERS OF ONE WITNESS AGREE, AT EVERY WITNESS: the data that the
table's items on forms read (`dataQ` over the reader by seats `seatTab`,
Johnson/Desc/Sound/FormsQ.lean and BordersFill.lean) and what the caller of the lookup on a layers'
link's calls reads (`valAt`, `msgLay`, `layNu` over `layMs`, Johnson/Desc/First/Look/). The library
has these as «two readings are one» at its own parameters, at every tuple of tables:
`cell_dataQ_plan`, `mask_dataQ_B` (Johnson/Road/K4/Rec/), with `mask_lay`
(Johnson/Road/K4/K4PinsLay.lean). Here they are joined AT THE TUPLE THAT `seatTab` MAKES OF A
WITNESS, which is the reader that the thread's data stand at; the library's own join stands at
another tuple (`partOf`), which agrees with this one inside the messages' ranges alone. Free of the
honest side's frame. Each proof is a chain of calls; the first follows the library's `tupleOf_part`.

  `tupleOf_seatTab`, `own_tuple`   the caller's tuple out of `seatTab`'s tables is the witness's
      own.
  `sym_two`   **symbol by symbol**: the data by address at a cell of a symbol array of tl is the
      caller's reading at that address.
  `mask_two`   **the data's mask row is the caller's reading at the place `.mask j`, BELOW THE
      PLACE's NUMBER OF SLOTS.**

Not shown here. hs (`SitsIn`, Johnson/Road/K4/K4PinsRead.lean): a condition on the plan: each member
of the caller's list sits at a seat of the segment's, and the member that is found there has its
shape. hB, hMB: two tests with code on the plan accept (`arraysPlanB`,
Johnson/Road/K4/Rec/Arrays.lean; `maskPlanB`, Rec/PinsBools.lean). hell: the place's number of slots
is at most the plan's length of the mask row. hR (`RecIs`, Rec/Whole.lean): THE ONE HYPOTHESIS ON
THE VERIFIER's STATE: the open segment's part reads as the plan says. All are hypotheses; no example
of them together is known. FROM THE PLACE's NUMBER OF SLOTS ON NOTHING IS SAID OF THE MASK ROW:
there the caller's reader has no entry and answers 0, and the data's row is whatever the table at
the seat holds. Nothing is said of what any cell or mask entry is worth, of integers, of an honest
prover's cells or of its coins. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 1 module under Johnson/Goal/ and at 1 under Johnson/Bridge/; it saw 28 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 2 is not counted: all the numbers are floors. They come with
the library's files that are called. It imports nothing of the honest side
(Johnson/Desc/ProofFile/Honest/). A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.
-/
import Johnson.Road.K4.K4PinsLay
import Johnson.Road.K4.ULayPins
import Johnson.Road.K4.Rec.PinsBools
import Johnson.Road.K4.Rec.Arrays
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.W
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Road.K4 (SitsIn tupleOf memAt_some planAt mask_lay)
open OnBytes.Road.K4.Rec (RecPlan RecIs arraysPlanB arrayPlan_of_B cellPlan_of_array cell_dataQ_plan
  maskPlanB maskEllP mask_dataQ_B)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent LayPub sigListCalls seatCalls valAt szOf ownPart
  msgLay lyMask)
open VerifiableInference.Desc.Sound (Mem MsgT msgsOf memTab numOf seatTab dataQ dataByAddr)
open VerifiableInference.OnPublicFiles (layMs layNu)

/-! ## 1 The tuple -/

section
variable {Cells Tok : Type} (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (seat : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers) (m : ℕ)

/-- CONDITIONAL: on hs. **The tuple out of `seatTab`'s tables is the witness's own.** c₀: the
tuple's second part; it is not read. -/
theorem tupleOf_seatTab (hs : SitsIn l seat ms N m) (w : Wit Cells Tok MsgT) (c₀ : Option Cells) :
    tupleOf cs l seat (seatTab cs arr ms w, c₀) = msgsOf cs l seat arr w := by
  funext i j
  obtain ⟨_, u, hu, hsh⟩ := hs i
  have hseat : u.1.seat u.2 = seat i := (memAt_some hu).2
  have key : ∀ mask row place, seatTab cs arr ms w (seat i) mask row place =
      w.tab cs (l.get i).1 (arr (seat i).1 (seat i).2) (seat i).1 (seat i).2 mask row place := by
    intro mask row place
    have hu' : (ms.find? fun y => decide (VerifiableInference.Desc.Sound.seatOf y = seat i)) =
        some u := hu
    have e : seatTab cs arr ms w (seat i) = memTab cs arr w u := by
      unfold seatTab
      rw [hu']
    rw [e]
    unfold memTab numOf
    rw [hsh, hseat]
  rcases j with q | q
  · exact key false q.1.val q.2.val
  · exact key true q.1.val q.2.val

end

/-! ## 2 The two readers -/

variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (D : Sent)
  (rad : OnBytes.OracleShape → ℕ) (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (rc : Cells → ℕ → ℕ → Cb.Gl.E) (posI : ℕ → Bool × ℕ × ℕ) (tl : HTailF2)
  (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (N : Numbers) (m : ℕ) (msgW : Wit Cells Tok MsgT → oW.Msg)

/-- CONDITIONAL: on hs. The first chain's part of the caller's tuple off a witness is the plan's
tuple out of `seatTab`'s tables. -/
theorem own_tuple (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (w : Wit Cells Tok MsgT) :
    ownPart (layMs x D rad oW seatT arr msgW w) =
      (planAt x D rad seatT rc posI).tuple (seatTab D.codes arr ms w, none) :=
  (tupleOf_seatTab D.codes (sigListCalls D rad x.link) seatT arr ms N m hs w none).symm

variable {own : List (ℕ × ℕ)} {R : RecPlan} {n m' : ℕ} {a : VerifiableInference.Desc.K9.Part}

/-- CONDITIONAL: on hs, hB and hR. **SYMBOL BY SYMBOL.** μ: a matrix of tl. i, c: a row of symbols
and a column inside its sizes. -/
theorem sym_two (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hB : arraysPlanB (planAt x D rad seatT rc posI) tl own R n m' = true) (hR : RecIs a R n m')
    (w : Wit Cells Tok MsgT) (μ : ℕ) (hμ : μ < (szOf tl).NM) (i : ℕ)
    (hi : i < Alg.symRows ((szOf tl).m μ)) (c : ℕ) (hc : c < (szOf tl).k μ) :
    dataByAddr (D.arrayOf.getD x.link #[]) (dataQ own a (seatTab D.codes arr ms w))
        (.cell (tl.gtTree.getD μ 0) i c) =
      (valAt D.codes (sigListCalls D rad x.link) (seatCalls D x.link)
        (ownPart (layMs x D rad oW seatT arr msgW w)) (.cell (tl.gtTree.getD μ 0) i c)).getD 0 := by
  obtain ⟨Ha⟩ := arrayPlan_of_B (planAt x D rad seatT rc posI)
    (List.all_eq_true.1 hB ⟨μ, hμ⟩ (List.mem_finRange _))
  obtain ⟨Hc⟩ := cellPlan_of_array (planAt x D rad seatT rc posI) Ha hi hc
  have q := cell_dataQ_plan (planAt x D rad seatT rc posI) Hc hR (seatTab D.codes arr ms w, none)
  have hn : (D.arrayOf.getD x.link #[])[tl.gtTree.getD μ 0]? = some Hc.bn := Hc.named
  rw [own_tuple x D rad seatT rc posI oW arr ms N m msgW hs w]
  simp only [dataByAddr, hn]
  exact q.symm

/-- CONDITIONAL: on hs, hMB, hR, hell and hj. **THE MASK ROW, BELOW THE PLACE's NUMBER OF SLOTS.**
q: the caller's public data; the reading at a mask place does not read them. -/
theorem mask_two (q : LayPub) (hs : SitsIn (sigListCalls D rad x.link) seatT ms N m)
    (hMB : maskPlanB (planAt x D rad seatT rc posI) own R n m' = true) (hR : RecIs a R n m')
    (hell : x.ns ≤ maskEllP (planAt x D rad seatT rc posI)) (w : Wit Cells Tok MsgT) (j : ℕ)
    (hj : j < x.ns) :
    (dataQ own a (seatTab D.codes arr ms w)).mask j =
      layNu x q tl D rad oW wOf nr nc seatT arr msgW w (.mask j) := by
  have h1 := mask_lay x D rad seatT rc posI tl oW wOf nr nc _ _
    (own_tuple x D rad seatT rc posI oW arr ms N m msgW hs w) j hj
  have h2 := mask_dataQ_B (planAt x D rad seatT rc posI) hMB hR (seatTab D.codes arr ms w, none) j
    (Nat.lt_of_lt_of_le hj hell)
  show _ = msgLay x tl D rad oW wOf nr nc (layMs x D rad oW seatT arr msgW w)
    (lyMask x.ns tl nr nc j)
  rw [h1, h2]

end OnBytes.Road.K4.W

#print axioms OnBytes.Road.K4.W.tupleOf_seatTab
#print axioms OnBytes.Road.K4.W.own_tuple
#print axioms OnBytes.Road.K4.W.sym_two
#print axioms OnBytes.Road.K4.W.mask_two
