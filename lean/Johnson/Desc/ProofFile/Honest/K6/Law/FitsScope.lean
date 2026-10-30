-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/FitsScope.lean: A JOINING FILE, ON THE TWO STRUCTURES OF
PREMISES OF Honest/K6/Law/FitsOf.lean: IN THE GOALS' SCOPE `HeadFull` IS MET; AT THE BLANK GROUND OF
AN OPENING `HeadTable` IS MET WHERE THE FIRST CHAIN's ENTRIES ARE THE WRITTEN ONES: A PREMISE HERE,
WHICH THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN PAYS (`AtMg.plans_written`): so the named public
premise `headFitsB` (Honest/K6/Wit.lean: 23 named tests with code on public numbers) accepts there
under that premise, and at that hypothesis under nothing more. This file imports modules of
lean/Johnson/Goal/ directly.

WHAT IT IS NOT. NEXT TO NOTHING IS RECKONED HERE: EACH FIELD IS ANOTHER's THEOREM, LAID IN, or is
read off one in a line (S2 and ls off two of the library's numbers; the three needs off its written
list). WHO DOES THE WORK FOR THE 23: the 17 tests on the laid numbers: THE LIBRARY's THEOREM
`laidOk_in_scope`, whole · the test on the weights' unit: `unitFits_of` (FitsOf.lean) over the
library's `head_unit` · the other five (a lookup is named; rows; room; the key points' lengths; the
rounds' ends): made in FitsOf.lean from written numbers, and THAT THE PUBLIC FILES IN SCOPE HAVE
THESE NUMBERS IS THE LIBRARY's, theorem by theorem (the list below), but for the six iota, whose
proof is made of the library's own lines (Johnson/Desc/K6/Honest/Law/IotaWritten.lean). THREE OF THE
FIVE (a lookup is named; the key points' lengths, whose test rejects where none is named; the
rounds' ends) HANG BESIDES ON `HeadTable`: 25 links: `IM.k6_of` · the last link's name:
`IM.ground_named` · the written table of steps: `cuts_of_plans`, UNDER THE PREMISE ON THE FIRST
CHAIN's ENTRIES. No run is spoken of: the tests read public numbers alone. THE FULL SIZE ALONE, the
format's second hash function (`OnBytes.secondHashFunction`) alone. The hypothesis h of the last two is a premise here:
that it is met is the library's to say (`P5J.head_exists_at_name`,
Johnson/P5J/HeadExistsAtName.lean, under four premises: it gives `P5J.AtMgA`, which extends `AtMg`:
Johnson/P5J/MgAtAll.lean). Nothing on any property.

What the file holds. `headFull_in_scope`: `HeadFull X` at what the verifier's own function returns
on public files in scope. `last_named`, `headTable_at_blank`: `HeadTable` at the blank ground of
an opening of the IOP as written in Lean. `headFitsB_at_blank`: the test accepts there; it keeps as
a premise that the first chain's entries are the written ones. `headFitsB_at_head`,
`headFitsB_at_head_some`: the same at the library's hypothesis on the first chain, where that
premise is paid.

Called, of lean/Johnson/Goal/: `Hd.core_of_scope` (Goal/Meaning/ScopeCore.lean);
`InScope.border_in_scope` (Goal/Meaning/HeadAtFullIs.lean); `InScope.numbers_in_scope`,
whose structure's fields are read, and `InScope.laidOk_in_scope` (Goal/Meaning/HeadCondScope.lean);
`InScope.kind_cols` (Goal/Meaning/HeadColsScope.lean); `Meaning.HeadS.keyFloor_in_scope`
(Goal/Meaning/HeadForInScope.lean).

Called besides. `headFitsB_of`, `unitFits_of` (Honest/K6/Law/FitsOf.lean); `iota_in_scope`
(Johnson/Desc/K6/Honest/Law/IotaWritten.lean); `Hd.public_of_core`
(Johnson/Meaning/PublicCore.lean), `numH_of_layout` (Johnson/Road/HeadPlace.lean); `InScope.need_is`
(Johnson/Desc/Kinds/Law/TablesPlanInScope.lean); `fs_in_scope` (Kinds/Law/HeadFsWritten.lean);
`calls_place` (Kinds/Law/K6PubInScope.lean); `cuts_of_plans`
(Johnson/Desc/First/Att/Row/K5FrontOne.lean: where the first chain's entries are the written ones,
the table of steps is the written table); `AtMg.plans_written` (Johnson/P5J/NumbersAtHead.lean);
`IM.ground_named` (Johnson/IMR/PureJoin.lean), `IM.k6_of` (Johnson/IMR/K6Seat.lean).
-/
import Johnson.Desc.ProofFile.Honest.K6.Law.FitsOf
import Johnson.Desc.K6.Honest.Law.IotaWritten
import Johnson.IMR.K6Seat
import Johnson.IMR.PureJoin
import Johnson.Meaning.PublicCore
import Johnson.Goal.Meaning.ScopeCore
import Johnson.Goal.Meaning.HeadAtFullIs
import Johnson.Goal.Meaning.HeadColsScope
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.Desc.Kinds.Law.TablesPlanInScope
import Johnson.Desc.First.Att.Row.K5FrontOne
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- The library's default table of scales is no instance in this file: no statement here can take it
in silence. An instance is taken away, none is added. -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Kinds.Head (laidOk sizesOf)
open OnBytes.Model.Verify (publicOf Public)
open Johnson.AtFull.Cut (cutWritten)
open Johnson.G (dryProofFull)

/-! ## 1 The public structure's numbers, in scope -/

/-- **IN THE GOALS' SCOPE THE PUBLIC STRUCTURE's NUMBERS ARE THE FULL SIZE's.** CONDITIONAL: in
scope; the files are read; X is what the verifier's own function returns on them. Each field is
a theorem of the library's, laid in, BUT FOR S2, ls and the three needs, which are reckoned here off
the library's equations, and iota (`iota_in_scope`, Johnson/Desc/K6/Honest/Law/IotaWritten.lean);
laid, the 17 tests on the laid numbers, is the library's `laidOk_in_scope`. -/
theorem headFull_in_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
    {X : Public} (hZ : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hX : publicOf P.pol P.KL lay = .ok X) : HeadFull X := by
  have Bc := OnBytes.Road.Hd.public_of_core hX (OnBytes.Road.Hd.core_of_scope hZ hR hX)
  have Fw := VerifiableInference.Desc.Kinds.Head.Law.InScope.fs_in_scope hZ hR hX
  have Nn := VerifiableInference.Desc.Kinds.Head.Law.InScope.numbers_in_scope hZ hR hX
  have hn := VerifiableInference.Desc.Kinds.Head.Law.InScope.need_is hZ hR hX
  have kf := Meaning.HeadS.keyFloor_in_scope hZ hR hX
  have hls : X.hS.la - X.hS.lt = 6 := by rw [Nn.la, Nn.lt]
  obtain ⟨pc, ec, sc, -, -⟩ := VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_place hZ hX
  exact {
    num := OnBytes.Road.Hd.numH_of_layout Bc.full Bc.head
    border := VerifiableInference.Desc.Kinds.Head.Law.InScope.border_in_scope hZ hR hX
    S2 := by
      show 2 ^ (X.hS.la - X.hS.lt) = 64
      rw [hls]
    needZ := by
      rw [hn]
      decide
    needFC := by
      rw [hn]
      decide
    needRow := by
      rw [hn]
      decide
    lt := Nn.lt
    ls := hls
    cols := fun q hq => by
      rw [kf]
      exact VerifiableInference.Desc.Kinds.Head.Law.InScope.kind_cols (sizesOf X.hS) Nn.lt hls Nn.d
        Nn.V q hq
    NC := Fw.NC
    dT := Fw.dT
    rK := Fw.rK
    kT := Fw.kT
    cK := Fw.cK
    iota := iota_in_scope hZ hR hX
    place := ⟨pc, ec, sc⟩
    laid := VerifiableInference.Desc.Kinds.Head.Law.InScope.laidOk_in_scope hZ hR hX }

/-! ## 2 At the blank ground -/

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription Inst} {Z : Pub}
  {Bs : PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- The last link of the blank ground is named "H". CONDITIONAL: in scope; the files are read; O: an
opening of the IOP as written in Lean. -/
theorem last_named (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    Bs.G₀.built.back?.map (·.name) = some "H" := by
  obtain ⟨-, l, hl, -, hn⟩ := IM.ground_named hS hR O.pub O.blank
  obtain ⟨_, _, _, _, -, -, -, -, -, hsz, -, -⟩ := IM.k6_of hS hR O
  have hb : Bs.G₀.built.back? = Bs.G₀.built[Bs.G₀.built.size - 1]? := rfl
  rw [hb, hsz, hl, Option.map_some, hn.name]

/-- **What the tests read beside the public structure, at the blank ground.** CONDITIONAL: in scope;
the files are read; O: an opening of the IOP as written in Lean; the first chain's entries are the
written ones. -/
theorem headTable_at_blank (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (p1 : Z.plans.1 = dryProofFull.1.map (·.1.entry)) : HeadTable Z Bs.G₀ := by
  obtain ⟨_, _, _, _, -, -, -, -, -, hsz, -, -⟩ := IM.k6_of hS hR O
  exact ⟨hsz, last_named hS hR O, H2K5.Row.cuts_of_plans O.pub p1⟩

/-- **THE NAMED PUBLIC PREMISE HOLDS AT THE BLANK GROUND.** CONDITIONAL: in scope; the files are
read; O: an opening of the IOP as written in Lean; the first chain's entries are the written ones.
Of the 23 tests 17 are the library's theorem, one is paid over its `head_unit`, five are made in
FitsOf.lean from numbers that the library's theorems give in scope (but for the six iota) and, three
of them, from the written table of steps, which is had under the premise on the entries. -/
theorem headFitsB_at_blank (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    (p1 : Z.plans.1 = dryProofFull.1.map (·.1.entry)) : headFitsB Z Bs.G₀ = true :=
  headFitsB_of (headFull_in_scope hS hR O.public) (headTable_at_blank hS hR O p1)
    (unitFits_of O.public)

end

/-! ## 3 At the library's hypothesis -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- **AT THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN: THE NAMED PUBLIC PREMISE HOLDS AT THE BLANK
GROUND OF THE OPENING OF THE IOP AS WRITTEN IN LEAN THAT IS LAID THERE.** CONDITIONAL: the
hypothesis h; O: an opening at h's own letters (there is but one: `IM.Open.unique`,
Johnson/IMR/SeatOpen.lean). That the first chain's entries are the written ones is the library's
`AtMg.plans_written` (Johnson/P5J/NumbersAtHead.lean). One layout file stands in h and in O: the
public files' own. -/
theorem headFitsB_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {Bs : PureBase}
    {base : List (Block S Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np)) : headFitsB Zp Bs.G₀ = true :=
  headFitsB_at_blank h.scope h.reads O (congrArg Prod.fst h.plans_written)

/-- **There is such an opening**: h's own. CONDITIONAL: the hypothesis h. -/
theorem headFitsB_at_head_some (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ Bs base, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base
      cF (Desc.K14.Law.seatZ Zp Np) (Desc.K14.Law.secondAt Zp Np) ∧
        headFitsB Zp Bs.G₀ = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨Bs, base, O, headFitsB_at_head h O⟩

end

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.headFull_in_scope
#print axioms ProofFile.Honest.K6.last_named
#print axioms ProofFile.Honest.K6.headTable_at_blank
#print axioms ProofFile.Honest.K6.headFitsB_at_blank
#print axioms ProofFile.Honest.K6.headFitsB_at_head
#print axioms ProofFile.Honest.K6.headFitsB_at_head_some
