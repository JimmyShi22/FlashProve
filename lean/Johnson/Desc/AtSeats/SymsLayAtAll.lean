-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/SymsLayAtAll.lean: THE FIELD hBlayB OF WHAT IS STILL OWED FOR KIND K1's
CONDITION (`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED
CONSTANT, IN THE FIELD's OWN TYPE: the closed test `blayB` (
Johnson/Desc/K1/Law/SymsHalvesB.lean: at each feed-forward segment the symbol arrays of the
segment's matrices are seated: `symsSeatedB`, Johnson/Desc/K1/Law/ArmSyms.lean) accepts.
Definitions, and statements with their proofs. THE TEST ASKS, AT SEGMENT 2 g, OF EACH MATRIX μ:
(i) the segment's list of arrays names the matrix's symbol array; (ii) the layout has an array of
that name in the naming segment; (iii) its message is an own message of moment 0 of this segment,
or one that this segment keeps. HOW. (i) is another file's theorem in the goals' scope:
`names_tie` (Johnson/Road/K4/NamesTie.lean): the name is (owner, name) by the public parameters'
label. `owner_cases` with `ix_of_core` (Johnson/Goal/Meaning/HidOwner.lean) makes that
pair a closed one: (2 g, "M" μ), or, at μ = 8 in a later group, (2 (g - 1), "M7"). (ii) and (iii)
read the layout and the shape alone, and under the first pin both are the written ones
(`layout_in_scope`, Johnson/Goal/Numbers/MadeInScope.lean; `hDsh_atAll`, TestsAtAll.lean): so
they are ONE FACT BY LEAN's KERNEL on written values. `seatOkB lay shp l b`: clauses (ii) and
  (iii) at a pair b. `layPair g μ`: the closed pair. `lays_written`: the kernel's fact: all 12 x
  9. LOOKED AT WITH THE EVALUATOR FIRST. `lays_bite`: it can fail: at "M8" of a later group's own
  segment; at "M9"; at the group before's "M6": each rejects. `syms_lay_atAll`: `symsSeatedB` at
  segment 2 g. `hBlayB_atAll`: the field. PREMISES: the head hA, the opening O, the first pin hP1.
A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns. What is not claimed. That the
head, the opening or the pin can be met. Nothing on the attention segments or the output head's.
Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.SymsHalvesB
import Johnson.Desc.K1.Law.TestsAtAll
import Johnson.Desc.AtSeats.ULayAtAll
import Johnson.Road.K4.NamesTie
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.Meaning.HidPlanNM

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open VerifiableInference.PlanWritten (madePinnedAt)
open Johnson.G (layoutFull)
open _root_.Desc.K14.Law (seatZ secondAt)
open ProofFile (Cl)
open IM (Open)

/-- Clauses (ii) and (iii) of the test, at a pair (segment, name). -/
def seatOkB (lay : ReqLayout) (shp : ReqShape) (l : ℕ) (b : ℕ × String) : Bool :=
  match reqArray lay b.1 b.2 with
  | none => false
  | some Ar => firstOrKeptB shp l b.1 Ar.message

/-- The pair that the label names, at matrix μ of group g. -/
def layPair (g μ : ℕ) : ℕ × String :=
  if μ == 8 && g != 0 then (2 * (g - 1), _root_.Meaning.nameOf 7)
  else (2 * g, _root_.Meaning.nameOf μ)

/-- **The kernel's fact on the written layout and shape.** -/
theorem lays_written : ((List.range 12).all fun g => (List.range 9).all fun μ =>
    seatOkB layoutFull shapeFull (2 * g) (layPair g μ)) = true := by decide +kernel

/-- It can fail. -/
theorem lays_bite : seatOkB layoutFull shapeFull 2 (2, _root_.Meaning.nameOf 8) = false ∧
    seatOkB layoutFull shapeFull 2 (2, _root_.Meaning.nameOf 9) = false ∧
    seatOkB layoutFull shapeFull 2 (0, _root_.Meaning.nameOf 6) = false := by decide +kernel

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA O hP1

/-- **The test at a feed-forward segment.** -/
theorem syms_lay_atAll (g : ℕ) (hg : g < 12) (hp : Layer.HPlan2) (hG : Zp.p.X.G[g]? = some hp) :
    symsSeatedB (hA.𝔇.pubD.d3.arrayOf.getD (2 * g) #[]) hA.𝔇.layout hA.𝔇.shape (2 * g) hp.tl =
      true := by
  have hX : Verify.publicOf Zl.pol Zl.KL (some Zl.lay) = .ok Zp.p.X := hA.pubOne
  have C := OnBytes.Road.Hd.core_of_scope hA.scope hA.reads hX
  obtain ⟨_, i7, i8⟩ := _root_.Meaning.ix_of_core hX C
  have etl : _root_.Meaning.tlAt Zp.p.X (2 * g) = hp.tl := by
    unfold _root_.Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show 2 * g / 2 = g by omega, hG]
    rfl
  have hk : 2 * g < 25 := by omega
  have e9 : hp.tl.NM = 9 := by
    rw [← etl, _root_.Meaning.nm_of_core hX C hk]
    exact _root_.Meaning.size_even hX C hg
  have hlay : hA.𝔇.layout = layoutFull :=
    VerifiableInference.PlanWritten.Joined.layout_in_scope hA.scope hA.laid.pub hP1
  rw [hlay, hDsh_atAll hA O hP1]
  unfold symsSeatedB
  refine List.all_eq_true.2 fun μ hμ => ?_
  have hμ9 : μ < 9 := by
    rw [← e9]
    exact List.mem_range.1 hμ
  have hμm : μ < (_root_.Meaning.matsAt Zp.p.X (2 * g)).size := by
    rw [_root_.Meaning.size_even hX C hg]
    exact hμ9
  have hμs : μ < (_root_.Meaning.sizesOf Zp.p.X (2 * g)).NM := by
    rw [(_root_.Meaning.follows_of_core hX C).NM _ hk]
    exact hμm
  have hn := OnBytes.Road.K4.names_tie hA.scope hA.reads O hg hμs
  rw [etl] at hn
  have hn' : (hA.𝔇.pubD.d3.arrayOf.getD (2 * g) #[])[hp.tl.gtTree.getD μ 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g) μ),
        _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g) μ))) := hn
  have hw : seatOkB layoutFull shapeFull (2 * g) (layPair g μ) = true :=
    List.all_eq_true.1 (List.all_eq_true.1 lays_written g (List.mem_range.2 hg)) μ
      (List.mem_range.2 hμ9)
  have hpair : (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g) μ),
      _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g) μ))) =
      layPair g μ := by
    by_cases e : μ = 8 ∧ g ≠ 0
    · have L : _root_.Meaning.labAt Zp.p.X (2 * g) μ = (1 + (g - 1)) * 256 + 7 := by
        rw [_root_.Meaning.lab_even hX C hg hμ9]
        unfold OnBytes.Road.labA
        rw [i7, i8, if_pos e, show 1 + (g - 1) = g by omega]
      obtain ⟨o1, o2⟩ := _root_.Meaning.owner_of (1 + (g - 1)) 7 (by norm_num)
      rw [L, o1, o2, _root_.Meaning.linkOf_group (by omega)]
      unfold layPair
      rw [if_pos (by simp [e.1, e.2])]
    · have L : _root_.Meaning.labAt Zp.p.X (2 * g) μ = (1 + g) * 256 + μ := by
        rw [_root_.Meaning.lab_even hX C hg hμ9]
        unfold OnBytes.Road.labA
        rw [i8, if_neg e]
      obtain ⟨o1, o2⟩ := _root_.Meaning.owner_of (1 + g) μ (by omega)
      rw [L, o1, o2, _root_.Meaning.linkOf_group hg]
      unfold layPair
      rw [if_neg (by simpa using e)]
  rw [hn', hpair]
  exact hw

/-- **The field hBlayB.** -/
theorem hBlayB_atAll :
    blayB hA.𝔇.pubD.d3.arrayOf (P5J.At.X Zp) hA.𝔇.layout hA.𝔇.shape = true := by
  unfold blayB
  refine List.all_eq_true.2 fun l hl => ?_
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases hs : (linksFull[l]?).getD .layers = ModelPart.layers
  · obtain ⟨e, h12⟩ := lay_even l hl' hs
    rw [Bool.or_eq_true]
    right
    cases hG : (P5J.At.X Zp).G[l / 2]? with
    | none => rfl
    | some hp =>
      have h := syms_lay_atAll hA O hP1 (l / 2) h12 hp hG
      rw [e] at h
      exact h
  · rw [Bool.or_eq_true]
    left
    simpa using hs

end

end VerifiableInference.Desc.K1
