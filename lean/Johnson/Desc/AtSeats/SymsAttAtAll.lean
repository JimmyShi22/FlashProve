-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/SymsAttAtAll.lean: THE FIELD hBattB OF WHAT IS STILL OWED FOR KIND K1's
CONDITION (`K1Owed`, Johnson/Desc/AtSeats/K01CondOfRest.lean), AT THE FIRST TABLE's CLOSED
CONSTANT, IN THE FIELD's OWN TYPE: the closed test `battB` (
Johnson/Desc/K1/Law/SymsHalvesB.lean: at each attention segment the symbol arrays of the segment's
matrices are seated: `symsSeatedB`, Johnson/Desc/K1/Law/ArmSyms.lean) accepts. Definitions, and
statements with their proofs. THE SISTER OF Johnson/Desc/AtSeats/SymsLayAtAll.lean, BY THE SAME
ROAD. HOW. (i) That the segment's list of arrays names the matrix's symbol array is a theorem
of K5's files in the goals' scope: `names_tie_att`
(Johnson/Desc/First/Att/Door/Law/K5NamesTie.lean): CALLED, not typed here.
`owner_label` (Johnson/Goal/Meaning/HidSeatsOf.lean) makes the pair a closed one: (2 g + 1, "M" μ)
at the four own matrices, (2 g, "M6") at the fifth, which the segment in front has sent. (ii) the
layout has it and (iii) its message is an own one of moment 0 or one that the segment keeps: they
read the layout and the shape alone, which under the first pin are the written ones: ONE FACT BY
LEAN's KERNEL. `attPair g μ`: the closed pair. `atts_written`: the kernel's fact: all 12 x 5.
  LOOKED AT WITH THE EVALUATOR FIRST. `atts_bite`: it can fail: at the segment's own "M4"; at
  "M5"; at the segment in front's "M0": each rejects. `att_odd`: an attention segment's number is
  odd and below 24: by evaluation. `syms_att_atAll`: `symsSeatedB` at segment 2 g + 1.
  `hBattB_atAll`: the field. PREMISES: the head hA, the opening O, the first pin hP1.
A PAYMENT BENEATH A FROZEN CONDITION: no statement above turns. What is not claimed. That the
head, the opening or the pin can be met. Nothing on the output head's segment. Nothing on
soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.AtSeats.SymsLayAtAll
import Johnson.Desc.First.Att.Door.Law.K5NamesTie
import Johnson.Goal.Meaning.HidSeatsOf

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

/-- The pair that the label names, at matrix μ of the attention segment of group g. -/
def attPair (g μ : ℕ) : ℕ × String :=
  if μ == 4 then (2 * g, _root_.Meaning.nameOf 6) else (2 * g + 1, _root_.Meaning.nameOf μ)

/-- **The kernel's fact on the written layout and shape.** -/
theorem atts_written : ((List.range 12).all fun g => (List.range 5).all fun μ =>
    seatOkB layoutFull shapeFull (2 * g + 1) (attPair g μ)) = true := by decide +kernel

/-- It can fail. -/
theorem atts_bite : seatOkB layoutFull shapeFull 3 (3, _root_.Meaning.nameOf 4) = false ∧
    seatOkB layoutFull shapeFull 3 (3, _root_.Meaning.nameOf 5) = false ∧
    seatOkB layoutFull shapeFull 3 (2, _root_.Meaning.nameOf 0) = false := by decide +kernel

theorem att_odd : ∀ l < 25, (linksFull[l]?).getD .layers = ModelPart.attention →
    2 * (l / 2) + 1 = l ∧ l / 2 < 12 := by decide

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
    (seatZ Zp Np) (secondAt Zp Np))
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA O hP1

/-- **The test at an attention segment.** -/
theorem syms_att_atAll (g : ℕ) (hg : g < 12) (Ap : Attention.Plan)
    (hAp : Zp.p.X.A[g]? = some Ap) :
    symsSeatedB (hA.𝔇.pubD.d3.arrayOf.getD (2 * g + 1) #[]) hA.𝔇.layout hA.𝔇.shape (2 * g + 1)
      Ap.seam.tl = true := by
  have hX : Verify.publicOf Zl.pol Zl.KL (some Zl.lay) = .ok Zp.p.X := hA.pubOne
  have C := OnBytes.Road.Hd.core_of_scope hA.scope hA.reads hX
  obtain ⟨i6, _, _⟩ := _root_.Meaning.ix_of_core hX C
  obtain ⟨_, _, n1, _⟩ := _root_.Meaning.matsAt_att_gid hX C hg
  have etl : _root_.Meaning.tlAt Zp.p.X (2 * g + 1) = Ap.seam.tl := by
    unfold _root_.Meaning.tlAt
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
      show (2 * g + 1) / 2 = g by omega, hAp]
    rfl
  have hk : 2 * g + 1 < 25 := by omega
  have e5 : Ap.seam.tl.NM = 5 := by
    rw [← etl, _root_.Meaning.nm_of_core hX C hk]
    exact _root_.Meaning.size_odd hX C hg
  have hlay : hA.𝔇.layout = layoutFull :=
    VerifiableInference.PlanWritten.Joined.layout_in_scope hA.scope hA.laid.pub hP1
  rw [hlay, hDsh_atAll hA O hP1]
  unfold symsSeatedB
  refine List.all_eq_true.2 fun μ hμ => ?_
  have hμ5 : μ < 5 := by
    rw [← e5]
    exact List.mem_range.1 hμ
  have hμm : μ < (_root_.Meaning.matsAt Zp.p.X (2 * g + 1)).size := by
    rw [_root_.Meaning.size_odd hX C hg]
    exact hμ5
  have hμs : μ < (_root_.Meaning.sizesOf Zp.p.X (2 * g + 1)).NM := by
    rw [(_root_.Meaning.follows_of_core hX C).NM _ hk]
    exact hμm
  have hn := H2K5.Names.names_tie_att hA.scope hA.reads O hg hμs
  rw [etl] at hn
  have hn' : (hA.𝔇.pubD.d3.arrayOf.getD (2 * g + 1) #[])[Ap.seam.tl.gtTree.getD μ 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g + 1) μ),
        _root_.Meaning.nameOf
          (_root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g + 1) μ))) := hn
  have hw : seatOkB layoutFull shapeFull (2 * g + 1) (attPair g μ) = true :=
    List.all_eq_true.1 (List.all_eq_true.1 atts_written g (List.mem_range.2 hg)) μ
      (List.mem_range.2 hμ5)
  have ol := _root_.Meaning.owner_label hX C hk hμm
  have hpair : (_root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g + 1) μ),
      _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g + 1) μ))) =
      attPair g μ := by
    by_cases e : μ = 4
    · subst e
      have oo : _root_.Meaning.ownerOf Zp.p.X (2 * g + 1) 4 = (2 * g, 6) := by
        unfold _root_.Meaning.ownerOf
        rw [if_neg (by omega), if_pos (by omega), show (2 * g + 1) / 2 = g by omega, n1,
          if_pos rfl, i6, show 2 * g + 1 - 1 = 2 * g by omega]
      rw [oo] at ol
      have eK : _root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g + 1) 4) = 2 * g :=
        congrArg Prod.fst ol
      have eA : _root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g + 1) 4) = 6 :=
        congrArg Prod.snd ol
      rw [eK, eA]
      rfl
    · have oo : _root_.Meaning.ownerOf Zp.p.X (2 * g + 1) μ = (2 * g + 1, μ) := by
        unfold _root_.Meaning.ownerOf
        rw [if_neg (by omega), if_pos (by omega), show (2 * g + 1) / 2 = g by omega, n1,
          if_neg (by omega)]
      rw [oo] at ol
      have eK : _root_.Meaning.ownerK (_root_.Meaning.labAt Zp.p.X (2 * g + 1) μ) = 2 * g + 1 :=
        congrArg Prod.fst ol
      have eA : _root_.Meaning.ownerA (_root_.Meaning.labAt Zp.p.X (2 * g + 1) μ) = μ :=
        congrArg Prod.snd ol
      rw [eK, eA]
      unfold attPair
      rw [if_neg (by simpa using e)]
  rw [hn', hpair]
  exact hw

/-- **The field hBattB.** -/
theorem hBattB_atAll :
    battB hA.𝔇.pubD.d3.arrayOf (P5J.At.X Zp) hA.𝔇.layout hA.𝔇.shape = true := by
  unfold battB
  refine List.all_eq_true.2 fun l hl => ?_
  have hl' : l < 25 := List.mem_range.1 hl
  by_cases hs : (linksFull[l]?).getD .layers = ModelPart.attention
  · obtain ⟨e, h12⟩ := att_odd l hl' hs
    rw [Bool.or_eq_true]
    right
    cases hG : (P5J.At.X Zp).A[l / 2]? with
    | none => rfl
    | some Ap =>
      have h := syms_att_atAll hA O hP1 (l / 2) h12 Ap hG
      rw [e] at h
      exact h
  · rw [Bool.or_eq_true]
    left
    simpa using hs

end

end VerifiableInference.Desc.K1
