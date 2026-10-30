-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09EndC.lean: ON THE SECOND ROAD: BENEATH `AtMgA.K9LastC` (K09LastC.lean): THE JOIN AT
THE THIRTEEN OTHER LINKS OF THE CLOSED CONSTANT, AND WITH IT THE END OF THE ROAD: at the twelve
attention links and at the output head's link the law's letters are laid and every field of
`AttLeftC` and of `HeadLeftC` is taken from its payer: NO NAMED DEBT IS LEFT: THE BATCHING KIND's
FIELD `h.Kind 𝔏 .K9` FROM THE HEAD `AtMgA` AND THE TOWER's THREE EQUATIONS. Theorems.

What is said.
  `sub_three`, `odd_of_att`, `last_of_head`: a link is of one of three sorts; an attention link has
    an odd number below 24; the output head's link is link 24. `attLeftC_at`, `headLeftC_at`: **the
    attention's clause and the output head's clause of `K9LeftC`, to the letter**, from: the head
    `AtMgA`; the opening of the description; the list that `At.laid? Zp` lists, with the facts along
    the fold; letters that sit at the link, with p the plan's own; what `digAt` answers there; a run
    at the smallness test's equations; the link's sort, and g < 12 at attention. NO OTHER PREMISE.
    LETTERS LAID: β := `BetaAll`; ψ :=
    `psiAll`; rd := `rdAll`, c := `parCOf A` at the attention's plan A of the link's number; hS,
    iU3, p6, kap := the plan's shape, `readsOf`, `parOf … (workOf …)`, `kapAll`; Kx := `kxAtt`,
    `kxHead` at the two places of the link's lookups; t3, l3 := `t3All`, `l3All` there, at another
    file's worths of the callers' forms (`bvAtt`, `pvAtt`, `kvAtt`; `bvHead`, `pvHead`; the output
    head's third worth, which no entry of that link reads, at 0); nU := `ProofFile.k8NU Bs.G₀ X` at the
    built link X; d := p.rows; the letters in which every payer is general are laid at hand: u :=
    tlD, lm := 0; at the output head's link l' := 24, piece := 4.
    PAYERS: the sort's own fields whole (`LPFK9.attOwesC_g`, `LPFK9.headOwesC_24`);
    the two places (`P1K9.bothPlaces_at_head`); Anumbers (`LPFK9.numbers_attC_at`,
    `numbers_headC_at`); AreadyS (`aready_att_hd2`, `aready_head_hd2`); hitems (`hitems_att_at`,
    `hitems_head_at`, with `ok0_att_hd2`, `ok0_head_hd2`, `in8_at`, `hrun_at`, and at the lookup's
    entries: "objects": `k3i_objects_att_at`, `k3i_objects_head_at`; "planes":
    `LPFK9.k3i_planes_att_g`, `k3i_planes_head_24`; "join": `LPFK9.k3i_join_att_g`,
    `k3i_join_head_at`); hLeft (`hLeftG_of_rest`, `AtMgA.leftRestG_at`, `leftD_at`); inSeg, inTot,
    inRun (`AtMgA.inSeg_at`, `inTot_at`, `inRun_at`, with `insF_after_attention`, `insF_after_head`,
    `ahs1_at`). `k9LastC_at_head`: **`h.K9LastC 𝔏` at every filling 𝔏.** `k09_kind_of_head`:
    **`h.Kind 𝔏 .K9` from the head `AtMgA` at the second hash function and the tower's own three
    equations on the flat lists' heads: no other premise.**

Limits. A JOIN OF THEOREMS THAT LAY: its worth is that Lean holds each payer against the field's own
type. «FROM THE
HEAD» MEANS: FROM ALL THE FIELDS OF `AtMgA` (Johnson/P5J/MgAtAll.lean), NOT FROM THE ENTRY TESTS
ALONE; THAT A HEAD EXISTS IS NOT SAID HERE: the theorem is an implication. THAT A STATE MEETS THE
CONDITION IN FRONT OF THE BATCHING (the table's promise and «reached») AT ANY OF THE 25 BORDERS IS
SHOWN NOWHERE BENEATH: six of `CoreLeftC`'s seven fields stand under that condition. The letters
laid at hand (u, lm, the worths at 0) stand in no end: nothing may be read off them. The batching
kind and the frame's 25 ties behind it hang on this one cone (`k09_behindTies`, K09Behind.lean,
opens the condition whole). The field is one kind's share of the tower's conditions: it says nothing
alone. AT THE SECOND HASH FUNCTION AND THE FULL SIZE ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09LastC
import Johnson.P5J.K09AreadyHd2
import Johnson.LPFK9R.OwesAtLetters
import Johnson.LPFE1R.HrunAt347
import Johnson.P1K9R.ItemObjectsHead
import Johnson.P1K9R.ItemJoinHead
import Johnson.LPFK9R.ItemPlanesAtLetters
import Johnson.LPFK9R.ItemJoinAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Stages (LinkH)
open OnBytes.PscRun (Sized)
open OnBytes.Tie.Pv.Tail.Closed (shapesOf layShapes attShapes nScores)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Link Chain)
open VerifiableInference.Desc.First (S ModelPart)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.Desc.First.Att.P (ParC)
open VerifiableInference.Desc.Kinds.Head.Law (tabsOfPlan)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K9Asks (funs_layers funs_att funs_head)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (batchAt onTR frontAt kx_of_table ledger_at_front
  part_at_batch_all K9Closed K9OwnL K9OwnA K9OwnH PosPlan OkCoreLess core_layers_front
  core_att_front core_head_front NumbersOk hmS_at digHeard_of_leftOn leftOn_digits_front
  leftOn_digits_head ledgerB_of_sized merge_clause_347 entsMerge_at_347 OkCore OkLayers OkAtt
  OkHead pi8)
open Johnson.Desc.First.Walk.Tied (Reach)
open _root_.Desc.K14.Law (seatZ secondAt)

open VerifiableInference.Desc.First.Att.P (parCOf)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (readsOf workOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

open VerifiableInference.Desc.LinkJoin (atRec AttLeftC HeadLeftC take_of_attOwesC take_of_headOwesC
  share_of_attOwesC share_of_headOwesC sortItems HitemsLeft hitems_att_at hitems_head_at
  in8_at hrun_at k3i_objects_att_at k3i_objects_head_at k3i_join_head_at insF_after_attention
  insF_after_head foldFacts_at SegAt hLeftG_of_rest)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.EntryUnit (entUnit)
open IM (subAt)

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps

/-- A link is of one of three sorts. -/
theorem sub_three (m : ℕ) : subAt m = .layers ∨ subAt m = .attention ∨ subAt m = .head := by
  unfold IM.subAt
  split_ifs <;> simp

/-- An attention link has an odd number below 24. -/
theorem odd_of_att {m : ℕ} (hm : m < 25) (hs : subAt m = .attention) :
    ∃ g < 12, m = 2 * g + 1 := by
  by_cases h1 : m = 24
  · subst h1
    exact absurd hs (by decide)
  · by_cases h2 : m % 2 = 0
    · exact absurd hs (by simp [IM.subAt, h1, h2])
    · exact ⟨m / 2, by omega, by omega⟩

/-- The head's link is link 24. -/
theorem last_of_head {m : ℕ} (hs : subAt m = .head) : m = 24 := by
  by_contra h1
  by_cases h2 : m % 2 = 0
  · exact absurd hs (by simp [IM.subAt, h1, h2])
  · exact absurd hs (by simp [IM.subAt, h1, h2])

/-- **THE ATTENTION's CLAUSE OF WHAT IS LEFT: FROM THE HEAD `AtMgA`.** -/
theorem attLeftC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (hLd : At.laid? Zp = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    {g : ℕ} (hg : g < 12) (hs : subAt (2 * g + 1) = .attention) {L : _} {p : _} {Q : _}
    {b₃ b₅ : _} (St : h.Sits (2 * g + 1) L p Q b₃ b₅) (kp : IM.k9At Zp (2 * g + 1) = some p)
    (pb : _) (xx : _) (tlD : HTailF2)
    (hdig : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g + 1) = some (xx, tlD))
    (run : _)
    (hAt : VerifiableInference.Desc.LinkJoin.At L (4, "K8.equations") run) :
    ∃ (β : Type) (rd : _) (c : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _)
      (d : ℕ), ∀ z,
      AttLeftC (F := FrK) h.𝔇 fullLinks At.ps z
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt (2 * g + 1)) (2 * g + 1) rd c
        Kx t3 l3 L u ψ nU p d (At.foldD Zp cF Ld).M.length pb (sortItems .attention) run xx tlD
        (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
        (At.foldD Zp cF Ld) := by
  have hm : 2 * g + 1 < 25 := by omega
  have seg' : SegAt (2 * g + 1) .attention L := hs ▸ St.seg
  obtain ⟨A, X, hA, e3, W⟩ := LPFK9.attOwesC_g h O hg hs L p St.lk St.seg St.drawB kp
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h (2 * g + 1) hm
  have OW := W (kxAtt pC.lm pC.first 0 pD.first (parCOf A) (ProofFile.k8NU Bs.G₀ X)) pC.lm pC.first 0
    pD.first tlD tlD kxAtt_k3 kxAtt_planes
    (fun pl e => by obtain rfl := Option.some.inj (hC.symm.trans e); rfl)
  have T := take_of_attOwesC OW
  refine ⟨BetaAll, rdAll, parCOf A, _, _, _, tlD, psiAll, _, p.rows, fun z => ⟨OW, ?_⟩⟩
  have ok := ok0_att_hd2 h O hg hA e3 hdig z tlD 0 hC hD
  have hK : ∀ q, OkAtt rdAll (parCOf A) (ProofFile.k8NU Bs.G₀ X) tlD q ∧
      kxAtt pC.lm pC.first 0 pD.first (parCOf A) (ProofFile.k8NU Bs.G₀ X) q →
      kxAll pC.lm pC.first 0 pD.first q := fun _ hq => kxAtt_k3 _ hq.2
  exact ⟨LPFK9.numbers_attC_at h.toAtMg (2 * g + 1) hm p kp seg' tlD _ _ tlD _ _ _ _ _ _ _ _
      kxAtt_numbers,
    aready_att_hd2 h O hg hA e3 hdig z p tlD 0 hC hD,
    hitems_att_at h z hm hs St.lk seg' T run hAt _ (fun n _ _ => numbered_snd _ n) _
      ⟨ok, fun a ha => by
        have := in8_at h hm z _ (foldFacts_at Fo z)
          (LPFK9.hall_of_moments _ _ _ _ _ (2 * g + 1) (h.toAtMg.shape_moments (2 * g + 1))) a ha
        rw [hs] at this
        exact this, fun a w ha e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact k3i_objects_att_at h z hm hs St.lk seg' hK rdAll (parCOf A) _ ok a w ha _ (by simp)
        · exact LPFK9.k3i_join_att_g h O hg hs L St.lk St.seg hA _ _ _ _ _ tlD tlD z _ ok a w ha
        · exact LPFK9.k3i_planes_att_g h O hg hs L St.lk St.seg hA hC _ _ _ _ tlD tlD z _ ok a w ha
        · exact k3i_objects_att_at h z hm hs St.lk seg' hK rdAll (parCOf A) _ ok a w ha _
            (by simp)⟩,
    hLeftG_of_rest h.𝔇 fullLinks At.ps z _ _ (2 * g + 1) L tlD psiAll _ _ xx tlD _ pb
      (h.leftRestG_at hLd Fo hm hdig z tlD psiAll _ _ (fun _ hq => hq.1.1.core)
        (fun a ho => leftD_at h hm hdig z a ho 0)),
    h.inSeg_at hm z,
    h.inRun_at hm z L (insF_after_attention seg' T)
      (ahs1_at h (2 * g + 1) hm St (share_of_attOwesC OW) z),
    h.inTot_at hm z⟩

/-- **THE CLAUSE OF WHAT IS LEFT AT THE OUTPUT HEAD's LINK: FROM THE HEAD `AtMgA`.** -/
theorem headLeftC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (hLd : At.laid? Zp = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    (hs : subAt 24 = .head) {L : _} {p : _} {Q : _} {b₃ b₅ : _}
    (St : h.Sits 24 L p Q b₃ b₅) (kp : IM.k9At Zp 24 = some p) (pb : _) (xx : _) (tlD : HTailF2)
    (hdig : VerifiableInference.Desc.First.Look.digAt (At.X Zp) 24 = some (xx, tlD))
    (run : _)
    (hAt : VerifiableInference.Desc.LinkJoin.At L (5, "K8.equations") run) :
    ∃ (β : Type) (hS : _) (iU3 l' piece : ℕ) (p6 : _) (kap : _) (Kx : _) (t3 : _) (l3 : _)
      (u : _) (ψ : S → β) (nU : _) (d : ℕ), ∀ z,
      HeadLeftC (F := FrK) h.𝔇 fullLinks At.ps z
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt 24) 24 hS iU3 l' piece p6 kap
        Kx t3 l3 L u ψ nU p d (At.foldD Zp cF Ld).M.length pb (sortItems .head) run xx tlD
        (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
        (At.foldD Zp cF Ld) := by
  have hm : 24 < 25 := by omega
  have seg' : SegAt 24 .head L := hs ▸ St.seg
  obtain ⟨X, e3, W⟩ := LPFK9.headOwesC_24 h O hs L p St.lk St.seg St.drawB kp
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h 24 hm
  have OW := W (kxHead pC.lm pC.first 0 pD.first (readsOf Bs.G₀.W) (ProofFile.k8NU Bs.G₀ X)) pC.lm
    pC.first 0 pD.first (fun _ _ _ => 0) tlD tlD kxHead_k3 kxHead_planes
    (fun pl e => by obtain rfl := Option.some.inj (hC.symm.trans e); rfl)
  have T := take_of_headOwesC OW
  refine ⟨BetaAll, _, _, 24, 4, _, kapAll, _, _, _, tlD, psiAll, _, p.rows, fun z => ⟨OW, ?_⟩⟩
  have ok := ok0_head_hd2 h O e3 hdig z tlD 0 hC hD
  have hK : ∀ q, OkHead Bs.G₀.W.hS (readsOf Bs.G₀.W) (parOf Bs.G₀.W.hS (workOf Bs.G₀.W)) kapAll
      (ProofFile.k8NU Bs.G₀ X) tlD q ∧
      kxHead pC.lm pC.first 0 pD.first (readsOf Bs.G₀.W) (ProofFile.k8NU Bs.G₀ X) q →
      kxAll pC.lm pC.first 0 pD.first q := fun _ hq => kxHead_k3 _ hq.2
  exact ⟨LPFK9.numbers_headC_at h.toAtMg 24 hm p kp seg' tlD _ _ _ _ tlD _ _ _ _ _ _ _ _
      kxHead_numbers,
    aready_head_hd2 h O e3 hdig z p tlD 0 hC hD,
    hitems_head_at h z St.lk seg' T run hAt _ (fun n _ _ => numbered_snd _ n) _
      ⟨ok, fun a ha => by
        have := in8_at h hm z _ (foldFacts_at Fo z)
          (LPFK9.hall_of_moments _ _ _ _ _ 24 (h.toAtMg.shape_moments 24)) a ha
        rw [hs] at this
        exact this, fun a w ha e he => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl
        · exact k3i_objects_head_at h z St.lk seg' hK _ _ _ kapAll _ ok a w ha _ (by simp)
        · exact k3i_join_head_at h z St.lk seg' T _ ok a w ha
        · exact LPFK9.k3i_planes_head_24 h O hs L St.lk St.seg hC _ _ _ _ _ tlD tlD z _ ok a w ha
        · exact k3i_objects_head_at h z St.lk seg' hK _ _ _ kapAll _ ok a w ha _ (by simp)⟩
      (hrun_at h z St.lk),
    hLeftG_of_rest h.𝔇 fullLinks At.ps z _ _ 24 L tlD psiAll _ _ xx tlD _ pb
      (h.leftRestG_at hLd Fo hm hdig z tlD psiAll _ _ (fun _ hq => hq.1.1.core)
        (fun a ho => leftD_at h hm hdig z a ho 0)),
    h.inSeg_at hm z,
    h.inRun_at hm z L (insF_after_head seg' T) (ahs1_at h 24 hm St (share_of_headOwesC OW) z),
    h.inTot_at hm z⟩

/-- **THE NAMED DEBT IS MET, AT EVERY FILLING.** -/
theorem k9LastC_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : h.K9LastC 𝔏 := by
  intro Ld hLd m hm L p Q b₃ b₅ St kp qb _ xx tlD hdig
  obtain ⟨L', R⟩ := atMgR_rch_of_head h
  obtain rfl : L' = Ld := Option.some.inj (R.listed.symm.trans hLd)
  have Fo := k9_fold_of_atMgR h L' R
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  rcases sub_three m with hs | hs | hs
  · exact Or.inl hs
  · obtain ⟨g, hg, rfl⟩ := odd_of_att hm hs
    exact Or.inr (Or.inl ⟨hs, fun run hAt =>
      attLeftC_at h O L' hLd Fo hg hs St kp _ xx tlD hdig run hAt⟩)
  · obtain rfl := last_of_head hs
    exact Or.inr (Or.inr ⟨hs, fun run hAt =>
      headLeftC_at h O L' hLd Fo hs St kp _ xx tlD hdig run hAt⟩)

/-- **SO THE FIELD: THE BATCHING KIND's LAW AT THE CLOSED CONSTANT, FROM THE HEAD `AtMgA` AND THE
THREE EQUATIONS.** -/
theorem k09_kind_of_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    h.Kind 𝔏 .K9 :=
  k09_kind_of_lastC h 𝔏 q₁ q₂ q₃ (k9LastC_at_head h 𝔏)

end P5J

#print axioms P5J.sub_three
#print axioms P5J.odd_of_att
#print axioms P5J.last_of_head
#print axioms P5J.attLeftC_at
#print axioms P5J.headLeftC_at
#print axioms P5J.k9LastC_at_head
#print axioms P5J.k09_kind_of_head
