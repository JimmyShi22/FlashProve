-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09LastC.lean: ON THE SECOND ROAD: BENEATH `AtMgA.K9LeftC` (K09LeftC.lean, which does
not turn): THE LAST JOIN SO FAR: AT THE TWELVE LAYERS' LINKS OF THE CLOSED CONSTANT THE LAW's
LETTERS ARE LAID AND EVERY FIELD OF `LayersLeftC` IS TAKEN FROM ITS PAYER: NOTHING IS LEFT THERE; at
all 25 links the letters that sit (`sits_kp`) and the one closed sentence «the link's plan fits»
(`AtMg.linkPlan`, Johnson/P5T/SortsAtMg.lean) are laid in. At the attention's links
and the head's link the list is `K9LeftC`'s own, unturned. A definition and theorems.

What is said.
  `numbered_snd`: the second parts of a numbered list are the list. `even_of_layers`: a layers' link
    has an even number below 24. `layersLeftC_at`: **the layers' clause of `K9LeftC` at m := 2 g, to
    the letter**, from: the head; the opening of the description; the list that `At.laid? Zp` lists,
    with the facts along the fold; letters that sit at the link, with p the plan's own; what `digAt`
    answers there; a run at the smallness test's equations; g < 12 and the link's sort. NO OTHER
    PREMISE. LETTERS LAID: β :=
    `BetaAll`; ψ := `psiAll`; Kx := `kxAll3 pC.lm pC.first 0 pD.first` at the two places pC, pD of
    the link's lookups; t3, l3 := `t3All`, `l3All` there; nU := `ProofFile.k8NU Bs.G₀ X` at the built link
    X; d := p.rows; the letters in which every payer is general are laid at hand: u := tlD, lm := 0,
    the three worths of the callers' forms at 0 (a layers' link has no such entry). PAYERS: the
    sort's own fields whole (`LPFK9.layersOwesC_whole`); that the two places are there
    (`P1K9.bothPlaces_at_head`, Johnson/P1K9R/AreadyClosed.lean); Anumbers
    (`LPFK9.numbers_layersC_at`); AreadyS (`aready_layers_hd`, K09AreadyHd.lean); hitems
    (`hitems_layers_at`, with `ok0_layers_hd`, `in8_at`, and, at the lookup's two entries,
    `k3i_layers_at`, Johnson/P1K9R/ItemObjectsAt.lean); hLeft (`hLeftG_of_rest`,
    `AtMgA.leftRestG_at`, `leftD_at`); inSeg, inTot, inRun (`AtMgA.inSeg_at`, `inTot_at`,
    `inRun_at`, with `insF_after_layers`, `ahs1_at`). `AtMgA.K9LastC h 𝔏`: at the list that
    `At.laid? Zp` lists: at every link, at ALL letters that sit there with the plan's own p, at the
    row's piece at the batching's number and at what `digAt` answers: the link is a layers' link, or
    `K9LeftC`'s own clause for an attention link or for the head's holds. `k9LeftC_of_last`:
    **`h.K9LeftC 𝔏` from it.** `k09_kind_of_lastC`: **so `h.Kind 𝔏 .K9`**, under the tower's own
    three equations on the flat lists' heads.

Limits. A JOIN OF THEOREMS THAT LAY: its worth is that Lean holds each payer
against the field's own type. `K9LastC` is
a named condition: AT THE THIRTEEN OTHER LINKS NOTHING IS PAID HERE BUT THE LETTERS THAT SIT AND THE
PLAN's FIT; IT IS SHOWN FROM THE HEAD IN K09EndC.lean (`k9LastC_at_head`). «Nothing is left at a
layers' link» says that the link's clause follows from the head; it does not say that the head can
be met. WHETHER `K9LastC` CAN BE MET IS NOT SAID: no member is known. «From the head» means: from
all the fields of `AtMgA` (Johnson/P5J/MgAtAll.lean), not from the entry tests alone; that a head
exists is not said here. The letters laid at hand (u, lm, the worths at 0) stand in no end: nothing
may be read off them. AT THE SECOND HASH FUNCTION ALONE. Nothing on soundness.

-/
import Johnson.P5J.K09LeftC
import Johnson.P5J.K09AreadyHd
import Johnson.P5J.K09LeftD
import Johnson.P5J.K09LeftAllG
import Johnson.P5J.InsideAtCore
import Johnson.P5T.SortsAtMg
import Johnson.LPFK9R.LayersOwesWhole
import Johnson.LPFK9R.SortNumbersAtMgC
import Johnson.LPFE1R.HitemsAtConst
import Johnson.LPFE1R.In8OfFacts
import Johnson.P1K9R.ItemObjectsAt
import Johnson.Desc.First.Link.Law.InRunOfKeeps

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

open VerifiableInference.Desc.LinkJoin (NumbersThree okFront_at okBack_at entsFront_at entsBack_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrK" => frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0

open VerifiableInference.Desc.LinkJoin (atRec CoreLeftC LayersLeftC AttLeftC HeadLeftC LayersOwesC
  take_of_layersOwesC share_of_layersOwesC sortItems HitemsLeft hitems_layers_at in8_at
  k3i_layers_at
  insF_after_layers foldFacts_at SegAt tmL lenL tmFour hLeftG_of_rest)
open VerifiableInference.Desc.First (FoldFacts)
open VerifiableInference.Desc.EntryUnit (entUnit)
open IM (subAt)

local notation "FD" => F0T OnBytes.secondHashFunction Zp Np cF
local notation "kAt" => batchAt fullLinks At.ps

/-- The second parts of a numbered list are the list. -/
theorem numbered_snd {K : Type} : ∀ (l : List K) (n : ℕ), (numbered n l).map (·.2) = l
  | [], _ => rfl
  | v :: l, n => by simp only [numbered, List.map_cons, numbered_snd l (n + 1)]

/-- A layers' link has an even number below 24. -/
theorem even_of_layers {m : ℕ} (hm : m < 25) (hs : subAt m = .layers) : ∃ g < 12, m = 2 * g := by
  by_cases h1 : m = 24
  · subst h1
    exact absurd hs (by decide)
  · by_cases h2 : m % 2 = 0
    · exact ⟨m / 2, by omega, by omega⟩
    · exact absurd hs (by simp [IM.subAt, h1, h2])

/-- **THE LAYERS' CLAUSE OF WHAT IS LEFT: FROM THE HEAD `AtMgA`.** -/
theorem layersLeftC_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (Ld : VerifiableInference.Desc.K12.Door.Laid) (hLd : At.laid? Zp = some Ld)
    (Fo : FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps)
    {g : ℕ} (hg : g < 12) (hs : subAt (2 * g) = .layers) {L : _} {p : _} {Q : _} {b₃ b₅ : _}
    (St : h.Sits (2 * g) L p Q b₃ b₅) (kp : IM.k9At Zp (2 * g) = some p) (pb : _) (xx : _)
    (tlD : HTailF2)
    (hdig : VerifiableInference.Desc.First.Look.digAt (At.X Zp) (2 * g) = some (xx, tlD))
    (run : _)
    (hAt : VerifiableInference.Desc.LinkJoin.At L (4, "K8.equations") run) :
    ∃ (β : Type) (p4 : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _) (d : ℕ), ∀ z,
      LayersLeftC (F := FrK) h.𝔇 fullLinks At.ps z
        (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt (2 * g)) (2 * g) p4 Kx t3 l3 L
        u ψ nU p d (At.foldD Zp cF Ld).M.length pb (sortItems .layers) run xx tlD
        (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
        (At.foldD Zp cF Ld) := by
  have hm : 2 * g < 25 := by omega
  have seg' : SegAt (2 * g) .layers L := hs ▸ St.seg
  obtain ⟨p4, X, e1, e2, W⟩ :=
    LPFK9.layersOwesC_whole h O (2 * g) hm hs L p St.lk St.seg St.drawB kp
  obtain ⟨pC, pD, hC, hD⟩ := P1K9.bothPlaces_at_head h (2 * g) hm
  have e3 : Bs.G₀.built[2 * g]? = some X := by simpa using e2
  have OW := W (kxAll3 pC.lm pC.first 0 pD.first) pC.lm pC.first 0 pD.first (fun _ _ _ _ => 0)
    (fun _ _ _ => 0) (fun _ _ _ => 0) tlD tlD (fun _ hq => hq.1)
  have A := take_of_layersOwesC OW
  refine ⟨BetaAll, p4, _, _, _, tlD, psiAll, _, p.rows, fun z => ⟨OW, ?_⟩⟩
  have ok := ok0_layers_hd h O hg e3 hdig e1 z tlD 0 hC hD
  have hK : ∀ q, OkLayers p4 (ProofFile.k8NU Bs.G₀ X) tlD q ∧ kxAll3 pC.lm pC.first 0 pD.first q →
      kxAll pC.lm pC.first 0 pD.first q := fun _ hq => hq.2.1
  exact ⟨LPFK9.numbers_layersC_at h.toAtMg (2 * g) hm p kp seg' tlD p4 _ tlD _ _ _ _ _ _ _ _
      kxAll3_numbers,
    aready_layers_hd h O hg e3 hdig e1 z p tlD 0 hC hD,
    hitems_layers_at h z hm hs St.lk seg' A run hAt _ (fun n _ _ => numbered_snd _ n) _
      ⟨ok, fun a ha => by
        have := in8_at h hm z _ (foldFacts_at Fo z)
          (LPFK9.hall_of_moments _ _ _ _ _ (2 * g) (h.toAtMg.shape_moments (2 * g))) a ha
        rw [hs] at this
        exact this, k3i_layers_at h z hm hs St.lk seg' hK p4 _ ok⟩,
    hLeftG_of_rest h.𝔇 fullLinks At.ps z _ _ (2 * g) L tlD psiAll _ _ xx tlD _ pb
      (h.leftRestG_at hLd Fo hm hdig z tlD psiAll _ _ (fun _ hq => hq.1.1.core)
        (fun a ho => leftD_at h hm hdig z a ho 0)),
    h.inSeg_at hm z,
    h.inRun_at hm z L (insF_after_layers seg' A)
      (ahs1_at h (2 * g) hm St (share_of_layersOwesC OW) z),
    h.inTot_at hm z⟩

/-- **WHAT IS LEFT OF THE CONDITION, THE LAYERS' LINKS JOINED.** -/
def AtMgA.K9LastC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) : Prop :=
  ∀ Ld, At.laid? Zp = some Ld →
  ∀ m < 25, ∀ L p Q b₃ b₅, h.Sits m L p Q b₃ b₅ → IM.k9At Zp m = some p →
    ∀ qb, (h.toAtMg.row 𝔏)[kAt m]? = some qb → ∀ xx tlD,
      VerifiableInference.Desc.First.Look.digAt (At.X Zp) m = some (xx, tlD) →
      subAt m = .layers ∨
      (subAt m = .attention ∧
        ∀ run, VerifiableInference.Desc.LinkJoin.At L (4, "K8.equations") run →
        ∃ (β : Type) (rd : _) (c : _) (Kx : _) (t3 : _) (l3 : _) (u : _) (ψ : S → β) (nU : _)
        (d : ℕ), ∀ z,
        AttLeftC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m rd c Kx t3 l3 L u ψ nU
          p d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB)) (sortItems .attention) run
          xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld)) ∨
      (subAt m = .head ∧ ∀ run, VerifiableInference.Desc.LinkJoin.At L (5, "K8.equations") run →
        ∃ (β : Type) (hS : _) (iU3 l' piece : ℕ) (p6 : _) (kap : _) (Kx : _) (t3 : _) (l3 : _)
        (u : _) (ψ : S → β) (nU : _) (d : ℕ), ∀ z,
        HeadLeftC (F := FrK) h.𝔇 fullLinks At.ps z
          (VerifiableInference.Desc.LinkJoin.RchAt h.toAtMg.rch z) (kAt m) m hS iU3 l' piece p6 kap
          Kx t3 l3 L u ψ nU p d (At.foldD Zp cF Ld).M.length (atRec qb (below L.batchB))
          (sortItems .head) run xx tlD
          (Params.settingOf (At.X Zp).P.frame) Cb.Gl.p (fun j => h.𝔇.l3.seat xx.link true j.1)
          (At.foldD Zp cF Ld))

/-- **WHAT IS LEFT, FROM IT.** -/
theorem k9LeftC_of_last (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (H : h.K9LastC 𝔏) : h.K9LeftC 𝔏 := by
  intro Ld hLd m hm
  obtain ⟨L', R⟩ := atMgR_rch_of_head h
  obtain rfl : L' = Ld := Option.some.inj (R.listed.symm.trans hLd)
  have Fo := k9_fold_of_atMgR h L' R
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨L, p, Q, b₃, b₅, St, kp⟩ := sits_kp h m hm
  refine ⟨L, p, Q, b₃, b₅, St, kp, h.toAtMg.linkPlan hm, fun qb hb xx tlD hdig => ?_⟩
  rcases H L' hLd m hm L p Q b₃ b₅ St kp qb hb xx tlD hdig with
    hs | G | G
  · obtain ⟨g, hg, rfl⟩ := even_of_layers hm hs
    exact Or.inl ⟨hs, fun run hAt =>
      layersLeftC_at h O L' hLd Fo hg hs St kp _ xx tlD hdig run hAt⟩
  · exact Or.inr (Or.inl G)
  · exact Or.inr (Or.inr G)

/-- **SO THE FIELD.** -/
theorem k09_kind_of_lastC (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D FD At.Tok) (q₁ : (FD).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (FD).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂) (q₃ : (FD).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (H : h.K9LastC 𝔏) : h.Kind 𝔏 .K9 :=
  k09_kind_of_leftC h 𝔏 q₁ q₂ q₃ (k9LeftC_of_last h 𝔏 H)

end P5J

#print axioms P5J.numbered_snd
#print axioms P5J.even_of_layers
#print axioms P5J.layersLeftC_at
#print axioms P5J.k9LeftC_of_last
#print axioms P5J.k09_kind_of_lastC
