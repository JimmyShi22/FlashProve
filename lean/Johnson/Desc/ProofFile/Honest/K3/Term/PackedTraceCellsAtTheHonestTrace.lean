-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT, UNDER THE LIBRARY's HEAD ON THE PUBLIC INPUT, AT INPUTS THAT HOLD THE HONEST TRACE.
Johnson/Desc/ProofFile/Honest/K3/Term/PackedTraceCellsAtTheHonestTrace.lean: the honest side of the
kind "lookup" (K3): the two named premises on the calls' cells
(`ScriptHoldsThePackedTraceCells`, `TraceCellsAreSmall`, Term/ScriptHoldsTheHonestValues.lean) AT THE
CLOSED LETTER `traceMatricesOfTheCells`, with the seams between links, the planes' sizes and the tail
PAID: from the senders' sentence `LaysFilling` AT THE LINKS AT OR IN FRONT OF THE LOOKUP's and the
readers' tie ALONE. (Asked at all 25 links at one number of challenges the sentence could not be met
together with the spender's bound on that number: a later link's senders have not spoken yet.)

  `linksTailIsTheMeanings`                    ON PUBLIC DATA: the two readers of a link's tail are one
  `ownersCellsAreTheBorrowersAtTheHonestTrace`  the seams, in the filling's own letters (`Sz.owner`)
  `ownersLinkIsBelowTwentyFive`               ON PUBLIC DATA
  `ownersLinkIsAtMostTheLink`                 by the filling's own text
  `laysFillingAtMoreChallenges`               the sentence is monotone in its number of challenges
  `packedTraceCellsAtTheHonestTrace`          sign 1, at a place read at its link, at `Meaning.tlAt`'s tail
  `traceCellsOfTheInputAreSmall`              sign 2, at every tail
  `packedTraceCellsAtAttention`, `…AtLayers`, `…AtTheHead`   sign 1 in the three forms that the bundle at
                                              the calls binds (`attAt` · `layAt` with `tlAt` · the head's place)

Limits. CONDITIONAL: the head; `validInputsHoldTheHonestTrace`; `readersReadTheTrace`; `lays`: NO FILE SHOWS
`LaysFilling` OF ANY SCRIPT, so nothing here is tested for emptiness. The input's trace type is
`Cells`, read by the identity. The full size and the earlier hash alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.PackedTraceCellsFromLaysFilling
import Johnson.Desc.ProofFile.Honest.K3.Term.PlanesSizesAreTheFillings
import Johnson.Desc.ProofFile.Honest.K3.Term.BorrowedMatricesBearOneNumber
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupDataAtTheHonestTrace
import Johnson.Desc.First.Look.K3PlanLetters
import Johnson.Desc.First.Look.K3PlanLettersLay
import Johnson.Desc.Sound.MgAt.K3CallsOwedScope
import Johnson.Desc.Sound.MgAt.K3HeadR
import Johnson.P1K8R.BlindOwesAt
import Johnson.Goal.Meaning.PlanNames

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName theTrace matAt_eq_some_iff below_of_mu)
open OnBytes.Model.Verify (publicOf)
open Inst.Model (Instance ppref ScalesAndPolicy)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (szOf attAt layAt attAt_letters layAt_letters)
open VerifiableInference.OnPublicFiles (attAt_odd layAt_even headAt_link)
open ProofFile.Honest.FirstThread (Script)
open ProofFile.Honest.K5 (LaysFilling)
open P5J (AtMgA TS CellsM)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "tailAt" => VerifiableInference.Desc.First.Look.tlAt

/-! ## 1 On public data, and the seams -/

section scope
variable {Zl : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : OnBytes.Model.Verify.Public}

/-- **The lookups' reader of a link's tail answers, and answers the library's `Meaning.tlAt`.**
CONDITIONAL: the three premises on the public files; the link is below 25. -/
theorem linksTailIsTheMeanings (inScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp)
    (publicPartMade : publicOf Zl.pol Zl.KL lay = .ok X) {link : ℕ} (linkBelow : link < 25) :
    tailAt X link = some (_root_.Meaning.tlAt X link) := by
  obtain ⟨p4, groups, -, -⟩ := _root_.Meaning.scope_plans inScope filesRead publicPartMade
  unfold VerifiableInference.Desc.First.Look.tlAt _root_.Meaning.tlAt
  simp only [p4, groups, ↓reduceIte]
  rw [if_neg (by omega : ¬ 24 < link)]
  by_cases h24 : link = 24
  · subst h24
    simp
  · rw [if_neg (by simp only [beq_iff_eq]; omega), if_neg h24]
    by_cases he : link % 2 = 0
    · obtain ⟨⟨P, hP⟩, -⟩ :=
        _root_.Meaning.scope_plans24 inScope filesRead publicPartMade (link / 2) (by omega)
      rw [if_pos (by simp only [beq_iff_eq]; exact he), if_pos he, hP]
      rfl
    · obtain ⟨-, a, ha, -⟩ :=
        _root_.Meaning.scope_plans24 inScope filesRead publicPartMade (link / 2) (by omega)
      rw [if_neg (by simp only [beq_iff_eq]; exact he), if_neg he, ha]
      rfl

/-- **THE SEAMS, in the filling's own letters**: at the honest trace's cells the owner's link and
name answer what the link and the matrix's own name answer. For a matrix of the link's own:
nothing. For the 24 borrowed ones: the three laws of Term/BorrowedMatricesBearOneNumber.lean. -/
theorem ownersCellsAreTheBorrowersAtTheHonestTrace (inScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp)
    (publicPartMade : publicOf Zl.pol Zl.KL lay = .ok X) (index : Cm.Idx)
    (request : Instance ppref) {link number : ℕ} {segment : Seg} {name : MatName}
    (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) (row column : ℕ) :
    OnBytes.HonestTrace.cellOf X (theTrace X index request) ((Sz.ref.owner segment name).1.no 12)
        (Sz.ref.owner segment name).2.label row column =
      OnBytes.HonestTrace.cellOf X (theTrace X index request) link name.label row column := by
  obtain ⟨hb, hno, -⟩ := (matAt_eq_some_iff Sz.ref _ _ _ _).1 isTheMatrix
  have hno' : segment.no 12 = link := hno
  subst hno'
  cases segment with
  | ff g =>
    have hg : g < 12 := hb
    by_cases hx : name = .xbI
    · subst hx
      by_cases h0 : g = 0
      · have e : Sz.ref.owner (.ff g) .xbI = (.ff g, .xbI) := if_pos h0
        rw [e]
      · have e : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
        rw [e]
        exact (groupReadsTheStreamOfTheGroupBefore inScope filesRead publicPartMade index request
          (Nat.pos_of_ne_zero h0) hg row column).symm
    · have e : Sz.ref.owner (.ff g) name = (.ff g, name) := by
        cases name <;> first | rfl | exact absurd rfl hx
      rw [e]
  | att g =>
    have hg : g < 12 := hb
    by_cases hx : name = .qa
    · subst hx
      exact attentionReadsTheQaOfItsGroup inScope filesRead publicPartMade index request hg row
        column
    · have e : Sz.ref.owner (.att g) name = (.att g, name) := by
        cases name <;> first | rfl | exact absurd rfl hx
      rw [e]
  | head =>
    by_cases hx : name = .xbL
    · subst hx
      exact (headReadsTheStreamOfTheLastGroup inScope filesRead publicPartMade index request row
        column).symm
    · have e : Sz.ref.owner .head name = (.head, name) := by
        cases name <;> first | rfl | exact absurd rfl hx
      rw [e]

/-- **The owner's link is one of the 25.** -/
theorem ownersLinkIsBelowTwentyFive (inScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp)
    (publicPartMade : publicOf Zl.pol Zl.KL lay = .ok X) {link number : ℕ} {segment : Seg}
    {name : MatName} (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) :
    (Sz.ref.owner segment name).1.no 12 < 25 := by
  have k2 := (ownerNumbersAtEveryLink inScope filesRead publicPartMade isTheMatrix).2
  have hb : (Sz.ref.owner segment name).1.Below 12 := below_of_mu (by rw [k2]; rfl)
  generalize (Sz.ref.owner segment name).1 = τ at hb
  cases τ with
  | ff g =>
    have hg : g < 12 := hb
    show 2 * g < 25
    omega
  | att g =>
    have hg : g < 12 := hb
    show 2 * g + 1 < 25
    omega
  | head => exact (by decide : 2 * 12 < 25)

end scope

/-- **The owner's link stands at or in front of the link.** By the filling's own text of who
committed a matrix: no premise on any file. -/
theorem ownersLinkIsAtMostTheLink {link number : ℕ} {segment : Seg} {name : MatName}
    (isTheMatrix : Sz.ref.matAt link number = some (segment, name)) :
    (Sz.ref.owner segment name).1.no 12 ≤ link := by
  obtain ⟨-, hno, -⟩ := (matAt_eq_some_iff Sz.ref _ _ _ _).1 isTheMatrix
  have hno' : segment.no 12 = link := hno
  subst hno'
  cases segment with
  | ff g =>
    by_cases hx : name = .xbI
    · subst hx
      by_cases h0 : g = 0
      · have e : Sz.ref.owner (.ff g) .xbI = (.ff g, .xbI) := if_pos h0
        rw [e]
      · have e : Sz.ref.owner (.ff g) .xbI = (.ff (g - 1), .xbO) := if_neg h0
        rw [e]
        show 2 * (g - 1) ≤ 2 * g
        omega
    · have e : Sz.ref.owner (.ff g) name = (.ff g, name) := by
        cases name <;> first | rfl | exact absurd rfl hx
      rw [e]
  | att g =>
    by_cases hx : name = .qa
    · subst hx
      show 2 * g ≤ 2 * g + 1
      omega
    · have e : Sz.ref.owner (.att g) name = (.att g, name) := by
        cases name <;> first | rfl | exact absurd rfl hx
      rw [e]
  | head =>
    by_cases hx : name = .xbL
    · subst hx
      exact (by decide : 2 * (12 - 1) ≤ 2 * 12)
    · have e : Sz.ref.owner .head name = (.head, name) := by
        cases name <;> first | rfl | exact absurd rfl hx
      rw [e]

/-! ## 2 The two signs at the closed letter -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc : Type}
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Cells) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  {weights : W₀ → Weights} {valid : Local W₀ Rc ProofFile.Inst Cells → Prop} {challengesHeard : ℕ}
  {readers : Local W₀ Rc ProofFile.Inst Cells → Readers}

/-- **The senders' sentence passes to every larger number of challenges.** -/
theorem laysFillingAtMoreChallenges {fewer more : ℕ} (atMost : fewer ≤ more)
    {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ} {link : ℕ}
    (lays : LaysFilling h Q valid fewer readers seat heard link) :
    LaysFilling h Q valid more readers seat heard link :=
  ⟨fun As A hl hA hs => by
      obtain ⟨Ad, hAd, hh⟩ := lays.reach As A hl hA hs
      exact ⟨Ad, hAd, Nat.le_trans hh atMost⟩,
    fun k v hd hv hN => lays.lays k v hd hv (Nat.le_trans atMost hN)⟩

/-- **SIGN 1 AT THE CLOSED LETTER, FROM THE SENDERS' SENTENCE AND THE READERS' TIE ALONE**, at a place
read at its link, at the library's tail of that link. THE SENTENCE IS ASKED AT THE LINKS AT OR IN FRONT
OF THE PLACE's ALONE, each at seats of its own: a link's matrices are its own or an earlier link's. -/
theorem packedTraceCellsAtTheHonestTrace
    (validInputsHoldTheHonestTrace : ∀ v, valid v →
      ∃ index request, InputHoldsTheHonestTrace Zp weights v index request)
    (readersReadTheTrace : ∀ v, (readers v).cells = v.trace)
    {x : PlaceL} (linkBelow : x.link < 25)
    (lays : ∀ earlier, earlier ≤ x.link →
      ∃ seat heard, LaysFilling h Q valid challengesHeard readers seat heard earlier) :
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x
      (_root_.Meaning.tlAt Zp.p.X x.link)
      (fun v => traceMatricesOfTheCells Zp.p.X v.trace.cell x.link) := by
  have every : ∀ earlier, ∃ (seat : MsgAddr → Option (ℕ × ℕ)) (heard : MsgAddr → ℕ),
      earlier ≤ x.link → LaysFilling h Q valid challengesHeard readers seat heard earlier := by
    intro earlier
    by_cases H : earlier ≤ x.link
    · obtain ⟨seat, heard, L⟩ := lays earlier H
      exact ⟨seat, heard, fun _ => L⟩
    · exact ⟨fun _ => none, fun _ => 0, fun H' => absurd H' H⟩
  choose seat heard laid using every
  exact packedCellsOfTheInputFromLaysFilling h Q (cells := id) (seat := seat) (heard := heard)
    linkBelow
    (planesSizesAreTheFillingsUnderTheHead h linkBelow
      (linksTailIsTheMeanings h.scope h.reads h.pubOne linkBelow))
    readersReadTheTrace
    (fun v isValid _ _ _ isTheMatrix row column _ _ => by
      obtain ⟨index, request, I⟩ := validInputsHoldTheHonestTrace v isValid
      have e : v.trace = ⟨OnBytes.HonestTrace.cellOf Zp.p.X (theTrace Zp.p.X index request)⟩ :=
        I.traceIsTheHonestTrace
      show v.trace.cell _ _ row column = v.trace.cell _ _ row column
      rw [e]
      exact ownersCellsAreTheBorrowersAtTheHonestTrace h.scope h.reads h.pubOne index request
        isTheMatrix row column)
    (fun _ _ _ isTheMatrix => laid _ (ownersLinkIsAtMostTheLink isTheMatrix))

include h in
/-- **SIGN 2 AT THE CLOSED LETTER**, at every tail: the sizes' shift is 2 ^ 17 whatever the tail. -/
theorem traceCellsOfTheInputAreSmall
    (validInputsHoldTheHonestTrace : ∀ v, valid v →
      ∃ index request, InputHoldsTheHonestTrace Zp weights v index request)
    {link : ℕ} (linkBelow : link < 25) (tl : HTailF2) :
    TraceCellsAreSmall valid tl (fun v => traceMatricesOfTheCells Zp.p.X v.trace.cell link) := by
  intro v isValid matrix column row
  obtain ⟨index, request, I⟩ := validInputsHoldTheHonestTrace v isValid
  have e : v.trace.cell = OnBytes.HonestTrace.cellOf Zp.p.X (theTrace Zp.p.X index request) := by
    rw [I.traceIsTheHonestTrace]
  have small : ∀ l a r c, |theTrace Zp.p.X index request l a r c| < 2 * 2 ^ 17 :=
    traceCellsAreSmall h.scope h.reads h.pubOne I.requestIsServed
  have namesFit : OnBytes.HonestTrace.NamesFit Zp.p.X (theTrace Zp.p.X index request) :=
    OnBytes.HonestTrace.namesFit_theTrace h.scope h.reads h.pubOne I.requestIsServed
  show |traceMatricesOfTheCells Zp.p.X v.trace.cell link matrix.val row.val column.val| <
    2 * ((2 ^ 17 : ℕ) : ℤ)
  rw [e, traceMatricesOfTheCellsAtATrace namesFit linkBelow
    (fun number r c => lt_trans (small link number r c) (by norm_num))]
  have s := small link matrix.val row.val column.val
  push_cast
  exact s

/-! ## 3 Sign 1 in the three forms that the bundle at the calls binds -/

/-- **At every answer of `attAt`.** -/
theorem packedTraceCellsAtAttention
    (validInputsHoldTheHonestTrace : ∀ v, valid v →
      ∃ index request, InputHoldsTheHonestTrace Zp weights v index request)
    (readersReadTheTrace : ∀ v, (readers v).cells = v.trace)
    {link : ℕ} (linkBelow : link < 25)
    (lays : ∀ earlier, earlier ≤ link →
      ∃ seat heard, LaysFilling h Q valid challengesHeard readers seat heard earlier) :
    ∀ x A tl, attAt Zp.p.X link = some (x, A, tl) →
      ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x tl
        (fun v => traceMatricesOfTheCells Zp.p.X v.trace.cell link) := by
  intro x A tl e
  have ho := attAt_odd e
  obtain ⟨g, rfl⟩ : ∃ g, link = 2 * g + 1 := ⟨link / 2, by omega⟩
  obtain ⟨hl, -, ht, -⟩ := attAt_letters h.scope h.reads h.pubOne (by omega : g < 12) e
  subst ht
  rw [← hl]
  exact packedTraceCellsAtTheHonestTrace h Q validInputsHoldTheHonestTrace readersReadTheTrace
    (by rw [hl]; exact linkBelow) (by rw [hl]; exact lays)

/-- **At every answer of `layAt` and `tlAt`.** -/
theorem packedTraceCellsAtLayers
    (validInputsHoldTheHonestTrace : ∀ v, valid v →
      ∃ index request, InputHoldsTheHonestTrace Zp weights v index request)
    (readersReadTheTrace : ∀ v, (readers v).cells = v.trace)
    {link : ℕ} (linkBelow : link < 25)
    (lays : ∀ earlier, earlier ≤ link →
      ∃ seat heard, LaysFilling h Q valid challengesHeard readers seat heard earlier) :
    ∀ x tl, layAt Zp.p.X link = some x → tailAt Zp.p.X link = some tl →
      ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x tl
        (fun v => traceMatricesOfTheCells Zp.p.X v.trace.cell link) := by
  intro x tl e et
  obtain ⟨p4, groups, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨he, h24⟩ := layAt_even p4 groups e
  obtain ⟨g, rfl⟩ : ∃ g, link = 2 * g := ⟨link / 2, by omega⟩
  obtain ⟨-, hl⟩ := layAt_letters h.scope h.reads h.pubOne (by omega : g < 12) e
  obtain rfl : tl = _root_.Meaning.tlAt Zp.p.X (2 * g) :=
    Option.some.inj (et.symm.trans (linksTailIsTheMeanings h.scope h.reads h.pubOne linkBelow))
  rw [← hl]
  exact packedTraceCellsAtTheHonestTrace h Q validInputsHoldTheHonestTrace readersReadTheTrace
    (by rw [hl]; exact linkBelow) (by rw [hl]; exact lays)

/-- **At the head's place and the public part's own tail of the head.** -/
theorem packedTraceCellsAtTheHead
    (validInputsHoldTheHonestTrace : ∀ v, valid v →
      ∃ index request, InputHoldsTheHonestTrace Zp weights v index request)
    (readersReadTheTrace : ∀ v, (readers v).cells = v.trace)
    (lays : ∀ earlier, earlier ≤ 24 →
      ∃ seat heard, LaysFilling h Q valid challengesHeard readers seat heard earlier) :
    ScriptHoldsThePackedTraceCells Q h.𝔇.sent h.𝔇.l3 valid challengesHeard x₀ Zp.p.X.H.tl
      (fun v => traceMatricesOfTheCells Zp.p.X v.trace.cell 24) := by
  have hl : x₀.link = 24 := (headAt_link h.headAt).trans (P1K8T.headLink_at h)
  have ht : Zp.p.X.H.tl = _root_.Meaning.tlAt Zp.p.X x₀.link := by
    rw [hl]
    unfold _root_.Meaning.tlAt
    rw [if_neg (by omega), if_pos rfl]
  rw [ht, ← hl]
  exact packedTraceCellsAtTheHonestTrace h Q validInputsHoldTheHonestTrace readersReadTheTrace
    (by rw [hl]; decide) (by rw [hl]; exact lays)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.linksTailIsTheMeanings
#print axioms ProofFile.Honest.K3.Term.ownersCellsAreTheBorrowersAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.ownersLinkIsBelowTwentyFive
#print axioms ProofFile.Honest.K3.Term.ownersLinkIsAtMostTheLink
#print axioms ProofFile.Honest.K3.Term.laysFillingAtMoreChallenges
#print axioms ProofFile.Honest.K3.Term.packedTraceCellsAtTheHonestTrace
#print axioms ProofFile.Honest.K3.Term.traceCellsOfTheInputAreSmall
#print axioms ProofFile.Honest.K3.Term.packedTraceCellsAtAttention
#print axioms ProofFile.Honest.K3.Term.packedTraceCellsAtLayers
#print axioms ProofFile.Honest.K3.Term.packedTraceCellsAtTheHead
