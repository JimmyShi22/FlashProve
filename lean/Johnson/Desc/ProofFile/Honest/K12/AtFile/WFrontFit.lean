-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontFit.lean: each member's count of sample rows and its pad
on entry to the last chain's own test.

  MessageFits            a message has as many sample rows as answers, and the public pad
  ownFit_at_end          at the own group at the end of the first chain's fold
  membersFit_at_own      behind the block "K14, second part": the elder members, and Omega from the
                         shared chain's end

Premises of ownFit_at_end, beside the fold and the record's lin.
- hsp: the shape does not split the row.
- hix: IndexIs: indexMasks_at_end (WFrontEndIs.lean) pays it.
- hW, hI: W's notice and the first sending's last notice count an answer: WFrontPlan.lean pays them.

Limits.
- Nothing on the trees.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontOwn
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontGroup

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (whereOf)
open VerifiableInference.Desc.K13.Law (linAt)
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ P₁₄ SharedOut batchLinearConstraintsSecondPart start₃E)
open VerifiableInference.Desc.Third.Law (laid_k14Second start₃E_inv start₃_inv firstOutFrom_inv)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A message has as many sample rows as answers, and the public pad.** -/
def MessageFits (cs : Codes) (y : OnBytes.Oracle) : Prop :=
  y.sampleRows.size = y.shape.answers ∧
    ∃ l, VerifiableInference.Desc.Own.padMade cs y.shape = some l ∧
      y.pad = l.map fun p => (p.part, p.index)

/-- **At the own group, at the end of the first chain's fold.** -/
theorem ownFit_at_end (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀)) {l : LinFirst}
    (hl : linAt e₁ = some l) (hsp : (whereOf Zp).lin.ownSplitNeeded = false)
    (hix : IndexIs Zp e₁)
    (hW : ∀ msg, linMessageW Zp.first.lin = some msg → ∃ n, msg[0]? = some n ∧
      n.shape.answers ≠ 0)
    (hI : ∃ hk : (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1 <
        (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
          (VerifiableInference.Desc.K1.gpOf Zp))).length,
      (VerifiableInference.Desc.K1.shapesOf (VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)))[(VerifiableInference.Desc.K1.firstPar Zp.first
        (VerifiableInference.Desc.K1.gpOf Zp)).sent.size - 1].answers ≠ 0)
    {G : Group} (hG : e₁.st.groups[l.own]? = some G) :
    ∀ a ∈ G.members.toList, ∀ y : OnBytes.Oracle, e₁.st.oracles[a]? = some y →
      MessageFits e₁.st.codes y := by
  intro a ha y hy
  rcases ownMembers_at_end h hf hl hsp hG a ha with rfl | e
  · obtain ⟨msg, hmsg, hall⟩ := sendW_at_end h hf hl
    obtain ⟨n, hn, hans⟩ := hW msg hmsg
    obtain ⟨z, hz, -, -, -, g, p, hp, ep⟩ := hall 0 n hn hans
    obtain rfl := Option.some.inj (hz.symm.trans hy)
    exact ⟨g, p, hp, ep⟩
  · unfold IndexIs at hix
    rw [hix] at e
    subst e
    obtain ⟨hk, hans⟩ := hI
    obtain ⟨z, hz, -, -, -, g, p, hp, ep⟩ := sentWell_at_end h hf _ hk hans
    obtain rfl := Option.some.inj (hz.symm.trans hy)
    exact ⟨g, p, hp, ep⟩

/-- **Behind the block "K14, second part".** -/
theorem membersFit_at_own {Cl : Type} (p : P₁₄) {codes : Codes} {S₀ : Params.LinShape}
    {st₁ : Statement} {book₁ : TreeBook} {roots₁ w₁ own₁ : ℕ} {mask₁ : Option ℕ}
    {pile₁ : List TensorRow} {o : SharedOut} {s₀ s : S₃} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {t : T12}
    (h₀ : start₃E codes S₀ st₁ book₁ roots₁ w₁ own₁ mask₁ pile₁ o = .ok s₀)
    (h₁ : (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s₀ rs gs = .ok s) (h₂ : enterOwn s = .ok t)
    (hO : ∀ G, st₁.groups[own₁]? = some G → ∀ a ∈ G.members.toList, ∀ y : OnBytes.Oracle,
      st₁.oracles[a]? = some y → MessageFits st₁.codes y)
    (hM : OnBytes.Means.SampledMembers st₁) (hΩ : WellSampled o.st) :
    ∀ G, t.st.groups[t.g]? = some G → ∀ a ∈ G.members.toList, ∀ y : OnBytes.Oracle,
      t.st.oracles[a]? = some y → MessageFits t.st.codes y := by
  obtain ⟨f, hf, hst⟩ := start₃E_inv _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨-, ef, -, eo, -, -⟩ := firstOutFrom_inv _ _ _ _ _ _ _ _ _ hf
  obtain ⟨ec₁, ec₂, e0⟩ := start₃_inv _ _ _ _ hst
  have es₀ : s₀.st = st₁ := by rw [e0]; exact ef
  have eown : s₀.loc.own = own₁ := by rw [e0]; exact eo
  obtain ⟨g₀, hb⟩ := VerifiableInference.Desc.Third.Law.start₃E_border _ _ _ _ _ _ _ _ _ _ _ h₀
  obtain ⟨b, y₀, G, dot, L⟩ := laid_k14Second p s₀ s rs gs h₁
  have et : t = { st := s.st, book := s.book, roots := s.roots, g := s.loc.own, pass := .nothing
                  mask := s.loc.mask } := (Except.ok.inj h₂).symm
  have hl : s.loc.own = s₀.loc.own := by rw [L.loc]
  have hGs := L.group'
  rw [← hl] at hGs
  subst et
  intro G' hG' a ha y hy
  have hG'' : s.st.groups[s.loc.own]? = some G' := hG'
  obtain rfl := Option.some.inj (hGs.symm.trans hG'')
  have hy' : s.st.oracles[a]? = some y := hy
  have hpos : (G.members.filter (· < s₀.st.oracles.size)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  have ha' : a ∈ (G.members.insertIdxIfInBounds
      (G.members.filter (· < s₀.st.oracles.size)).size s₀.st.oracles.size).toList := ha
  rw [OnBytes.Means.toList_insertIdxIfInBounds] at ha'
  have hcod : s.st.codes = s₀.st.codes := L.codes
  show MessageFits s.st.codes y
  rcases (List.mem_insertIdx hpos).1 ha' with rfl | hm
  · rw [L.copy] at hy'
    obtain rfl := Option.some.inj hy'
    have hbd : b.shared = o := by
      have e := L.border.symm.trans hb
      rw [Option.some.injEq] at e
      rw [e]
    have hw := hΩ b.shared.omega y₀ (by rw [← hbd]; exact L.there) L.sampled
    obtain ⟨a₁, l, hl₁, e⟩ := hw
    refine ⟨by simpa using a₁, l, ?_, e⟩
    show VerifiableInference.Desc.Own.padMade s.st.codes y₀.shape = some l
    rw [hcod, es₀, ← ef, ec₁, ← ec₂]
    exact hl₁
  · have hlt : a < s₀.st.oracles.size := by
      obtain ⟨z, hz, -⟩ := hM _ G (by rw [← es₀]; exact L.group) a hm
      rw [es₀]
      exact (Array.getElem?_eq_some_iff.1 hz).1
    rw [L.old a hlt, es₀] at hy'
    have := hO G (by rw [← eown, ← es₀]; exact L.group) a hm y hy'
    rw [hcod, es₀]
    exact this

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.ownFit_at_end
#print axioms ProofFile.Honest.K12.AtFile.membersFit_at_own
