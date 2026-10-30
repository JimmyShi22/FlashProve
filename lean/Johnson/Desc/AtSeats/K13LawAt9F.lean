-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.AtSeats.K13LawAt9
import Johnson.Desc.K13.Law.FactsOfFold
/-
K13's SHARE IN THE COUNTED FORM, WITH THE STRUCTURE «FoldFacts» ITSELF AS THE PREMISE: InScope → ‹what is laid› → ‹named Bools on the list of rounds› → FoldFacts → the
ties in the second form, at mgAll 𝔇 Mg₀. k13_law_at9 at codes · shape · layout := f.sent's and the proximity test's data := f's own (d12Of f): so the six
equations of data that factsK13_of_fold asks are rfl; «pubP says nothing at the eight» comes out of FillsK13C's field quiet (quietC_of_cA13). TWELVE FIELDS OF FoldFacts ARE SPENT:
tidy · codes · shape · layout · pileMasks · pileWithin · oneRow · weightsOk · bookInOrder · seatsCarried · msgShapes · bookFits.
The statement was made by program out of k13_law_at9's own binder text.
NO SOUNDNESS.
-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)

open _root_.Desc.K14.Law (roundsIn)
open OnBytes.Params (Rounds)
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (Pub)
open VerifiableInference.Desc.Sound (TiedAtR HandsOn)

open VerifiableInference.Desc.Sound (mgAll MgData CellsQ)

/-- The proximity test's data, out of the fold's. -/
abbrev d12Of (f : First.FoldData) : K12.Door.K12Data := ⟨f.ft, f.L, f.M⟩

/-- The eight names of the class are among the items at which FillsK13C asks pubP's silence. -/
theorem quietC_of_cA13 (q : First.Pub) (h : cA13 q = true) : q ∈ quietC := by
  cases q with
  | more seg name =>
    cases seg with
    | some m => simp [cA13, k13PlusItemC, First.weightsItem, K12.Door.k12Item] at h
    | none =>
      simp only [cA13, k13PlusItemC, First.weightsItem, K12.Door.k12Item, Option.isNone_none,
        Bool.true_and, Bool.or_eq_true, beq_iff_eq] at h
      rcases h with (((rfl | rfl) | rfl) | rfl) | (((rfl | rfl) | rfl) | rfl) <;> decide
  | _ => simp [cA13, k13PlusItemC, First.weightsItem, K12.Door.k12Item] at h

theorem k13_law_at9F {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base₀ c A B)
    {a : ℕ} {R₁ R₂ R₃ : Rounds} {e₁ : List (List ByteArray × ByteArray)}
    {all : List LeftT} {X₁ X₂ Xi Xi₉ Tok : Type} {rows cols nR₉ : ℕ}
    {X₉ : OnBytes.Model.Verify.Public}
    {T : ThreeAt (ckP .two) (dataOf a R₁ R₂ R₃) all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Desc.Wit (CellsQ rows cols) Tok MsgT)}
    (hT : OfDesc _ T) (N : Numbers) (𝔇 : MgData Xi₉ ProofFile.InstPub Tok rows cols nR₉ X₉)
    (Mg₀ : Meaning ProofFile.InstPub (Desc.Wit (CellsQ rows cols) Tok MsgT)) (h0 : Mg₀.more = {})
    (f : First.FoldData) (reqW : ProofFile.InstPub → Array UInt32)
    {arr : ℕ → ℕ → ℕ} {nR : ℕ}
    {mat : (CellsQ rows cols) → Fin nR → (Fin (K13.whereOf Z).lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : ProofFile.InstPub × S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf f.sent.codes s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → ProofFile.InstPub × S → Option (CellsQ rows cols)}
    (N₁₃ : Numbers)
    (rw₁₃ : ProofFile.InstPub × S → Desc.Wit (CellsQ rows cols) Tok MsgT → Wit GE nR (K13.whereOf Z).lin.kCol)
    (c₀ : (CellsQ rows cols)) (tokOf : ProofFile.InstPub × S → Tok)
    {b₁ : Block (ProofFile.InstPub × S) Cl} {l₁ : List (Block (ProofFile.InstPub × S) Cl)}
    {rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁)
      (ProofFile.InstPub × S) (Desc.Wit (CellsQ rows cols) Tok MsgT) ds} {r : Fmt.RoundView}
    (hC : (T.p₁, T.l₁) = cutRow rest₁ [r] 0 0 (dataOf a R₁ R₂ R₃).ds₁ b₁ l₁)
    (herr : ∀ ds : List RDT, (rest₁ 355 ds).err = _root_.Iop.Err.cap 128 (uLT (ckP .two) ds))
    (hCapB : capB (K13.whereOf Z) = true)
    (hWr : WrittenAs e₁ (c.blocksInOrder.flatMap (·.rounds)) R₁)
    (hNt : N.treesAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.treesAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hNm : N.msgsAt (flatPlacesOf Sound.linksFull true)[355 + 1]? =
      N.msgsAt (flatPlacesOf Sound.linksFull true)[355]?)
    (hbase : N.index.1 < nTrees ((dataOf a R₁ R₂ R₃).ds₁.take (inFront355 c)))
    (hFlC : FillsK13C (K13.whereOf Z) N (mgAll 𝔇 Mg₀) f.sent.codes arr mat G smp ms decT) (hft : (d12Of f).ft = 0)
    (hPl : PlanM3 (d12Of f).L (d12Of f).M ms f.sent.codes N)
    (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl (K13.whereOf Z) x x' →
      (mgAll 𝔇 Mg₀).inOrder x = true → (mgAll 𝔇 Mg₀).inOrder x' = true)
    (Rch : ℕ → (ProofFile.InstPub × S) ×
      (frameAt (dataOf a R₁ R₂ R₃) all (dataOf a R₁ R₂ R₃).key₁ T.ft₁).E.Str → Prop)
    (H : First.FoldFacts Rch (fun x => x.1) f reqW Sound.linksFull
      (flatPlacesOf Sound.linksFull true))
    (hHand : ∀ i q, (T.p₁ :: T.l₁)[i]? = some q → HandsOn Rch i (q.withMap ((fun k => extQAt f.sent.codes G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i))) :
    ∀ i q p, (T.p₁ :: T.l₁)[i]? = some q → (flatPlacesOf Sound.linksFull true)[i]? = some p →
      p.kind = KindName.K13 →
      TiedAtR N (mgAll 𝔇 Mg₀) Sound.linksFull (flatPlacesOf Sound.linksFull true) (fun a => a) Rch i
        (q.withMap ((fun k => extQAt f.sent.codes G arr smp ms decT c₀ tokOf N Sound.linksFull (flatPlacesOf Sound.linksFull true)
        (fun a => a) k) i)) :=
  k13_law_at9 hS hR O hT N 𝔇 Mg₀ h0 f.sent.shape f.sent.layout N₁₃ rw₁₃ (d12Of f) c₀ tokOf hC herr hCapB hWr hNt hNm
    hbase hFlC hft hPl hsmp hdec hrest Rch
    (fun j x hr hm => factsK13_of_fold H _ _ _ rfl rfl rfl rfl rfl rfl
      (fun q hq y => hFlC.quiet q (quietC_of_cA13 q hq) y) j x hr hm) hHand

end VerifiableInference.Desc.K13.Law
