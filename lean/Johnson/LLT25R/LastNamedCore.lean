-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastNamedCore.lean:

`endedX_inv` · `tenant_is` · `Readers₃.ofNamed`: THE TWO EQUATIONS OF MAKE, `Readers₃`,
ARE THEOREMS AT THE TWO TABLES' OWN READERS OF OOD SAMPLES (smp₁ := `smpNamed cs seats`, smp₂ :=
`smpSt cs oNo stSh`), at Oc := `ocEnd … ∧ Rc`, from `PlanOk₃`, hS (the handed book numbers the
messages as the list seats does) and hN (wherever X says yes of d, the plan's number of whoever of
mine sits at Omega's seat is d.loc.oOmega).
Nothing on soundness.
-/
import Johnson.LLT25R.LastV
import Johnson.LLT25R.LastReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open VerifiableInference.Desc.K13 (Where)
open _root_.Desc.K14 (St)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open _root_.Desc.K14.Law.Fence (CoreFacts MemberFacts)
open H2K.Pin (NTuple)

/-- What `endedX X` returns. -/
theorem endedX_inv {X : St → Bool} {d : St} {e : SharedOut} (he : endedX X d = some e) :
    X d = true ∧ e.st = d.st ∧ e.omega = d.loc.oOmega := by
  unfold endedX at he
  split at he
  · rename_i hXd
    obtain ⟨en, hen, rfl⟩ := Option.map_eq_some_iff.1 he
    unfold _root_.Desc.K14.ended at hen
    simp only at hen
    split at hen
    · obtain rfl := Option.some.inj hen
      exact ⟨hXd, rfl, rfl⟩
    · cases hen
  · cases he

variable (seats : List (ℕ × ℕ)) (oNo : Mem → ℕ)

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (N : H2U.Places4) (c : Chain S Cl) {Cells Tok
          P₀ : Type} (D : WholeD) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ) (dB : RDT) (dt : List
                 RDT) (get : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → P₀ × First.S)
    (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
    (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (M₁ : Meaning P₀ (Wit Cells Tok
    MsgT)) (MS : MeaningS St ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁)
    (Wit Cells Tok MsgT)) (stOf : St → OnBytes.Statement) (bookOf : St → OnBytes.TreeBook) (Pm₀ :
    PromMeaning St) (N₁ : Numbers) (Ns : NumbersS) (links : List ModelPart) (X : St → Bool) (r :
          Fmt.M1.Stage → ℕ) (Ld : VerifiableInference.Desc.K12.Door.Laid)

variable (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁ × St) × (FL o mk Z (seatK Z N) N c).S₃) → Option Cells) (c₀' : Cells) (a₁ :
    Block (FL o mk Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl) (k₁ : List (Block (FL o mk
    Z (seatK Z N) N c).S₁ (FL o mk Z (seatK Z N) N c).Cl)) (a₂ : Block St (FL o mk Z (seatK Z N) N
    c).Cl) (k₂ : List (Block St (FL o mk Z (seatK Z N) N c).Cl)) (rest₁ : (i : ℕ) → (ds : List RDT)
    → Rest (ckP .two) (frameAt D (allOf D) D.key₁ 0) ((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z
    (seatK Z N) N c).S₁) (Wit Cells Tok MsgT) ds) (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP
    .two) (frameAt D (allOf D) D.key₂ 0) (((FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z
    N) N c).S₁) × St) (Wit Cells Tok MsgT) ds) (d wEnd : Wit Cells Tok MsgT)

variable (Rc : (FL o mk Z (seatK Z N) N c).XiPub × (FL o mk Z (seatK Z N) N c).S₁ → Prop)

/-- Omega's tenant in the shared table's numbers, off the tests on the plan. -/
theorem tenant_is (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links (First.flatPlaces true
    links true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld) : Ns.tenant .oOmega = (D.t₁ + 1, 0) := by
  obtain ⟨xO, hxO, sxO, -⟩ := hP.omegaSeat
  rcases mem_mineOf.1 hxO with ⟨-, h | h⟩ | ⟨-, h⟩
  · exact absurd ((show seatOf xO = N₁.w from h).symm.trans sxO) hP.seatsApart.2.2
  · exact absurd ((show seatOf xO = N₁.index from h).symm.trans sxO) hP.seatsApart.2.1
  · exact (show seatOf xO = Ns.tenant .oOmega from h).symm.trans sxO

/-- **The two equations of make, at the two tables' own readers.** -/
theorem Readers₃.ofNamed (hP : PlanOk₃ o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links
    (First.flatPlaces true links true) r (N₁.treesAt none) 0 1 (vAt Z N₁) Ld)
    (hS : ∀ q y, ocEnd get N₁ M₁ links (First.flatPlaces true links true) q y → Rc q → (get
        q).2.failed = none → ∀ f, firstOfS (get q).2 = some f → SeatsNumber seats f.book)
    (hN : ∀ x ∈ (mineOf ms₁ ms₂ N₁ Ns), seatOf x = (D.t₁ + 1, 0) → ∀ d, X d = true → oNo x =
        d.loc.oOmega) :
    Readers₃ o mk Z N c D G arr get (smpNamed (p14At Z).codes seats) (smpSt (p14At Z).codes oNo
        stSh) ms₁ ms₂ decT₁ decT₂ M₁ MS stOf bookOf Pm₀ N₁ Ns X (fun q y => ocEnd get N₁ M₁ links
        (First.flatPlaces true links true) q y ∧ Rc q) 1 (vAt Z N₁) where
  readE := fun a f hon hf i x _ hi hw => by
    have hO := tenant_is o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links r Ld hP
    refine smpLast_elder (p14At Z).codes get Ns seats _ a.1 x ?_ f hf i hi (hS _ _ hon.1.1 hon.1.2
        hon.2.1 f hf)
    rw [hO]
    rcases hw with hw | hw
    · rw [hw]; exact hP.seatsApart.2.1
    · rw [hw]; exact hP.seatsApart.2.2
  readO := fun a e _ he x hx hw => by
    have hO := tenant_is o mk Z N c D G arr dB dt ms₁ ms₂ N₁ Ns links r Ld hP
    obtain ⟨hXd, e1, e2⟩ := endedX_inv he
    rw [smpLast_omega (p14At Z).codes get Ns oNo _ a.1 x (hw.trans hO.symm), e1, e2, hN x hx hw _
        hXd]

end LLT25

#print axioms LLT25.Readers₃.ofNamed
