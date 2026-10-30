-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/RidersMore.lean: THREE MORE RIDERS AT OUR BLOCKS, AND KIND K13's CALL ANEW.
Statements with their proofs.
  `rider3_bookOnly`: KIND-FREE IN THE ITEM: a public item whose test reads the book of trees alone,
  and whose `pubP` says nothing, is a rider at kind K13's block: that block leaves the book
  (`core_same_M3`).
  `bookFitsItem`, `rider3_bookFits`: so is "K12.bookFits" (its test:
  `Sound.bookFitsB` of the book).
  `openingZero_ledgers`: the first segment's opening keeps "every ledger is that of so many takes
  since it was made": its sending by `firstAtS_ledgersFit` (LedgersB.lean); its quiet part leaves
  the statement.
  `riderG_pileWithin`: "K13.pileWithin" is a rider at the first segment's opening: the ledgers' half
  by that; the rows' half because no row lies on the table behind it (`openingZero_noRows`,
  RidersG.lean).
  `fillM3_paid5`: **`FillM3` at any list Q of riders** that holds the proximity test's three, and
  beside the four of `knownK13` at most "K13.weightsOk", "K13.pileWithin", "K13.oneRow",
  "K12.bookFits". Its premises are `fillM3_paid4`'s (FillM3Paid4.lean) and what Mg says at
  "K12.bookFits".
What is not claimed. The premises; `OwedWithinM3` among them. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.RidersG
import Johnson.Desc.K13.Law.FillM3Paid4
import Johnson.Desc.K13.Law.LedgersB
import Johnson.Desc.K13.Law.LedgersC
import Johnson.Desc.Sound.BookTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open Desc.Plain
open Johnson.Pack (sigOf)
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

section
variable {Pp W Cl : Type}

/-- An item whose test reads the book of trees alone is a rider at kind K13's block. -/
theorem rider3_bookOnly {P : Where} {Mg : Meaning Pp W} {q : Pub} {f : TreeBook → Bool}
    (hM : ∀ x, Mg.pub q x = f x.2.book) (hP : ∀ x, Mg.pubP q x) : Rider3 Cl P Mg q :=
  fun x x' h => ⟨fun h0 => by
    rw [hM] at h0 ⊢
    rw [(core_same_M3 h).1]
    exact h0, fun _ => hP x'⟩

/-- The public item "K12.bookFits". -/
def bookFitsItem : Pub := First.moreItem (none, "K12.bookFits")

theorem rider3_bookFits {P : Where} {Mg : Meaning Pp W}
    (hM : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hP : ∀ x, Mg.pubP bookFitsItem x) : Rider3 Cl P Mg bookFitsItem := rider3_bookOnly hM hP

variable {q : Params.First} {gp : GPar} {nm : String} {X : LayPar} {fvs : List Bool} {kCol : ℕ}

/-- The first segment's opening keeps the ledgers' clause. -/
theorem openingZero_ledgers {s t : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.openingZero q gp nm X fvs kCol : Block S Cl).decide s [r₁, r₂] gs = .ok t)
    (hf : LedgersFit s.st) : LedgersFit t.st := by
  obtain ⟨s₁, g₁, h1, h2⟩ := K1.openingZero_mid h
  have a : LedgersFit s.st → LedgersFit s₁.st := firstAtS_ledgersFit q gp s _ _ s₁ h1
  have e : t.st = s₁.st :=
    (Johnson.Desc.First.Walk.Tied.openedZeroGives X fvs kCol s₁ t h2).2.2.1.2.2.1
  rw [e]
  exact a hf

variable {N : Numbers} {Mg : Meaning Pp W} {Q : List Pub} {p : Option Place}

/-- "K13.pileWithin" is a rider at the first segment's opening. -/
theorem riderG_pileWithin (hm : Pub.noneSent ∈ Q) (hw : pileWithinItem ∈ Q)
    (hNS : ∀ x, Mg.pub .noneSent x = noneSentC N x.2)
    (hM : ∀ x, Mg.pub pileWithinItem x = pileWithinC x.2) (hP : ∀ x, Mg.pubP pileWithinItem x) :
    RiderG Cl q gp nm X fvs kCol N Mg Q p pileWithinItem := fun x x' h hQ _ => by
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  have h0 := hQ _ hm
  rw [hNS, noneSentC_eq, Bool.and_eq_true] at h0
  have h1 := hQ _ hw
  rw [hM] at h1
  unfold pileWithinC at h1
  rw [Bool.and_eq_true] at h1
  refine ⟨?_, fun _ => hP x'⟩
  rw [hM]
  unfold pileWithinC
  rw [Bool.and_eq_true]
  refine ⟨(ledgersC x'.2).2 (openingZero_ledgers hd ((ledgersC x.2).1 h1.1)), ?_⟩
  unfold rowsWithinC
  rw [openingZero_noRows hd h0.2]
  rfl

end

/-- **`FillM3` at a door that has "K12.bookFits" too.** -/
theorem fillM3_paid5 {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} (Q : List Pub)
    (hF : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L)
    (hW : ∀ x, Mg.pub weightsItem x = First.weightsB x.2) (hWP : ∀ x, Mg.pubP weightsItem x)
    (hB : ∀ x, Mg.pub bookFitsItem x = Sound.bookFitsB x.2.book)
    (hBP : ∀ x, Mg.pubP bookFitsItem x) (hPl : PlanM3 L M ms cs N)
    (hIn : bookItem ∈ Q ∧ seatsItem ∈ Q ∧ shapesItem ∈ Q)
    (hQ : ∀ q ∈ Q, q ∈ knownK13 ∨ q = weightsItem ∨ q = pileWithinItem ∨ q = oneRowItem ∨
      q = bookFitsItem)
    (hO : OwedWithinM3) (hsmp : SmpReads smp) (hdec : DecBlind decT)
    (hrest : ∀ x x', StepM3 Cl P x x' → rest x = true → rest x' = true) :
    FillM3 Cl P N Mg (rwBook arr mat) Q :=
  fillM3_at Q (mgK13_of_fills hF) (planK13_of hPl) hIn.1 hIn.2.1 hIn.2.2 seed3 pinsStay hsmp hdec
    hrest fun q hq hk => by
      rcases hQ q hq with h | rfl | rfl | rfl | rfl
      · exact absurd h hk
      · exact rider3_keeps weightsKeeps hW hWP
      · exact rider3_pileWithin hO hF.within (hF.quiet _ (by simp [quietK13]))
      · exact rider3_oneRow hF.oneRow (hF.quiet _ (by simp [quietK13]))
      · exact rider3_bookFits hB hBP

end VerifiableInference.Desc.K13.Law
