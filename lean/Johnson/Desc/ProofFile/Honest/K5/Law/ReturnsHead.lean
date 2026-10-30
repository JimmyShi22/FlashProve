-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/ReturnsHead.lean: CONDITIONAL: UNDER THE HYPOTHESIS ON THE
PUBLIC INPUT (P5J.AtMgA, Johnson/P5J/MgAtAll.lean) three of the four things that the maker of the
one honest prover makes before it looks at the filling (`MakerHas`, Law/ReturnsOf.lean) are there:
THE BOOK IS LEFT; and where the verifier's test on the public files accepts too, of the book "its
maker returns" alone. Three theorems; no definition. No property is claimed.

Main names:
  `strays_head` the first chain of the description's own term at the hypothesis's letters
    (`P5J.F0T`) is the hypothesis's chain, as `strays` reads it: a line on strays that is shown at
    the one is shown at the other
  `made_head` from h and "the list of sendings has seven chains and the book's maker returns B":
    there is a ground at which `MakerHas` holds at the hypothesis's letters
  `made_live` from h, hl: the test `FlashProve.protocolDataWellFormed` accepts the public files, and "wherever the
    list of sendings is these seven chains the book's maker returns": there are a ground and a book
    at which `MakerHas` holds. That the list has seven chains is `P1Opts.sends_of_laid`
    (Johnson/Top/H0/Opts/SendsOfLaid.lean)

ALL THREE ARE CONDITIONAL on h. It is spent for three of its fields: the public part is made, the
description's maker returns, and that return opened in its letters (`h.laid`,
Johnson/P5J/LaidOpens.lean).
ON h AND hl: they are hypotheses here. Both can be met: at the full-size public files as
Ladder/Stored.lean spells them h has a member with no premise (`headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean) and the test accepts (`theLive_zFull`,
AtFullSide/Top/LiveAtFull.lean); this file calls neither. Whether h gives hl: no theorem that says
so was found; the library's theorems go from hl to a member of h.

Limits. THAT THE BOOK's MAKER (`bookWhole`, Honest/BookWhole.lean) RETURNS AT ANY FILES IS NOT SHOWN
HERE, and no theorem that concludes so was found in the library or beside it: where it fails the
maker of the prover returns at no filling. At the library's full size and at the format's second
hash function (OnBytes.secondHashFunction) alone: h is typed there.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsOf
import Johnson.P5J.MgAtAll
import Johnson.Top.H0.Opts.SendsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The first chain of the description's own term at the hypothesis's letters is the
hypothesis's, as `strays` reads it.** CONDITIONAL: h. -/
theorem strays_head {V W Y : Type} (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hs : List (Placed V W Y)) :
    strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder hs = strays cF.blocksInOrder hs := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact open_strays O hs

/-- **UNDER THE HYPOTHESIS THE BOOK ALONE IS LEFT OF WHAT THE MAKER MAKES.** CONDITIONAL: h; book:
the list of sendings has seven chains and the book's maker returns. -/
theorem made_head (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x) {B : ProverCoinCounts}
    (book : ∃ c0 c1 c2 c3 p0 p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [c0, c1, c2, c3, p0, p1, p2] ∧
        bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) p0 p1 p2 (mergesByName cF.blocksInOrder) = .ok B) :
    ∃ G, MakerHas OnBytes.secondHashFunction Z.pol Z.lay Z.KL Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF) B := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨Bs.G₀, h.laid.pub, O.blank, h.laid.value, ?_⟩
  rw [open_merges O]
  exact book

/-- **WHERE THE VERIFIER's TEST ON THE PUBLIC FILES ACCEPTS TOO, "THE BOOK's MAKER RETURNS" ALONE IS
LEFT.** CONDITIONAL: h; hl: the test `protocolDataWellFormed` accepts the public files; book: wherever the list of
sendings is these seven chains, the book's maker returns at its last three. That the list has seven
chains is `P1Opts.sends_of_laid`. -/
theorem made_live (h : AtMgA OnBytes.secondHashFunction Z D r₀ Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (book : ∀ k0 k1 k2 e p1 p2,
      Johnson.G.sendsOf Z.pol Z.lay Z.KL = .ok [k0, k1, k2, e, Zp.made.proof.1, p1, p2] →
        ∃ B, bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp.made.proof.1 p1 p2
          (mergesByName cF.blocksInOrder) = .ok B) :
    ∃ G B, MakerHas OnBytes.secondHashFunction Z.pol Z.lay Z.KL Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF) B := by
  obtain ⟨k0, k1, k2, e, p1, p2, hs⟩ := P1Opts.sends_of_laid hl h.laid.pub
  obtain ⟨B, hB⟩ := book k0 k1 k2 e p1 p2 hs
  obtain ⟨G, m⟩ := made_head h ⟨k0, k1, k2, e, _, p1, p2, hs, hB⟩
  exact ⟨G, B, m⟩

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.strays_head
#print axioms ProofFile.Honest.K5.made_head
#print axioms ProofFile.Honest.K5.made_live
