-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3CallsKeeps.lean: the lookup on a link's CALLS: WHAT A YES OF K3.block's
decide MAKES AND KEEPS OF THE PUBLIC ITEMS THAT THE TABLE OF JOINTS' ROW NAMES THERE
(asks ledger, lookIn, freeAbove; makes lookOut, look, left, callerIn;
linkFresh rides): freeAbove · linkFresh's first half and what its second reads · ledger · left.
Definitions with code, statements and proofs. Ties: no error term. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.block's decide at seatCalls claim.
USER: K3CallsBehind.lean, K3CallsBehindR.lean (the field "behind" of AttAtTable, LayAtTable) and
  others. k3_calls_left: nobody yet.
LETTERS: piece, laid, before, p, guests free; h: the shape that p makes.

Main names:
  `freeAboveB s`: a Bool: every slot from the ledger's next free number on is free: TO THE LETTER
    the test that has been run (outside this file) at the honest walk's borders.
  `digitsUnheardB s`: the like: nothing is heard yet at the digits' seat.
  `freeAboveAtB n s`, `linkFreshB arrs s`: the two with their second halves: the ledger's number of
    slots is n; the open link's table of arrays is arrs: the fillings of freeAbove m, linkFresh m.
  `freeAboveB_iff`: at a ledger that has its sizes the Bool is the library's FreeAbove
    (OnBytes/Tie/Pv/Psc/PscRoom.lean): the step between the walk's Bool and the law
    decide_freeAbove (K3KeepsFree.lean, which says in its Limits that this step is nobody's).
  `k3_calls_freeAbove`: under k3OnIn a yes keeps freeAboveB. (THE SAME LAW AS decide_freeAbove, at
    the Bool and at the calls' seat, proved apart: when that lemma stands in a file without the
    head's chain beneath, this proof is to be its call through freeAboveB_iff.)
  `k3_calls_unheard`: a yes leaves digitsUnheardB's value; `k3_calls_linkSame`: and the open link's
    context (link?: its number and its table of arrays).
  `k3_calls_ledger`: behind a yes the ledger is there and sized.
  `k3_calls_left`: behind a yes K3LeftAt holds (Johnson/Top/H/K3LeftStatement.lean): what the item
    left is meant to say, at Q := "sized, and the lookup's slots free".

Limits. look and callerIn: NOT HERE (look's second half is in K3CallsTurnsSharp.lean's TurnsCalls;
callerIn's "the caller has not been heard" is asked of nobody in front). formsInT "objects", whose
maker the table names this block: NOT HERE: it reads the run's reader.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsLookOut
import Johnson.Desc.First.Look.K3CallsTurnsSharp

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open OnBytes.PscRun
open VerifiableInference.Desc.K3 (sizedB freeB k3OnIn k3OnOut)

/-- Every slot from the ledger's next free number on is free. -/
def freeAboveB (s : Desc.First.S) : Bool :=
  s.fork?.any fun G => (List.range (G.ns - G.next)).all fun j => !G.gotF.getD (G.next + j) true

/-- Nothing is heard yet at the digits' seat. -/
def digitsUnheardB (s : Desc.First.S) : Bool := (s.tl?.bind (·.heard)).isNone

/-- Free above, and the ledger's number of slots is n. -/
def freeAboveAtB (n : ℕ) (s : Desc.First.S) : Bool :=
  freeAboveB s && s.fork?.any fun G => G.ns == n

/-- Nothing is heard at the digits' seat, and the open link's table of arrays is arrs. -/
def linkFreshB (arrs : Array (Nat × String)) (s : Desc.First.S) : Bool :=
  digitsUnheardB s && s.link?.any fun L => L.arrayOf == arrs

/-- **The walk's Bool is the library's "free above"**, at a ledger that has its sizes: the Bool
reads the slots below the ledger's number of slots; FreeAbove speaks of all numbers; beyond the
arrays nothing is filled. -/
theorem freeAboveB_iff {s : Desc.First.S} {F : Fork} (hF : s.fork? = some F) (hS : Sized F) :
    freeAboveB s = true ↔ FreeAbove F := by
  unfold freeAboveB
  rw [hF]
  simp only [Option.any_some, List.all_eq_true, List.mem_range, Bool.not_eq_true']
  constructor
  · intro h j hj hf
    unfold Filled at hf
    by_cases hlt : j < F.ns
    · have q := h (j - F.next) (by omega)
      rw [show F.next + (j - F.next) = j by omega] at q
      rw [getD_in _ _ q] at hf
      cases hf
    · have hout : ¬ j < F.gotF.size := by
        rw [hS.2.2]
        exact hlt
      simp only [Array.getD, dif_neg hout] at hf
      cases hf
  · intro h j hj
    have hin : F.next + j < F.gotF.size := by
      rw [hS.2.2]
      omega
    refine getD_out _ _ hin ?_
    have hn := h (F.next + j) (Nat.le_add_right _ _)
    unfold Filled at hn
    cases hv : F.gotF.getD (F.next + j) false with
    | false => rfl
    | true => exact absurd hv hn

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (hs : p.shape = some h) (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

include hs in
/-- **freeAbove is kept.** -/
theorem k3_calls_freeAbove (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) (hfa : freeAboveB s = true) : freeAboveB s' = true := by
  obtain ⟨F, F', g, hF, -, -, hF', -, L, E⟩ :=
    k3_calls_leaves claim piece laid before p guests hs s s' rs cols hw hd hIn
  unfold freeAboveB at hfa ⊢
  rw [hF] at hfa
  rw [hF']
  simp only [Option.any_some, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at hfa ⊢
  intro j hj
  have hns : F'.ns = F.ns := L.padLeft.rest.2.1
  have hin : F'.next + j < F'.gotF.size := by
    rw [L.padLeft.fit.2.2]
    omega
  refine getD_out _ _ hin ?_
  have e : F.next + (Forest.elems h + j) = F'.next + j := by
    rw [E.next]
    omega
  have q := hfa (Forest.elems h + j) (by
    rw [E.next, hns] at hj
    omega)
  rw [e] at q
  have hFn : ¬ Filled F (F'.next + j) := by
    intro hc
    unfold Filled at hc
    rw [getD_in _ _ q] at hc
    cases hc
  have hF'n : ¬ Filled F' (F'.next + j) := by
    intro hc
    rcases (E.marks _).1 hc with h1 | ⟨-, h2, -⟩
    · exact hFn h1
    · rw [E.next] at h2
      omega
  unfold Filled at hF'n
  cases hv : F'.gotF.getD (F'.next + j) false with
  | false => rfl
  | true => exact absurd hv hF'n

/-- **Nothing is laid at the digits' seat.** -/
theorem k3_calls_unheard
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') : digitsUnheardB s' = digitsUnheardB s := by
  unfold digitsUnheardB
  rw [(k3_calls_turns claim piece laid before p guests s s' rs cols hd).tl]

/-- **The open link's context is the same.** -/
theorem k3_calls_linkSame
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') : s'.link? = s.link? :=
  (k3_calls_sameBut claim piece laid before p guests s s' rs cols hd).link

include hs in
/-- **The ledger behind is there and sized.** -/
theorem k3_calls_ledger (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) : (s'.fork?.any sizedB) = true := by
  obtain ⟨F, F', g, -, -, -, hF', -, L, -⟩ :=
    k3_calls_leaves claim piece laid before p guests hs s s' rs cols hw hd hIn
  rw [hF']
  exact sizedB_of L.padLeft.fit

include hs in
/-- **What the lookup on the calls left.** -/
theorem k3_calls_left (hw : okRoundsE rs = true)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) :
    K3LeftAt (fun s : Desc.First.S => s.fork?) (fun s : Desc.First.S => s.lookHeard?) h p.lm p.first
      (fun F => freeB F p.first (Forest.elems h) = true) s' := by
  obtain ⟨F, F', g, -, hn, hfree, hF', hg, L, -⟩ :=
    k3_calls_leaves claim piece laid before p guests hs s s' rs cols hw hd hIn
  exact ⟨F, F', g, _, hfree, hn, L, hg, hF'⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.freeAboveB_iff
#print axioms VerifiableInference.OnPublicFiles.k3_calls_freeAbove
#print axioms VerifiableInference.OnPublicFiles.k3_calls_unheard
#print axioms VerifiableInference.OnPublicFiles.k3_calls_linkSame
#print axioms VerifiableInference.OnPublicFiles.k3_calls_ledger
#print axioms VerifiableInference.OnPublicFiles.k3_calls_left
