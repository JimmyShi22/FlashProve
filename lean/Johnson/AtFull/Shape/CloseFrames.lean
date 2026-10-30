-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/CloseFrames.lean: THE CLOSING OF A SEGMENT (kind K10), AT ALL 25 LINKS OF THE
PROOF FILE's OWN FIRST CHAIN, IN THE FRAME's OWN FORM: the two premises that the rule for acceptance
asks at a member: Carries and Returns (Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the
reader shA of Johnson/AtFull/Shape/FrameForm.lean (the chain's shape and the rows' makes). A joining
of another house's laws (Johnson/Desc/K10/Honest/AtPair.lean: closeGF, closeOrdB, closing_atF);
nothing is evaluated.

  THE STEP ON ShA: optE (closeGF Q) (Johnson/AtFull/Shape/FrameOpt.lean: a step that may refuse, as
    the frame's letters take it).
  **`close_frame`** (l < 25): p by IM.k9At Zp l · Q by ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p: for
    every ft, every table of steps G with G (LPFK10.ixK10 l) = optE (closeGF Q) and every table vals
    with vals (LPFK10.ixK10 l) s rs gs = closeOrdB s: Carries and Returns at that member.
    (LPFK10.ixK10 l = 14 l + 12, and 350 at the head's link: that house's number_is.)

Limits. TWO PREMISES OF THE RULE AT 25 OF 358 MEMBERS. G and vals are letters: no table is laid.
close_frame does not say that a member stands at its number; it asks that vals equals closeOrdB, and
its proof uses only that a yes of vals gives a yes of closeOrdB. closeOrdB (every tensor among the
terms and forms of each row that goes into the batching is in order) SUFFICES FOR "returns"; it is
not what the decision tests; that it accepts at a state of a run is a debt by name, and
is shown of no state but a small example's. UNDER THE HEAD: that it has a member is shown in scope,
where the reader returns and `protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that
these three hold together, at two named sets of public files, in a side library. At the earlier
hash. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameOpt
import Johnson.Desc.K10.Honest.AtPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link KindName roundsFit noDigest)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open ProofFile.Honest (Carries Returns carries_seat returns_seat)
open ProofFile.Honest.K10.YesFree

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

theorem close_frame (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par),
      IM.k9At Zp l = some p ∧ ProofFile.k10Par Zp (ProofFile.k9Stretches Zp) p = some Q ∧
      ∀ (ft : Nat) (G : Nat → ShA → Except String ShA)
        (vals : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool),
        G (LPFK10.ixK10 l) = optE (closeGF Q) →
        (∀ s rs gs, vals (LPFK10.ixK10 l) s rs gs = closeOrdB s) →
        Carries cF.blocksInOrder ft (firstZA G vals) (LPFK10.ixK10 l) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (LPFK10.ixK10 l) := by
  obtain ⟨p, Q, b, hp, hQ, hn, hb, hf, hc, -, hr⟩ := closing_atF h l hl
  refine ⟨p, Q, hp, hQ, fun ft G vals hG hv => ⟨?_, ?_⟩⟩
  · refine carries_seat hn fun rs cols _ s s' u hd hu => ?_
    have hu' : G (LPFK10.ixK10 l) (shA s) = .ok u := hu
    rw [hG] at hu'
    have hd' : closeGF Q (shA s) = some (chainF s') := hc s s' _ _ hd
    exact Option.some.inj ((optE_ok.1 hu').symm.trans hd')
  · refine returns_seat hn fun rs cols hF s u hu hvv => ?_
    have hu' : G (LPFK10.ixK10 l) (shA s) = .ok u := hu
    rw [hG] at hu'
    have hvv' : vals (LPFK10.ixK10 l) s (rs.map noDigest) (b.shown ft rs cols) = true := hvv
    rw [hv] at hvv'
    obtain ⟨f1, f2⟩ := (hf ft rs cols).1 hF
    exact hr s u _ _ (optE_ok.1 hu') hvv' (by rw [List.length_map]; exact f1)
      (shapedAll_noDigest f2)

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.close_frame
