-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/PlaceThree.lean: THE FIRST THREE CLAUSES OF WHAT IS OWED AT A PLACE OF THE CODE SWITCH
    (`K2PlaceOwes`, Johnson/Top/H0/K2Ties/Counted.lean), AT THE COMPOSED MEANING's CONSTANT's OWN
    ROW OF PIECES. Three theorems. A law file: no sub-protocol imports it.

Why. `K2PlaceOwes` asks of the piece q that stands at the place: q is the piece written out (`k2Q`);
    it holds the strict reading of a sub-protocol B, lifted over the public part; it accepts at no
    marked state. None of the three hangs on the code switch's law.

What is said.
  `two_of_forall`: a list that goes along a list of two, member by member, has two members.
  `k2_written_at_row`: under the constant's head, at its row `h.row L` (L's three lists the
      description's own), at a number i below 357 at which the description's first chain holds B,
      where B declares the code switch's two rounds at numbers p: q = `k2Q ((below B).lift …) q.base
      d₁ d₂ extq` for some d₁ d₂ extq, and the two written rounds have the declared entries and
      kinds (the fields he, hk of `K2AllOwes`). CALLS: the kind-free `atRow_more`,
      `atRow_lift` (Johnson/Desc/Kinds/Law/RowAtConst.lean) and `atRow_in` (RowLenAtConst.lean);
      `k2Q_of_facts` (Johnson/Top/H0/K2Ties/WrittenOut.lean).
  `k2_unmarked_at`: where B sits on the kind's behind a door with `LeftDoor`
      (Johnson/P1K2R/SitsLeft.lean) and `EndsUnmarked` (Johnson/P1K2R/SitsNoMark.lean): the third
      clause, in `K2PlaceOwes`' own form. By `unmarked_of_seat`
      (Johnson/Top/H0/K2Ties/NoMarkSeat.lean).

Limits. That the chain cF of the head is the chain of which Johnson/P1K2R/SitsNoMark.lean's
    `k02_leftU_file` speaks, and that its numbers 14 l + 2, 339 and 353 are the places of the kind
    in the constant's list, is NOT JOINED here. At the second hash function alone.
    No soundness is claimed.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Kinds.Law.RowAtConst
import Johnson.Desc.Kinds.Law.RowLenAtConst
import Johnson.Top.H0.K2Ties.WrittenOut
import Johnson.Top.H0.K2Ties.NoMarkSeat
import Johnson.P1K2R.SitsNoMark

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes.Maker Iop
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 codeSwitchKind ownPiece)
open VerifiableInference.Desc.First.K2Caller (k2Q k2Q_of_facts)
open VerifiableInference.Desc.First.K2Ties (unmarked_of_seat)
open VerifiableInference.Desc.Kinds.Head.Law (atRow_more atRow_lift atRow_in)
open H2K.JointK (Sits)
open _root_.Run (ckP)
open ProofFile (Cl)

theorem two_of_forall {α β : Type} {R : α → β → Prop} {ds : List α} {r₁ r₂ : β} (h : List.Forall₂ R
    ds [r₁, r₂]) : ∃ d₁ d₂, ds = [d₁, d₂] ∧ R d₁ r₁ ∧ R d₂ r₂ := by
  cases h with
  | cons h1 t =>
    cases t with
    | cons h2 t' =>
      cases t'
      exact ⟨_, _, rfl, h1, h2⟩

/-- **The piece at a place of the kind, written out, at the constant's own row.** -/
theorem k2_written_at_row {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np :
                  H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) (L :
                                    P5J.Free OnBytes.Flat.numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) (q₁ : (P5J.F0T
                                                OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁) (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np
                                                                     cF).shared.blocksInOrder = L.c₂ :: L.k₂) (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ ::
                                                                              L.k₃) (i : ℕ) (q) (hq : (h.row L)[i]? = some q) (hi : i < 357) (B : Block P5J.TS ProofFile.Cl) (hB :
                                                                                    cF.blocksInOrder[i]? = some B) (p : P2) (hr : B.rounds = VerifiableInference.Desc.First.K2.rounds p) :
    ∃ d₁ d₂ extq, q = k2Q ((below B).lift Prod.snd fun t s => (t.1, s)) q.base d₁ d₂ extq ∧ [d₁,
        d₂].map (·.entry) = (VerifiableInference.Desc.First.K2.rounds p).map (·.entry) ∧ ∀ d ∈ [d₁,
        d₂], Fmt.kindOf d.entry.name = some d.kind := by
  obtain ⟨hm, herr⟩ := atRow_more h L q₁ q₂ q₃ i q hq (atRow_in h i hi)
  have hl := atRow_lift h L q₁ q₂ q₃ i q B hq hB
  have hb : q.b.rounds = VerifiableInference.Desc.First.K2.rounds p := by
    rw [hl]
    exact hr
  obtain ⟨r₁, r₂, e⟩ : ∃ r₁ r₂, VerifiableInference.Desc.First.K2.rounds p = [r₁, r₂] := ⟨_, _, rfl⟩
  have hF := hm.same
  rw [hb, e] at hF
  obtain ⟨d₁, d₂, hd, h1, h2⟩ := two_of_forall hF
  obtain ⟨extq, hQ⟩ := k2Q_of_facts q d₁ d₂ hd hm.back herr
  refine ⟨d₁, d₂, extq, ?_, ?_, ?_⟩
  · rw [← hl]
    exact hQ
  · rw [e]
    simp only [List.map_cons, List.map_nil, h1.1, h2.1]
  · intro d hd'
    rcases List.mem_cons.1 hd' with rfl | hd'
    · rw [h1.1]
      exact h1.2.1
    · rcases List.mem_cons.1 hd' with rfl | hd'
      · rw [h2.1]
        exact h2.2.1
      · cases hd'

/-- **No accept at a marked state**, in the form in which `K2PlaceOwes` asks it. -/
theorem k2_unmarked_at {F : Frame} {P W : Type} (p : P2) (B : Block S Cl) (enter : S → Except String
    S) (leave : S → S → Except String S) (hS : Sits B (codeSwitchKind p : Block S Unit) enter leave) (hD :
                LeftDoor enter leave) (hE : EndsUnmarked leave) (bq : Block (P × S) Cl) (base : ℕ) (d₁ d₂ : RDT)
    (extq : (P × S) × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W) :
    ∀ a τ b, (ownPiece (k2Q (F := F) bq base d₁ d₂ extq) B (fun _ _ w => w) (k2Q (F := F) bq base d₁
        d₂ extq).err).ior.red.out a τ = some b → a.1.failed = none :=
  unmarked_of_seat (W := W) (⟨below (codeSwitchKind p), base, [d₁, d₂], [], fun _ _ w => w, Err.cap 128 (uLT
                  (ckP .two) [d₁, d₂])⟩ : Piece (ckP .two) F S Unit W) p rfl rfl B enter leave hS.rounds hS.step
      hD.1 hD.2 hE (fun _ _ w => w)

end P1K2

#print axioms P1K2.two_of_forall
#print axioms P1K2.k2_written_at_row
#print axioms P1K2.k2_unmarked_at
