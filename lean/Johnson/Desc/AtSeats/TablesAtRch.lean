-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/TablesAtRch.lean: THE INVARIANT `TablesOk`
(Johnson/Desc/K1/Law/TablesOk.lean: where the output head's reads' tables are laid, they are what
the reads' quiet step would lay off this very state) ALONG THE REACHED STATES OF THE PROOF FILE's
FIRST CHAIN, AT THREE OF THE FOUR BORDERS OF EACH SEGMENT's TWO LATER SENDINGS OF KIND K1: behind
the reads' place; in front of and behind the digits' place. FROM THE GOALS' SCOPE ALONE.
Statements with their proofs. It is no invariant that every sub-protocol keeps (the reply's
hearing turns the covered positions; the head's own hearing turns what was heard): so it is had BY
POSITION: in every segment the order is: K1 (reads), K8, K1 (digits). `tables_behind_reads`:
  behind the reads' place: one step back; the sub-protocol there is the lot's own, alone
  (`k01_flat_reads`); behind its quiet step the invariant holds with nothing in front
  (`tablesOk_behind_reads`, Johnson/Desc/K1/Law/TablesWalk.lean). `k8_kind_at`, `k8_flat`: the
  sub-protocol between the two is kind K8's, alone. `tables_front_digits`: one step more: K8's
  keeps it (`quietT_small`). `tables_behind_digits`: one step more: `tablesOk_later`.
  `tables_three_rchAt`: the three along `RchAt`.
What is not claimed. The fourth border (in front of the reads' place). That the scope can be met.
Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.TablesWalk
import Johnson.Desc.K1.Law.K01LawTied
import Johnson.IMR.K8Seat
import Johnson.Top.H0.Walk.ReachAt
import Johnson.Top.H0.Walk.ReachInv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw stepYes_decide)
open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S kindsBeforeBatching)
open OnBytes.Model.Stages (LinkH)
open IM (Open k1Ix k1Reads subAt)
open ProofFile (Cl)

/-- Between a segment's two later sendings stands kind K8. -/
theorem k8_kind_at (l : ℕ) :
    (kindsBeforeBatching (subAt l) (l == 0))[k1Ix l false + 1]? = some KindName.K8 := by
  unfold subAt
  by_cases h24 : l = 24
  · subst h24
    rfl
  · have e : k1Ix l false = 3 := by
      show (if false then 5 else 3) + (if l = 24 then 1 else 0) = _
      rw [if_neg h24]
      rfl
    rw [e, if_neg h24]
    by_cases he : l % 2 = 0
    · rw [if_pos he]
      cases (l == 0) <;> rfl
    · rw [if_neg he]
      cases (l == 0) <;> rfl

theorem k1Ix_true (l : ℕ) : k1Ix l true = k1Ix l false + 2 := by
  show (if true then 5 else 3) + (if l = 24 then 1 else 0) =
    (if false then 5 else 3) + (if l = 24 then 1 else 0) + 2
  by_cases h : l = 24 <;> simp [h]

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **The flat list's entry between the two.** -/
theorem k8_flat (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) :
    ∃ (b : Block S Cl) (Xl : LinkH), c.blocksInOrder[14 * l + k1Ix l false + 2 + 1]? = some b ∧
      IM.LaidAlone ProofFile.sameReply b (First.K8.whole (ProofFile.k8ParW Z Bs.G₀ Xl l)) b.name
        { chain := 1, link := some l, piece := k1Ix l false + 1 + 1, kind := .K8 } := by
  obtain ⟨Lk, b, Xl, e1, e2, _, _, h⟩ := IM.k8_alone O l (subAt l) (IM.subs_scope hS hR O l hl)
    (k1Ix l false + 1) (k8_kind_at l) (by have := IM.k1Ix_range l false
                                          have := IM.k1Ix_range l true
                                          rw [k1Ix_true] at this
                                          omega)
  have h5 := IM.hear_at_flat e1 e2
  rw [IM.flatIx_scope hS hR O (by omega) (k1Ix l false + 1)] at h5
  have e : 14 * l + k1Ix l false + 2 + 1 = 14 * l + (k1Ix l false + 1) + 2 := by omega
  rw [← e] at h5
  exact ⟨b, Xl, h5, h⟩

variable {Q : Type} {start : Q → S}

/-- **Behind the reads' place.** -/
theorem tables_behind_reads (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * l + k1Ix l false + 2 + 1) a) :
    TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.2 := by
  obtain ⟨b, Xl, reads, hb, _, hla⟩ := k01_flat_reads hS hR O l hl
  cases h with
  | @succ _ z s s' b' _ hb' hy =>
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact tablesOk_behind_reads Z Bs.G₀ l Xl reads s s' rs gs
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1

/-- **In front of the digits' place.** -/
theorem tables_front_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * l + k1Ix l false + 2 + 1 + 1) a) :
    TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.2 := by
  obtain ⟨b, Xl, hb, hla⟩ := k8_flat hS hR O l hl
  cases h with
  | @succ _ z s s' b' h0 hb' hy =>
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact quietT_small _ _ _ _ s s' rs gs
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
      (tables_behind_reads hS hR O l hl (z, s) h0)

/-- **Behind the digits' place.** -/
theorem tables_behind_digits (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : ℕ) (hl : l < 25) (a : Q × S)
    (h : Reach 0 c.blocksInOrder start (14 * l + k1Ix l false + 2 + 1 + 1 + 1) a) :
    TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.2 := by
  obtain ⟨b, digits, hb, hla⟩ := k01_flat_digits hS hR O l hl
  have hix : 14 * l + k1Ix l true + 2 = 14 * l + k1Ix l false + 2 + 1 + 1 := by
    rw [k1Ix_true]
    omega
  rw [hix] at hb
  obtain ⟨_, Xl, _, _, _, _⟩ := k01_flat_reads hS hR O l hl
  cases h with
  | @succ _ z s s' b' h0 hb' hy =>
    obtain rfl : b = b' := Option.some.inj (hb.symm.trans hb')
    obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
    exact tablesOk_later Z Bs.G₀ l true Xl digits s s' rs gs
      ((IM.yes_alone hla (fun e => nomatch e) s s' rs gs).1 hd).1
      (tables_front_digits hS hR O l hl (z, s) h0)

/-- **The three, along "reached at the description's first chain".** -/
theorem tables_three_rchAt (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Str : Type} (l : ℕ) (hl : l < 25)
    (j : ℕ) (hj : j = 14 * l + k1Ix l false + 2 + 1 ∨ j = 14 * l + k1Ix l true + 2 ∨
      j = 14 * l + k1Ix l true + 2 + 1) (a : (ProofFile.InstPub × S) × Str)
    (h : RchAt (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z)
      c) j a) : TablesOk Bs.G₀.W.hS Bs.G₀.W.HLy Bs.G₀.W.H a.1.2 := by
  have hr := rchAt_raw h
  have hix : 14 * l + k1Ix l true + 2 = 14 * l + k1Ix l false + 2 + 1 + 1 := by
    rw [k1Ix_true]
    omega
  rcases hj with rfl | rfl | rfl
  · exact tables_behind_reads hS hR O l hl a.1 hr
  · rw [hix] at hr
    exact tables_front_digits hS hR O l hl a.1 hr
  · rw [hix] at hr
    exact tables_behind_digits hS hR O l hl a.1 hr

end

end VerifiableInference.Desc.K1
