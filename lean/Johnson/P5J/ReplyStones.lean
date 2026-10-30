-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/ReplyStones.lean: THE THREE PREMISES ON THE DRIVER's STRUCTURE H OF THE FRAME FACT ON
THE REPLY (`eachRep_at_driver`, Johnson/P5J/ReplyAtDriver.lean: hc, hs, hK) AT ONE H, where the
proof file's IOP as written in Lean is opened (`IM.Open`, Johnson/IMR/SeatOpen.lean). A joining of
several other files' theorems.

  `heardV_of_same`: what the guard's test `ProofFile.sameReply` lets pass leaves the reading `heardV`.
  `hearsOnce_at_block`: the step from the list base to H: where every member of base at a place of
    the kind K7 hears once, so does what `H.block` gives there (it is that member, or that member
    with something joined behind it under the guard, which leaves the reading).
  `reply_stones_open`: in the goals' scope, at the second hash function: there is an H with
    (R1) `firstChain H fullLinks true = some c` · (R2) what `H.same` lets pass leaves `heardV` ·
    (R3) what `H.block` gives at a place of the kind K7 hears once: FROM ONE PREMISE hK: every
    member of base at a place of the kind K7 hears once.
What is called: `ProofFile.Law.pure_first_at` (Johnson/Desc/ProofFile/Law/FirstSame.lean) ·
`LPFK9.k13_stands`, `LPFK9.subs_full` (Johnson/LPFK9R/SubsFull.lean) · `IM.sameReply_eq`
(Johnson/IMR/SeatForm.lean) · `hearsOnce_andThen`, `guarded_or` (Johnson/Desc/Sound/).
Limits. hK IS A PREMISE: the law of the kind K7's seat. At OnBytes.secondHashFunction alone (`subs_full` stands
there). No member is shown: that such an opening exists is not said here. Nothing on soundness. On
hiding nothing.

-/
import Johnson.P5J.ReplyAtDriver
import Johnson.P5J.MeansQ
import Johnson.Desc.ProofFile.Law.FirstSame
import Johnson.LPFK9R.SubsFull
import Johnson.IMR.SeatForm
import Johnson.Desc.Sound.SeatGuardLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P5J
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (Blocks firstChain)

/-- **What the guard's test lets pass leaves the reading.** -/
theorem heardV_of_same (t s : TS) (h : ProofFile.sameReply t s = true) :
    heardV (fun s : TS => s) s = heardV (fun s : TS => s) t := by
  have e : t.out.reply = s.out.reply := IM.sameReply_eq h
  have e' : s.heardTok? = t.heardTok? := by
    unfold VerifiableInference.Desc.First.S.heardTok? VerifiableInference.Desc.First.S.heard
    rw [e]
  unfold heardV
  rw [e']

/-- **From the list base to the driver's structure.** fr: what may be joined behind a member. -/
theorem hearsOnce_at_block {base : List (Block TS ProofFile.Cl)}
    {fr : List (ProofFile.FrameRole × Block TS ProofFile.Cl)} {H : Blocks TS ProofFile.Cl}
    (hB : ∀ a b, H.block a = some b → ∃ b0 ∈ base, b0.place = a ∧
      (b = b0 ∨ ∃ x ∈ fr, ∃ l, x.1 = .behind l b0.name ∧ b0.place.link = some l ∧
        b = b0.andThen b0.name (x.2.guarded ProofFile.sameReply fun _ => false)))
    (hK : ∀ b0 ∈ base, b0.place.kind = KindName.K7 → b0.HearsOnce (heardV fun s : TS => s)) :
    ∀ a b, H.block a = some b → a.kind = KindName.K7 →
      b.HearsOnce (heardV fun s : TS => s) := by
  intro a b hb ha
  obtain ⟨b0, h0, hp, hc⟩ := hB a b hb
  have h1 := hK b0 h0 (by rw [hp]; exact ha)
  rcases hc with rfl | ⟨x, _, l, _, _, rfl⟩
  · exact h1
  · refine VerifiableInference.Desc.hearsOnce_andThen b0.name h1 ?_
    rcases VerifiableInference.Desc.guarded_or (same := ProofFile.sameReply) (fun _ => false) x.2
      (h := heardV fun s : TS => s) heardV_of_same with hf | hl
    · exact nomatch hf
    · exact hl

/-- **THE THREE AT ONE H**, from the law of the kind K7's seat over base. -/
theorem reply_stones_open {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {F : FileDescription ProofFile.Inst}
    {Zp : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)} {c : Chain TS ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL F Zp Bs base c A B)
    (hK : ∀ b0 ∈ base, b0.place.kind = KindName.K7 → b0.HearsOnce (heardV fun s : TS => s)) :
    ∃ H : Blocks TS ProofFile.Cl, firstChain H fullLinks true = some c ∧
      (∀ t s, H.same t s = true → heardV (fun s : TS => s) s = heardV (fun s : TS => s) t) ∧
      ∀ a b, H.block a = some b → a.kind = KindName.K7 →
        b.HearsOnce (heardV fun s : TS => s) := by
  obtain ⟨H, hf, hs, hB⟩ := ProofFile.Law.pure_first_at O.chain (LPFK9.k13_stands O)
  rw [LPFK9.subs_full hZ hR O] at hf
  refine ⟨H, hf, fun t s h => ?_, hearsOnce_at_block hB hK⟩
  rw [hs] at h
  exact heardV_of_same t s h

end P5J

#print axioms P5J.heardV_of_same
#print axioms P5J.hearsOnce_at_block
#print axioms P5J.reply_stones_open
