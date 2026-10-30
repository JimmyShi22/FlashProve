-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkForm.lean: CONDITIONAL. THE FULL SIZE ALONE. A LAW, NOT A
PART: its imports reach modules under Johnson/Goal/ (among others through Johnson/IMR/K4Seat.lean):
no file that defines a part of the description may import it.

What is here. THE WIDER MARKS' SENTENCE IN THE FORM IN WHICH THE FRAME's LIST OF ALL MARKS ASKS IT.
The frame's `marksHead_hM` (Honest/Law/MarksHead.lean, as its writers have handed it out; not
imported here) takes, for K4's marks, a hypothesis h₄: at every cut of the first chain's members but
the last, for every mark of `k4MarksWide` that stands at the member's place, at data that fit the
member's declared rounds: `MarkDebt` at the mark's own stated share. `k4_markDebt_form` ENDS IN THAT
HYPOTHESIS' TEXT, sign for sign, with the kit `Run.ckP .two` in the place of its letter for a kit,
and the opened description's public data and ground in the place of its two letters. NO INEQUALITY
AND NO NUMBER IS LEFT TO THE CALLER: the number is the mark's stated share. The proof is five calls:
a mark of the list is `k4MarkWide` at a group below twelve (`k4MarksWide_of_mem`,
Law/K4MarksWide.lean); it stands at the library's place of K4's member of that group
(`k4MarkWide_at`, here); the member at that place is K4's own and declares K4's rounds
(`k4_member_rounds`, Law/MemberAt.lean); so the data's entries and kinds are the table's
(`ent_of_kindFits`, Law/CoinRow.lean); then `k4_markWideDebt_table` (Law/MarkWideDebt.lean).

Not shown here. THE FIVE HYPOTHESES ARE GIVEN NOWHERE HERE: hS, hR and O (the public files are in
scope, are read, and the description is opened at them), hnd (the members' places are distinct: the
frame has it from the description's own test on its places: `places_nodup`, Honest/Law/Cuts.lean;
not called), cut (the chain is a list and one last member). MET FOR NOTHING AT EVERY MEMBER THAT
DOES NOT STAND AT K4's PLACE OF A GROUP: there no mark of the list passes the filter: the sentence
has content at K4's own members alone. AT THE KIT `Run.ckP .two` ALONE: a round's challenge is a
string of hash blocks; the law that Law/MarkWideDebt.lean calls has its own limit: the uniform law
on one round's messages is named, not derived. THE CALL OF `marksHead_hM` ITSELF HAS NOT BEEN
THROUGH LEAN. The share is a stated product; it is evaluated nowhere. No example of the hypotheses
together has been through Lean.

No property is claimed.

  `k4MarkWide_at`   the wider mark of a group stands at the library's place of K4's member of that
      group.
  `k4_markDebt_form`   **the hypothesis on K4's marks of the frame's `marksHead_hM`, to its letter,
      at strings of hash blocks.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideDebt
import Johnson.Desc.ProofFile.Honest.K4.Law.K4MarksWide
import Johnson.Desc.ProofFile.Honest.K4.Law.CoinRow
import Johnson.Desc.ProofFile.Honest.K4.Law.MemberAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open scoped ENNReal
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- The wider mark of a group stands at the library's place of K4's member of that group. -/
theorem k4MarkWide_at (W : OnBytes.Model.Layer.Pub) (hp : OnBytes.Model.Layer.HPlan2) (g a s : ℕ) :
    (k4MarkWide ⟨W, hp, g, 2 * g, 3, a, s⟩).place = IM.k4Place g := by
  rw [k4MarkWide_place]
  rfl

/-- CONDITIONAL: on all five hypotheses. **THE WIDER MARKS' SENTENCE, AT EVERY CUT OF THE CHAIN, AT
THE MARK's OWN STATED SHARE**, at strings of hash blocks. -/
theorem k4_markDebt_form (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hnd : (c.blocksInOrder.map (·.place)).Nodup) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : c.blocksInOrder = pre₁ ++ [e₁]) (PM : Block S ProofFile.Cl → List Fmt.Drawn → Prop) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K4.k4MarksWide Z Bs.G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (mk.share.val) := by
  intro A b b' B e mk hmk dsb hfit
  obtain ⟨hm, hpl⟩ := List.mem_filter.1 hmk
  obtain ⟨g, hp, hg, hh, rfl⟩ := k4MarksWide_of_mem hm
  have hpl' : b.place = IM.k4Place g :=
    (eq_of_beq hpl).symm.trans (k4MarkWide_at Bs.G₀.W.layers hp g 0 (2 * g))
  have hb : b ∈ c.blocksInOrder := by
    rw [cut, e]
    simp
  have hr := k4_member_rounds hS hR O hnd hb hg hpl' hh
  have hK := hfit
  rw [hr] at hK
  obtain ⟨hent, hkind⟩ := ent_of_kindFits dsb _ hK
  exact k4_markWideDebt_table ⟨Bs.G₀.W.layers, hp, g, 2 * g, 3, 0, 2 * g⟩ dsb hent hkind (PM b)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4MarkWide_at
#print axioms ProofFile.Honest.K4.k4_markDebt_form
