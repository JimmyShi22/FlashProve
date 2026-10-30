-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MemberAt.lean: CONDITIONAL. THE MEMBER OF THE FIRST CHAIN THAT
STANDS AT THE PLACE OF THE LAYERS' OWN ROUNDS (kind K4) OF A GROUP IS THE LOT's OWN SUB-PROTOCOL;
AND ITS DECLARED ROUNDS.

What is here. A LAW ON THE DESCRIPTION's FIRST CHAIN: no prover, no run, no coin and no input is in
it. Statements and proofs: the library's `IM.k4_of` (Johnson/IMR/K4Seat.lean: at each group below 12
the third hearing member of segment 2 g is K4's lot's sub-protocol, seated alone at K4's place),
`IM.hear_at_flat` (Johnson/IMR/FlatIx.lean: it is a member of the flat list), and the places being
distinct.

  `k4_member_at_place`: **a member b of the chain's flat list at K4's place of group gk is the
      lot's own sub-protocol, seated alone there**, at parameters x with the ground's layers and its
      plan of that group.
  `k4_member_rounds`: **its declared rounds are K4's own entries**, at the ground's layers, the
      plan hp that the ground has at gk, and gk.

Not shown here. THE HYPOTHESES ARE PAID NOWHERE HERE: hS · hR: the public files lie in the goals'
scope and are read · O: the description is opened, with the format's second hash function itself in
the place that its maker keeps for it · hnd: the places of the chain's members are distinct · hb: b
is a member · hk: the group's number is below 12 · hpl: b stands at K4's place of that group · hh:
the ground has the plan hp there. THE FULL SIZE ALONE (the scope). Nothing on what the member
decides. No example of the hypotheses together has been through Lean.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.IMR.K4Seat
import Johnson.IMR.FlatIx

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- CONDITIONAL: on all seven hypotheses. **THE MEMBER AT K4's PLACE OF A GROUP IS K4's OWN.** -/
theorem k4_member_at_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hnd : (c.blocksInOrder.map (·.place)).Nodup) {b : Block S ProofFile.Cl} (hb : b ∈ c.blocksInOrder) {gk : ℕ}
    (hk : gk < 12) (hpl : b.place = IM.k4Place gk) :
    ∃ x : Bool × OnBytes.Desc.First.K4.Par,
      IM.LaidAlone ProofFile.sameReply b (ProofFile.k4Block x) b.name (IM.k4Place gk) ∧ x.2.g = gk ∧
        x.2.P = Bs.G₀.W.layers ∧ Bs.G₀.W.G[gk]? = some x.2.hp := by
  obtain ⟨Lk, b₀, x, e1, e2, -, hla, -, eg, eP, ehp, -, -⟩ := IM.k4_of hS hR O gk hk
  have hb₀ : b₀ ∈ c.blocksInOrder := List.mem_of_getElem? (IM.hear_at_flat e1 e2)
  have e0 : b = b₀ :=
    List.inj_on_of_nodup_map hnd hb hb₀ (hpl.trans (IM.alone_place hla).symm)
  rw [e0]
  exact ⟨x, hla, eg, eP, ehp⟩

/-- CONDITIONAL: on all eight hypotheses. **ITS DECLARED ROUNDS ARE K4's OWN ENTRIES.** -/
theorem k4_member_rounds (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂)
    (hnd : (c.blocksInOrder.map (·.place)).Nodup) {b : Block S ProofFile.Cl} (hb : b ∈ c.blocksInOrder) {gk : ℕ}
    (hk : gk < 12) (hpl : b.place = IM.k4Place gk) {hp : OnBytes.Model.Layer.HPlan2}
    (hh : Bs.G₀.W.G[gk]? = some hp) :
    b.rounds = (OnBytes.Desc.First.K4.entries Bs.G₀.W.layers hp gk).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound)) := by
  obtain ⟨x, hla, eg, eP, ehp⟩ := k4_member_at_place hS hR O hnd hb hk hpl
  have ehp' : x.2.hp = hp := Option.some.inj (ehp.symm.trans hh)
  rw [IM.alone_rounds hla, ← eP, ← ehp', ← eg]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_member_at_place
#print axioms ProofFile.Honest.K4.k4_member_rounds
