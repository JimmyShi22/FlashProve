-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimLot.lean: the closing of a segment (K10): the numbers that the lot reads, the
seated block and the side at its place, at one Q. Two definitions; six theorems.

  `par_mem`           the closing's numbers that the lot reads at a segment are in `closePars` (Honest/K10/AtLot.lean)
  `Tied`              of a chain c, the public part Z, a link l, and p, Q, b: the lot reads p and Q at l; b is c's
                   block at the closing's number; b = the kind's block at Q, seated (the library's `IM.seatedAs`); Q is
                   in `closePars Z`; b's place is `closePlace Q`; b's rounds and b's oracle messages, each list by
                   itself, are the first and the second members of `closeRounds Q`
  `tied_at_scope`     under the library's three premises (in scope; the files read; `IM.Open`, which the library has of
                   its description's return), at each link l < 25: there are p, Q, b with `Tied c Z l p Q b`
  `Tied.zip`          the two lists zipped are `closeRounds Q`
  `Tied.plan`         where b passes its own test on the plan, Q passes `closePlan` (Honest/K10/Sim.lean): by the
                   library's `IM.alone_planOk`, `IM.retype_planOk` (Johnson/IMR/SeatForm.lean)
  `find_of_nodup`     a small one on lists
  `closeRow`          the row: [(`closePart (foldShellT true J foldWords)`, `closeSim J.pub.par`)]
  **`member_at_scope`**   there, at any job J whose place's numbers are Q and any list of falls: `Side.seated`
                   (Honest/Side.lean), off c.blocksInOrder at `closePlace Q`, with the row `closeRow J`, yields a side; its
                   block is b; its members are [`closeAt true J`] (Honest/K10/Sim.lean); it passes `Side.fits`

Called, of the library: `IM.k9_alone`, `IM.k10Par_fields`, `IM.subs_scope` (Johnson/IMR/LinkSeat.lean),
`IM.places_scope` (PlacesScope.lean), `IM.places_nodup` (BorderW.lean). Of this kind: `seated_at_scope`
(Johnson/Desc/K10/Honest/KeepsSeat.lean), `seated_lists`, `links_of_where`, `members_is`, `moves_len`, `closePlan_iff`.

Limits. Whether the three premises can be had together is no theorem (the head of Johnson/IMR/K6Seat.lean says so). At
`OnBytes.secondHashFunction` alone. At the c of `IM.Open`: that the description's first chain is c is not carried here
(`open_first`, LotPlaces.lean). That the places of `closePars Z` have no double, and that each of its Q is one
of these 25: not here (`places_once`, `pars_tied`, there). J is a letter with J.pub.par = Q: its other fields are
free. That the stretch of declared rounds has 2 + k rounds, the book's cut at that place, the rounds in front: nothing
here. At the first chain alone. No property of the protocol is claimed: nothing is said on its soundness, completeness,
binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimBlock
import Johnson.Desc.ProofFile.Honest.K10.AtLot
import Johnson.Desc.ProofFile.Honest.K10.LotLinks
import Johnson.IMR.PlacesScope
import Johnson.IMR.BorderW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)

/-- The closing's numbers that the lot reads at a segment are in the list of places at which the kind's halves are
laid. -/
theorem par_mem {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where} {Q : Par}
    (hp : ProofFile.k9Where (ProofFile.k9Stretches Z) l = some p)
    (hQ : ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q) : Q ∈ closePars Z := by
  unfold closePars
  refine List.mem_filterMap.2 ⟨l, links_of_where hp, ?_⟩
  rw [hp]
  exact hQ

/-- **What is said of a chain, the public part, a link, and p, Q, b**: the lot reads p and Q at the link; b is the
chain's block at the closing's number; b is the kind's block at Q, seated (the equation); Q is in `closePars`; b's
place is `closePlace Q`; b's rounds and its oracle messages are the first and the second members of `closeRounds Q`. -/
def Tied (c : Chain S ProofFile.Cl) (Z : ProofFile.Pub) (l : Nat) (p : VerifiableInference.Desc.K9.Where) (Q : Par)
    (b : Block S ProofFile.Cl) : Prop :=
  IM.k9At Z l = some p ∧ ProofFile.k10Par Z (ProofFile.k9Stretches Z) p = some Q ∧
    c.blocksInOrder[14 * l + (if l = 24 then 9 else 7) + 5]? = some b ∧
    b = IM.seatedAs ProofFile.sameReply (K9.closing (Cl := Unit) Q).retype b.name
      (IM.cAt l (IM.subAt l) 1 .K10) ∧
    Q ∈ closePars Z ∧ b.place = closePlace Q ∧
    b.rounds = (closeRounds Q).map (·.1) ∧ b.oracles = (closeRounds Q).map (·.2)

/-- **At every link, in scope.** -/
theorem tied_at_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c Z l p Q b := by
  obtain ⟨_, p, Q, b, _, hp, hQ, _, hn, hb, _⟩ := YesFree.seated_at_scope hS hR O l hl
  obtain ⟨_, p', _, hp', hpc, _, hlk, hpe, _⟩ :=
    IM.k9_alone O l (IM.subAt l) (IM.subs_scope hS hR O l hl)
  obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
  obtain ⟨q1, q2⟩ := IM.k10Par_fields hQ
  refine ⟨p', Q, b, hp, hQ, hn, hb, par_mem hp hQ, ?_, ?_, ?_⟩
  · rw [hb]
    show IM.cAt l (IM.subAt l) 1 .K10 = closePlace Q
    unfold closePlace
    rw [q1, q2, hlk, hpe, hpc]
  · rw [hb]
    exact (seated_lists Q _ _).1
  · rw [hb]
    exact (seated_lists Q _ _).2

/-- The two lists zipped. -/
theorem Tied.zip {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where}
    {Q : Par} {b : Block S ProofFile.Cl} (h : Tied c Z l p Q b) :
    b.rounds.zip b.oracles = closeRounds Q := by
  obtain ⟨_, _, _, _, _, _, h1, h2⟩ := h
  rw [h1, h2, List.zip_map']
  exact List.map_id' _

/-- Where the block passes its own test on the plan, the place's numbers pass `closePlan` (Honest/K10/Sim.lean). -/
theorem Tied.plan {c : Chain S ProofFile.Cl} {Z : ProofFile.Pub} {l : Nat} {p : VerifiableInference.Desc.K9.Where}
    {Q : Par} {b : Block S ProofFile.Cl} (h : Tied c Z l p Q b) (hb : b.planOk = true) : closePlan Q := by
  obtain ⟨_, _, _, he, _⟩ := h
  rw [IM.alone_planOk he] at hb
  exact (closePlan_iff (Cl' := Unit) Q).2 (IM.retype_planOk _ hb).1

/-- In a list whose members' marks are all different, the first member with a member's mark is that member. -/
theorem find_of_nodup {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) : ∀ (l : List α) (k : Nat) (b : α),
    (l.map f).Nodup → l[k]? = some b → l.find? (fun x => f x == f b) = some b
  | [], _, _, _, h => by cases h
  | a :: l, 0, b, _, h => by
      obtain rfl : a = b := Option.some.inj h
      exact List.find?_cons_of_pos (p := fun x => f x == f a) (beq_self_eq_true _)
  | a :: l, k + 1, b, hn, h => by
      rw [List.map_cons, List.nodup_cons] at hn
      have hb : b ∈ l := List.mem_of_getElem? h
      have hne : ¬ (f a == f b) = true := fun e =>
        hn.1 (by rw [eq_of_beq e]; exact List.mem_map_of_mem hb)
      exact (List.find?_cons_of_neg (p := fun x => f x == f b) hne).trans
        (find_of_nodup f l k b hn.2 h)

variable {V W X Pb : Type}

/-- The row: the cured part with the simulator's form. -/
def closeRow (J : CloseJob W) : List (Part V W X × Sim Pb) :=
  [(closePart (foldShellT true J foldWords), closeSim J.pub.par)]

/-- **At every link, in scope: what `Side.seated` (Honest/Side.lean) yields off c.blocksInOrder at the closing's place**, with
`closeRow J` as its row, at any job whose place's numbers are Q and any list of falls: it yields a side; its block is b;
its one member is the literal member `closeAt true J`; it passes `Side.fits`. -/
theorem member_at_scope {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (l : Nat) (hl : l < 25) :
    ∃ (p : VerifiableInference.Desc.K9.Where) (Q : Par) (b : Block S ProofFile.Cl), Tied c Z l p Q b ∧
      ∀ (J : CloseJob W) (_ : J.pub.par = Q) (fs : List (Fall S)),
        ∃ σ : Side S ProofFile.Cl V W X Pb,
          Side.seated c.blocksInOrder (closePlace Q) (closeRow J) fs = some σ ∧
          σ.block = b ∧ σ.row = closeRow J ∧ σ.members = [closeAt true J] ∧ σ.fits = true := by
  obtain ⟨p, Q, b, hT⟩ := tied_at_scope hS hR O l hl
  refine ⟨p, Q, b, hT, fun J hJ fs => ?_⟩
  have hz := hT.zip
  obtain ⟨_, _, hn, _, _, hp, h1, h2⟩ := hT
  have hnd : (c.blocksInOrder.map (·.place)).Nodup := by
    rw [IM.places_scope hS hR O]
    exact IM.places_nodup
  have hf := find_of_nodup (·.place) c.blocksInOrder _ b hnd hn
  refine ⟨{ block := b, row := closeRow J, fall := fallOf fs (closePlace Q) }, ?_, rfl, rfl, ?_, ?_⟩
  · unfold Side.seated
    rw [← hp, hf]
    rfl
  · exact members_is true J _ rfl (by rw [hJ]; exact hz)
  · unfold Side.fits
    have e1 : (closeRow (V := V) (X := X) (Pb := Pb) J).zipIdx.all
        (fun s => s.1.2.addr == ⟨b.place, s.2⟩) = true := by
      show ((closeSim (Pb := Pb) J.pub.par).addr == ⟨b.place, 0⟩ && true) = true
      rw [hp, hJ, Bool.and_true]
      exact beq_self_eq_true _
    have e2 : (Side.half (S := S) (Cl := ProofFile.Cl) (Pb := Pb)
        { block := b, row := closeRow (V := V) (X := X) J, fall := fallOf fs (closePlace Q) }).rounds =
        b.rounds.length := by
      show 0 + (closePart (V := V) (X := X) (foldShellT true J foldWords)).moves.length = _
      rw [moves_len, h1, List.length_map, hJ, Nat.zero_add]
    have e3 : b.oracles.length = b.rounds.length := by
      rw [h1, h2, List.length_map, List.length_map]
    show (_ && _ == _ && _ == _) = true
    rw [e1, e2, e3, beq_self_eq_true]
    rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.par_mem
#print axioms ProofFile.Honest.K10.Tied
#print axioms ProofFile.Honest.K10.tied_at_scope
#print axioms ProofFile.Honest.K10.Tied.zip
#print axioms ProofFile.Honest.K10.Tied.plan
#print axioms ProofFile.Honest.K10.find_of_nodup
#print axioms ProofFile.Honest.K10.closeRow
#print axioms ProofFile.Honest.K10.member_at_scope
