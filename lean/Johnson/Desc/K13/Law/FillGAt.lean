-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FillGAt.lean: WHAT THE TIE AT THE FIRST SEGMENT's OPENING ASKS OF THE TABLE's
LETTERS (`FillG`, Johnson/Desc/K13/Law/AtTableFirst.lean) OUT OF WHAT THE LETTERS SAY AND TESTS ON
THE PLAN. Statements with their proofs. `inOrderG_rides`: "in order" as our layer lays it rides
  over a step of the joined block, where what
    other layers say of it rides and the joined block's own test on the plan says yes.
  `knownG`: the five public items of which our files show that they ride past the block: the
    proximity test's three, "K13.pileMasks", "no reply is held".
  `fillG_at`: **`FillG` at any list mk of items that come**, at any list Q of riders. IT
  TAKES: `MgK13`, `MgG`, "no reply is held" as the table's own layer lays it; `PlanG`; the joined
    block's test on the plan; that the index masks' number is the last of the place's messages;
    that the plan's three lists go on with what the place lays, and the book counts from the
    place's first tree; the decoder reads the public part alone; what other layers say of "in
    order" rides; the constraints go back; the making of every item of mk that is not one of
    `madeSix`; and a rider's premise for every item of Q that is not one of the five.
What is not claimed. These premises. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.OthersGAt
import Johnson.Desc.K13.Law.PileMasks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker
open Desc.Plain
open Johnson.Pack (sigOf)
open Johnson.Desc.First.Walk (LayPar)
open VerifiableInference.Desc.First (S Pub Meaning Numbers unheardB)
open VerifiableInference.Desc.First.Look (K3Data)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)
open VerifiableInference.Desc.K12.Door (toTree)

/-- "In order" rides over a step of the joined block. -/
theorem inOrderG_rides {Pp W Cl : Type} {P : Where} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {N : Numbers} {rest : Pp × S → Bool} {Mg : Meaning Pp W} {nR : ℕ}
    {rw : Pp × S → W → Wit GE nR P.lin.kCol} {q : Params.First} {gp : GPar} {nm : String}
    {X : LayPar} {fvs : List Bool} {kCol : ℕ} (hS : Sentences P cs sh ly N rest Mg rw)
    (hrest : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → rest x = true → rest x' = true)
    (hplan : (K1.openingZero q gp nm X fvs kCol : Block S Cl).planOk = true) (x x' : Pp × S)
    (h : StepG Cl q gp nm X fvs kCol x x') (h0 : Mg.inOrder x = true) :
    Mg.inOrder x' = true := by
  obtain ⟨ft, rs, cols, n, hst⟩ := h.2
  obtain ⟨r₁, r₂, gs, hd⟩ := h.decide
  rw [hS.inOrder, Bool.and_eq_true] at h0 ⊢
  exact ⟨hrest x x' h h0.1,
    inOrderK13_rides' (openingZero_tidy q gp nm X fvs kCol hplan ft _ rs cols _ n hst)
      (openingZero_plan q gp nm X fvs kCol _ _ _ _ hd) h0.2⟩

/-- The five public items of which our files show that they ride past the block. -/
def knownG : List Pub := [bookItem, seatsItem, shapesItem, pileMasksItem, .unheard]

/-- **`FillG` at any list of items that come.** -/
theorem fillG_at {Pp Cl Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid} {q : Params.First} {gp : GPar} {nm : String}
    {X : LayPar} {fvs : List Bool} {kCol : ℕ} {nsOf : ℕ → Option ℕ} {d : K3Data} {dg : Bool}
    (Q : List Pub) (p : Option Place) (mk : List Pub)
    (hMg : MgK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) (hG : MgG N Mg nsOf d dg)
    (hU : ∀ x, Mg.pub .unheard x = unheardB x.2) (hUP : ∀ x, Mg.pubP .unheard x)
    (hPl : PlanG X nsOf d dg sh ly) (hm : Pub.noneSent ∈ Q)
    (hplan : (K1.openingZero q gp nm X fvs kCol : Block S Cl).planOk = true)
    (hidx : N.indexNo = (K1.firstPar q gp).sent.size - 1)
    (hft : (K1.firstPar q gp).gp.firstTree = 0)
    (hp : ((toTree L).places.drop (N.msgsAt p)).take (K1.firstPar q gp).sent.size =
      K12.Coin.placesOf (N.treesAt p) (K1.firstPar q gp).sent.size (K1.layOf (K1.firstPar q gp)))
    (hs : ((toTree L).shapes.drop (N.treesAt p)).take (K1.layOf (K1.firstPar q gp)).shapes.size =
      (K1.layOf (K1.firstPar q gp)).shapes.toList)
    (hx : (M.drop (N.msgsAt p)).take (K1.shapesOf (K1.firstPar q gp)).length =
      K1.shapesOf (K1.firstPar q gp))
    (hdec : DecBlind decT)
    (hrest : ∀ x x', StepG Cl q gp nm X fvs kCol x x' → rest x = true → rest x' = true)
    (hconstr : ∀ x x' y y' w m c, StepG Cl q gp nm X fvs kCol x x' →
      (∀ q' ∈ Q, Mg.pub q' x = true) → First.bookAt N p x.2 = true → y'.cell = y.cell →
      Mg.constr m c x' y' w → Mg.constr m c x y w)
    (hmore : ∀ x x' i, StepG Cl q gp nm X fvs kCol x x' → (∀ q' ∈ Q, Mg.pub q' x = true) →
      First.bookAt N p x.2 = true → Mg.inOrder x = true → i ∈ mk → i ∉ madeSix →
      Mg.pub i x' = true ∧ Mg.pubP i x')
    (hR : ∀ i ∈ Q, i ≠ .noneSent → i ∉ knownG → RiderG Cl q gp nm X fvs kCol N Mg Q p i) :
    FillG Cl q gp nm X fvs kCol N Mg Q p mk :=
  fillG_of hMg.ours hG.noneSent hm
    (othersG_at Q p mk hMg hG hPl hm hdec hmore (inOrderG_rides hMg.ours hrest hplan) hrest
      hconstr)
    hplan hidx fun i hi hne => by
      by_cases hk : i ∈ knownG
      · simp only [knownG, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl
        · exact riderG_book hi (by rw [hft]; exact hMg.book)
            (hMg.quiet _ (by simp [knownK13]))
        · exact riderG_seats (L := toTree L) hi hMg.seats (hMg.quiet _ (by simp [knownK13])) hp hs
        · exact riderG_shapes hi hMg.shapes (hMg.quiet _ (by simp [knownK13])) hx
        · exact riderG_pileMasks hm hG.noneSent hMg.masks (hMg.quiet _ (by simp [knownK13]))
        · exact riderG_reply hi id hU hUP
      · exact hR i hi hne hk

end VerifiableInference.Desc.K13.Law
