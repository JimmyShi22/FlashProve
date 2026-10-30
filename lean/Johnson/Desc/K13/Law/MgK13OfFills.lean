-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/MgK13OfFills.lean: THE LIGHT STRUCTURE OF KIND K13's PREMISES ON THE LETTERS
(`FillsK13`, Johnson/Desc/K13/Law/FillsK13.lean) GIVES THE ONE THAT THE LAWS SPEND (`MgK13`,
Johnson/Desc/K13/Law/MgK13.lean): each test as code is the test of which the laws speak
(Johnson/Desc/K13/Law/FillK13Laws.lean). One statement with its proof.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillsK13
import Johnson.Desc.K13.Law.MgK13

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker
open Johnson.Pack (sigOf)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)
open VerifiableInference.Desc.Sound (MsgT Sending Mem)

theorem mgK13_of_fills {Pp Xi Cells Tok : Type} {nR : ℕ} {P : Where} {N : Numbers}
    {Mg : Meaning Pp (Desc.Wit Cells Tok MsgT)} {cs : Codes} {sh : Params.ReqShape}
    {ly : Params.ReqLayout} {rest : Pp × S → Bool} {arr : ℕ → ℕ → ℕ}
    {mat : Cells → Fin nR → (Fin P.lin.kCol → Bool) → GE} {G : FileDescription Xi}
    {smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp}
    {ms : List Mem} {decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells}
    {M : List OracleShape} {L : K12.Door.Laid}
    (h : FillsK13 P N Mg cs sh ly rest arr mat G smp ms decT M L) :
    MgK13 P N Mg cs sh ly rest arr mat G smp ms decT M L where
  ours :=
    { pile := h.pile
      pileOne := h.pileOne
      frontOk := fun x => by rw [h.frontOk, frontOkC_eq]
      evalLaid := fun x => by rw [h.evalLaid, evalLaidC_eq]
      wSits := fun x => by rw [h.wSits, wSitsC_eq, wSeatC_eq]
      indexIs := fun x => by rw [h.indexIs, indexIsC_eq]
      indexThere := fun x => by rw [h.indexThere, indexThereC_eq]
      inOrder := h.inOrder
      pubP := fun q hq => h.quiet q (by
        rcases hq with rfl | rfl | rfl <;> simp [quietK13]) }
  sig :=
    { held := h.held
      shown := h.shown
      noColl := h.noColl
      pin := h.pin
      pinW := h.pinW
      decodes := h.decodes }
  book := h.book
  seats := h.seats
  shapes := h.shapes
  masks := h.masks
  quiet := fun q hq => h.quiet q (by
    simp only [knownK13, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl <;> simp [quietK13, bookItem, seatsItem, shapesItem])

end VerifiableInference.Desc.K13.Law
