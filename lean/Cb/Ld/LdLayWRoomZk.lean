-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayWRoomZk.lean: room of the two lookups' links from the clause on zero knowledge
(`A.ZkAt`); room of the two chains of Cb/Ld/LdLayWPend.lean; the window event's probability as a
count. (not all hypotheses are named here: see `Spec.ldLayW_roomD`, `Spec.ldLayW_upTo_room`,
`Spec.ldLayW_upToLast_room`)

Statements (in `Cb.Spec`) and proofs: applications. For all data: no toy occurs here. Room:
`Link.RoomAt`, Cb/Ld/LdLayWGive.lean; `A.RoomD`, `S.RoomD`, `L.RoomD`: Cb/Ld/LdLayWRoom.lean.
`A.RoomD k` asks, of a body A: the front's lookup's link; the range check's draw; the digits'
lookup's link: each has room at k. `S.RoomD k` asks, of a closed segment S: `S.A.RoomD k`, and: the
two probabilities of the closing's link from bridge to fold add up to less than 1. `L.RoomD k` asks
`S.RoomD k` of every segment S of the list L.

Main names:
  `Spec.ldLayW_roomD`: E of characteristic pp, `A.OK pp`, `A.ZkAt pp X` (`LdRefD.ZkAt`,
    Cb/Req1/LdReqRefZkP.lean: the clause that `lay`, `layT` (fields of `LdReqRefD`,
    Cb/Req1/LdReqRefFinal.lean) ask of a body), the draw has room at k ⇒ `A.RoomD k`: both lookups
    are masked blocks, and a masked block withholds nothing.
  `Spec.ldLayW_upTo_room`: under E of characteristic pp, `first.Hyp`, `S.OK pp`, `S.A.RoomD k`: the
    chain up to the digits' lookup of a first segment, as one link, has room at k.
  `Spec.ldLayW_upToLast_room`: under `(ldReqRef1 R first b L T).Hyp`, `T.tail.Hyp`, `L.RoomD k`,
    `T.A.RoomD k`: the chain up to the last three moves of the request, as one link, has room at k.
  `GPack.link_room` (its statement: `roomQ k`, Cb/Ld/LdLayWRoom.lean: `l.GoodB → l.RoomAt k`): a
    group's own link from bridge to fold has room, if it has `Link.GoodB` (all of the bundle but
    zero knowledge: Ior/KnowCollRulesChain.lean): its two probabilities (`pBad`, `pHid`) are 0.
  `Spec.ldLayW_ev_cnt`: an event that reads the verifier's message `p.Chal` (the ternary matrix,
    two bits for each coefficient) alone has the probability (number of values of `p.Chal` in it) /
    (number of values of `p.Chal`).

Limits: this file does not say that a draw has room (for `LdRrD.draw`: `Spec.ldLayW_draw_room`,
Cb/Ld/LdLayWRef.lean: if some ternary matrix is outside the window event). It says nothing on a
closing's link that is not the group's own.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayWPend
import Cb.Ld.LdRngProofs
import Cb.Ld.LdGroupPack

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

namespace Spec

def ldLayW_roomD : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (A : LdRefD E Kc I)
      (X : MaskFact A.V.Fp.s0.J.W → Prop) (k : Kc),
    A.OK pp → A.ZkAt pp X → A.Xa.Q.D.draw.RoomAt k → A.RoomD k

def ldLayW_upTo_room : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (pp : ℕ) [CharP E pp] (I : LdRefIx E) (a : LdStage E Kc)
      (first : LdSendD a) (S : LdRefS E Kc I first.tgt) (d : a.J.W) (k : Kc),
    first.Hyp → S.OK pp → S.A.RoomD k → ((S.upTo (.one first.link)).link d).RoomAt k

def ldLayW_upToLast_room : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b)
      (T : LdRefT R b) (d : a.J.W) (k : Kc),
    (ldReqRef1 R first b L T).Hyp → T.tail.Hyp → L.RoomD k → T.A.RoomD k →
    ((ldReqUpToLast R first b L T).link d).RoomAt k

def ldLayW_ev_cnt : Prop :=
  ∀ (p : RngPar) (P : p.Chal → Prop),
    prRho (s := [IOR.drawRound p.Chal]) {ρ | P (show p.Chal × Unit from ρ).1} =
      (cnt P : ℝ≥0∞) / Fintype.card p.Chal

end Spec

theorem ldLayW_roomD : Spec.ldLayW_roomD := by
  intro E Kc _ _ pp _ I A X k h hZ hd
  obtain ⟨hne, W, F, κ, RdL, hG, hFo, hFF, hL⟩ := hZ
  haveI := hne
  exact ⟨ldLayW_room_free Kc _ _ _ k
      (ldSegRef_preZk_goodM E pp Kc _ _ _ A.V.Fp F.Dt F.RdK F.Cc hFo.lk).mm.free,
    hd,
    ldLayW_room_free Kc _ _ _ k
      (ldSegRef_asm_goodM E Kc _ _ pp A.Xa RdL h.inj h.named h.adm hL.maskL hL.rdL).mm.free⟩

theorem send_room {E Kc : Type} [Field E] [Fintype E] {a : LdStage E Kc}
    (first : LdSendD a) (k : Kc) : roomQ k _ _ first.link :=
  link_room_nums k first.link (by rw [((ldSeg_rounds E Kc).1 _ first).2.2.1, ((ldSeg_rounds E Kc).1 _ first).2.2.2, add_zero]; exact zero_lt_one)

theorem ldLayW_upTo_room : Spec.ldLayW_upTo_room := by
  intro E Kc _ _ pp _ I a first S d k hF hS hr
  have hB := S.upTo_allB (ldReqRef_seg E Kc pp I _ S hS) _
    ((allB_one _).2 (goodB_of_goodT' (first.goodT hF)))
  refine ldLayW_room Kc _ _ _ d k hB (each_room_mp k _ hB ?_)
  unfold LdRefS.upTo
  rw [ldLayW_onto, ldLayW_onto, ldLayW_onto, ldLayW_append, each_one]
  have hq := S.A.Xa.Q.room S.A.Xa.mult S.A.Xa.ent S.A.Xa.A.nRows S.A.Xa.lk k (S.A.room_lk k hr)
  unfold LdDgP.prog at hq
  rw [LdProg.each_snoc] at hq
  exact ⟨⟨⟨⟨send_room first k, LdMv.room_step k _ rfl⟩, S.A.room_front k hr⟩,
      S.A.Xa.Q.D.room k hr.draw⟩,
    hq.1⟩

theorem ldLayW_upToLast_room : Spec.ldLayW_upToLast_room := by
  intro F E Kc _ _ _ _ _ R a first b L T d k hH hT hL hr
  have hB : (ldReqUpToLast R first b L T).AllB :=
    LdProg.onto_allB _ _
      (LdSegs.onto_allB _ _ ((allB_one _).2 (goodB_of_goodT' (first.goodT hH.first))) hH.segs) hT
  refine ldLayW_room Kc _ _ _ d k hB (each_room_mp k _ hB ?_)
  unfold ldReqUpToLast
  rw [ldLayW_onto, ldLayW_segs, each_one]
  exact ⟨⟨send_room first k, L.room k hL⟩, T.room k hr⟩

/-- A group's own link from bridge to fold has room, if it has `Link.GoodB`: its two probabilities
are 0. -/
theorem GPack.link_room {E B Kc : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E}
    {mem kp : S.O → Prop} [DecidablePred kp] {clP : {o // kp o} → Prop} {Pn : Type} [Fintype Pn]
    {d e t : ℕ} {Lst mC mS mW : ℕ → ℕ} {L L₂ t₂ : ℕ}
    (pk : GPack S mem kp clP Pn d e t Lst mC mS mW L L₂ t₂) (Sb : B → Type)
    (sl : ∀ b, Slf E (Sb b) pk.G.C.J) (Z : Evader E (pk.G.Row B)) {St₀ Wp : Type} {E₀ : ExtSpec}
    (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp)) (dw : S.Wit × Wp) (k : Kc) :
    roomQ k _ _ (pk.link Sb sl Z A₀ dw) := by
  refine link_room_nums k _ ?_
  show ((0 : ℝ≥0∞) + (0 + (0 + 0))) + ((0 : ℝ≥0∞) + (0 + (0 + 0))) < 1
  simp

theorem ldLayW_ev_cnt : Spec.ldLayW_ev_cnt := fun p P =>
  (prRho_draw (IOR.drawRound p.Chal) P).trans (pr_unif_eq P)

end Cb
