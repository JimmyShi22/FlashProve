--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/Member.lean: FACTS ON THE KINDS' TEXTS THAT A MEMBER OF THE ROW OF THE EIGHT
WANTS, at the functional pin of Johnson/Desc/K14/Law/FunPin.lean (of every message sent so far the
witness's main words are a decoder's; the other vector is the decoder's).

  size_of_grows   a statement that grows loses no message.
  linPoint_oU_member  "LIN point" leaves what the small record notes of o_u and of o_omega.
  size_of_yes, grows_of_blocks   so at a yes of a piece of each of the eight blocks.
  oU_lt, oU_lt3   behind "send o_u" (H2), and behind "(rec_gamma)" (H3), the number that the record
                  notes for o_u is a number of a message sent.
  seated_of_front, noted_lt7   in front of "LIN zeta" (On7) so are o_omega's and o_u's.
  hdetU_fun, hdetO_fun   the row's two premises "the pin determines the words that are read", from
                  the pin's form and these: at any promise, at any decoder.

What is not claimed. D and DV, the decoder, are letters. That the pin goes back at a yes is not
here: Johnson/Desc/K14/Law/Fenced.lean. Nothing on BadKey, Dec, Tab, g, on the written rounds, or on
the sending kind's premises. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.FunPin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

/-- A statement that grows loses no message. -/
theorem size_of_grows {T T' : Statement} (g : Grows T T') : T.oracles.size ≤ T'.oracles.size := by
  by_contra h
  have hlt : T'.oracles.size < T.oracles.size := Nat.lt_of_not_le h
  obtain ⟨x', hx', _⟩ := g.2.2 T'.oracles.size (T.oracles[T'.oracles.size]'hlt)
    (Array.getElem?_eq_getElem hlt)
  exact Nat.lt_irrefl _ (Array.getElem?_eq_some_iff.1 hx').1

/-- "LIN point" leaves what the small record notes of o_u and of o_omega. -/
theorem linPoint_oU_member (p : Par) (d d' : St) (rs : List Fmt.RoundView)
    (h : linPoint p d rs = some d') :
    d'.loc.oU = d.loc.oU ∧ d'.loc.oOmega = d.loc.oOmega := by
  unfold linPoint at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨u0, _, ⟨gU, d1⟩, h1, h2⟩ := h
    obtain ⟨l1, _, _⟩ := newGroupP_same d d1 _ _ gU h1
    split at h2
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      obtain ⟨l2, _, _⟩ := newGroupP_same d1 d2 _ _ gO h3
      exact ⟨by show d2.loc.oU = _; rw [l2, l1], by show d2.loc.oOmega = _; rw [l2, l1]⟩
    · simp only [Option.bind_eq_some_iff, Option.some.injEq] at h2
      obtain ⟨⟨gO, d2⟩, h3, rfl⟩ := h2
      simp only [Prod.mk.injEq] at h3
      obtain ⟨_, rfl⟩ := h3
      exact ⟨by show d1.loc.oU = _; rw [l1], by show d1.loc.oOmega = _; rw [l1]⟩
  · cases h

/-- Behind "send o_u" the number noted for o_u is a number of a message sent. -/
theorem oU_lt {p : Par} {d0 d2 : St} (h : H2 p d0 d2) :
    d2.loc.oU.oracle < d2.st.oracles.size := by
  obtain ⟨_, d1, a1, a2, rs1, ftU, sentU, idsU, _, hU, rU, cU, _, h2⟩ := h
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv p a2 d2 idsU h2
  obtain ⟨nU, sU0, _⟩ := withU_first p.S sentU hU
  obtain ⟨_, x, hx, _⟩ := recvP_first ftU d1 a1 sentU idsU rU nU sU0 o ho
  have h1 : o < a1.st.oracles.size := (Array.getElem?_eq_some_iff.1 hx).1
  rw [l2, s2]
  exact Nat.lt_of_lt_of_le h1 (size_of_grows cU.grows)

/-- So behind "(rec_gamma)". -/
theorem oU_lt3 {p : Par} {d0 d2 d3 : St} (h : H3 p d0 d2 d3) :
    d3.loc.oU.oracle < d3.st.oracles.size := by
  obtain ⟨h2, rs3, h3⟩ := h
  obtain ⟨o3, l3⟩ := onward_laysRec p d2 d3 rs3 h3
  rw [l3]
  exact Nat.lt_of_lt_of_le (oU_lt h2) (size_of_grows o3.grows)

/-- In front of "LIN zeta" the two messages are seated. -/
theorem seated_of_front {p : Par} {d0 d2 d3 d6 : St} {r4 : Fmt.RoundView}
    {cols : List (Nat × List UInt64)} (h : SharedFront p d0 d2 d3 d6 r4 cols) :
    ∃ codes, Seated d6.st codes p.S d6.loc := by
  obtain ⟨hS, d1, a1, a2, d4, b1, b2, d5, rs1, rs3, rs6, ftU, ftO, sentU, idsU, idsO,
    h1, hU, rU, cU, cUl, h2, h3, h4, rO, cO, cOl, h5, h6⟩ := h
  obtain ⟨oU1, lU1⟩ := onward_recvP ftU d1 a1 sentU idsU rU
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv p a2 d2 idsU h2
  obtain ⟨o3, l3⟩ := onward_laysRec p d2 d3 rs3 h3
  obtain ⟨o4, l4⟩ := onward_loc p d3 d4 r4 cols h4
  obtain ⟨oO1, lO1⟩ := onward_recvP ftO d4 b1 (withOmega p.S) idsO rO
  obtain ⟨s5, oo, sp, hoo, l5⟩ := behindOmega_inv p b2 d5 idsO h5
  obtain ⟨o6, l6⟩ := onward_joins p d5 d6 rs6 h6
  have A : Onward a1 d4 := ((cU.trans (Onward.of_st s2)).trans o3).trans o4
  have B : Onward b1 d6 := (cO.trans (Onward.of_st s5)).trans o6
  have l : d6.loc = { d2.loc with oOmega := oo, oSp := sp } := by
    rw [l6, l5, cOl, lO1, l4, l3]
  have hoU : d6.loc.oU = d2.loc.oU := by rw [l]
  have hcA : a2.st.codes = d1.st.codes := (oU1.trans cU).grows.1
  obtain ⟨nU, sU0, shU⟩ := withU_first p.S sentU hU
  obtain ⟨nO, sO0, shO⟩ := withOmega_first p.S
  exact ⟨d1.st.codes, seated_behind d1.st.codes p.S d6.loc d6.st d1 a1 d4 b1 ftU ftO sentU
    (withOmega p.S) idsU idsO nU nO rfl rU sU0 shU (by rw [hoU, l2]; exact ho) A.grows rO sO0 shO
    (by rw [l]; exact hoo) B.grows (by rw [hoU, l2, ← hcA])⟩

variable {W : Type} {F : Frame}

/-- So the two numbers noted are numbers of messages sent. -/
theorem noted_lt7 {p : Par} {x : St × F.E.Str} (h : On7 p x) :
    x.1.loc.oOmega < x.1.st.oracles.size ∧ x.1.loc.oU.oracle < x.1.st.oracles.size := by
  obtain ⟨d0, d2, d3, r4, cols, hF⟩ := h
  obtain ⟨codes, hs⟩ := seated_of_front hF
  obtain ⟨a, ha, _⟩ := hs.omega
  obtain ⟨b, hb, _⟩ := hs.u
  exact ⟨(Array.getElem?_eq_some_iff.1 ha).1, (Array.getElem?_eq_some_iff.1 hb).1⟩

variable (rg : W → Words GE) (wv : W → Nat → GE) (D : St × F.E.Str → Words GE)
  (DV : St × F.E.Str → Nat → GE)

/-- **The pin determines o_u's words in front of "LOC"**: row3to8's hdetU, at any promise. -/
theorem hdetU_fun (p : Par) (Prm : St × F.E.Str → Prop) :
    ∀ (x : St × F.E.Str) w w', (∃ d0 d2, H3 p d0 d2 x.1) → Prm x → PinF rg wv D DV x w →
      PinF rg wv D DV x w' → AgreeOn x.1.loc.oU.oracle (rg w) (rg w') := by
  rintro x w w' ⟨d0, d2, h3⟩ _ h h'
  exact agree_of_two (h.1 _ (oU_lt3 h3)) (h'.1 _ (oU_lt3 h3))

/-- **The pin determines o_omega's and o_u's words in front of "LIN zeta"**: row3to8's hdetO, at any
promise. -/
theorem hdetO_fun (p : Par) (Prm : St × F.E.Str → Prop) :
    ∀ (x : St × F.E.Str) w w', On7 p x → Prm x → PinF rg wv D DV x w → PinF rg wv D DV x w' →
      AgreeOn x.1.loc.oOmega (rg w) (rg w') ∧ AgreeOn x.1.loc.oU.oracle (rg w) (rg w') := by
  intro x w w' h7 _ h h'
  obtain ⟨hO, hU⟩ := noted_lt7 h7
  exact ⟨agree_of_two (h.1 _ hO) (h'.1 _ hO), agree_of_two (h.1 _ hU) (h'.1 _ hU)⟩

/-- **No message is lost at a yes of a piece whose block's decision makes the statement grow.** -/
theorem size_of_yes {C : CK} (pc : Piece C F St Unit W)
    (hg : ∀ d rs gs d', pc.b.decide d rs gs = .ok d' → Grows d.st d'.st) :
    ∀ a τ b, pc.ior.red.out a τ = some b → a.1.st.oracles.size ≤ b.1.st.oracles.size := by
  intro a τ b hout
  obtain ⟨_, gs, hd⟩ := piece_yes pc a τ b hout
  exact size_of_grows (hg _ _ gs _ hd)

/-- **At each of the eight blocks a yes makes the statement grow**; two codes. -/
theorem grows_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hS : P.S.sharedSplitNeeded = true) :
    ∀ b ∈ [b1, b2, b3, b4, b5, b6, b7, b8], ∀ d rs gs d', b.decide d rs gs = .ok d' →
      Grows d.st d'.st := by
  obtain ⟨⟨sentU, _, hs2⟩, hs5⟩ := send_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  have hq := quiet_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hbl
  intro b hb d rs gs d' h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact linPoint_grows P.par d d' rs (point_of_blocks P _ b2 b3 b4 b5 b6 b7 b8 hbl d rs gs d' h)
  · obtain ⟨ft, ids, a1, a2, r, c, _, k⟩ := hs2 d rs gs d' h
    have e := (behindU_inv P.par a2 d' ids k).1
    rw [e]
    exact ((onward_recvP ft d a1 _ ids r).1.trans c).grows
  · exact (onward_laysRec P.par d d' rs (hq.1 d rs gs d' h)).1.grows
  · have k := loc_of_blocks P b1 b2 b3 _ b5 b6 b7 b8 hbl d rs gs d' h
    obtain ⟨r4, cols, hr, hg⟩ := loc_one _ _ _ _ _ k
    rw [hr, hg] at k
    exact (onward_loc P.par d d' r4 cols k).1.grows
  · obtain ⟨ft, ids, a1, a2, r, c, _, k⟩ := hs5 d rs gs d' h
    have e := (behindOmega_inv P.par a2 d' ids k).1
    rw [e]
    exact ((onward_recvP ft d a1 _ ids r).1.trans c).grows
  · exact (onward_joins P.par d d' rs (hq.2 d rs gs d' h)).1.grows
  · have k := zeta_of_blocks P b1 b2 b3 b4 b5 b6 _ b8 hbl d rs gs d' h
    obtain ⟨r7, hr⟩ := linZeta_one _ _ _ k
    rw [hr] at k
    rw [linZeta_inv d d' r7 k]
    exact Grows.refl _
  · have k := decidesBySplit_of_blocks P b1 b2 b3 b4 b5 b6 b7 _ hbl d rs gs d' h
    obtain ⟨r8, hr⟩ := split_one _ _ _ _ hS k
    rw [hr] at k
    exact (onward_split P.par d d' r8 hS k).1.grows

end Desc.K14.Law
