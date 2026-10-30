-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/OnFront.lean: the promise at the borders of "(rec_gamma)" and "LOC" (On4: the
stored table's shape meets its conditions, and o_u has its table at every statement that grows out
of the record's) BY MAKE: it holds behind the sending of o_u, and it stays.

  SeatedU, SeatedU.grows   the statement has the codes; o_u has the shape that the public shape
                  names; its layout is that of its shape.
  placedU_of_seatedU       so o_u has its table, which holds a row's message and its random tail.
  on4_behind      behind "LIN point", the receiving of o_u, a stretch that goes onward and the
                  kind's note, the promise holds.
  On4.onward      a step onward that leaves the small record keeps it.
  on4_of_blocks   where the shared chain's first two blocks' own decisions say yes one behind the
                  other, the promise holds of the record behind them, whatever the oracles are.
  rec_goodIn3'    "(rec_gamma)" in the form of the rule of composition with that promise at both
                  borders: so the promises chain from the sending of o_u to behind "LOC".

What is not claimed. Nothing on the sending itself as a block of the rule: that is its kind's. The
premises of rec_goodIn3 stay; «the pin goes back» is asked UNDER THE PROMISE IN FRONT OF THE BLOCK
ALONE, not of every statement. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.GoodQuiet
import Johnson.Desc.K14.Law.GoodLoc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words)
open VerifiableInference.Desc (Grows Block noDigest)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)

/-- The statement has the codes; o_u has the shape that the public shape names; its layout is that
of its shape. -/
structure SeatedU (T : Statement) (codes : Codes) (S : LinShape) (u : FoldedRow) : Prop where
  sameCodes : T.codes = codes
  shaped : ∃ x, T.oracles[u.oracle]? = some x ∧ x.shape = S.fold.u
  lay : u.lay = vectorLay codes S.fold.u S.fold.rowsHigh

/-- A statement that grows keeps it. -/
theorem SeatedU.grows {T T' : Statement} {codes : Codes} {S : LinShape} {u : FoldedRow}
    (h : SeatedU T codes S u) (g : Grows T T') : SeatedU T' codes S u := by
  obtain ⟨y, hy, sy⟩ := h.shaped
  obtain ⟨y', hy', gy⟩ := g.2.2 _ y hy
  exact ⟨g.1.trans h.sameCodes, ⟨y', hy', gy.1.trans sy⟩, h.lay⟩

/-- The message o_u has its table, which holds a row's message and its random tail. -/
theorem placedU_of_seatedU {T : Statement} {codes : Codes} {S : LinShape} {u : FoldedRow}
    (h : SeatedU T codes S u) (hok : linOk codes S = true) : PlacedU T S.fold u := by
  obtain ⟨y, hy, sy⟩ := h.shaped
  simp only [linOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  have hF : foldeqOk codes S.fold = true := by tauto
  simp only [foldeqOk, FoldeqShape.ok, Bool.and_eq_true, decide_eq_true_eq] at hF
  have c1 : 0 < S.fold.u.mainRows := by tauto
  have c2 : S.fold.entries ≤ vectorRoom codes S.fold.u S.fold.rowsHigh := by tauto
  have tU := tableBits_main T _ y hy (by rw [sy]; omega) S.fold.rowsHigh
  rw [sy, h.sameCodes] at tU
  have hE : S.fold.entries ≤ 2 ^ u.lay.bits := by
    rw [h.lay]; exact Nat.le_trans c2 (vectorRoom_le _ _ _)
  have e2 : S.fold.index.code.ell ≤ S.fold.tailFirst := le_roundUp _ _ (Nat.two_pow_pos _)
  unfold FoldeqShape.entries at hE
  refine ⟨tU.1, by rw [tU.2, h.lay], ceilLog2_le _ _ (by omega), hE, ?_⟩
  unfold FoldeqShape.tailFirst
  exact Nat.mul_mod_left _ _

variable {W : Type} {C : CK} {F : Frame}

/-- **Behind the sending of o_u the promise holds.** -/
theorem on4_behind (p : Par) (d0 d1 a1 a2 d2 : St) (rs1 : List Fmt.RoundView) (ftU : Nat)
    (sentU : Array OracleNotice) (idsU : Array Nat) (h1 : linPoint p d0 rs1 = some d1)
    (hU : withU p.S = some sentU) (rU : recvP ftU d1 sentU = some (idsU, a1))
    (cU : Onward a1 a2) (h2 : behindU p a2 idsU = some d2) (y : F.E.Str) :
    On4 p ((d2, y) : St × F.E.Str) := by
  have hok := linPoint_ok p d0 d1 rs1 h1
  have g01 := linPoint_grows p d0 d1 rs1 h1
  obtain ⟨oU1, _⟩ := onward_recvP ftU d1 a1 sentU idsU rU
  obtain ⟨s2, o, mask, ho, l2⟩ := behindU_inv p a2 d2 idsU h2
  obtain ⟨nU, sU0, shU⟩ := withU_first p.S sentU hU
  obtain ⟨_, x, hx, sx⟩ := recvP_first ftU d1 a1 sentU idsU rU nU sU0 o ho
  obtain ⟨x2, hx2, gx2⟩ := cU.grows.2.2 _ x hx
  have hc : a2.st.codes = d0.st.codes := ((g01.trans oU1.grows).trans cU.grows).1
  have hSeat : SeatedU d2.st d0.st.codes p.S d2.loc.oU := by
    refine ⟨by rw [s2]; exact hc, ?_, by rw [l2, ← hc]⟩
    rw [s2, l2]
    exact ⟨x2, hx2, (gx2.1.trans sx).trans shU⟩
  exact ⟨index_ok_of_linOk _ _ hok, fun T g => placedU_of_seatedU (hSeat.grows g) hok⟩

/-- A step onward that leaves the small record keeps the promise. -/
theorem On4.onward {p : Par} {a b : St × F.E.Str} (h : On4 p a) (o : Onward a.1 b.1)
    (l : b.1.loc = a.1.loc) : On4 p b :=
  ⟨h.1, fun T g => by rw [l]; exact h.2 T (o.grows.trans g)⟩

/-- **Where the first two blocks' own decisions say yes, the promise holds.** -/
theorem on4_of_blocks (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (d0 d1 d2 : St)
    (rs1 rs2 : List Fmt.RoundView) (gs1 gs2 : List (List (Nat × List UInt64)))
    (h1 : b1.decide d0 rs1 gs1 = .ok d1) (h2 : b2.decide d1 rs2 gs2 = .ok d2) (y : F.E.Str) :
    On4 P.par ((d2, y) : St × F.E.Str) := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have k1 : linPoint P.par d0 rs1 = some d1 := why_some h1
  obtain ⟨idsU, a1, a2, rU, cU, _, k2⟩ := sendAt_inv _ _ _ _ _ _ d1 d2 rs2 gs2 h2
  rw [parK1_sent] at rU
  exact on4_behind P.par d0 d1 a1 a2 d2 rs1 _ sentU idsU k1 hU rU cU k2 y

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)
variable (rw : W → Words K) (Pin : St × F.E.Str → W → Prop)

/-- **"(rec_gamma)" in the form of the rule of composition**, with the promise at both borders. -/
theorem rec_goodIn3' (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (pc : Piece C F St Unit W)
    (hpc : pc.b = b3) (hext : ∀ a τ w, pc.ext a τ w = w) (Prm : St × F.E.Str → Prop)
    (hback : ∀ a τ b w, On4 P.par a → Prm a → pc.ior.red.out a τ = some b → Pin b w → Pin a w)
    (Q : St × F.E.Str → Words K → Prop)
    (hQ : ∀ (a : St × F.E.Str) τ (b : St × F.E.Str) m, b.2 = pc.ior.imp a.2 τ → Onward a.1 b.1 →
      b.1.loc = a.1.loc → Q b m → Q a m) :
    pc.GoodIn (fun a => On4 P.par a ∧ Prm a) (On4 P.par)
      (fun a w => Base ρ rw Pin a w ∧ Q a (rw w)) (fun a w => Base ρ rw Pin a w ∧ Q a (rw w)) :=
  rec_goodIn3 ρ rw Pin P b1 b2 b3 b4 b5 b6 b7 b8 hbl pc hpc hext _ _
    (fun a τ b w ha => hback a τ b w ha.1 ha.2)
    (fun a b rs ha h => ha.1.onward (onward_laysRec P.par a.1 b.1 rs h).1
      (onward_laysRec P.par a.1 b.1 rs h).2) Q hQ

end Desc.K14.Law
