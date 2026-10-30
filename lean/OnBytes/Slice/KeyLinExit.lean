-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/KeyLinExit.lean: the test for a linear claim on a stored table ends in three proximity
tests.

The test (OnBytes/Slice/KeyLinVec.lean) leaves rows on three vectors, which are parts of sent
messages. Five sent messages take part: the index masks, W, the folded row, Omega, and the holder of
the element that splits the fold's row. Three groups close the rows
(OnBytes/Slice/KeyGroup.lean):
 the folded row and the holder: the drawn columns' rows and one half of the fold's row;
 Omega and the holder: the other half;
 the index masks, W and Omega: the evaluation's row and the dot product's row.
Omega and the holder are members of two groups each. They have one format, one radius and so one
decoding, whichever group reads them.

The result (KClose.three_exits). Let all five messages decode. If one of the rows that the test
leaves is false of the vectors read off the decodings, then at one of the three groups no message on
the first stage's tables is near the group's word and meets all the group's rows. What is asked of
the groups' rows: they contain the rows of OnBytes/Slice/KeyLinRows.lean, as far as the members'
entries go (Gp.Has). They may contain any further rows, such as sample rows.

Main definitions: Gp.Has, KClose, KClose.GU, GO, GW, KClose.Fx, KClose.Rows.

Main theorems: Gp.val_of_has, KClose.left_of_rows, KClose.three_exits.

Not claimed. What the three files named above do not claim. The case in which a message does not
decode is Gp.exit_of_undecodable at a group that has the message.

-/
import OnBytes.Slice.KeyLinRows

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run

namespace Gp
variable {s : Sg} (G : Gp s)

/-- The rows contain the vector v with the target τ, as far as the members' entries go. -/
def Has {n : ℕ} (tg : Fin n → GE) (vs : Fin n → s.cIn.J → GE) (v : s.cIn.J → GE) (τ : GE) : Prop :=
  ∃ b, tg b = τ ∧ ∀ k, vs b (G.ent k) = v (G.ent k)

variable {G}

/-- If all rows hold, a vector that they contain has its target as its value. -/
theorem val_of_has {n : ℕ} {tg : Fin n → GE} {vs : Fin n → s.cIn.J → GE} {v : s.cIn.J → GE}
    {τ : GE} (h : G.Has tg vs v τ) {m : G.Msgs} (hr : G.RowsHold m tg vs) : G.val m v = τ := by
  obtain ⟨b, hb, hv⟩ := h
  rw [← hb, ← hr b]
  exact Finset.sum_congr rfl fun k _ => by rw [hv k]

end Gp

/-- **How the test's rows are closed**: the formats of the five messages, the first stages of the
three proximity tests, the seven seats, and where the vectors stand in the messages. lW, lU, lO: the
entries of w', u', ω'. jK: the entry that splits the fold's row. φZ: the nF entries of the index
masks on which the claim has coefficients. -/
structure KClose (K : KLin) where
  MZ : Mb
  MW : Mb
  MU : Mb
  MO : Mb
  MK : Mb
  sU : Sg
  sO : Sg
  sW : Sg
  σU : Site sU MU
  σKU : Site sU MK
  σO : Site sO MO
  σKO : Site sO MK
  σZ : Site sW MZ
  σW : Site sW MW
  σOW : Site sW MO
  lW : K.D.Col → MW.cd.J
  lU : K.S.Co → MU.cd.J
  lO : Fin K.nY → MO.cd.J
  jK : MK.cd.J
  nF : ℕ
  φZ : Fin nF → MZ.cd.J

namespace KClose
variable {K : KLin} (C : KClose K)

/-- The group of the folded row and the holder. -/
abbrev GU : Gp C.sU := Gp.two C.MU C.MK C.σU C.σKU
/-- The group of Omega and the holder. -/
abbrev GO : Gp C.sO := Gp.two C.MO C.MK C.σO C.σKO
/-- The group of the index masks, W and Omega. -/
abbrev GW : Gp C.sW := Gp.three C.MZ C.MW C.MO C.σZ C.σW C.σOW

/-- One thing for each of the five messages: T M is a kind of thing that belongs to a format. -/
structure Five (T : Mb → Type) where
  z : T C.MZ
  w : T C.MW
  u : T C.MU
  o : T C.MO
  k : T C.MK

/-- the five messages -/
abbrev Fx : Type := C.Five fun M => M.cd.J → GE
/-- the five sent words -/
abbrev Ws : Type := C.Five fun M => M.cd.Word

variable {C}

/-- What the first group reads of five things. -/
def Five.gu {T : Mb → Type} (x : C.Five T) : ∀ i, T (C.GU.mb i) :=
  Duo.pick (T := fun i => T (C.GU.mb i)) x.u x.k
/-- What the second group reads of five things. -/
def Five.go {T : Mb → Type} (x : C.Five T) : ∀ i, T (C.GO.mb i) :=
  Duo.pick (T := fun i => T (C.GO.mb i)) x.o x.k
/-- What the third group reads of five things. -/
def Five.gw {T : Mb → Type} (x : C.Five T) : ∀ i, T (C.GW.mb i) :=
  Tri.pick (T := fun i => T (C.GW.mb i)) x.z x.w x.o

variable (C)

/-- **The three groups' rows contain the rows that the test leaves.** c: the claim. cZ: its
coefficients on the index masks. ψs, Q, ζ: the three drawn values. v: the share that the prover
names when the fold's row is split. -/
structure Rows (f : K.S.Pos → Run.PQ.SgX) (c : K.Cl) (cZ : Fin C.nF → GE) (ψs : K.D.Pt)
    (Q : Fin K.t → K.S.Pos) (ζ : Fin K.l → GE) (v : GE) {nU nO nW : ℕ}
    (tU : Fin nU → GE) (vU : Fin nU → C.sU.cIn.J → GE)
    (tO : Fin nO → GE) (vO : Fin nO → C.sO.cIn.J → GE)
    (tW : Fin nW → GE) (vW : Fin nW → C.sW.cIn.J → GE) : Prop where
  col : ∀ i, C.GU.Has tU vU (KLin.colV C.GU .a C.lU (Q i)) (foldAll ψs.1 (K.tab f) (Q i))
  halfU : C.GU.Has tU vU (KLin.uHalfV C.GU .a C.lU ζ ψs.2 .b C.jK) (0 - v)
  halfO : C.GO.Has tO vO (KLin.omHalfV C.GO .a C.lO ζ .b C.jK) v
  eval : C.GW.Has tW vW (KLin.evalV C.GW .b C.lW c.ψ .a C.φZ cZ) c.τ
  dot : C.GW.Has tW vW (KLin.dotV C.GW .c C.lO c.g .b C.lW ψs) 0

variable {C}

/-- **If all rows of the three groups hold of the five messages, the rows that the test leaves hold
of the vectors read off them.** -/
theorem left_of_rows (hU : C.GU.Apart) (hO : C.GO.Apart) (hW : C.GW.Apart) (x : C.Fx)
    {f : K.S.Pos → Run.PQ.SgX} {c : K.Cl} {cZ : Fin C.nF → GE}
    (hrest : c.rest = ∑ a, cZ a * x.z (C.φZ a)) {ψs : K.D.Pt} {Q : Fin K.t → K.S.Pos}
    {ζ : Fin K.l → GE} {v : GE} {nU nO nW : ℕ}
    {tU : Fin nU → GE} {vU : Fin nU → C.sU.cIn.J → GE}
    {tO : Fin nO → GE} {vO : Fin nO → C.sO.cIn.J → GE}
    {tW : Fin nW → GE} {vW : Fin nW → C.sW.cIn.J → GE}
    (hR : C.Rows f c cZ ψs Q ζ v tU vU tO vO tW vW)
    (h1 : C.GU.RowsHold x.gu tU vU) (h2 : C.GO.RowsHold x.go tO vO)
    (h3 : C.GW.RowsHold x.gw tW vW) :
    K.Left f c (fun a => x.w (C.lW a)) ψs (fun k => x.u (C.lU k)) Q (fun y => x.o (C.lO y)) ζ where
  col := (KLin.col_iff hU x.gu .a C.lU f ψs.1 Q).1 fun i => Gp.val_of_has (hR.col i) h1
  fold := KLin.fold_of_halves hO hU x.go x.gu .a C.lO .a C.lU ζ ψs.2 .b C.jK .b C.jK rfl v
    (Gp.val_of_has hR.halfO h2) (Gp.val_of_has hR.halfU h1)
  eval := by
    rw [hrest]
    exact (KLin.eval_iff hW x.gw .b C.lW c.ψ .a C.φZ cZ c.τ).1 (Gp.val_of_has hR.eval h3)
  dot := (KLin.dot_iff hW x.gw .c C.lO c.g .b C.lW ψs).1 (Gp.val_of_has hR.dot h3)

/-- **The three exits.** All five messages decode, and one of the rows that the test leaves is false
of the vectors read off the decodings. Then at one of the three groups no message on the first
stage's tables is near the group's word and meets all the group's rows. -/
theorem three_exits {eU dU eO dO eW dW : ℕ} (hU : C.GU.OK eU dU) (hO : C.GO.OK eO dO)
    (hW : C.GW.OK eW dW) (y : C.Ws) (x : C.Fx)
    (hz : C.MZ.fix y.z = some x.z) (hw : C.MW.fix y.w = some x.w) (hu : C.MU.fix y.u = some x.u)
    (ho : C.MO.fix y.o = some x.o) (hk : C.MK.fix y.k = some x.k)
    {fU : C.sU.cIn.Word} {fO : C.sO.cIn.Word} {fW : C.sW.cIn.Word}
    (tieU : C.GU.Tie y.gu fU) (tieO : C.GO.Tie y.go fO) (tieW : C.GW.Tie y.gw fW)
    {f : K.S.Pos → Run.PQ.SgX} {c : K.Cl} {cZ : Fin C.nF → GE}
    (hrest : c.rest = ∑ a, cZ a * x.z (C.φZ a)) {ψs : K.D.Pt} {Q : Fin K.t → K.S.Pos}
    {ζ : Fin K.l → GE} {v : GE} {nU nO nW : ℕ}
    {tU : Fin nU → GE} {vU : Fin nU → C.sU.cIn.J → GE}
    {tO : Fin nO → GE} {vO : Fin nO → C.sO.cIn.J → GE}
    {tW : Fin nW → GE} {vW : Fin nW → C.sW.cIn.J → GE}
    (hR : C.Rows f c cZ ψs Q ζ v tU vU tO vO tW vW)
    (hno : ¬ K.Left f c (fun a => x.w (C.lW a)) ψs (fun k => x.u (C.lU k)) Q
      (fun y => x.o (C.lO y)) ζ) :
    (∀ w, ¬ ConL C.sU.cIn.N eU (Slf.All fun _ : Fin nU => (Slf.idf (E := GE) (J := C.sU.cIn.J)))
        ((tU, vU), fU) w) ∨
      (∀ w, ¬ ConL C.sO.cIn.N eO (Slf.All fun _ : Fin nO => (Slf.idf (E := GE) (J := C.sO.cIn.J)))
        ((tO, vO), fO) w) ∨
      ∀ w, ¬ ConL C.sW.cIn.N eW (Slf.All fun _ : Fin nW => (Slf.idf (E := GE) (J := C.sW.cIn.J)))
        ((tW, vW), fW) w := by
  by_cases h1 : C.GU.RowsHold x.gu tU vU
  · by_cases h2 : C.GO.RowsHold x.go tO vO
    · refine Or.inr (Or.inr (Gp.exit_of_false_row hW tieW tW vW x.gw ?_ fun h3 =>
        hno (left_of_rows hU.apart hO.apart hW.apart x hrest hR h1 h2 h3)))
      intro i
      cases i
      · exact hz
      · exact hw
      · exact ho
    · refine Or.inr (Or.inl (Gp.exit_of_false_row hO tieO tO vO x.go ?_ h2))
      intro i
      cases i
      · exact ho
      · exact hk
  · refine Or.inl (Gp.exit_of_false_row hU tieU tU vU x.gu ?_ h1)
    intro i
    cases i
    · exact hu
    · exact hk

end KClose

end OnBytes.Slice
