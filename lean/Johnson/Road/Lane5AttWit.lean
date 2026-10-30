-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttWit.lean

Values and guards for the records of the attention link's files.

By theorem:
* "sized_met": a record meets AttSized (Johnson/Road/Lane5AttAddr.lean). The record is typed here.
  It is not what the verifier's function shape returns: its table of exponentials is empty.
* "sizeOK_small": the library's condition SizeOK (Inst/Model/Att/Scales.lean) holds at the sizes
  ⟨1, 1, 4, 7, 2, 4, 2307⟩ and the shift 12.

By a run at every build (#guard; no theorem): at two configurations that are typed here, with the
numbers of the full-size and of the small example of OnBytes/Model/TestAttentionShape.lean but
Ty = 2^18, the verifier's function shape ends well, and
* full: every number of AttSized is as AttSized says; the group has one shift; the table of
  exponentials holds the library's refExp at all 2,307 rows (the hypothesis hE of
  Johnson/Road/Lane5AttLink.lean; also a theorem: Johnson/Road/Lane5AttExp.lean);
* small: dimOf is ⟨1, 1, 4, 7, 2, 4, 2307⟩; one shift, 12; ldh = 7.

Not claimed: that these configurations are those of a parameter file.
-/
import Johnson.Road.Lane5AttShape
import Johnson.Road.Lane5AttCongr
import Inst.Model.Att.Scales
import Inst.Model.TablesRef

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Attention (Cfg Shape Line shape)

/-- A record with the reference numbers. -/
def shapeRef : Shape :=
  { cf := { lt := 10, lB := 6, lgk := 3, ldh := 7, ll := 2, H := 40, lmS := 16, wcH := 8, wcO := 64,
            wcQ := 64 },
    T := 1024, lnT := 4, HA := 5, Lam := 4, dh := 128, dq := 5120, nM := 22, nD := 19, oMr := 0,
    oZr := 640, oIb := 1280, oRh := 0, oRhp := 20480, atQ := ⟨0, 2, 4, 5120⟩,
    atK := ⟨40960, 2, 4, 1024⟩, atV := ⟨49152, 2, 4, 1024⟩, atO := ⟨57344, 2, 4, 5120⟩, u0 := 2307 }

/-- **AttSized has a value.** -/
theorem sized_met : AttSized shapeRef :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The library's condition on the sizes, at the sizes of the small example and the shift 12. -/
theorem sizeOK_small :
    Inst.Model.AttSeg.SizeOK (scl := sclSh 12) ⟨1, 1, 4, 7, 2, 4, 2307⟩ :=
  @Inst.Model.AttSeg.SizeOK.mk (sclSh 12) ⟨1, 1, 4, 7, 2, 4, 2307⟩ (by decide) (by decide)
    (by decide) (by decide +kernel)

/-! ## Guards -/

/-- The call list of both examples. -/
def lines0 : List Line :=
  [⟨"KR", .kr, [.rm, .rd]⟩, ⟨"KFD", .kfd, [.fm, .fd]⟩, ⟨"R16", .r16, [.wl, .ix]⟩,
    ⟨"WH", .wh, [.wh]⟩]

/-- The numbers of the full-size example. -/
def cfFull : Cfg :=
  { lt := 10, lB := 6, lgk := 3, ldh := 7, ll := 2, S := 12, rx := 8, kFD := 16, lmS := 16,
    la := 16, lmb := 14, nmin := 20, H := 40, sh := #[8, 8, 8, 8], wcH := 8, wcO := 64, wcQ := 64,
    NAs := 1, Ty := 2 ^ 18, lines := lines0 }

/-- The numbers of the small example. -/
def cfSmall : Cfg :=
  { lt := 6, lB := 4, lgk := 1, ldh := 7, ll := 2, S := 12, rx := 8, kFD := 16, lmS := 11, la := 8,
    lmb := 13, nmin := 20, H := 4, sh := #[12, 12, 12, 12], wcH := 64, wcO := 128, wcQ := 128,
    NAs := 1, Ty := 2 ^ 18, lines := lines0 }

/-- The numbers of a shape that AttSized names, in its order. -/
def numbers (S : Shape) : List ℕ :=
  [S.cf.lgk, S.lnT, S.cf.lB, S.cf.ldh, S.HA, S.Lam, S.cf.lt, S.cf.H, S.T, S.dh, S.dq, S.nM, S.nD,
    S.cf.lmS, S.cf.wcH, S.cf.wcO, S.cf.wcQ, S.oMr, S.oZr, S.oIb, S.oRh, S.oRhp, S.u0]

/-- The sizes as a list. -/
def dimList (D : Inst.Model.AttSeg.Dim) : List ℕ := [D.lg, D.lP, D.lB, D.ln, D.na, D.nl, D.u0]

/-- One shift, as a test. -/
def oneShiftB (S : Shape) : Bool :=
  (List.range S.Lam).all fun l => S.cf.sh.getD l 0 == S.cf.sh.getD 0 0

#guard (shape cfFull).toOption.map numbers ==
  some [3, 4, 6, 7, 5, 4, 10, 40, 1024, 128, 5120, 22, 19, 16, 8, 64, 64, 0, 640, 1280, 0, 20480,
    2307]
#guard (shape cfFull).toOption.map (fun S => (S.atQ, S.atK, S.atV, S.atO)) ==
  some (⟨0, 2, 4, 5120⟩, ⟨40960, 2, 4, 1024⟩, ⟨49152, 2, 4, 1024⟩, ⟨57344, 2, 4, 5120⟩)
#guard (shape cfFull).toOption.map (fun S => (S.kAs, oneShiftB S, S.cf.sh.getD 0 0)) ==
  some (7200, true, 8)
#guard (shape cfFull).toOption.map (fun S => dimList (dimOf S)) == some [3, 3, 6, 7, 5, 4, 2307]
-- the hypothesis hE at the full-size example: all 2,307 rows
#guard (shape cfFull).toOption.map (fun S =>
    (List.range S.u0).all fun ι => ((S.Tt.getD ι 0 : ℕ) : ℤ) == Inst.Model.tbRef.Exp ι) == some true
#guard (shape cfSmall).toOption.map (fun S => dimList (dimOf S)) == some [1, 1, 4, 7, 2, 4, 2307]
#guard (shape cfSmall).toOption.map (fun S => (oneShiftB S, S.cf.sh.getD 0 0, S.cf.ldh)) ==
  some (true, 12, 7)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.sized_met
#print axioms OnBytes.Road.L5.sizeOK_small
