-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionClaimsB.lean: tests of OnBytes/Model/AttentionClaimsB.lean.

The tests run when this file is compiled. The program does not import this file.

What is tested: the key forms of the calls of kinds R16 and WH. They are made on a small record with
made-up slots, weights and points. For REM, the terms of wl and ix and the key form of WH, the
constant and the coefficient of each slot that the formula names are compared with the numbers that
the formulas of claim 5 in AttentionSubProof::run of verifier/src/vf_attention_check.h give, worked
out by hand. For the key forms that joinR16 sets, one coefficient of each term is compared, and how
often each call is set.

What is not tested: that no other slot occurs in a form; the claims themselves, which need a whole
sub-proof.
-/
import OnBytes.Model.AttentionClaimsB

namespace OnBytes.Attention.TestClaimsB

open OnBytes.Model

/-- The coefficient of slot j in a form: the sum over the places where the slot occurs. -/
def coefOf (f : Aff) (j : Nat) : E :=
  f.slots.foldl (fun s x => if x.1 == j then addE s x.2 else s) zeroE

/-- A record with made-up values. The five values ACC, ZO, ZC, RH, RHP have the slots 10 to 14, the
two bits of the index 15 and 16, RH2 and RHP2 19 and 20. The weights of wl's pieces add up to 3,
those of ix's to 4 and those of wh's to 6. zsl is 5, and the token of ix is the point (2, 7). -/
def sampleDivide : Divide where
  pwW := #[{ lam := 0, a := 0, wp := ofNat 1 }, { lam := 0, a := 1, wp := ofNat 2 }]
  pwX := #[{ lam := 0, a := 0, wp := ofNat 4 }]
  pwH := #[{ lam := 0, a := 0, wp := ofNat 6 }]
  qWH := 1
  zsl := ofNat 5
  zgW := #[]
  ziW := #[]
  zcW := #[]
  zgX := #[]
  ziX := #[ofNat 2, ofNat 7]
  zgH := #[]
  ziH := #[]
  zcH := #[]
  s5 := 10
  sIB := 15
  s5h := 19
  scE := {}
  gam := zeroE
  sCl := 21
  vpm := {}
  wJv := #[]
  vpd := {}

/-- A shape with tokens of two bits and three calls: one that holds wl and ix, the one of kind WH,
and one that holds only ix. -/
def sampleShape : Shape where
  cf := { lt := 2 }
  calls := #[{ call := default, kind := .r16, segs := [.wl, .ix] },
    { call := default, kind := .wh, segs := [.wh] },
    { call := default, kind := .r16, segs := [.ix] }]

-- REM = 2 ACC + ZC - 2 ZO
#guard coefOf (remForm sampleDivide) 10 == ofNat 2
#guard coefOf (remForm sampleDivide) 11 == ofInt (-2)
#guard coefOf (remForm sampleDivide) 12 == ofNat 1
#guard (remForm sampleDivide).const == zeroE

-- the term of wl: -4 (REM - 2^16 (RH + 384)) + 5 (2 ZC - 3 - REM - 2^16 (RHP + 384))
#guard coefOf (keyWL sampleDivide) 10 == ofInt (-18)
#guard coefOf (keyWL sampleDivide) 11 == ofNat 18
#guard coefOf (keyWL sampleDivide) 12 == ofNat 1
#guard coefOf (keyWL sampleDivide) 13 == ofNat 262144
#guard coefOf (keyWL sampleDivide) 14 == ofInt (-327680)
#guard (keyWL sampleDivide).const == ofInt (-25165839)

-- the term of ix: 2^14 (4 (2 * 2 + 7) - IB_0 - 2 IB_1)
#guard coefOf (keyIX sampleShape sampleDivide) 15 == ofInt (-16384)
#guard coefOf (keyIX sampleShape sampleDivide) 16 == ofInt (-32768)
#guard (keyIX sampleShape sampleDivide).const == ofNat 720896

-- the key form of WH: (RH2 + 768) + 2^20 (RHP2 + 768)
#guard coefOf (keyWH sampleDivide) 19 == ofNat 1
#guard coefOf (keyWH sampleDivide) 20 == ofNat 1048576
#guard (keyWH sampleDivide).const == ofNat 805307136

-- each call of kind R16 is set once, and no other call
#guard (joinR16 sampleShape sampleDivide (Joins.empty 3)).joined == #[1, 0, 1]

-- the first call has both terms, the third only the term of ix
#guard coefOf ((joinR16 sampleShape sampleDivide (Joins.empty 3)).kf.getD 0 {}) 13 == ofNat 262144
#guard coefOf ((joinR16 sampleShape sampleDivide (Joins.empty 3)).kf.getD 0 {}) 15 == ofInt (-16384)
#guard coefOf ((joinR16 sampleShape sampleDivide (Joins.empty 3)).kf.getD 2 {}) 13 == zeroE
#guard coefOf ((joinR16 sampleShape sampleDivide (Joins.empty 3)).kf.getD 2 {}) 15 == ofInt (-16384)

end OnBytes.Attention.TestClaimsB
