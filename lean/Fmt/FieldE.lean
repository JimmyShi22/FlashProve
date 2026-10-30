-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/FieldE.lean: the arithmetic of the format's two fields and of their cubic extensions, on words:
total functions that can be evaluated.

The format page rules how elements are spelled; a protocol's decision also has to compute with them.

Sources. The format page (docs/format/FORMAT.md, which comes with the programs), rules
R1.2 to R1.4
(Fmt/Rules1.lean: Fld, Fld.p, Fld.c, Fld.ok); this file has not been held against the page as it
ships, and may differ from it. No Mathlib.

1. What the file contains.
   F = Z / p. An element is a word below p.
   E = F[X] / (X^3 - c). An element is a triple (e_0, e_1, e_2) for e_0 + e_1 X + e_2 X^2
     (abbreviation `Ext3`).
   `Fld.mulE`: c_0 = a_0 b_0 + c (a_1 b_2 + a_2 b_1); c_1 = a_0 b_1 + a_1 b_0 + c a_2 b_2;
     c_2 = a_0 b_2 + a_1 b_1 + a_2 b_0.
   `Fld.invE`: with A_0 = a_0^2 - c a_1 a_2, A_1 = c a_2^2 - a_0 a_1, A_2 = a_1^2 - a_0 a_2 and
     N = a_0 A_0 + c (a_2 A_1 + a_1 A_2): a (A_0 + A_1 X + A_2 X^2) = N, so the inverse is
     (A_0, A_1, A_2) / N.
   How. Nothing is done for speed.
   Total. A word that is not below p is taken modulo p; every result is below p, but that of
     `Fld.ofF`, which copies its word.

2. What is checked when the file compiles. 46 tests (#guard). Sums, differences, products, inverses
in F and in E at borders (0, 1, p - 1, X, X^2) and at random elements, in both fields: answers of a
short Python program written for this file, which multiplies in E by convolution and reduction and
inverts by the power p^3 - 2: other formulas than here. X^3 = c. a · a^(-1) = 1. The sum of a small
example of this library's own.

3. Theorems. `Fld.ok_add`, `Fld.ok_sub`, `Fld.ok_mul`, `Fld.ok_neg`: every result is below p.

4. What is not claimed. No theorem that these are field operations. That F, E are the fields of the
formal side is a connection for another file. This file claims nothing on time.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules1

namespace Fmt

/-- an element of the extension field: e_0 + e_1 X + e_2 X^2 -/
abbrev Ext3 : Type := UInt64 × UInt64 × UInt64

namespace Fld

/-- a natural number as an element of F -/
def red (f : Fld) (n : Nat) : UInt64 := UInt64.ofNat (n % f.p)

def add (f : Fld) (a b : UInt64) : UInt64 := f.red (a.toNat + b.toNat)
def neg (f : Fld) (a : UInt64) : UInt64 := f.red (f.p - a.toNat % f.p)
def sub (f : Fld) (a b : UInt64) : UInt64 := f.red (a.toNat + (f.p - b.toNat % f.p))
def mul (f : Fld) (a b : UInt64) : UInt64 := f.red (a.toNat * b.toNat)
/-- a^e -/
def pow (f : Fld) (a : UInt64) (e : Nat) : UInt64 := f.red (powMod a.toNat e f.p)
/-- the inverse; 0 at 0 -/
def inv (f : Fld) (a : UInt64) : UInt64 := f.pow a (f.p - 2)
/-- the constant c with X^3 = c -/
def cW (f : Fld) : UInt64 := f.red f.c

def zeroE : Ext3 := (0, 0, 0)
def oneE : Ext3 := (1, 0, 0)
def ofF (a : UInt64) : Ext3 := (a, 0, 0)

def addE (f : Fld) (a b : Ext3) : Ext3 := (f.add a.1 b.1, f.add a.2.1 b.2.1, f.add a.2.2 b.2.2)
def subE (f : Fld) (a b : Ext3) : Ext3 := (f.sub a.1 b.1, f.sub a.2.1 b.2.1, f.sub a.2.2 b.2.2)
def negE (f : Fld) (a : Ext3) : Ext3 := (f.neg a.1, f.neg a.2.1, f.neg a.2.2)
def scaleE (f : Fld) (s : UInt64) (a : Ext3) : Ext3 := (f.mul s a.1, f.mul s a.2.1, f.mul s a.2.2)

/-- The product in E. -/
def mulE (f : Fld) (a b : Ext3) : Ext3 :=
  (f.add (f.mul a.1 b.1) (f.mul f.cW (f.add (f.mul a.2.1 b.2.2) (f.mul a.2.2 b.2.1))),
   f.add (f.add (f.mul a.1 b.2.1) (f.mul a.2.1 b.1)) (f.mul f.cW (f.mul a.2.2 b.2.2)),
   f.add (f.add (f.mul a.1 b.2.2) (f.mul a.2.1 b.2.1)) (f.mul a.2.2 b.1))

/-- the three cofactors -/
def adjE (f : Fld) (a : Ext3) : Ext3 :=
  (f.sub (f.mul a.1 a.1) (f.mul f.cW (f.mul a.2.1 a.2.2)),
    f.sub (f.mul f.cW (f.mul a.2.2 a.2.2)) (f.mul a.1 a.2.1),
    f.sub (f.mul a.2.1 a.2.1) (f.mul a.1 a.2.2))

/-- the norm -/
def normE (f : Fld) (a : Ext3) : UInt64 :=
  f.add (f.mul a.1 (f.adjE a).1)
    (f.mul f.cW (f.add (f.mul a.2.2 (f.adjE a).2.1) (f.mul a.2.1 (f.adjE a).2.2)))

/-- The inverse in E; 0 at 0. -/
def invE (f : Fld) (a : Ext3) : Ext3 := f.scaleE (f.inv (f.normE a)) (f.adjE a)

/-- all three words are below p -/
def okE (f : Fld) (a : Ext3) : Bool := f.ok a.1 && f.ok a.2.1 && f.ok a.2.2

theorem p_pos (f : Fld) : 0 < f.p := by cases f <;> decide
theorem p_lt (f : Fld) : f.p < 2 ^ 64 := by cases f <;> decide

/-- Every result of `red` is below p. -/
theorem ok_red (f : Fld) (n : Nat) : f.ok (f.red n) = true := by
  have h1 : n % f.p < f.p := Nat.mod_lt _ f.p_pos
  have h2 : n % f.p < 2 ^ 64 := Nat.lt_trans h1 f.p_lt
  unfold ok red
  rw [UInt64.toNat_ofNat_of_lt' h2]
  exact decide_eq_true h1

theorem ok_add (f : Fld) (a b : UInt64) : f.ok (f.add a b) = true := ok_red f _
theorem ok_sub (f : Fld) (a b : UInt64) : f.ok (f.sub a b) = true := ok_red f _
theorem ok_neg (f : Fld) (a : UInt64) : f.ok (f.neg a) = true := ok_red f _
theorem ok_mul (f : Fld) (a b : UInt64) : f.ok (f.mul a b) = true := ok_red f _

end Fld

/-! ## Tests -/

#guard Fld.add .one 2305843009213693950 2305843009213693950 == 2305843009213693949 && Fld.sub .one 2305843009213693950 2305843009213693950 == 0 && Fld.mul .one 2305843009213693950 2305843009213693950 == 1
#guard Fld.add .one 2305843009213693950 1 == 0 && Fld.sub .one 2305843009213693950 1 == 2305843009213693949 && Fld.mul .one 2305843009213693950 1 == 2305843009213693950
#guard Fld.add .one 487097493416467536 1015176720250886294 == 1502274213667353830 && Fld.sub .one 487097493416467536 1015176720250886294 == 1777763782379275193 && Fld.mul .one 487097493416467536 1015176720250886294 == 2255059125039016427
#guard Fld.add .one 24150551631594028 1899237372196348346 == 1923387923827942374 && Fld.sub .one 24150551631594028 1899237372196348346 == 430756188648939633 && Fld.mul .one 24150551631594028 1899237372196348346 == 498754180542962702
#guard Fld.add .one 1152921504606846975 2 == 1152921504606846977 && Fld.sub .one 1152921504606846975 2 == 1152921504606846973 && Fld.mul .one 1152921504606846975 2 == 2305843009213693950
#guard Fld.add .one 0 487097493416467536 == 487097493416467536 && Fld.sub .one 0 487097493416467536 == 1818745515797226415 && Fld.mul .one 0 487097493416467536 == 0
#guard Fld.inv .one 2 == 1152921504606846976
#guard Fld.inv .one 2305843009213693950 == 2305843009213693950
#guard Fld.inv .one 487097493416467536 == 1190337071788586914
#guard Fld.inv .one 1899237372196348346 == 461591440003575242
#guard Fld.mulE .one (68894002905173635, 447559341737483745, 1908741832908578207) (2046878971528392693, 1319980654490779941, 1589130579403683858) == (847061638831802603, 928942023516509552, 1488017563255599193) && Fld.addE .one (68894002905173635, 447559341737483745, 1908741832908578207) (2046878971528392693, 1319980654490779941, 1589130579403683858) == (2115772974433566328, 1767539996228263686, 1192029403098568114) && Fld.subE .one (68894002905173635, 447559341737483745, 1908741832908578207) (2046878971528392693, 1319980654490779941, 1589130579403683858) == (327858040590474893, 1433421696460397755, 319611253504894349)
#guard Fld.mulE .one (1831064611126100316, 1505734421936247462, 2076898655024105201) (905261698750015026, 536816378072814593, 2256022315389847208) == (18763373006530365, 1398309134586072694, 430915896527467253) && Fld.addE .one (1831064611126100316, 1505734421936247462, 2076898655024105201) (905261698750015026, 536816378072814593, 2256022315389847208) == (430483300662421391, 2042550800009062055, 2027077961200258458) && Fld.subE .one (1831064611126100316, 1505734421936247462, 2076898655024105201) (905261698750015026, 536816378072814593, 2256022315389847208) == (925802912376085290, 968918043863432869, 2126719348847951944)
#guard Fld.mulE .one (2305843009213693950, 2305843009213693950, 2305843009213693950) (2305843009213693950, 2305843009213693950, 2305843009213693950) == (11, 7, 3) && Fld.addE .one (2305843009213693950, 2305843009213693950, 2305843009213693950) (2305843009213693950, 2305843009213693950, 2305843009213693950) == (2305843009213693949, 2305843009213693949, 2305843009213693949) && Fld.subE .one (2305843009213693950, 2305843009213693950, 2305843009213693950) (2305843009213693950, 2305843009213693950, 2305843009213693950) == (0, 0, 0)
#guard Fld.mulE .one (0, 1, 0) (0, 0, 1) == (5, 0, 0) && Fld.addE .one (0, 1, 0) (0, 0, 1) == (0, 1, 1) && Fld.subE .one (0, 1, 0) (0, 0, 1) == (0, 1, 2305843009213693950)
#guard Fld.mulE .one (0, 0, 1) (0, 0, 1) == (0, 5, 0) && Fld.addE .one (0, 0, 1) (0, 0, 1) == (0, 0, 2) && Fld.subE .one (0, 0, 1) (0, 0, 1) == (0, 0, 0)
#guard Fld.mulE .one (1, 2, 3) (68894002905173635, 447559341737483745, 1908741832908578207) == (505429356702578419, 1546358730612176708, 704699515885372651) && Fld.addE .one (1, 2, 3) (68894002905173635, 447559341737483745, 1908741832908578207) == (68894002905173636, 447559341737483747, 1908741832908578210) && Fld.subE .one (1, 2, 3) (68894002905173635, 447559341737483745, 1908741832908578207) == (2236949006308520317, 1858283667476210208, 397101176305115747)
#guard Fld.invE .one (68894002905173635, 447559341737483745, 1908741832908578207) == (1457388823448970194, 360661153802571805, 1223858803421635805)
#guard Fld.invE .one (2305843009213693950, 2305843009213693950, 2305843009213693950) == (576460752303423488, 1729382256910270463, 0)
#guard Fld.invE .one (0, 1, 0) == (0, 0, 1844674407370955161)
#guard Fld.invE .one (1, 2, 3) == (2088519147322946438, 799309797123596785, 1359195000638742920)
#guard Fld.add .two 18446744069414584320 18446744069414584320 == 18446744069414584319 && Fld.sub .two 18446744069414584320 18446744069414584320 == 0 && Fld.mul .two 18446744069414584320 18446744069414584320 == 1
#guard Fld.add .two 18446744069414584320 1 == 0 && Fld.sub .two 18446744069414584320 1 == 18446744069414584319 && Fld.mul .two 18446744069414584320 1 == 18446744069414584320
#guard Fld.add .two 12666134067308569882 16717761278189153089 == 10937151276083138650 && Fld.sub .two 12666134067308569882 16717761278189153089 == 14395116858534001114 && Fld.mul .two 12666134067308569882 16717761278189153089 == 832426969990088222
#guard Fld.add .two 18240668888807141456 10178462783263353390 == 9972387602655910525 && Fld.sub .two 18240668888807141456 10178462783263353390 == 8062206105543788066 && Fld.mul .two 18240668888807141456 10178462783263353390 == 13744764068574418834
#guard Fld.add .two 9223372034707292160 2 == 9223372034707292162 && Fld.sub .two 9223372034707292160 2 == 9223372034707292158 && Fld.mul .two 9223372034707292160 2 == 18446744069414584320
#guard Fld.add .two 0 12666134067308569882 == 12666134067308569882 && Fld.sub .two 0 12666134067308569882 == 5780610002106014439 && Fld.mul .two 0 12666134067308569882 == 0
#guard Fld.inv .two 2 == 9223372034707292161
#guard Fld.inv .two 18446744069414584320 == 18446744069414584320
#guard Fld.inv .two 12666134067308569882 == 15284000069394950474
#guard Fld.inv .two 10178462783263353390 == 657872430220937363
#guard Fld.mulE .two (1132550243566649460, 12145036622389590759, 1232591813377523900) (12495788675808754094, 4388754207325127985, 11412258346114291893) == (12244281738622937231, 282400616314993865, 906292728466988164) && Fld.addE .two (1132550243566649460, 12145036622389590759, 1232591813377523900) (12495788675808754094, 4388754207325127985, 11412258346114291893) == (13628338919375403554, 16533790829714718744, 12644850159491815793) && Fld.subE .two (1132550243566649460, 12145036622389590759, 1232591813377523900) (12495788675808754094, 4388754207325127985, 11412258346114291893) == (7083505637172479687, 7756282415064462774, 8267077536677816328)
#guard Fld.mulE .two (3249475539463731196, 432758696477627105, 12684029643605633124) (17325955976017324654, 16557898854825017012, 28733411961894615) == (7035354627994880608, 13500670080344592480, 8664035574471199180) && Fld.addE .two (3249475539463731196, 432758696477627105, 12684029643605633124) (17325955976017324654, 16557898854825017012, 28733411961894615) == (2128687446066471529, 16990657551302644117, 12712763055567527739) && Fld.subE .two (3249475539463731196, 432758696477627105, 12684029643605633124) (17325955976017324654, 16557898854825017012, 28733411961894615) == (4370263632860990863, 2321603911067194414, 12655296231643738509)
#guard Fld.mulE .two (18446744069414584320, 18446744069414584320, 18446744069414584320) (18446744069414584320, 18446744069414584320, 18446744069414584320) == (5, 4, 3) && Fld.addE .two (18446744069414584320, 18446744069414584320, 18446744069414584320) (18446744069414584320, 18446744069414584320, 18446744069414584320) == (18446744069414584319, 18446744069414584319, 18446744069414584319) && Fld.subE .two (18446744069414584320, 18446744069414584320, 18446744069414584320) (18446744069414584320, 18446744069414584320, 18446744069414584320) == (0, 0, 0)
#guard Fld.mulE .two (0, 1, 0) (0, 0, 1) == (2, 0, 0) && Fld.addE .two (0, 1, 0) (0, 0, 1) == (0, 1, 1) && Fld.subE .two (0, 1, 0) (0, 0, 1) == (0, 1, 18446744069414584320)
#guard Fld.mulE .two (0, 0, 1) (0, 0, 1) == (0, 2, 0) && Fld.addE .two (0, 0, 1) (0, 0, 1) == (0, 0, 2) && Fld.subE .two (0, 0, 1) (0, 0, 1) == (0, 0, 0)
#guard Fld.mulE .two (1, 2, 3) (1132550243566649460, 12145036622389590759, 1232591813377523900) == (5146160953755952330, 3358943920373448758, 10473571719442069477) && Fld.addE .two (1, 2, 3) (1132550243566649460, 12145036622389590759, 1232591813377523900) == (1132550243566649461, 12145036622389590761, 1232591813377523903) && Fld.subE .two (1, 2, 3) (1132550243566649460, 12145036622389590759, 1232591813377523900) == (17314193825847934862, 6301707447024993564, 17214152256037060424)
#guard Fld.invE .two (1132550243566649460, 12145036622389590759, 1232591813377523900) == (4648824005501666961, 7573980475502113009, 13530567242447601033)
#guard Fld.invE .two (18446744069414584320, 18446744069414584320, 18446744069414584320) == (1, 18446744069414584320, 0)
#guard Fld.invE .two (0, 1, 0) == (0, 0, 9223372034707292161)
#guard Fld.invE .two (1, 2, 3) == (15337742259962688087, 7876137917278137126, 12021473663213998771)

/-! X^3 = c; a · a^(-1) = 1; 0 has the "inverse" 0; a word that is not below p is taken modulo p; a
small example of this library's own: (1, 2, 3) + (3, 4, 7) + (10, 18, 7) + (15, 28, 7) -/
#guard [Fld.one, Fld.two].all fun f => f.mulE (0, 1, 0) (f.mulE (0, 1, 0) (0, 1, 0)) == (f.cW, 0, 0)
#guard [Fld.one, Fld.two].all fun f => [((5, 6, 7) : Ext3), (0, 0, 9), (0, 3, 0), (12345678901234567, 2, 998877665544332211)].all fun a => f.mulE a (f.invE a) == Fld.oneE
#guard [Fld.one, Fld.two].all fun f => f.invE Fld.zeroE == Fld.zeroE && f.inv 0 == 0
#guard Fld.add .one 2305843009213693951 5 == 5 && Fld.mul .two 18446744069414584322 7 == 7
#guard [((3, 4, 7) : Ext3), (10, 18, 7), (15, 28, 7)].foldl (Fld.addE .two) (1, 2, 3) == (29, 52, 24)
#guard [Fld.one, Fld.two].all fun f => f.okE (f.mulE (18446744073709551615, 18446744073709551615, 18446744073709551615) (18446744073709551615, 1, 18446744073709551615))

end Fmt
