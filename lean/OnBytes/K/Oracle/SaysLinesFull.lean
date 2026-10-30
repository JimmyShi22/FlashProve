-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/SaysLinesFull.lean: a whole parameter file of the full-size example, as a closed
term, has the lines of the full-size ground: `EntryGround.SaysLines` holds of it.

`EntryGround.SaysLines` (OnBytes/Tie/EntryGround.lean) is one equation on a parameter file: the
lines that `Params.readLines` reads from it are the ground's. The theorems on the entry file's
checker have it as a hypothesis (OnBytes/K/Oracle/ArmO.lean: `EntryArmO.zero`).
OnBytes/K/Left/TestSaysLines.lean proves it, by the kernel's evaluation, of the 32 lines `full32`,
and OnBytes/K/Left/SaysLinesPrefix.lean of every byte string that begins with these
(`full_says_of_prefix`). Here the 152 lines that stand behind them in the file are written out,
and the whole file is the one behind the other. The reader is not evaluated anew.

Whose bytes. `fullPolicy` is meant to be the full-size example's parameter file,
prover/examples/target_full_f2/policy.txt: 184 lines, 2629 bytes: public parameters, no
weights. The sha256 sum of the 32 lines of `full32`, each with its line feed, and then the text
written here, taken outside Lean, is
  ce9e126bb3ba7179319a31981a3fc36ca505d738348971f379dfc795f94a3fae
which is the sum that the head of OnBytes/K/Left/TestSaysLines.lean gives for that file. A FILE ON A
DISK IS STILL COMPARED WITH THESE BYTES BY ITS SUM, OUTSIDE LEAN: sha256sum policy.txt.

Main definitions: `fullBehindText`, `fullPolicy`.
Main theorem: `full_saysLines`.

What is not claimed. THAT ANY CALL OF THE PROGRAM ON THIS PARAMETER FILE ENDS IN 0: no key file, no
entry file and no proof file is read here, and `PortYesAt` (OnBytes/K/Top.lean) is shown of no
files. That these bytes are those of a file in the repository: nothing in OnBytes/ reads a folder of
examples. The number of bytes and the sum are no theorems. `SaysLines` asks for what the first 32
lines say: of the 152 lines behind them, of the layout file and of the scale file nothing is said.
Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.SaysLinesPrefix

set_option autoImplicit false

namespace OnBytes.K.Oracle

open OnBytes.K.Left (full_says_of_prefix)
open OnBytes.K.Left.TestSaysLines (bytesOf full32)

/-- What stands behind the first 32 lines of the full-size example's parameter file, as text: 152
lines, each ended by a line feed. -/
def fullBehindText : String := "prof 20
lt 10
L 48
ll 2
d 5120
H 40
G 8
dh 128
f 16384
fe 8192
NE 128
V 202048
eps1_lo 53687
eps1_hi 0
eps2_lo 53687
eps2_hi 0
cs 12
theta0_lo 500000
theta0_hi 0
hq 2
hv 1
ho 1
hgD 1
huD 1
hdD 1
hr 1
ut 1
la 16
nmin 20
D 2048
tau 128
lmaf 16
NAf 3
lmad 15
NAd 1
lmar 13
lmb 16
lmq 16
lmx 16
wb_qk 13
wb_v 13
wb_o 13
wb_g 13
wb_u 13
wb_gs 13
wb_us 13
wb_gr 13
wb_ur 13
wb_dn 13
wb_dnr 13
wb_r 13
iota_0 1
iota_1 1
iota_2 1
iota_3 2
iota_4 1
iota_5 1
iota_6 0
iota_7 0
seed_lo 1
seed_hi 0
lB 6
S 12
rx 8
kFM 15
kFD 16
lmS 16
NAs 1
lmh 13
lmo 16
lmbA 14
iotaA_0 57
MF 44
KF 30
epsF_lo 53687
epsF_hi 0
toksrc 1
lmhf 16
NHf 4
lmhd 14
lmhr 13
lmbH 15
wb_emb 21
wb_head 13
iotaH_0 1
iotaH_1 1
iotaH_2 1
iotaH_3 0
iotaH_4 0
iotaH_5 0
C 256
theta 256
cap 0
s 15
sh 8
sT 4
F 24
lidb 28
nminH 27
rcl 1
gcl 1
xl 5
tsilu0 2048398297
tsilu1 192427613
tsilu2 2862900154
tsilu3 2853881485
tsilu4 2797826050
tsilu5 1420723544
tsilu6 3686369553
tsilu7 2593882461
tsig0 1965976300
tsig1 2359599336
tsig2 2246761285
tsig3 2426172242
tsig4 3869868832
tsig5 310049175
tsig6 339407438
tsig7 2601410768
trope0 786409086
trope1 1563166184
trope2 1100635208
trope3 2272768750
trope4 1260813977
trope5 3744463197
trope6 3300849996
trope7 4050797957
texp0 3648852807
texp1 2402568834
texp2 4186852988
texp3 523559909
texp4 1873895626
texp5 3042864545
texp6 1726265496
texp7 165292856
call R16a R16 G U
call R16b R16 N1 N1H N2 N2H O D V
call R16c R16 QK QKH XR LR LT DD
call R8 R8 GH UH OH DH VH ROW LH SEL L3 G0
call FC FC CN1 CN2 CQK CV CLR
call FS FS MR CG
call FL FL F
call R16d R16 UT
callA KR KR RM RD
callA KFD KFD FM FD
callA R16 R16 WL IX
callA WH WH WH
callH R16a R16 NF NFH HD0
callH R16b R16 HD1
callH R8 R8 ROW HD2
callH FEa FE HE0
callH FEb FE HE1
callH FC FC CNF
"

/-- The whole parameter file: the 32 lines `full32`, each with its line feed, and then the
152 lines behind them. -/
def fullPolicy : ByteArray := bytesOf full32 ++ fullBehindText.toUTF8

/-- The lines that `Params.readLines` reads from this whole parameter file are the
full-size ground's. Of a call of the program on that file nothing is said. -/
theorem full_saysLines : Tie.recordGround.SaysLines fullPolicy :=
  full_says_of_prefix _

end OnBytes.K.Oracle
