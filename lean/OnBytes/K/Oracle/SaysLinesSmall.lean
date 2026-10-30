-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Oracle/SaysLinesSmall.lean: a whole parameter file of the small example, as a closed
term, has the lines of the small ground: `EntryGround.SaysLines` holds of it.

`EntryGround.SaysLines` (OnBytes/Tie/EntryGround.lean) is one equation on a parameter file: the
lines that `Params.readLines` reads from it are the ground's. The theorems on the entry file's
checker have it as a hypothesis (OnBytes/K/Oracle/ArmO.lean: `EntryArmO.zero`).
OnBytes/K/Left/TestSaysLines.lean proves it, by the kernel's evaluation, of the 32 lines `small32`,
and OnBytes/K/Left/SaysLinesPrefix.lean of every byte string that begins with these
(`small_says_of_prefix`). Here the 151 lines that stand behind them in the file are written out,
and the whole file is the one behind the other. The reader is not evaluated anew.

Whose bytes. `smallPolicy` is meant to be the small example's parameter file,
prover/examples/target_small_f2_roomy/policy.txt: 183 lines, 2479 bytes: public parameters, no
weights. The sha256 sum of the 32 lines of `small32`, each with its line feed, and then the text
written here, taken outside Lean, is
  8d9ae1dda2e503550cafade93c54c1b8ecc8eb4b6dab3b843c72a478bb892d2f
which is the sum that the head of OnBytes/K/Left/TestSaysLines.lean gives for that file. A FILE ON A
DISK IS STILL COMPARED WITH THESE BYTES BY ITS SUM, OUTSIDE LEAN: sha256sum policy.txt.

Main definitions: `smallBehindText`, `smallPolicy`.
Main theorem: `small_saysLines`.

What is not claimed. THAT ANY CALL OF THE PROGRAM ON THIS PARAMETER FILE ENDS IN 0: no key file, no
entry file and no proof file is read here, and `PortYesAt` (OnBytes/K/Top.lean) is shown of no
files. That these bytes are those of a file in the repository: nothing in OnBytes/ reads a folder of
examples. The number of bytes and the sum are no theorems. `SaysLines` asks for what the first 32
lines say: of the 151 lines behind them, of the layout file and of the scale file nothing is said.
Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.SaysLinesPrefix

set_option autoImplicit false

namespace OnBytes.K.Oracle

open OnBytes.K.Left (small_says_of_prefix)
open OnBytes.K.Left.TestSaysLines (bytesOf small32)

/-- What stands behind the first 32 lines of the small example's parameter file, as text: 151
lines, each ended by a line feed. -/
def smallBehindText : String := "prof 20
lt 6
L 8
ll 2
d 512
H 4
G 2
dh 128
f 1024
fe 512
NE 4
V 512
eps1_lo 1
eps1_hi 0
eps2_lo 1
eps2_hi 0
cs 12
theta0_lo 10000
theta0_hi 0
hq 2
hv 1
ho 1
hgD 1
huD 1
hdD 1
hr 1
ut 1
la 8
nmin 20
D 2048
tau 128
lmaf 13
NAf 3
lmad 12
NAd 1
lmar 12
lmb 13
lmq 13
lmx 13
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
iota_0 0
iota_1 0
iota_2 0
iota_3 1
iota_4 0
iota_5 0
iota_6 0
iota_7 0
seed_lo 31
seed_hi 0
lB 4
S 12
rx 8
kFM 15
kFD 16
lmS 11
NAs 1
lmh 12
lmo 13
lmbA 13
iotaA_0 52
MF 43
KF 30
epsF_lo 1
epsF_hi 0
toksrc 1
lmhf 14
NHf 1
lmhd 12
lmhr 12
lmbH 13
wb_emb 21
wb_head 13
iotaH_0 0
iotaH_1 0
iotaH_2 0
iotaH_3 0
iotaH_4 0
iotaH_5 0
C 256
theta 256
cap 0
s 16
sh 8
sT 4
F 24
lidb 24
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
trope0 2232934348
trope1 2156588140
trope2 3599599331
trope3 498649753
trope4 3675316650
trope5 2999201840
trope6 1537898906
trope7 2900737701
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

/-- The whole parameter file: the 32 lines `small32`, each with its line feed, and then the
151 lines behind them. -/
def smallPolicy : ByteArray := bytesOf small32 ++ smallBehindText.toUTF8

/-- The lines that `Params.readLines` reads from this whole parameter file are the
small ground's. Of a call of the program on that file nothing is said. -/
theorem small_saysLines : Tie.smallRecordGround.SaysLines smallPolicy :=
  small_says_of_prefix _

end OnBytes.K.Oracle
