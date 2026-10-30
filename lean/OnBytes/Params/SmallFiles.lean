-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/SmallFiles.lean: what the tests of the small example read besides a parameter file's
first 32 lines: the lines after them, and copies of the scale file and the layout file.

The text of the layout file is held in OnBytes/Plan/TestReqFrame.lean. That these copies are the
files of prover/examples/target_small_f2_roomy is not tested here: nothing in this directory reads
that folder. The file is no part of the program.
-/
import OnBytes.Model.Verify
import OnBytes.Plan.TestReqFrame

namespace OnBytes.Params.SmallFiles

/-- The lines of the parameter file after its first 32. -/
def policyTail : String := "prof 20
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

/-- The bytes of KL.bin. -/
def scales : ByteArray :=
  Fmt.unhex (String.join
    ["1d0000001d0000001100000007000000090000000f000000090000002b0000001e0000002b0000001e000000",
     "0c000000010000001d0000001d0000001100000007000000090000000f000000090000002b0000001e000000",
     "2b0000001e0000000c000000010000001d0000001d0000001100000007000000090000000f00000009000000",
     "2b0000001e0000002b0000001e0000000c000000010000001d0000001d000000110000000700000009000000",
     "0f000000090000002b0000001e0000002b0000001e0000000c000000000000001d0000001d00000011000000",
     "07000000090000000f000000090000002b0000001e0000002b0000001e0000000c000000010000001d000000",
     "1d0000001100000007000000090000000f000000090000002b0000001e0000002b0000001e0000000c000000",
     "010000001d0000001d0000001100000007000000090000000f000000090000002b0000001e0000002b000000",
     "1e0000000c000000010000001d0000001d0000001100000007000000090000000f000000090000002b000000",
     "1e0000002b0000001e0000000c000000000000000d000000080000000f0000000d000000080000000f000000",
     "0d000000080000000f0000000d000000080000000f000000"])

/-- The bytes of layout.txt. -/
def layout : ByteArray := Plan.TestReqFrame.file.toUTF8

end OnBytes.Params.SmallFiles
