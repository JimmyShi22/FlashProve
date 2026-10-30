-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules6Round.lean: the verifier's message of one round (`drawRound`), from the field, the plan's
entry, the round's kind and the row of words.

In a proof file of the programs a round's verifier message is computed from the hash answer to that
round's query. This file fixes, as a total function, which field elements, positions, matrix entries
and digest are read from 64-bit words of that answer (the row: `rowOf`, Fmt/Rules5.lean), and in
which order. The plan's entry (`Entry`, Fmt/Plan.lean) has the numbers of the round's draws; the
kind (`Kind`) says what the message consists of.

Sources. Section 6 of the format page (docs/format/FORMAT.md);
this file has not been held against the page as it ships,
and may differ from it. The
file stands on Fmt/Plan.lean (Entry,
Kind) and Fmt/Rules6.lean (the draws); Fmt/Rules4.lean is imported for the example plan's entries.
   Only two draws must not be 0: a seed's factor, and the challenge for the further variable of a
   sum-check, which stands alone in its round.

1. What the file contains. Definitions that can be evaluated.
   `wordsAtMost e k`: The most words that the round's draws use: 18 for each element of the
      extension field that may be 0, 36 for each that must not, 1 for each position, one for each 32
      matrix entries (rounded up), 4 for a seal. It follows from the entry and the kind.
   `Drawn`: What a round draws: elements; positions as drawn, repeats kept ("the draws"; "the list"
      is `listOf` of them; which of the two is used for what: Fmt/Rules6.lean, `listOf`); matrix
      entries; the seal's digest.
   The order follows from the kind and the entry (R6.2). Elements (kind 1): one after the other;
   either all or none must not be 0. The joining round (kind 2): exactly one element, which may
   be 0. Seeds (kind 3): s seeds one after the other, each whole: the v coordinates of its point,
   then its factor, which is not 0; the entry has s (v + 1) elements, s of them not 0; s is the
   plan's number of answers to a sample (R6.9). Positions (kind 4): at least one position; the
   positions, then the element if the entry has one (R6.10). Matrix entries (kind 5), in one
   portion. The seal (kind 6).
   `Entry.fits` (e.fits k s): The entry has its kind's draws and no others (R6.2's last sentence: an
      entry that has other draws is no entry of the format).
   `drawRoundD` is total. It draws (1) the positions; (2) the elements: in a round of seeds drawNZ
   seeds of (drawE - drawNZ) / drawNZ coordinates, and what that division leaves over as plain
   elements; in every other kind the plain elements, then those that must not be 0; (3) the matrix
   entries; (4) the seal, in a round of that kind alone. At an entry that fits its kind this is the
   page's order.

2. What is checked when the file compiles. 26 tests (#guard). Among them the page's known answers on
what the six rounds of its example chain draw, in both fields. The values are the page's. The rows
of words are given here as numbers: they were made by the page's reference lines from the chain's
values and are not printed on the page. That these rows are what the hash gives is a matter of the
section on a round's query, not of this file.

3. Theorems.
   `round_within`: see its statement. So the verifier's message is a total function of
      `blocksFor (wordsAtMost e k)` blocks of the answer, those from `firstBlock` on
      (Fmt/Rules5.lean).
   `round_reads`, `words_page`: see their statements.

4. What is not claimed. The hash. Which kind a round's name has. The laws of the draws.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Rules4
import Fmt.Rules6

namespace Fmt

/-- The most words of a round. -/
def wordsAtMost (e : Entry) (k : Kind) : Nat :=
  e.poss + (18 * (e.drawE - e.drawNZ) + 36 * e.drawNZ) +
    (e.trits + 31) / 32 + (if k = .sealed then 4 else 0)

/-- The entry has its kind's draws and no others (s: the plan's answers to a sample). -/
def Entry.fits (e : Entry) (k : Kind) (s : Nat) : Bool :=
  match k with
  | .elems => e.poss == 0 && e.trits == 0 && (e.drawNZ == 0 || e.drawNZ == e.drawE)
  | .join => e.poss == 0 && e.trits == 0 && e.drawE == 1 && e.drawNZ == 0
  | .seeds =>
    e.poss == 0 && e.trits == 0 && e.drawNZ == s &&
      decide (e.drawNZ ≤ e.drawE) && (e.drawE - e.drawNZ) % e.drawNZ == 0
  | .positions => e.trits == 0 && decide (e.drawE ≤ 1) && e.drawNZ == 0 && decide (1 ≤ e.poss)
  | .entries => e.poss == 0 && e.drawE == 0 && e.drawNZ == 0
  | .sealed => e.poss == 0 && e.trits == 0 && e.drawE == 0 && e.drawNZ == 0
  | .nothing => e.poss == 0 && e.trits == 0 && e.drawE == 0 && e.drawNZ == 0

/-- What a round draws. -/
structure Drawn where
  elems : List Ext
  /-- the positions as they are drawn -/
  poss : List Nat
  trits : List Int
  digest : Option ByteArray
  deriving DecidableEq

/-- a seed as a list: its point's coordinates, then its factor -/
def drawSeedL (f : Fld) (v : Nat) : Dr (List Ext) :=
  (drawSeed f v).bind fun s => Dr.pure (s.1 ++ [s.2])

/-- the plain elements, then those that must not be 0 -/
def drawPlainNZ (f : Fld) (a b : Nat) : Dr (List Ext) :=
  ((drawE f).times a).bind fun x => ((drawNZ f).times b).bind fun y => Dr.pure (x ++ y)

/-- `s` seeds of `v` coordinates one after the other, then `a` plain elements -/
def drawSeeds (f : Fld) (s v a : Nat) : Dr (List Ext) :=
  ((drawSeedL f v).times s).bind fun x => ((drawE f).times a).bind fun y => Dr.pure (x.flatten ++ y)

/-- the elements of a round -/
def drawElems (f : Fld) (e : Entry) (k : Kind) : Dr (List Ext) :=
  if k = .seeds then
    drawSeeds f e.drawNZ ((e.drawE - e.drawNZ) / e.drawNZ) ((e.drawE - e.drawNZ) % e.drawNZ)
  else drawPlainNZ f (e.drawE - e.drawNZ) e.drawNZ

/-- the seal, in a round of that kind -/
def drawDigest (k : Kind) : Dr (Option ByteArray) :=
  if k = .sealed then drawSeal.bind fun d => Dr.pure (some d) else Dr.pure none

/-- The draws of a round, as one draw. -/
def drawRoundD (f : Fld) (e : Entry) (k : Kind) : Dr Drawn :=
  (drawPoss e.logN e.poss).bind fun ps =>
    (drawElems f e k).bind fun es =>
      (drawTrits e.trits).bind fun ts => (drawDigest k).bind fun d => Dr.pure ⟨es, ps, ts, d⟩

/-- The verifier's message of a round. -/
def drawRound (f : Fld) (e : Entry) (k : Kind) (row : Row) : Drawn := (drawRoundD f e k row 0).1

/-! ## The toy chain: the page's known answers on what its six rounds draw, with tests of the counts
and of `Entry.fits` -/

/-- entry i of the toy plan (Fmt/Rules4.lean; the entries are the same in both fields) -/
def toyE (i : Nat) : Entry := (Toy4.plan .two).entries.getD i default
def toyE1 : Entry := toyE 0
def toyE2 : Entry := toyE 1
def toyE3 : Entry := toyE 2
def toyE4 : Entry := toyE 3
def toyE5 : Entry := toyE 4
def toyE6 : Entry := toyE 5
#guard (Toy4.plan .one).entries = (Toy4.plan .two).entries
#guard (Toy4.plan .two).entries.length = 6

-- the most words: one element; nothing; five positions and an element; a seed with two coordinates;
-- forty entries; a seal
#guard (wordsAtMost toyE1 .elems, wordsAtMost toyE2 .nothing, wordsAtMost toyE3 .positions, wordsAtMost toyE4 .seeds, wordsAtMost toyE5 .entries, wordsAtMost toyE6 .sealed) = (18, 0, 23, 72, 2, 4)
#guard wordsAtMost { name := "", drawE := 1, drawNZ := 1 } .elems = 36
-- the toy plan's entries fit their kinds; six cases that do not fit
#guard toyE1.fits .elems 1 && toyE2.fits .nothing 1 && toyE3.fits .positions 1 && toyE4.fits .seeds 1 && toyE5.fits .entries 1 && toyE6.fits .sealed 1
#guard !toyE3.fits .elems 1 && !toyE4.fits .elems 1 && !toyE5.fits .elems 1 && !toyE1.fits .seeds 1 && !toyE4.fits .seeds 2 && !toyE1.fits .nothing 1
-- a round of positions has at least one (R6.2, as this file reads the page named in the head
-- under Sources)
#guard (({ name := "", poss := 1, logN := 3 } : Entry).fits .positions 1) && !(({ name := "", logN := 3 } : Entry).fits .positions 1)
-- a joining round: exactly one element, which may be 0
#guard (({ name := "", drawE := 1 } : Entry).fits .join 1) && !(({ name := "", drawE := 2 } : Entry).fits .join 1) && !(({ name := "", drawE := 1, drawNZ := 1 } : Entry).fits .join 1) && !(({ name := "" } : Entry).fits .join 1)
#guard (({ name := "", drawE := 6, drawNZ := 2 } : Entry).fits .seeds 2) && !(({ name := "", drawE := 5, drawNZ := 2 } : Entry).fits .seeds 2)

-- field 2
#guard drawRound .two toyE1 .elems (rowOfList [4610700807997304418, 4447928095050642327, 12963931155414147300, 7316495064490161295, 9627543865146201643, 17041659379238995004, 2068571094369960751, 8287861782963183266, 501739776139779677, 13526335325956458812, 9135273636743051189, 16746030413144416361, 18147828123808823225, 14605912229045104261, 896408257804061545, 8311661561574733133, 15937757663663855203, 3213723600068886691, 5282282169967508537, 17186598970097633214]) = ⟨[(4610700807997304418, 4447928095050642327, 12963931155414147300)], [], [], none⟩
#guard drawRound .two toyE2 .nothing (rowOfList [12354448834341817819, 126212792592033193, 4029872107364622512, 11435141415038443070, 12657239840053921944, 3771027790021433138, 505295597059228153, 8637694814681865732, 5940644312738632807, 14111213921665854855, 7986610134626306536, 7783061811497082273, 11385961644973025727, 3918559913975858428, 5714416595316743881, 15691128705641129969, 12054740051592991361, 13049762026144749705, 15050644197690980623, 10190320388360704959]) = ⟨[], [], [], none⟩
#guard drawRound .two toyE3 .positions (rowOfList [761715879284156485, 5407778897541481343, 16377593880405237190, 17394999009710959118, 2584030404969074506, 1566154797897025065, 5902544055155014206, 6066228902280467927, 243428715784950778, 4736459390498520263, 15156229368269691735, 16590575468362014508, 7673268033104511672, 721167539076033217, 15010036237424613907, 4318359232911303999, 12055203944340634740, 10421748948597599056, 2306808682174944579, 2068581109753638995]) = ⟨[(1566154797897025065, 5902544055155014206, 6066228902280467927)], [69, 895, 454, 526, 842], [], none⟩
#guard drawRound .two toyE4 .seeds (rowOfList [10242453029133591669, 14074992841984905743, 12408565391145546959, 3606079508961713394, 16625540050041287054, 18228235731105415187, 12223257125875722716, 11485735129323258346, 7129091038179324709, 8138125449690818618, 5786533347796794886, 3425711999272777021, 13450314337361311588, 5860344836325390424, 6398138571331445133, 18177106029380937458, 15152378140625556080, 16074720687293283637, 6709863202317961575, 12640620702912069517]) = ⟨[(10242453029133591669, 14074992841984905743, 12408565391145546959), (3606079508961713394, 16625540050041287054, 18228235731105415187), (12223257125875722716, 11485735129323258346, 7129091038179324709)], [], [], none⟩
#guard drawRound .two toyE5 .entries (rowOfList [13627850108354113316, 16561230518035631712, 17875217669734244795, 3949140810549710828, 5316073592340150661, 17677560510585717462, 6527107672316530961, 10194511842025536207, 12975780683622380517, 6838901628616046180, 12357493773895318809, 4045237580775173268, 7086454895768003455, 15050140664192294729, 14968456739817654994, 16396453615153257078, 16661666623225340951, 17592843933941463954, 17229278679736183890, 12597086773135560140]) = ⟨[], [], [0, 1, 0, 0, -1, -1, 0, 0, -1, 1, -1, 0, 0, 0, 1, 1, 0, 0, -1, 1, 1, 0, 1, -1, -1, -1, 1, 0, 1, -1, -1, 0, 0, 0, 0, 1, 0, -1, 0, 1], none⟩
#guard drawRound .two toyE6 .sealed (rowOfList [3804188586346634763, 12923372657207053766, 10348770870300310960, 15491657320995474777, 4753705063955000720, 10320255431761882581, 10108487872262455086, 15722747101499116918, 2382757105872608136, 17128095423109332469, 14832662655191176370, 7758716608452357946, 7306767493548635126, 6109155973249838469, 9025235938092561572, 4086216008772558693, 14555503284279433904, 10568950831573442625, 4397385834964221081, 17284238985789151589]) = ⟨[], [], [], some (unhex "0b5ec9235d31cb34c68dd2f4f50a59b3b0fd28c246389e8f59cd0350416cfdd6")⟩

-- field 1
#guard drawRound .one toyE1 .elems (rowOfList [409361236637539239, 13875093353919802321, 18375975118052437409, 4747347617797856483, 12416614927290238099, 10285966553800591836, 17977077498212227143, 3764079069212059611, 5744302054688637660, 3663713147533976599, 6003962735315431538, 5477468991126165475, 13732876626097089100, 11430907896777378969, 12221713564574188791, 1836475567173694980, 800921451944235111, 1249802763430285802, 2527847368501215831, 9849179913327778626]) = ⟨[(409361236637539239, 40035298637638609, 2235074053556579745)], [], [], none⟩
#guard drawRound .one toyE2 .nothing (rowOfList [11489041672710379727, 148690670925575898, 17193056928187241250, 3881691247290886139, 7648748786645377134, 14460063301641312920, 9106371119692836817, 8759393925790833187, 11447801152002265712, 9565813861089338699, 3891809444969744983, 12297956942505807717, 564663932515883610, 2018301808218326220, 6178478517137141979, 10609287403343581741, 17068085943754279766, 590757599551075793, 11129070947069036326, 608702539956212371]) = ⟨[], [], [], none⟩
#guard drawRound .one toyE3 .positions (rowOfList [12352698250889138100, 11312787718948871198, 7608562481084622452, 13395911791667189510, 959350876131387382, 6638102729428215534, 12715955312110949344, 703665205314857216, 4372299234428109712, 16864810268925699685, 6129002111986896833, 13385634013498133470, 922355155994615258, 2147203148146431146, 4154137367561376854, 17608855420835963834, 15754108804717602300, 2213376081953122448, 5305367489326672020, 18023279981595047179]) = ⟨[(2026416711000827630, 1186740266042479584, 703665205314857216)], [948, 30, 628, 774, 1014], [], none⟩
#guard drawRound .one toyE4 .seeds (rowOfList [11744355855624809282, 14590334464206605646, 14306350652064282452, 2536038229860350416, 3263889381702428848, 12195925057355322765, 14043924588744123218, 11618678807615419577, 14053268819938684235, 4457635236639666358, 2462293540211652989, 15109104686227699087, 671494052769669630, 11814845322586461318, 16256609320779650256, 12761186562419029184, 4418471518553011533, 5037001907176695760, 12504224622574528578, 3972562261196100431]) = ⟨[(215140809556339522, 755276408924441934, 471292596782118740), (230195220646656464, 958046372488734896, 666710011286853005), (208866533461959506, 89463761546949817, 218210764656520523)], [], [], none⟩
#guard drawRound .one toyE5 .entries (rowOfList [9672494816844992897, 2338171623786530135, 963155022564369331, 9958641046822886960, 13063673781647918837, 16742819049857979484, 12491898829162093409, 10658953334713592490, 16822534566383587007, 5036141006068866432, 8740615956044409817, 10632576237755472981, 18178187141777160860, 5956900450117985219, 13618808196766041724, 7567766506403266308, 2596447995660993989, 10087506142543616147, 13957005984213841550, 17179184768819186533]) = ⟨[], [], [1, 0, 0, 0, 1, 0, 1, 1, 0, 0, 1, -1, 1, 0, -1, -1, 1, 0, 0, -1, 0, 0, 1, 0, -1, 0, -1, 0, 0, 1, 0, 0, -1, 1, 1, 1, 1, 1, 0, -1], none⟩
#guard drawRound .one toyE6 .sealed (rowOfList [4313368366129357533, 2403853395751883961, 3999734293751476960, 16613732548310972745, 10280610973528018410, 8730607729743216506, 3028049871564594541, 12859036412003401334, 13322679822653878511, 13306046776258699474, 11440918076226955941, 13927478794906667290, 6479925830817116317, 13481643415251373791, 11984802044355312817, 17858352629125816954, 7143573154126163898, 6860086225182266015, 7205588473707744892, 13674211181235592616]) = ⟨[], [], [], some (unhex "dd228c00ad29dc3bb954e861ed335c21e032010f26e9813749b96bb7bad58fe6")⟩

-- the words used up in rounds 1, 3, 4, 5, 6 (by the reference program; not printed on the page):
-- field 2, field 1
#guard ((drawRoundD .two toyE1 .elems (rowOfList [4610700807997304418, 4447928095050642327, 12963931155414147300, 7316495064490161295, 9627543865146201643, 17041659379238995004, 2068571094369960751, 8287861782963183266, 501739776139779677, 13526335325956458812, 9135273636743051189, 16746030413144416361, 18147828123808823225, 14605912229045104261, 896408257804061545, 8311661561574733133, 15937757663663855203, 3213723600068886691, 5282282169967508537, 17186598970097633214]) 0).2, (drawRoundD .two toyE3 .positions (rowOfList [761715879284156485, 5407778897541481343, 16377593880405237190, 17394999009710959118, 2584030404969074506, 1566154797897025065, 5902544055155014206, 6066228902280467927, 243428715784950778, 4736459390498520263, 15156229368269691735, 16590575468362014508, 7673268033104511672, 721167539076033217, 15010036237424613907, 4318359232911303999, 12055203944340634740, 10421748948597599056, 2306808682174944579, 2068581109753638995]) 0).2, (drawRoundD .two toyE4 .seeds (rowOfList [10242453029133591669, 14074992841984905743, 12408565391145546959, 3606079508961713394, 16625540050041287054, 18228235731105415187, 12223257125875722716, 11485735129323258346, 7129091038179324709, 8138125449690818618, 5786533347796794886, 3425711999272777021, 13450314337361311588, 5860344836325390424, 6398138571331445133, 18177106029380937458, 15152378140625556080, 16074720687293283637, 6709863202317961575, 12640620702912069517]) 0).2, (drawRoundD .two toyE5 .entries (rowOfList [13627850108354113316, 16561230518035631712, 17875217669734244795, 3949140810549710828, 5316073592340150661, 17677560510585717462, 6527107672316530961, 10194511842025536207, 12975780683622380517, 6838901628616046180, 12357493773895318809, 4045237580775173268, 7086454895768003455, 15050140664192294729, 14968456739817654994, 16396453615153257078, 16661666623225340951, 17592843933941463954, 17229278679736183890, 12597086773135560140]) 0).2, (drawRoundD .two toyE6 .sealed (rowOfList [3804188586346634763, 12923372657207053766, 10348770870300310960, 15491657320995474777, 4753705063955000720, 10320255431761882581, 10108487872262455086, 15722747101499116918, 2382757105872608136, 17128095423109332469, 14832662655191176370, 7758716608452357946, 7306767493548635126, 6109155973249838469, 9025235938092561572, 4086216008772558693, 14555503284279433904, 10568950831573442625, 4397385834964221081, 17284238985789151589]) 0).2) = (3, 8, 9, 2, 4)
#guard ((drawRoundD .one toyE1 .elems (rowOfList [409361236637539239, 13875093353919802321, 18375975118052437409, 4747347617797856483, 12416614927290238099, 10285966553800591836, 17977077498212227143, 3764079069212059611, 5744302054688637660, 3663713147533976599, 6003962735315431538, 5477468991126165475, 13732876626097089100, 11430907896777378969, 12221713564574188791, 1836475567173694980, 800921451944235111, 1249802763430285802, 2527847368501215831, 9849179913327778626]) 0).2, (drawRoundD .one toyE3 .positions (rowOfList [12352698250889138100, 11312787718948871198, 7608562481084622452, 13395911791667189510, 959350876131387382, 6638102729428215534, 12715955312110949344, 703665205314857216, 4372299234428109712, 16864810268925699685, 6129002111986896833, 13385634013498133470, 922355155994615258, 2147203148146431146, 4154137367561376854, 17608855420835963834, 15754108804717602300, 2213376081953122448, 5305367489326672020, 18023279981595047179]) 0).2, (drawRoundD .one toyE4 .seeds (rowOfList [11744355855624809282, 14590334464206605646, 14306350652064282452, 2536038229860350416, 3263889381702428848, 12195925057355322765, 14043924588744123218, 11618678807615419577, 14053268819938684235, 4457635236639666358, 2462293540211652989, 15109104686227699087, 671494052769669630, 11814845322586461318, 16256609320779650256, 12761186562419029184, 4418471518553011533, 5037001907176695760, 12504224622574528578, 3972562261196100431]) 0).2, (drawRoundD .one toyE5 .entries (rowOfList [9672494816844992897, 2338171623786530135, 963155022564369331, 9958641046822886960, 13063673781647918837, 16742819049857979484, 12491898829162093409, 10658953334713592490, 16822534566383587007, 5036141006068866432, 8740615956044409817, 10632576237755472981, 18178187141777160860, 5956900450117985219, 13618808196766041724, 7567766506403266308, 2596447995660993989, 10087506142543616147, 13957005984213841550, 17179184768819186533]) 0).2, (drawRoundD .one toyE6 .sealed (rowOfList [4313368366129357533, 2403853395751883961, 3999734293751476960, 16613732548310972745, 10280610973528018410, 8730607729743216506, 3028049871564594541, 12859036412003401334, 13322679822653878511, 13306046776258699474, 11440918076226955941, 13927478794906667290, 6479925830817116317, 13481643415251373791, 11984802044355312817, 17858352629125816954, 7143573154126163898, 6860086225182266015, 7205588473707744892, 13674211181235592616]) 0).2) = (3, 8, 9, 2, 4)

/-! ## Tests of this library's own (no known answer of the page) -/

-- two seeds of one coordinate each, one after the other
#guard drawRound .two { name := "", drawE := 4, drawNZ := 2 } .seeds (rowOfList [1, 1, 1, 0, 0, 0, 2, 2, 2, 3, 3, 3, 4, 4, 4]) = ⟨[(1, 1, 1), (2, 2, 2), (3, 3, 3), (4, 4, 4)], [], [], none⟩
-- the same entry in a round of elements: two plain ones, then two that must not be 0
#guard drawRound .two { name := "", drawE := 4, drawNZ := 2 } .elems (rowOfList [1, 1, 1, 0, 0, 0, 2, 2, 2, 3, 3, 3, 4, 4, 4]) = ⟨[(1, 1, 1), (0, 0, 0), (2, 2, 2), (3, 3, 3)], [], [], none⟩
-- a round of seeds without a factor: plain elements
#guard drawRound .two { name := "", drawE := 2 } .seeds (rowOfList [1, 2, 3, 4, 5, 6]) = ⟨[(1, 2, 3), (4, 5, 6)], [], [], none⟩

/-! ## A total function of a fixed number of words -/

theorem within_drawSeedL (f : Fld) (v : Nat) : (drawSeedL f v).Within (v * 18 + 36) :=
  Dr.within_bind (L := 0) (within_drawSeed f v) fun _ => Dr.within_pure _

theorem within_drawPlainNZ (f : Fld) (a b : Nat) : (drawPlainNZ f a b).Within (a * 18 + b * 36) :=
  Dr.within_bind (Dr.within_times (within_drawE f) a) fun _ =>
    Dr.within_bind (L := 0) (Dr.within_times (within_drawNZ f) b) fun _ => Dr.within_pure _

theorem within_drawSeeds (f : Fld) (s v a : Nat) :
    (drawSeeds f s v a).Within (s * (v * 18 + 36) + a * 18) :=
  Dr.within_bind (Dr.within_times (within_drawSeedL f v) s) fun _ =>
    Dr.within_bind (L := 0) (Dr.within_times (within_drawE f) a) fun _ => Dr.within_pure _

theorem within_drawElems (f : Fld) (e : Entry) (k : Kind) :
    (drawElems f e k).Within (18 * (e.drawE - e.drawNZ) + 36 * e.drawNZ) := by
  unfold drawElems
  by_cases h : k = .seeds
  · rw [if_pos h]
    refine Dr.within_mono (within_drawSeeds f _ _ _) (Nat.le_of_eq ?_)
    have hd := Nat.div_add_mod (e.drawE - e.drawNZ) e.drawNZ
    generalize (e.drawE - e.drawNZ) / e.drawNZ = q at hd ⊢
    generalize (e.drawE - e.drawNZ) % e.drawNZ = t at hd ⊢
    rw [← hd, Nat.mul_add, Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm (e.drawNZ * q) 18,
      Nat.mul_comm e.drawNZ 36, Nat.mul_comm t 18]
    omega
  · rw [if_neg h]
    exact Dr.within_mono (within_drawPlainNZ f _ _) (by omega)

theorem within_drawDigest (k : Kind) : (drawDigest k).Within (if k = .sealed then 4 else 0) := by
  unfold drawDigest
  by_cases h : k = .sealed
  · rw [if_pos h, if_pos h]
    exact Dr.within_bind (K := 4) (L := 0) within_drawSeal fun _ => Dr.within_pure _
  · rw [if_neg h, if_neg h]
    exact Dr.within_pure _

theorem within_drawRoundD (f : Fld) (e : Entry) (k : Kind) :
    (drawRoundD f e k).Within (wordsAtMost e k) :=
  Dr.within_mono (Dr.within_bind (within_drawPoss e.logN e.poss) fun _ =>
      Dr.within_bind (within_drawElems f e k) fun _ =>
        Dr.within_bind (within_drawTrits e.trits) fun _ =>
          Dr.within_bind (L := 0) (within_drawDigest k) fun _ => Dr.within_pure _)
    (by unfold wordsAtMost; omega)

/-- States: from every place of every row the round's draws end at most wordsAtMost e k words
further on and read these words alone. -/
def Spec.round_within : Prop :=
  ∀ (f : Fld) (e : Entry) (k : Kind), (drawRoundD f e k).Within (wordsAtMost e k)

/-- States: two rows with the same first wordsAtMost e k words give the same message. -/
def Spec.round_reads : Prop :=
  ∀ (f : Fld) (e : Entry) (k : Kind) (r r' : Row),
    (∀ t, t < wordsAtMost e k → r t = r' t) → drawRound f e k r = drawRound f e k r'

/-- States: wordsAtMost is `mostWords` (Fmt/Rules6.lean: the page's formula) at the entry's numbers,
one portion. -/
def Spec.words_page : Prop :=
  ∀ (e : Entry) (k : Kind),
    wordsAtMost e k = mostWords e.drawE e.drawNZ e.poss [e.trits] (decide (k = .sealed))

theorem round_within : Spec.round_within := within_drawRoundD

theorem round_reads : Spec.round_reads := fun f e k r r' h =>
  congrArg Prod.fst ((within_drawRoundD f e k).reads r r' 0 fun t _ h2 => h t (by omega))

theorem words_page : Spec.words_page := by
  intro e k
  unfold wordsAtMost mostWords
  by_cases h : k = .sealed
  · simp [h]
    omega
  · simp [h]
    omega

end Fmt
