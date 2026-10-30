-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/RunPure.lean: WHAT A FILE OF EVALUATIONS AND A COMMAND (NOT NAMED HERE) BOTH CALL,
  THE SMALL
  SIZE: PURE FUNCTIONS: no IO, no reading of files, no table of controls: from the three
public files (Z), a hash on bytes (O), the user's commitment, prompt and output, and what a parser
  hands over, to the fast form's twelve steps by name.
  planOkSmall Z          does the planner take the public files: ASKED FIRST
  frontSmall Z           the further tests on the public files alone, by name (frontNamesSmall): the
    «one test on three public files» (ownSmallAtB) · sizes · ground · one sR serves both
    files.
                         EACH CAN SAY NO AT SOME PUBLIC FILES.
  byConstructionSmall Z  what holds by construction: NO TESTS (so classed by reading):
    «b ≤ K» AMONG THEM: K is made of the same dry
    data as b; a
                         carrier holds what a round SENDS and its nonce, not what is DRAWN
                           (OnBytes/Maker/Carrier.lean: Round): so b cannot be counted off a real
                           file's strings.
  itemMadeSmall          is sp's item made (its C6)
  stepsSmall Z O …       LPFD.Small.stepsFSmallPlan
    (Johnson/Top/Fire/Code/Vals/FastSmall.lean;
    fastStepsT (Johnson/PV/KitWholeS.lean), WHICH IS fastSteps (VerifyVFastStepsDS.lean in
    Johnson/Top/Fire/Code/; fastStepsT_eq: no premise; ckPT_eq) WITH THE KIT ckPT .two, MADE FOR A
    RUN, IN ckP .two's PLACE IN THE TWO GREAT ARMS, at the fast family F := famPrepQ pr bk O ‹the
    two hints›, WHICH IS famSQ … bk O pr (famBound_eq := rfl, in FastSmall.lean); pr, bk AND F EACH
    BOUND ONCE, OUTSIDE WHAT IS CALLED A QUERY AT A TIME; bk THE REAL ONE; and hash := hashOf O)
    WITH ALL OF m's EIGHT ARGUMENTS, DK, DP AND K MADE INSIDE, OF Z AND O
                         ALONE, AND THE THREE cfg (fT's, e's, fB's) OVERWRITTEN WITH THE PUBLIC c.
                           none where c has not 32 bytes.
  armTSmall | armLSmall | armBSmall    one arm alone, by FastSmall.lean's names, at the same
    arguments. none where c has not 32 bytes, or the arm's string is not laid (at the proof's: or no
    instance is built).
  wholeSmall             LPFD.Small.fastFSmallPlan there.
  Turn, …With            for controls alone: a turn of dK, dP or pdL. The plain names are the …With
    at no turn.
WHAT COMES FROM WHERE: A THIRD SOURCE BESIDE THE FILES: CONSTANTS OF THE SMALL SIZE TYPED IN THE
  LIBRARY (smallRecordGround · srS · srD · sizesSmall · dsSmall …). FROM Z ALONE: every letter of
  FastSmall.lean's value; DK, DP; K; c; the seven; dK, dP, pdL; sR; sp; linkF; the three cfg. THE
  CALLER's: O · commitment, prompt, output, aux (THE USER's) · cm,
rcd, copy, fT, e, fB (THE PROVER's SIDE).
STAND-INS AND READINGS THAT ARE LAID INSIDE, TO BE NAMED BY WHOEVER PRINTS (standInsSmall; ELEVEN):
  runK, runP · DK, DP · p · seed · K · num · sp · dec, ds, xs · linkF · c and the seven (made at the
  fixed hash). okS AND bk HAVE LEFT THE LIST: okS := PV.OkOwn.okOwnS (isOwn, Johnson/Flat/
  FrontSetOwnAt.lean: «the reply is 0», asked of the request's EARLY part: the chain maps xin by the
  carrier's early) · bk := W4M.shoutAt (PV.MSmall.bkSV …), laid inside FastSmall.lean's value.
THE TYPING's TESTS STAND INSIDE THE TERM: fastSteps | fastF call File.toBPrfAt and assembleW
  themselves (piTE | piLE | piBE, Johnson/Top/Fire/Code/VerifyVFastDS.lean): a carrier of which no
  string is laid gives laidT | laidL | laidB = false.
No theorem. No soundness.
  OVER FastSmall.lean (ds · xs · dec letters of its …At). ds AND
  xs ARE NO LETTERS HERE: THE BODIES LAY PV.EntryFive.dsS | xsS: ds: Johnson/PV/LinkSmall.lean's
  linkFS takes an equivalence to the link's shape AT dsSmall: at a free ds «Equiv.refl» does not
  type (Lean's word) · xs: never tried as a
  letter: SO WHOEVER HAS A DESCRIPTION's OWN ROUNDS' DATA FOR THE LINK HOLDS THEM BY VALUE AGAINST
  dsS IN A ROW; linkF's law and K (made of dsS's rounds) then stand as
  they are. THE FIVE BODIES STAND ONCE AT TWO LETTERS MORE: …SmallAllWith τ Z O c seven DK DP runK
  runP dec …; …SmallAtWith ARE THESE AT DK := dkLanded Z, dec := PV.EntryFive.decS:
  BY UNFOLDING.
BENEATH THEM: THE FIVE BODIES AT TWO LETTERS MORE THAN …SmallRunWith: …SmallAtWith τ Z O c
  seven DP runK runP … → FastSmall.lean's GENERAL …At (GS Z) c …; …SmallRunWith ARE
  THESE AT (cOf Z) (sevenOf Z) (FastSmall.lean's …SmallRun Z BY UNFOLDING: cOf_is_cB := rfl);
  …SmallThruWith: THESE AT c := PV.Head.cThru O Z, seven := PV.Head.sevenThru O smallRecordGround Z
  c (Johnson/PV/HeadCore.lean: the two public readings THROUGH THE O THAT IS HANDED IN) ·
  thruRowsSmall · standInsAt.
BENEATH THESE: THE FIVE BODIES IN GENERAL FORMS …SmallRunWith τ Z O DP
  runK runP …, AND THE FIVE NAMES …SmallWith ARE THESE AT THE «Plan» LETTERS:
  THE SAME TERMS BY UNFOLDING (…SmallPlan Z DK DP := …At (GS Z) (cB Z) DK DP (runKPlanS …)
  (runPPlanS …) = …SmallRun at these). ALSO: KAt ·
  byConstructionAt · runKPlan · runPPlan.
runKSmall | runPSmall (Johnson/Flat/WireAt.lean) ARE okAt a (dry…) && decide…; THE «Plan» FORMS ARE
  THE SECOND HALVES ALONE. THE DROPPED CONJUNCTS ARE GuardsPassSmall, WHICH ownSmallAt_gives
  DRAWS FROM ownSmallAtB: frontSmall's FIRST ROW: IT GATES, BUT IN FRONT OF THE TERM; AND
  dvESmallPlan LAYS THE
SAME DECISIONS ON THE STATEMENT's SIDE: SO fastF_reads_is_verifyV SPEAKS HERE OF A verifyV WITHOUT
  THAT CONJUNCT.


-/
import Johnson.Top.Fire.Code.Vals.FastSmall
import Johnson.Top.Fire.Code.PvFront
import Johnson.PV.RunArgsSmall
import Johnson.PV.OkOwn
import Johnson.PV.LinkSmall
import Johnson.PV.HeadCore
import Johnson.PV.DataCond
import OnBytes.Maker.DataLog

set_option autoImplicit false

namespace PV.RunPure.Small
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutDS (FileIn EntryIn FastSteps)
open OnBytes.Flat (RecSmall)
open _root_.Iop (Dig)

/-- The configuration's digest of the three public files. -/
def cOf (Z : OnBytes.K.Pub) : ByteArray := PV.Front.cBytes Z

/-- It is LPFD.Small.cB, by unfolding. -/
theorem cOf_is_cB (Z : OnBytes.K.Pub) : cOf Z = LPFD.Small.cB Z := rfl

/-- The seven further digests. -/
def sevenOf (Z : OnBytes.K.Pub) : List ByteArray := PV.Front.moreBytes OnBytes.Tie.smallRecordGround
    Z (cOf Z)

/-- The number of blocks but one, at the two whole files' data. -/
abbrev KAll (DK DP : OnBytes.Maker.WholeD) : ℕ := LPFD.Small.KS DK DP

/-- The same at the key file's dry run's data. -/
abbrev KAt (Z : OnBytes.K.Pub) (DP : OnBytes.Maker.WholeD) : ℕ := KAll (LPFD.Small.dkLanded Z) DP

/-- The same at the dry run's data. -/
abbrev KSmallOf (Z : OnBytes.K.Pub) : ℕ := KAt Z (LPFD.Small.dpLanded Z)

/-- The bytes of the request tree's salt. -/
def sRSmall (Z : OnBytes.K.Pub) : ℕ := (LPFD.Small.GS Z).k.oneTime.binding.saltBytes

def sameBytes (a b : ByteArray) : Bool := a.data == b.data

/-- Does the planner take the three public files. ASKED FIRST: where it does not, FastSmall.lean's
  value falls to a stand-in of which nothing is assumed, and nothing further is evaluated. -/
def planOkSmall (Z : OnBytes.K.Pub) : Bool := LPFD.Small.planOk Z

/-- The names of `frontSmall`'s rows. -/
def frontNamesSmall : List String :=
  ["the-one-test-on-the-public-files", "public-sizes", "public-ground-fits", "one-sR-serves-both"]

/-- **The further tests on the public files alone**, behind `planOkSmall`. EACH CAN SAY NO AT SOME
  PUBLIC FILES. The first: ownSmallAtB (Johnson/Top/ArmsAtFilesSmall.lean:301): the
  parameter
file says the lines of the fixed public parameters; the makers' tests on the dry runs pass (else DK,
  DP fall in silence to empty data); the two tests on the numbers of blocks. -/
def frontSmall (Z : OnBytes.K.Pub) : List (String × Bool) :=
  let G₀ := OnBytes.Tie.smallRecordGround
  let c := cOf Z
  frontNamesSmall.zip
    [OnBytes.K.ArmsAtFiles.ownSmallAtB Z, PV.Front.sizesB G₀ Z c, PV.Front.groundFitsB G₀ Z c,
      sRSmall Z == (LPFD.Small.GS Z).c.first.binding.saltBytes]

/-- **WHAT HOLDS BY CONSTRUCTION: NO TESTS**: each says yes at every input (or at every input at
  which the planner says yes): TO BE PRINTED AS «by construction», NEVER COUNTED AS A TEST PASSED.
  They gate all the
same: a no would be a fault of ours. -/
def byConstructionAll (Z : OnBytes.K.Pub) (DK DP : OnBytes.Maker.WholeD) : List (String × Bool) :=
  [("every round's blocks, and the seed's, fit K: K IS the greater of the most that a round of DK, \
      ds, DP asks and 94",
      PV.Front.blocksFitSmallB DK DP (KAll DK DP)),
    ("the plan's own two cfg are c: the planner makes them of the same three files", sameBytes (cOf
        Z) (LPFD.Small.GS Z).k.oneTime.given.cfg && sameBytes (cOf Z) (LPFD.Small.GS
        Z).c.first.given.cfg),
    ("c has 32 bytes; the further digests are seven", (cOf Z).size == 32 && (sevenOf Z).length ==
        7)]

/-- The same at the key file's dry run's data. -/
def byConstructionAt (Z : OnBytes.K.Pub) (DP : OnBytes.Maker.WholeD) : List (String × Bool) :=
    byConstructionAll Z (LPFD.Small.dkLanded Z) DP

/-- The same at both dry runs' data. -/
def byConstructionSmall (Z : OnBytes.K.Pub) : List (String × Bool) := byConstructionAt Z
    (LPFD.Small.dpLanded Z)

/-- Is the value of the statement's item «request» made (sp falls to no byte in silence where it is
  not). none: no instance is built. -/
def itemMadeSmall (Z : OnBytes.K.Pub) (prompt output aux : List Token) : Option Bool :=
  (PV.Front.buildSmall' (prompt, output) aux).map fun x => (PV.RunArgs.spS Z.pol Z.KL x).1.size != 0

/-- **Is the instance that is built at the further tokens aux′ the one that is built at aux?** BY
  THE REQUEST's TWO STRINGS (sp): the law apartS (declared nowhere in this library): on okOwn's
  yeses they are one to one in the instance. none: one of the two is not built. WHY: the builder
  takes the window's token at t as
(prompt ++ output ++ padding).getD t tokenZero and never tests the padding's length
  (VerifiableInference/RequestOfTokens.lean:42-53, by reading): SO A
  TURN OF THE FURTHER TOKENS MAY LEAVE THE INSTANCE AS IT IS: a second spelling of the same proof,
  no altered input: WHICH OF THE TWO IT
IS HANGS ON WHETHER THE WINDOW IS FULL (at both stored examples it is) AND IS THEREFORE COMPUTED,
  NOT TYPED. -/
def sameInstanceSmall (Z : OnBytes.K.Pub) (prompt output aux aux' : List Token) : Option Bool :=
  match PV.Front.buildSmall' (prompt, output) aux, PV.Front.buildSmall' (prompt, output) aux' with
  | some x, some y =>
    let a := PV.RunArgs.spS Z.pol Z.KL x
    let b := PV.RunArgs.spS Z.pol Z.KL y
    some (a.1.data == b.1.data && a.2.data == b.2.data)
  | _, _ => none

/-- Where the two instances part («whether the instance's
  window differs at that position»): is the request's first string (the summary) the same · is its
  second (the request file's own words: T tokens, r, e) the same · the first 32-bit word at which
  the second
strings part (from 0: below T it is the token's place in the window); none: they do not part, or
  their lengths do. -/
def whereInstancesPartSmall (Z : OnBytes.K.Pub) (prompt output aux aux' : List Token) : Option (Bool
    × Bool × Option Nat) :=
  match PV.Front.buildSmall' (prompt, output) aux, PV.Front.buildSmall' (prompt, output) aux' with
  | some x, some y =>
    let a := PV.RunArgs.spS Z.pol Z.KL x
    let b := PV.RunArgs.spS Z.pol Z.KL y
    let at_ := if a.2.size != b.2.size then none else ((List.range a.2.size).find? fun i => a.2.get!
        i != b.2.get! i).map (· / 4)
    some (a.1.data == b.1.data, a.2.data == b.2.data, at_)
  | _, _ => none

/-- The stand-ins that are laid inside: letter · what · whose. thru: c and the seven digests are
  read through O. -/
def standInsAt (thru : Bool) : List (String × String × String) :=
  [("runK", "runKPlanS G DK: THE OLDER LEAN PROGRAM's DECISION decideKey, the numbers of trees \
      DK's; ITS CONJUNCT okAt (the makers' tests on the dry run) HAS LEFT THE TERM: asked in front \
      alone", "the value's keeper's, declared"),
    ("runP", "runPPlanS G DP: THE OLDER LEAN PROGRAM's DECISION decideProof, the numbers of trees \
        DP's; ITS CONJUNCT okAt (the makers' tests on the dry run) HAS LEFT THE TERM: asked in \
        front alone", "the value's keeper's, declared"),
    ("DK,DP", "dataKSmall G | dataPSmall G: the rounds' data of the older program's dry runs",
        "the value's keeper's, declared"),
    ("dec,ds,xs", "decS: THE OLDER LEAN PROGRAM's DECISION ON THE LINK: IT DECIDES armL · dsS: the \
        library's written rounds' data (OnBytes/Flat/LinkSibAt.lean:153) · xsS: the stored \
        openings as the value lays them", "PV's, declared"),
    (if thru then ("plan,item",
        "sp's ITEM HOLDS FIVE DIGESTS UNDER THE FORMAT's EARLIER HASH: NOT THROUGH O: they enter \
        the proof file's first query's string · in the plan that hash only gates: three tests on \
        tables (three of its seven uses evaluated: idle; four read)",
        "PV's and the value's keeper's")
     else ("c,seven", "c, the seven further digests (so dK, dP, pdL), the plan's data and sp's \
         item ARE MADE AT THE FORMAT's FIXED HASH, NOT THROUGH O",
         "PV's and the value's keeper's"))]

/-- The declared lines where the two whole files' rounds' data are MADE OF THE PLAN (dkPlan |
  dpPlan, Johnson/Top/Fire/Code/Vals/DvSmall.lean), of a list of declared lines. -/
def standInsPlanData (base : List (String × String × String)) : List (String × String × String) :=
  base.map fun s =>
    if s.1 == "DK,DP" then ("DK,DP",
        "dkPlan | dpPlan: the rounds' data MADE OF THE PLAN (the landed dataKAt | dataPAt at one \
        madeOf of the three public files): NO DRY RUN", "the value's keeper's, declared")
    else s

/-- Four rows (PV.DataCond.condRows): the one-to-one coding's four premises, evaluated AT WHATEVER
  IS LAID. -/
def codingRows (DK DP : OnBytes.Maker.WholeD) (c : ByteArray) : List (String × Bool) :=
  PV.DataCond.condRows OnBytes.Slice.srS.P.T.a DK DP (KAll DK DP) c

/-- Two rows more: every written round's positions have at most 64 bits:
  whole_sound_typed's premise in its very shape (OnBytes.Maker.DataLog.logD_gives), AT WHATEVER IS
  LAID. -/
def readingRows (DK DP : OnBytes.Maker.WholeD) : List (String × Bool) :=
    OnBytes.Maker.DataLog.logRows DK DP

/-- **WHAT HAS LEFT «STAND-IN» AND STAYS IN THE PRINT UNDER A SECOND HEADING**, so that nothing
  vanishes unseen: a value with a named law, or a reading of
  which no law is asked.
The fields: letter · what is laid · were the named laws in the library's
  build («landed») or not («scratch») · the sentence, in pieces of at most 125
  signs. NONE IS THEREBY DONE: a law on a value is not its place in a D. -/
def valuesSmall : List (String × String × String × List String) :=
  [("linkF", "linkFS", "scratch, kernel-checked, off the trunk",
      ["A VALUE; ITS LAW: linkS_is | linkF_is: it is the landed linkAt's put at this carrier; no \
      premise but c's 32 bytes",
      "linkLaws_any pays what the one-to-one coding asks of it; its one premise, on the label, is \
          paid inside mSOne | mFOne"]),
    ("sp", "spS", "scratch, kernel-checked, off the trunk",
        ["A VALUE; ITS LAW: apartS | apartF: on okOwn's yeses its two strings are one to one, by \
        the request file's bytes alone",
      "its item: see plan,item"]),
    ("seed", "recSeedK", "landed",
        ["A VALUE; ITS LAW: the landed entrySmall_seedLawK | entryFull_seedLawK: for every word, \
        fixed before the blocks:",
      "over K uniform digests the seed is a collision seed with probability at most 2^-128: the \
          shape of FlatTwo.seedLaw"]),
    ("num", "numCopy", "landed (words of the landed text; no law)",
        ["A READING UNDER NO LAW: the landed SeedW.num: «A letter; no law» (Seeds.lean:81-83)",
      "no proof leans on its test, which can only make the verifier refuse (Cms.lean:61)"]),
    ("K", "LPFD.Small.KS DK DP", "scratch, kernel-checked, off the trunk",
        ["A VALUE; ITS LAW: KS_serves | KS_least: the least number that serves every round of the \
        three files' data and the seed",
      "the floor is the seed's need less one (KS_is)",
      "(K1) not walked: whether the theorem's hypothesis on the wires asks more of K",
      "the entry's rounds that a run lays (dsS | dsF) have the library's rounds' entries and \
          kinds: dsS_rounds; KS_entry_run"]),
    ("p", "pAt (saltG G)", "landed (a walk of the landed text; no law)",
        ["A READING UNDER NO LAW: the main theorem on soundness is general in p: no named \
        hypothesis constrains it",
      "its error does not read p; the verifier's strict tests on the two salts' lengths (p.sMT, \
          p.sFS) read it alone",
      "hiding's statements were not walked for p"])]

/-- The same with c and the seven at the fixed hash. -/
def standInsSmall : List (String × String × String) := standInsAt false

/-- For controls alone: a turn of the key file's three digests, the proof file's three, the entry's
  one. -/
structure Turn where
  dK : OnBytes.Maker.Page.Pd3 → OnBytes.Maker.Page.Pd3 := id
  dP : OnBytes.Maker.Page.Pd3 → OnBytes.Maker.Page.Pd3 := id
  pdL : Dig 256 → Dig 256 := id

/-! ## THE GENERAL FORMS: THE FIVE BODIES, ONCE: letters: c, the digest of the three public files ·
  seven, the seven further digests · DK, DP, the two whole files' data · runK, runP, their decisions
  · dec, the link's decision (FastSmall.lean's …At (GS Z) c DK DP runK runP ds xs dec …;
  ds xs := dsS xsS HERE) -/

variable (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) (c : ByteArray) (seven : List
    ByteArray) (DK DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP : LPFD.Small.RunPS)
  (dec : RecSmall × RecSmall → _root_.Fmt.View → Bool)

/-- **The twelve steps.** -/
def stepsSmallAllWith (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256) (rcd
    : RecSmall) (copy : ℕ)
    (fT : FileIn) (e : EntryIn) (fB : FileIn) : Option FastSteps :=
  if hc : c.size = 32 then
    some (LPFD.Small.stepsFAt (LPFD.Small.GS Z) c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS
        dec (_root_.Fmt.HO O) (PV.RunArgs.spS Z.pol Z.KL)
      PV.OkOwn.okOwnS (sRSmall Z)
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      commitment prompt output aux cm rcd copy { fT with cfg := c } { e with cfg := c } { fB with
          cfg := c })
  else none

/-- The whole fast form, one Bool. -/
def wholeSmallAllWith (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256) (rcd
    : RecSmall) (copy : ℕ)
    (fT : FileIn) (e : EntryIn) (fB : FileIn) : Option Bool :=
  if hc : c.size = 32 then
    some (LPFD.Small.fastFAt (LPFD.Small.GS Z) c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS
        dec (_root_.Fmt.HO O) (PV.RunArgs.spS Z.pol Z.KL)
      PV.OkOwn.okOwnS (sRSmall Z)
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      commitment prompt output aux cm rcd copy { fT with cfg := c } { e with cfg := c } { fB with
          cfg := c })
  else none

/-- The key's arm alone. -/
def armTSmallAllWith (cm : Dig 256) (rcd : RecSmall) (fT : FileIn) : Option Bool :=
  if hc : c.size = 32 then
    LPFD.Small.armTAt (LPFD.Small.GS Z) c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS dec
        (_root_.Fmt.HO O) (PV.RunArgs.spS Z.pol Z.KL)
      PV.OkOwn.okOwnS (sRSmall Z)
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      cm rcd { fT with cfg := c }
  else none

/-- The entry's arm alone. -/
def armLSmallAllWith (cm : Dig 256) (rcd : RecSmall) (e : EntryIn) : Option Bool :=
  if hc : c.size = 32 then
    LPFD.Small.armLAt (LPFD.Small.GS Z) c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS dec
        (_root_.Fmt.HO O) (PV.RunArgs.spS Z.pol Z.KL)
      PV.OkOwn.okOwnS (sRSmall Z)
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      cm rcd { e with cfg := c }
  else none

/-- The proof's arm alone. -/
def armBSmallAllWith (prompt output aux : List Token) (e : EntryIn) (fB : FileIn) : Option Bool :=
  if hc : c.size = 32 then
    LPFD.Small.armBAt (LPFD.Small.GS Z) c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS dec
        (_root_.Fmt.HO O) (PV.RunArgs.spS Z.pol Z.KL)
      PV.OkOwn.okOwnS (sRSmall Z)
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      prompt output aux { e with cfg := c } { fB with cfg := c }
  else none

end PV.RunPure.Small

namespace PV.RunPure.Small

/-! ## THE SAME FIVE BODIES WITH THE PLAN's VALUES A LETTER TOO (for the hash's line; the
  full size's twin: RunPureFull.lean): G IN LPFD.Small.GS Z's PLACE, AND G.k.oneTime.binding.saltBytes IN sRSmall Z's. MADE OF THE FIVE
  TEXTS ABOVE BY PROGRAM: two substitutions and the name. WHY A SECOND TEXT AND NOT «…AllWith := …AllAt τ (GS Z) Z …»: proofs that say
  «unfold …AllWith at h» and then split on the «if» (Seam10S.lean [not in this library]) would meet the name …AllAt there. SO THE FIVE ABOVE KEEP THEIR
  BYTES, AND FIVE EQUATIONS, EACH rfl, TIE THEM: …AllWith_at. sp, THE REQUEST's TWO STRINGS, IS A LETTER TOO, IN PV.RunArgs.spS Z.pol Z.KL's PLACE:
  that is Z's one use in the five bodies, SO Z IS NO LETTER OF THE …AllAt FORMS. -/

section At
open VerifiableInference VerifiableInference.OnPublicFiles
open VerifiableInference.OnPublicFiles.SlotsBehindCutDS (FileIn EntryIn FastSteps)
open OnBytes.Flat (RecSmall)
open _root_.Iop (Dig)

variable (τ : Turn) (G : OnBytes.Flat.FilesParameters LPFD.Small.XS RecSmall) (sp : LPFD.Small.XS → ByteArray × ByteArray) (O : ByteArray → ByteArray) (c : ByteArray)
  (seven : List ByteArray) (DK DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP : LPFD.Small.RunPS)
  (dec : RecSmall × RecSmall → _root_.Fmt.View → Bool)

/-- **The twelve steps.** At the plan's values G. -/
def stepsSmallAllAt (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256) (rcd
    : RecSmall) (copy : ℕ)
    (fT : FileIn) (e : EntryIn) (fB : FileIn) : Option FastSteps :=
  if hc : c.size = 32 then
    some (LPFD.Small.stepsFAt G c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS
        dec (_root_.Fmt.HO O) sp
      PV.OkOwn.okOwnS G.k.oneTime.binding.saltBytes
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      commitment prompt output aux cm rcd copy { fT with cfg := c } { e with cfg := c } { fB with
          cfg := c })
  else none

/-- The whole fast form, one Bool. At the plan's values G. -/
def wholeSmallAllAt (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256) (rcd
    : RecSmall) (copy : ℕ)
    (fT : FileIn) (e : EntryIn) (fB : FileIn) : Option Bool :=
  if hc : c.size = 32 then
    some (LPFD.Small.fastFAt G c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS
        dec (_root_.Fmt.HO O) sp
      PV.OkOwn.okOwnS G.k.oneTime.binding.saltBytes
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      commitment prompt output aux cm rcd copy { fT with cfg := c } { e with cfg := c } { fB with
          cfg := c })
  else none

/-- The key's arm alone. At the plan's values G. -/
def armTSmallAllAt (cm : Dig 256) (rcd : RecSmall) (fT : FileIn) : Option Bool :=
  if hc : c.size = 32 then
    LPFD.Small.armTAt G c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS dec
        (_root_.Fmt.HO O) sp
      PV.OkOwn.okOwnS G.k.oneTime.binding.saltBytes
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      cm rcd { fT with cfg := c }
  else none

/-- The entry's arm alone. At the plan's values G. -/
def armLSmallAllAt (cm : Dig 256) (rcd : RecSmall) (e : EntryIn) : Option Bool :=
  if hc : c.size = 32 then
    LPFD.Small.armLAt G c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS dec
        (_root_.Fmt.HO O) sp
      PV.OkOwn.okOwnS G.k.oneTime.binding.saltBytes
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      cm rcd { e with cfg := c }
  else none

/-- The proof's arm alone. At the plan's values G. -/
def armBSmallAllAt (prompt output aux : List Token) (e : EntryIn) (fB : FileIn) : Option Bool :=
  if hc : c.size = 32 then
    LPFD.Small.armBAt G c DK DP runK runP PV.EntryFive.dsS PV.EntryFive.xsS dec
        (_root_.Fmt.HO O) sp
      PV.OkOwn.okOwnS G.k.oneTime.binding.saltBytes
      (W4M.linkFS _ (Equiv.refl _) (KAll DK DP) c hc (τ.pdL (PV.RunArgs.pdLOf seven)))
      (τ.dK (PV.RunArgs.pd3At seven 4)) (τ.dP (PV.RunArgs.pd3At seven 1)) O
      prompt output aux { e with cfg := c } { fB with cfg := c }
  else none

variable (Z : OnBytes.K.Pub)

/-- The form without the letter is this one at the planner's own values and the request's two strings at the format's own second hash. -/
theorem stepsSmallAllWith_at (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256) (rcd : RecSmall) (copy : ℕ)
    (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    stepsSmallAllWith τ Z O c seven DK DP runK runP dec commitment prompt output aux cm rcd copy fT e fB =
      stepsSmallAllAt τ (LPFD.Small.GS Z) (PV.RunArgs.spS Z.pol Z.KL) O c seven DK DP runK runP dec commitment prompt output aux cm rcd copy fT e fB := rfl

/-- The form without the letter is this one at the planner's own values and the request's two strings at the format's own second hash. -/
theorem wholeSmallAllWith_at (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256) (rcd : RecSmall) (copy : ℕ)
    (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    wholeSmallAllWith τ Z O c seven DK DP runK runP dec commitment prompt output aux cm rcd copy fT e fB =
      wholeSmallAllAt τ (LPFD.Small.GS Z) (PV.RunArgs.spS Z.pol Z.KL) O c seven DK DP runK runP dec commitment prompt output aux cm rcd copy fT e fB := rfl

/-- The form without the letter is this one at the planner's own values and the request's two strings at the format's own second hash. -/
theorem armTSmallAllWith_at (cm : Dig 256) (rcd : RecSmall) (fT : FileIn) :
    armTSmallAllWith τ Z O c seven DK DP runK runP dec cm rcd fT =
      armTSmallAllAt τ (LPFD.Small.GS Z) (PV.RunArgs.spS Z.pol Z.KL) O c seven DK DP runK runP dec cm rcd fT := rfl

/-- The form without the letter is this one at the planner's own values and the request's two strings at the format's own second hash. -/
theorem armLSmallAllWith_at (cm : Dig 256) (rcd : RecSmall) (e : EntryIn) :
    armLSmallAllWith τ Z O c seven DK DP runK runP dec cm rcd e =
      armLSmallAllAt τ (LPFD.Small.GS Z) (PV.RunArgs.spS Z.pol Z.KL) O c seven DK DP runK runP dec cm rcd e := rfl

/-- The form without the letter is this one at the planner's own values and the request's two strings at the format's own second hash. -/
theorem armBSmallAllWith_at (prompt output aux : List Token) (e : EntryIn) (fB : FileIn) :
    armBSmallAllWith τ Z O c seven DK DP runK runP dec prompt output aux e fB =
      armBSmallAllAt τ (LPFD.Small.GS Z) (PV.RunArgs.spS Z.pol Z.KL) O c seven DK DP runK runP dec prompt output aux e fB := rfl

end At

/-! ## DK := the key file's dry run's data; dec := decS, `verify-on-bytes`'s DECISION ON THE LINK:
  THE FIVE GENERAL FORMS …SmallAtWith, BY UNFOLDING -/

def stepsSmallAtWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) (c : ByteArray)
    (seven : List ByteArray) (DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP :
    LPFD.Small.RunPS) :=
  stepsSmallAllWith τ Z O c seven (LPFD.Small.dkLanded Z) DP runK runP PV.EntryFive.decS
def wholeSmallAtWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) (c : ByteArray)
    (seven : List ByteArray) (DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP :
    LPFD.Small.RunPS) :=
  wholeSmallAllWith τ Z O c seven (LPFD.Small.dkLanded Z) DP runK runP PV.EntryFive.decS
def armTSmallAtWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) (c : ByteArray)
    (seven : List ByteArray) (DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP :
    LPFD.Small.RunPS) :=
  armTSmallAllWith τ Z O c seven (LPFD.Small.dkLanded Z) DP runK runP PV.EntryFive.decS
def armLSmallAtWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) (c : ByteArray)
    (seven : List ByteArray) (DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP :
    LPFD.Small.RunPS) :=
  armLSmallAllWith τ Z O c seven (LPFD.Small.dkLanded Z) DP runK runP PV.EntryFive.decS
def armBSmallAtWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) (c : ByteArray)
    (seven : List ByteArray) (DP : OnBytes.Maker.WholeD) (runK : LPFD.Small.RunKS) (runP :
    LPFD.Small.RunPS) :=
  armBSmallAllWith τ Z O c seven (LPFD.Small.dkLanded Z) DP runK runP PV.EntryFive.decS

/-! ## c AND THE SEVEN AT THE FORMAT's FIXED HASH: THE FIVE NAMES …SmallRunWith: FastSmall.lean's
  …SmallRun Z by unfolding (cOf_is_cB) -/

def stepsSmallRunWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := stepsSmallAtWith
    τ Z O (cOf Z) (sevenOf Z)
def wholeSmallRunWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := wholeSmallAtWith
    τ Z O (cOf Z) (sevenOf Z)
def armTSmallRunWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armTSmallAtWith τ
    Z O (cOf Z) (sevenOf Z)
def armLSmallRunWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armLSmallAtWith τ
    Z O (cOf Z) (sevenOf Z)
def armBSmallRunWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armBSmallAtWith τ
    Z O (cOf Z) (sevenOf Z)

/-! ## c AND THE SEVEN THROUGH THE O THAT IS HANDED IN (PV.Head.cThru |
  sevenThru: what the eight public strings are answered at hashOf O: cThru_hash | sevenThru_hash) -/

/-- c through O. -/
def cThruOf (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) : ByteArray := PV.Head.cThru O Z
/-- The seven through O, at c through O. -/
def sevenThruOf (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) : List ByteArray :=
    PV.Head.sevenThru O OnBytes.Tie.smallRecordGround Z (cThruOf Z O)

def stepsSmallThruWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) :=
    stepsSmallAtWith τ Z O (cThruOf Z O) (sevenThruOf Z O)
def wholeSmallThruWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) :=
    wholeSmallAtWith τ Z O (cThruOf Z O) (sevenThruOf Z O)
def armTSmallThruWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armTSmallAtWith
    τ Z O (cThruOf Z O) (sevenThruOf Z O)
def armLSmallThruWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armLSmallAtWith
    τ Z O (cThruOf Z O) (sevenThruOf Z O)
def armBSmallThruWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armBSmallAtWith
    τ Z O (cThruOf Z O) (sevenThruOf Z O)

/-- Two rows: through O the readings are today's (at O := the format's hash they
  are due yes; at O turned at one public string, no). -/
def thruRowsSmall (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) : List (String × Bool) :=
  [("c-through-O-is-today's", sameBytes (cThruOf Z O) (cOf Z)),
    ("the-seven-through-O-are-today's", (sevenThruOf Z O).length == (sevenOf Z).length &&
        ((sevenThruOf Z O).zip (sevenOf Z)).all fun x => sameBytes x.1 x.2)]

/-! ## AT THE «Plan» LETTERS: the dry run's data; `verify-on-bytes`'s two decisions without their
  dry runs: FastSmall.lean's …SmallPlan by unfolding. -/

def runKPlan (Z : OnBytes.K.Pub) : LPFD.Small.RunKS := LPFD.Small.runKPlanS (LPFD.Small.GS Z)
    (LPFD.Small.dkLanded Z)
def runPPlan (Z : OnBytes.K.Pub) : LPFD.Small.RunPS := LPFD.Small.runPPlanS (LPFD.Small.GS Z)
    (LPFD.Small.dpLanded Z)

def stepsSmallWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := stepsSmallRunWith τ
    Z O (LPFD.Small.dpLanded Z) (runKPlan Z) (runPPlan Z)
def wholeSmallWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := wholeSmallRunWith τ
    Z O (LPFD.Small.dpLanded Z) (runKPlan Z) (runPPlan Z)
def armTSmallWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armTSmallRunWith τ Z
    O (LPFD.Small.dpLanded Z) (runKPlan Z) (runPPlan Z)
def armLSmallWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armLSmallRunWith τ Z
    O (LPFD.Small.dpLanded Z) (runKPlan Z) (runPPlan Z)
def armBSmallWith (τ : Turn) (Z : OnBytes.K.Pub) (O : ByteArray → ByteArray) := armBSmallRunWith τ Z
    O (LPFD.Small.dpLanded Z) (runKPlan Z) (runPPlan Z)

/-- **What a command and a file of evaluations (not named here) call.** -/
def stepsSmall := stepsSmallWith {}
def wholeSmall := wholeSmallWith {}
def armTSmall := armTSmallWith {}
def armLSmall := armLSmallWith {}
def armBSmall := armBSmallWith {}

end PV.RunPure.Small
