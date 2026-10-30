-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/PricedEntryLit.lean: the priced plan of an entry file's chain, at the full size and at the
small example's, as written values, for statements that Lean's kernel is to evaluate. Data alone:
definitions without a function; no theorem. In the form of Johnson/G/PricedKeyLit.lean (the key
file's three priced plans); here every round stands once, in the
plan's order: no
runs are needed (42 and 25 rounds).
Main names:
  `pricedEntrySetFull`, `pricedEntrySetSmall`: the settings.
  `pricedEntryRoundsFull`, `pricedEntryRoundsSmall`: the rounds: all seven fields of `PlanRound`.
  `pricedEntryFull`, `pricedEntrySmall`: the plans (`OnBytes.Params.Planned`).
Whence the numbers: a program wrote this file from a print that Lean's evaluator made, field by
field, of `finishHeld recordSet .once (linkPlan ...)` at the library's typed link, table and test
(OnBytes/Params/EntryStagesRecord.lean) and of the like at the small example's typed values: closed
terms: no file was read.
Limits: this file by itself holds the written values against nothing:
`entry_written` (Johnson/Goal/Written/MadeOfSized.lean) holds `pricedEntryFull` against what the
planner's routine returns at the written link, by Lean's kernel; `pricedEntrySmall`: no file does.
THE PLAN BEGINS WITH AN ENTRY UNDER THE NAME "RECORD" (the table's own sample): so it has one round
more than the chain's declared rounds. No round has `wordFault`. That an error bounds what its name
says is claimed nowhere here. Nothing on soundness.

-/
import OnBytes.Params.Planner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes.Params

/-- The setting of the entry file's plan at the full size. -/
def pricedEntrySetFull : Setting :=
  { p := 18446744069414584321, degree := 3, target := 128, printed := true, rowsFactor := false,
    instances := 1, samples := 1, saltBytes := 40, nonceBytes := 8,
    positionBytes := 0, workField := ⟨0, 0, 0⟩, workSample := ⟨0, 0, 0⟩, workCloseness := ⟨0, 0, 0⟩,
    workQuery := ⟨20, 28, 32⟩, workSmall := ⟨0, 0, 0⟩ }

/-- The priced rounds of the entry file's chain at the full size, in order. -/
def pricedEntryRoundsFull : List PlanRound := [
  ⟨⟨"RECORD", 1, 0, 0, 0, 0, 30, 1, 0, 0, 0, 0⟩,
    ⟨3755380325514963501249834132025331418367756793549814235138, -370⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"LINK point", 1, 0, 0, 0, 0, 11, 0, 0, 0, 0, 0⟩,
    ⟨5641398792174831251450983777434499364659277752246707779410, -320⟩, none, .closeness, .johnson,
    .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 30, 1, 0, 0, 0, 0⟩,
    ⟨5750426123444787861288808514663788734375627590123153047556, -366⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"SEND answer", 1, 0, 48, 0, 2, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0⟩, none, .zero, .johnson, .once, false⟩,
  ⟨⟨"LINK", 1, 32, 0, 0, 0, 0, 0, 124, 32, 0, 0⟩,
    ⟨4220767437209519005251666678818349608156700753922080498174, -289⟩, none, .query, .johnson,
    .once, false⟩,
  ⟨⟨"LINK phi", 1, 0, 0, 0, 0, 29, 0, 0, 0, 0, 0⟩,
    ⟨5688623451667637019644719158570916231373643426915694936067, -379⟩, none, .field, .johnson,
    .once, false⟩,
  ⟨⟨"BAT", 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 129⟩,
    ⟨4462627018118577317135081408878908422887944412494208958467, -370⟩, none, .field, .johnson,
    .once, false⟩,
  ⟨⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨4462627018118577317135081408878908422887944412494208958467, -377⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .field, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6163927232324311236243568214919051141665252357847992833725, -320⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 24, 1, 0, 0, 0, 0⟩,
    ⟨5168425023530204451145292883313415769743808109751640793092, -364⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"CS", 1, 32, 24, 0, 1, 1, 0, 97, 24, 0, 293⟩,
    ⟨5346164723177360757215104878677792444569279475676477302597, -288⟩, some ⟨(24, 4194304, 97),
    (13, 64, 97), .johnson, 182⟩, .query, .johnson, .once, false⟩,
  ⟨⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨3359230227924423584876407434156101395250815299514871578627, -375⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .field, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6160754878957107914315227371027059493617502141514163854436, -320⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6160754878957107914315227371027059493617502141514163854436, -320⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6160754341287662789480693035335150888125676273354427855504, -320⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6160754341287662789480693035335150888125676273354427855504, -320⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6160754341287662789480693035335150888125676273354427855504, -320⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 19, 1, 0, 0, 0, 0⟩,
    ⟨6103594510132582422857453967206902468113041159726717435908, -363⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"CS", 1, 32, 24, 0, 1, 1, 0, 49, 21, 0, 149⟩,
    ⟨4142193731250609984605699178772266745413990221110122944229, -289⟩, some ⟨(21, 131072, 49), (12,
    128, 49), .johnson, 182⟩, .query, .johnson, .once, false⟩,
  ⟨⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨5835743023693524183945875688533957168391927308646273253380, -375⟩, some ⟨(17, 8192, 49), (12,
    128, 49), .johnson, 318⟩, .field, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6182717028940346327430706340602975856483898385658083738248, -320⟩, some ⟨(17, 8192, 49), (12,
    128, 49), .johnson, 318⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6182717028940346327430706340602975856483898385658083738248, -320⟩, some ⟨(17, 8192, 49), (12,
    128, 49), .johnson, 318⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6182716995336006220893260908732031351230362905977620195368, -320⟩, some ⟨(17, 8192, 49), (12,
    128, 49), .johnson, 318⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6182716995336006220893260908732031351230362905977620195368, -320⟩, some ⟨(17, 8192, 49), (12,
    128, 49), .johnson, 318⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 15, 1, 0, 0, 0, 0⟩,
    ⟨3394369123507327817402133800786830762120126786342397555202, -361⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"CS", 1, 32, 24, 0, 1, 1, 0, 49, 17, 0, 149⟩,
    ⟨4223833885626869801730942374518104785043460714643564262347, -289⟩, some ⟨(17, 8192, 49), (12,
    128, 49), .johnson, 318⟩, .query, .johnson, .once, false⟩,
  ⟨⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨4934635645034965302601291942510331429154938533046481059844, -374⟩, some ⟨(13, 512, 50), (12,
    128, 50), .johnson, 570⟩, .field, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266961075204650660050565167301293367659931521758422174735, -320⟩, some ⟨(13, 512, 50), (12,
    128, 50), .johnson, 570⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266961075204650660050565167301293367659931521758422174735, -320⟩, some ⟨(13, 512, 50), (12,
    128, 50), .johnson, 570⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266961074441058644395824405862567829090272673509983123440, -320⟩, some ⟨(13, 512, 50), (12,
    128, 50), .johnson, 570⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266961074441058644395824405862567829090272673509983123440, -320⟩, some ⟨(13, 512, 50), (12,
    128, 50), .johnson, 570⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 11, 1, 0, 0, 0, 0⟩,
    ⟨4506015798149649508169211557364102136735133604176469360643, -362⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"CS", 1, 32, 24, 0, 1, 1, 0, 50, 13, 0, 152⟩,
    ⟨4207501897484987781006910233653396483850826100320976035792, -288⟩, some ⟨(13, 512, 50), (12,
    128, 50), .johnson, 570⟩, .query, .johnson, .once, false⟩,
  ⟨⟨"BASE lambda", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6240748493940257443590946103965774368380932782012698845664, -320⟩, some ⟨(14, 512, 40), (14,
    512, 40), .johnson, 348⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"BASE", 1, 32, 26496, 0, 0, 0, 0, 40, 14, 0, 0⟩,
    ⟨3820755601718385479001872769705778087334764665333536034250, -289⟩, some ⟨(14, 512, 40), (14,
    512, 40), .johnson, 348⟩, .query, .johnson, .once, false⟩]

/-- The entry file's priced plan at the full size. -/
def pricedEntryFull : Planned := { set := pricedEntrySetFull, rounds := pricedEntryRoundsFull }

/-- The setting of the entry file's plan at the small example's size. -/
def pricedEntrySetSmall : Setting :=
  { p := 18446744069414584321, degree := 3, target := 128, printed := true, rowsFactor := false,
    instances := 1, samples := 1, saltBytes := 40, nonceBytes := 8,
    positionBytes := 0, workField := ⟨0, 0, 0⟩, workSample := ⟨0, 0, 0⟩, workCloseness := ⟨0, 0, 0⟩,
    workQuery := ⟨20, 28, 32⟩, workSmall := ⟨0, 0, 0⟩ }

/-- The priced rounds of the entry file's chain at the small example's size, in order. -/
def pricedEntryRoundsSmall : List PlanRound := [
  ⟨⟨"RECORD", 1, 0, 0, 0, 0, 20, 1, 0, 0, 0, 0⟩,
    ⟨5912655143704453476220503744237291720752397332754121162756, -367⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"LINK point", 1, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0⟩,
    ⟨6241388434982496688645595337947643203339360964215992267446, -320⟩, none, .closeness, .johnson,
    .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 21, 1, 0, 0, 0, 0⟩,
    ⟨3476909123875143387766712409172925074446185764483121438722, -363⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"SEND answer", 1, 0, 48, 0, 2, 0, 0, 0, 0, 0, 0⟩, ⟨0, 0⟩, none, .zero, .johnson, .once, false⟩,
  ⟨⟨"LINK", 1, 32, 0, 0, 0, 0, 0, 102, 23, 0, 0⟩,
    ⟨3667813152673829402147699310937174383013098785673495372038, -288⟩, none, .query, .johnson,
    .once, false⟩,
  ⟨⟨"LINK phi", 1, 0, 0, 0, 0, 19, 0, 0, 0, 0, 0⟩,
    ⟨3727029157989141495629298759063703737796525003841317371906, -379⟩, none, .field, .johnson,
    .once, false⟩,
  ⟨⟨"BAT", 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 107⟩,
    ⟨4893641389288168618798625930255004918058697972251762622467, -369⟩, none, .field, .johnson,
    .once, false⟩,
  ⟨⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨5909302809706467766096453953515477636901069249511562412036, -376⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .field, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6257844412605998331574588729749920754458783955069895691692, -320⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6257844412605998331574588729749920754458783955069895691692, -320⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6257844412605998331574588729749920754458783955069895691692, -320⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6257844412605998331574588729749920754458783955069895691692, -320⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6257844412605998331574588729749920754458783955069895691692, -320⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6257844412605998331574588729749920754458783955069895691692, -320⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 17, 1, 0, 0, 0, 0⟩,
    ⟨3439686243876080627853602411479639407682689297336281595907, -362⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"CS", 1, 32, 24, 0, 1, 1, 0, 97, 17, 0, 293⟩,
    ⟨4420548765459220428152929839940714382111329560090417488941, -288⟩, some ⟨(17, 32768, 97), (13,
    64, 97), .johnson, 483⟩, .query, .johnson, .once, false⟩,
  ⟨⟨"FOLD epsilon", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨3285670441911480002725829169174580926741673358649582419971, -374⟩, some ⟨(14, 2048, 66), (12,
    128, 66), .johnson, 600⟩, .field, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266338447760574463805421126910206204836140139382553426669, -320⟩, some ⟨(14, 2048, 66), (12,
    128, 66), .johnson, 600⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266338447760574463805421126910206204836140139382553426669, -320⟩, some ⟨(14, 2048, 66), (12,
    128, 66), .johnson, 600⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266338447378741633756998272809526817829230935594973636093, -320⟩, some ⟨(14, 2048, 66), (12,
    128, 66), .johnson, 600⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"FOLD round", 1, 0, 48, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266338447378741633756998272809526817829230935594973636093, -320⟩, some ⟨(14, 2048, 66), (12,
    128, 66), .johnson, 600⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"SEND seed", 1, 0, 32, 1, 0, 13, 1, 0, 0, 0, 0⟩,
    ⟨5159529365814120941780403617219459111524033946004422393860, -363⟩, none, .sample, .johnson,
    .once, false⟩,
  ⟨⟨"CS", 1, 32, 24, 0, 1, 1, 0, 66, 14, 0, 200⟩,
    ⟨4911642851699224808260968642418534993311795336396889717297, -289⟩, some ⟨(14, 2048, 66), (12,
    128, 66), .johnson, 600⟩, .query, .johnson, .once, false⟩,
  ⟨⟨"BASE lambda", 1, 0, 24, 0, 0, 1, 0, 0, 0, 0, 0⟩,
    ⟨6266338447674183580496835990942970962829472139317116988686, -320⟩, some ⟨(14, 2048, 66), (14,
    512, 66), .johnson, 600⟩, .closeness, .johnson, .once, false⟩,
  ⟨⟨"BASE", 1, 32, 64608, 0, 0, 0, 0, 66, 14, 0, 0⟩,
    ⟨4911642851699224808260951740833070344708123163209021488337, -289⟩, some ⟨(14, 2048, 66), (14,
    512, 66), .johnson, 600⟩, .query, .johnson, .once, false⟩]

/-- The entry file's priced plan at the small example's size. -/
def pricedEntrySmall : Planned := { set := pricedEntrySetSmall, rounds := pricedEntryRoundsSmall }

end Johnson.G
