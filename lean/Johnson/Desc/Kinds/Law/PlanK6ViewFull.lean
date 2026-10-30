-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6ViewFull.lean: a written View (Johnson/Desc/Kinds/PlanK6Test.lean), and
Lean's kernel's evaluation that the cheap public test accepts it.

WHERE THE TERM COMES FROM. viewFull WAS WRITTEN BY A PROGRAM, NOT BY HAND. A Lean script
(not in this library, 90aec934...) evaluated viewOf cs arr msR N Wp lay6 num at
the three public files
of the full-size stored example (synthetic weights) and printed the value as a Lean term. The
printout's sha256:
c0f0feb1165f95e21fe6f8e2bb0912b1b61894cf486bcbfab7952b3f39ff79ba.
The program read that term and wrote it out again (structures as ⟨...⟩, in the order of their
fields; lines of at most 100 characters), and checked that the sequence of its 1676 numbers and
truth values is the printout's.
The script's arguments. cs: the codes. N := P5T.numbersOf ps and msR := Sound.msOf (P5T.memberLists
rows ps), where ps lists the oracle messages of the request's own rounds. arr: a lookup table, which
the same printout compares with P5T.arrOf ps at every one of the 199 entries of ps and beyond them;
every oracle message of msR and of the segment is one of the 199. Wp: the verifier's public part.
lay6: the request's layout. num l m: the index of (0, l, m) among arrOf's own keys.

What is proved.
  viewFull           the written View: 8 matrices, 5 numbers in the segment, 167 oracle messages.
  viewFull_yes       planK6V viewFull 145 0 = true. Lean's kernel evaluates it.
  viewFull_no        a negative test.
  planK6C_of_view    whoever shows viewOf cs arr msR N Wp lay6 num = viewFull has planK6C cs arr msR
          N Wp lay6 num 145 0 = true.

Not proved here. THAT viewFull IS THE View OF ANY ARGUMENTS: that rests on Lean's evaluator and one
printout; it is planK6C_of_view's premise. Meaning.laidThere. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PlanK6View

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

/-- The written View. Written by a program from a printout: see the file's header. -/
def viewFull : View :=
  { NHf := 4
    ns := 3570
    arrs := [
      (0, some ⟨145, [
        (63, 3145727), (63, 3932159), (63, 4063231), (63, 4128767), (63, 4161535), (95, 4128767),
        (63, 4177919), (95, 4161535), (63, 4186111), (95, 4177919), (63, 4190207), (95, 4186111),
        (99, 4128767), (63, 4192255), (95, 4190207), (63, 4193279), (95, 4192255), (99, 4177919),
        (63, 4193791), (95, 4193279), (63, 4194047), (95, 4193791), (99, 4190207), (63, 4194175),
        (95, 4194047), (99, 4192255), (63, 4194239), (95, 4194175), (63, 4194271), (95, 4194239),
        (63, 4194287), (95, 4194271), (99, 4194047), (63, 4194295), (63, 4194299), (95, 4194295),
        (99, 4194239), (95, 4194299), (99, 4194287), (99, 4194295)]⟩),
      (1, some ⟨145, [
        (95, 2097151), (95, 3670015), (95, 3932159), (95, 4063231), (99, 3670015), (101, 3145727),
        (99, 3932159), (101, 3670015), (99, 4063231), (101, 3932159), (101, 4063231),
        (102, 3932159), (89, 2359295), (99, 4161535), (101, 4128767), (101, 4161535),
        (102, 4128767), (91, 2949119), (99, 4186111), (101, 4177919), (101, 4186111),
        (102, 4177919), (92, 2572287), (101, 4190207), (102, 4186111), (92, 2711551), (99, 4193279),
        (101, 4192255), (99, 4193791), (101, 4193279), (101, 4193791), (102, 4193279),
        (92, 2835455), (95, 4194287), (101, 4194175), (102, 4194047), (92, 2847487), (99, 4194271),
        (101, 4194271), (101, 4194287)]⟩),
      (2, some ⟨145, [
        (31, 2097151), (31, 3670015), (99, 2097151), (99, 3145727), (102, 2097151), (73, 3145727),
        (102, 3145727), (82, 3145727), (102, 3670015), (86, 2621439), (89, 2621439), (89, 2883583),
        (89, 3145727), (102, 4063231), (91, 2228223), (91, 3014655), (91, 3080191), (91, 3145727),
        (102, 4161535), (92, 2392063), (92, 2588671), (92, 2605055), (92, 2621439), (92, 2719743),
        (92, 2727935), (92, 2736127), (102, 4190207), (92, 2797567), (102, 4192255), (92, 2820095),
        (92, 2836479), (92, 2837503), (92, 2838527), (99, 4194175), (92, 2847743), (92, 2847999),
        (92, 2848255), (101, 4194239), (102, 4194239), (102, 4194271)]⟩),
      (3, some ⟨145, [
        (63, 2097151), (63, 3670015), (71, 3145727), (101, 2097151), (75, 3145727), (77, 3145727),
        (83, 3145727), (84, 3145727), (86, 3145727), (87, 2621439), (90, 2359295), (90, 2621439),
        (90, 2883583), (91, 2359295), (91, 2490367), (92, 2162687), (92, 2228223), (92, 2293759),
        (92, 2424831), (92, 2457599), (92, 2637823), (92, 2654207), (92, 2670591), (92, 2744319),
        (92, 2752511), (92, 2760703), (92, 2801663), (92, 2805759), (92, 2822143), (92, 2824191),
        (92, 2839551), (92, 2840575), (92, 2841599), (101, 4194047), (92, 2848511), (92, 2848767),
        (92, 2849023), (102, 4194175), (92, 2850751), (92, 2850911)]⟩),
      (4, some ⟨145, [
        (79, 3145727), (87, 3145727), (88, 2621439), (91, 2621439), (91, 2752511), (92, 2490367),
        (92, 2523135), (92, 2768895), (92, 2777087), (92, 2826239), (92, 2828287), (92, 2842623),
        (102, 4193791), (92, 2849279)]⟩),
      (5, some ⟨145, [
        (92, 2686975), (92, 2785279), (92, 2809855), (92, 2813951), (92, 2830335), (92, 2832383),
        (92, 2843647), (92, 2844671), (92, 2846207), (92, 2846719), (92, 2849535), (92, 2849791),
        (92, 2850431), (92, 2850559), (92, 2850815), (92, 2850879), (92, 2850943), (92, 2850975),
        (99, 4194299), (101, 4194295), (101, 4194299), (102, 4194295), (102, 4194279),
        (102, 4194299), (102, 4194283), (102, 4194285), (102, 4194287), (92, 2850976)]⟩),
      (6, some ⟨145, [
        (81, 3145727), (85, 3145727), (88, 3145727), (90, 3145727), (91, 2883583), (92, 2359295),
        (92, 2555903), (92, 2703359), (92, 2793471), (92, 2818047), (92, 2834431), (92, 2845695),
        (92, 2847231), (92, 2850047), (92, 2850303), (92, 2850687)]⟩),
      (7, some ⟨135, [
        (1, 2097151), (1, 3145727), (1, 3670015), (1, 3932159), (1, 4063231), (2, 3932159),
        (1, 4128767), (1, 4161535), (2, 4128767), (1, 4177919), (1, 4186111), (2, 4177919),
        (1, 4190207), (1, 4192255), (2, 4190207), (1, 4193279), (1, 4193791), (2, 4193279),
        (1, 4194047), (2, 4193791), (1, 4194175), (2, 4194047), (1, 4194271), (1, 4194287)]⟩)]
    groupNums := [144, 135, 145, 147, 148]
    mems := [
      ⟨false, false, 0, 106, 1, 4194304, 8192⟩, ⟨false, false, 1, 9, 0, 4194304, 0⟩,
      ⟨false, false, 2, 3, 0, 4194304, 0⟩, ⟨false, false, 4, 0, 1, 0, 256⟩,
      ⟨false, false, 5, 1, 0, 4194304, 0⟩, ⟨false, false, 6, 31, 0, 4194304, 0⟩,
      ⟨false, false, 7, 2, 0, 4194304, 8192⟩, ⟨false, false, 1, 9, 0, 4194304, 0⟩,
      ⟨false, false, 2, 3, 0, 4194304, 0⟩, ⟨false, false, 8, 42, 1, 4194304, 8192⟩,
      ⟨false, false, 10, 1, 0, 4194304, 0⟩, ⟨false, false, 11, 14, 0, 4194304, 0⟩,
      ⟨false, false, 12, 2, 0, 4194304, 8192⟩, ⟨false, false, 2, 3, 0, 4194304, 0⟩,
      ⟨false, false, 13, 104, 1, 4194304, 8192⟩, ⟨false, false, 14, 9, 0, 4194304, 0⟩,
      ⟨false, false, 15, 3, 0, 4194304, 0⟩, ⟨false, false, 17, 1, 0, 4194304, 0⟩,
      ⟨false, false, 18, 31, 0, 4194304, 0⟩, ⟨false, false, 19, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 14, 9, 0, 4194304, 0⟩, ⟨false, false, 15, 3, 0, 4194304, 0⟩,
      ⟨false, false, 20, 42, 1, 4194304, 8192⟩, ⟨false, false, 22, 1, 0, 4194304, 0⟩,
      ⟨false, false, 23, 14, 0, 4194304, 0⟩, ⟨false, false, 24, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 15, 3, 0, 4194304, 0⟩, ⟨false, false, 25, 104, 1, 4194304, 8192⟩,
      ⟨false, false, 26, 9, 0, 4194304, 0⟩, ⟨false, false, 27, 3, 0, 4194304, 0⟩,
      ⟨false, false, 29, 1, 0, 4194304, 0⟩, ⟨false, false, 30, 31, 0, 4194304, 0⟩,
      ⟨false, false, 31, 2, 0, 4194304, 8192⟩, ⟨false, false, 26, 9, 0, 4194304, 0⟩,
      ⟨false, false, 27, 3, 0, 4194304, 0⟩, ⟨false, false, 32, 42, 1, 4194304, 8192⟩,
      ⟨false, false, 34, 1, 0, 4194304, 0⟩, ⟨false, false, 35, 14, 0, 4194304, 0⟩,
      ⟨false, false, 36, 2, 0, 4194304, 8192⟩, ⟨false, false, 27, 3, 0, 4194304, 0⟩,
      ⟨false, false, 37, 104, 1, 4194304, 8192⟩, ⟨false, false, 38, 9, 0, 4194304, 0⟩,
      ⟨false, false, 39, 3, 0, 4194304, 0⟩, ⟨false, false, 41, 1, 0, 4194304, 0⟩,
      ⟨false, false, 42, 31, 0, 4194304, 0⟩, ⟨false, false, 43, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 38, 9, 0, 4194304, 0⟩, ⟨false, false, 39, 3, 0, 4194304, 0⟩,
      ⟨false, false, 44, 42, 1, 4194304, 8192⟩, ⟨false, false, 46, 1, 0, 4194304, 0⟩,
      ⟨false, false, 47, 14, 0, 4194304, 0⟩, ⟨false, false, 48, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 39, 3, 0, 4194304, 0⟩, ⟨false, false, 49, 104, 1, 4194304, 8192⟩,
      ⟨false, false, 50, 9, 0, 4194304, 0⟩, ⟨false, false, 51, 3, 0, 4194304, 0⟩,
      ⟨false, false, 53, 1, 0, 4194304, 0⟩, ⟨false, false, 54, 31, 0, 4194304, 0⟩,
      ⟨false, false, 55, 2, 0, 4194304, 8192⟩, ⟨false, false, 50, 9, 0, 4194304, 0⟩,
      ⟨false, false, 51, 3, 0, 4194304, 0⟩, ⟨false, false, 56, 42, 1, 4194304, 8192⟩,
      ⟨false, false, 58, 1, 0, 4194304, 0⟩, ⟨false, false, 59, 14, 0, 4194304, 0⟩,
      ⟨false, false, 60, 2, 0, 4194304, 8192⟩, ⟨false, false, 51, 3, 0, 4194304, 0⟩,
      ⟨false, false, 61, 104, 1, 4194304, 8192⟩, ⟨false, false, 62, 9, 0, 4194304, 0⟩,
      ⟨false, false, 63, 3, 0, 4194304, 0⟩, ⟨false, false, 65, 1, 0, 4194304, 0⟩,
      ⟨false, false, 66, 31, 0, 4194304, 0⟩, ⟨false, false, 67, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 62, 9, 0, 4194304, 0⟩, ⟨false, false, 63, 3, 0, 4194304, 0⟩,
      ⟨false, false, 68, 42, 1, 4194304, 8192⟩, ⟨false, false, 70, 1, 0, 4194304, 0⟩,
      ⟨false, false, 71, 14, 0, 4194304, 0⟩, ⟨false, false, 72, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 63, 3, 0, 4194304, 0⟩, ⟨false, false, 73, 104, 1, 4194304, 8192⟩,
      ⟨false, false, 74, 9, 0, 4194304, 0⟩, ⟨false, false, 75, 3, 0, 4194304, 0⟩,
      ⟨false, false, 77, 1, 0, 4194304, 0⟩, ⟨false, false, 78, 31, 0, 4194304, 0⟩,
      ⟨false, false, 79, 2, 0, 4194304, 8192⟩, ⟨false, false, 74, 9, 0, 4194304, 0⟩,
      ⟨false, false, 75, 3, 0, 4194304, 0⟩, ⟨false, false, 80, 42, 1, 4194304, 8192⟩,
      ⟨false, false, 82, 1, 0, 4194304, 0⟩, ⟨false, false, 83, 14, 0, 4194304, 0⟩,
      ⟨false, false, 84, 2, 0, 4194304, 8192⟩, ⟨false, false, 75, 3, 0, 4194304, 0⟩,
      ⟨false, false, 85, 104, 1, 4194304, 8192⟩, ⟨false, false, 86, 9, 0, 4194304, 0⟩,
      ⟨false, false, 87, 3, 0, 4194304, 0⟩, ⟨false, false, 89, 1, 0, 4194304, 0⟩,
      ⟨false, false, 90, 31, 0, 4194304, 0⟩, ⟨false, false, 91, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 86, 9, 0, 4194304, 0⟩, ⟨false, false, 87, 3, 0, 4194304, 0⟩,
      ⟨false, false, 92, 42, 1, 4194304, 8192⟩, ⟨false, false, 94, 1, 0, 4194304, 0⟩,
      ⟨false, false, 95, 14, 0, 4194304, 0⟩, ⟨false, false, 96, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 87, 3, 0, 4194304, 0⟩, ⟨false, false, 97, 104, 1, 4194304, 8192⟩,
      ⟨false, false, 98, 9, 0, 4194304, 0⟩, ⟨false, false, 99, 3, 0, 4194304, 0⟩,
      ⟨false, false, 101, 1, 0, 4194304, 0⟩, ⟨false, false, 102, 31, 0, 4194304, 0⟩,
      ⟨false, false, 103, 2, 0, 4194304, 8192⟩, ⟨false, false, 98, 9, 0, 4194304, 0⟩,
      ⟨false, false, 99, 3, 0, 4194304, 0⟩, ⟨false, false, 104, 42, 1, 4194304, 8192⟩,
      ⟨false, false, 106, 1, 0, 4194304, 0⟩, ⟨false, false, 107, 14, 0, 4194304, 0⟩,
      ⟨false, false, 108, 2, 0, 4194304, 8192⟩, ⟨false, false, 99, 3, 0, 4194304, 0⟩,
      ⟨false, false, 109, 104, 1, 4194304, 8192⟩, ⟨false, false, 110, 9, 0, 4194304, 0⟩,
      ⟨false, false, 111, 3, 0, 4194304, 0⟩, ⟨false, false, 113, 1, 0, 4194304, 0⟩,
      ⟨false, false, 114, 31, 0, 4194304, 0⟩, ⟨false, false, 115, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 110, 9, 0, 4194304, 0⟩, ⟨false, false, 111, 3, 0, 4194304, 0⟩,
      ⟨false, false, 116, 42, 1, 4194304, 8192⟩, ⟨false, false, 118, 1, 0, 4194304, 0⟩,
      ⟨false, false, 119, 14, 0, 4194304, 0⟩, ⟨false, false, 120, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 111, 3, 0, 4194304, 0⟩, ⟨false, false, 121, 104, 1, 4194304, 8192⟩,
      ⟨false, false, 122, 9, 0, 4194304, 0⟩, ⟨false, false, 123, 3, 0, 4194304, 0⟩,
      ⟨false, false, 125, 1, 0, 4194304, 0⟩, ⟨false, false, 126, 31, 0, 4194304, 0⟩,
      ⟨false, false, 127, 2, 0, 4194304, 8192⟩, ⟨false, false, 122, 9, 0, 4194304, 0⟩,
      ⟨false, false, 123, 3, 0, 4194304, 0⟩, ⟨false, false, 128, 42, 1, 4194304, 8192⟩,
      ⟨false, false, 130, 1, 0, 4194304, 0⟩, ⟨false, false, 131, 14, 0, 4194304, 0⟩,
      ⟨false, false, 132, 2, 0, 4194304, 8192⟩, ⟨false, false, 123, 3, 0, 4194304, 0⟩,
      ⟨false, false, 133, 104, 1, 4194304, 8192⟩, ⟨false, false, 134, 9, 0, 4194304, 0⟩,
      ⟨false, false, 135, 3, 0, 4194304, 0⟩, ⟨false, false, 137, 1, 0, 4194304, 0⟩,
      ⟨false, false, 138, 31, 0, 4194304, 0⟩, ⟨false, false, 139, 2, 0, 4194304, 8192⟩,
      ⟨false, false, 134, 9, 0, 4194304, 0⟩, ⟨false, false, 135, 3, 0, 4194304, 0⟩,
      ⟨false, false, 140, 42, 1, 4194304, 8192⟩, ⟨false, false, 142, 1, 0, 4194304, 0⟩,
      ⟨false, false, 143, 14, 0, 4194304, 0⟩, ⟨true, true, 144, 2, 0, 4194304, 8192⟩,
      ⟨true, true, 135, 3, 0, 4194304, 0⟩, ⟨true, true, 145, 103, 1, 4194304, 8192⟩,
      ⟨true, false, 147, 1, 0, 4194304, 0⟩, ⟨true, false, 148, 24, 0, 4194304, 0⟩,
      ⟨false, false, 149, 2, 0, 4194304, 8192⟩, ⟨false, false, 151, 16, 8, 262144, 4096⟩,
      ⟨false, false, 153, 8, 8, 32768, 2048⟩, ⟨false, false, 155, 8, 8, 4096, 1024⟩,
      ⟨false, false, 157, 16, 16, 256, 256⟩, ⟨false, false, 159, 1, 1, 256, 1024⟩,
      ⟨false, false, 161, 1, 1, 262144, 256⟩] }

/-- **The cheap test accepts the written View.** Lean's kernel evaluates it. -/
theorem viewFull_yes : planK6V viewFull 145 0 = true := by
  decide +kernel

/-- A negative test: with one more oracle message of the segment numbered 145 the test rejects. -/
theorem viewFull_no :
    planK6V { viewFull with groupNums := 145 :: viewFull.groupNums } 145 0 = false := by
  decide +kernel

/-- So the test accepts at arguments whose View is the written one. -/
theorem planK6C_of_view (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
    (msR : List VerifiableInference.Desc.Sound.Mem) (N : VerifiableInference.Desc.First.Numbers)
    (Wp : OnBytes.Model.Verify.Public) (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ)
    (h : viewOf cs arr msR N Wp lay6 num = viewFull) :
    planK6C cs arr msR N Wp lay6 num 145 0 = true := by
  rw [planK6C_eq, h]
  exact viewFull_yes

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewFull_yes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewFull_no
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6C_of_view
