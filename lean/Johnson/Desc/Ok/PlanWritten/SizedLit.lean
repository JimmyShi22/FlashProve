-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/SizedLit.lean: written values, and nothing else: of what the library's
planner makes of the stored full-size public files: the proof file's sizes and codes (`ProofSized`,
OnBytes/Params/DeriveReq.lean), the link's (`LinkSized`, OnBytes/Params/Derive.lean), and the six
settings of the proof file's three plans. Definitions alone.

Where the values are from. They were laid here by a program from a print: an evaluation, outside
this library's build, of the fields of `m.p.chains.made.sized` and of the three plans as read back,
at the three public files of the stored full-size example; each value was printed by its type's own
derived form, as a term of Lean. No number was typed by hand. The program struck nothing and added
line breaks alone.

Main names. `proofSizedFull`; `linkSizedFull`; `sixFull`: for the first, the shared and the second
chain's plan: field, the bytes of a salt, of a nonce, of a listed position, the answers to a sample,
whether a sum-check's message leaves out a coefficient.

Limits. That these are what the planner makes of any files is proved nowhere: the tests that hold
them against the planner are in Johnson/Desc/Ok/PlanWritten/Sized.lean, and
their yes is a run's to
show. They are no second witness: print and test go through this library's own planner. Nothing on
soundness.

-/
import OnBytes.Params.DeriveReq
import OnBytes.Params.Derive
import Fmt.Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

/-- The proof file's sizes and codes at the full size. -/
def proofSizedFull : OnBytes.Params.ProofSized :=
  { set :=
      { p := 18446744069414584321, degree := 3, target := 128, printed := true,
        rowsFactor := false, instances := 1, samples := 1, saltBytes := 40,
        nonceBytes := 8, positionBytes := 0,
        workField := { request := 0, shared := 0, once := 0 },
        workSample := { request := 0, shared := 0, once := 0 },
        workCloseness := { request := 0, shared := 0, once := 0 },
        workQuery := { request := 20, shared := 28, once := 32 },
        workSmall := { request := 0, shared := 0, once := 0 } },
    codes :=
      { base :=
          #[{ logN := 23, ell := 4194304, r := 219 }, { logN := 22, ell := 262144, r := 55 },
            { logN := 19, ell := 32768, r := 55 }, { logN := 16, ell := 4096, r := 55 },
            { logN := 13, ell := 256, r := 46 }, { logN := 15, ell := 256, r := 44 },
            { logN := 24, ell := 4194304, r := 101 }, { logN := 21, ell := 131072, r := 54 },
            { logN := 17, ell := 8192, r := 54 }, { logN := 13, ell := 512, r := 54 },
            { logN := 14, ell := 512, r := 51 }, { logN := 22, ell := 262144, r := 3571 },
            { logN := 18, ell := 16384, r := 51 }, { logN := 14, ell := 1024, r := 51 },
            { logN := 15, ell := 1024, r := 41 }, { logN := 18, ell := 16384, r := 55 },
            { logN := 15, ell := 2048, r := 55 }],
        mask :=
          #[{ logN := 17, ell := 8192, r := 219 }, { logN := 17, ell := 4096, r := 55 },
            { logN := 16, ell := 2048, r := 55 }, { logN := 15, ell := 1024, r := 55 },
            { logN := 13, ell := 256, r := 46 }, { logN := 15, ell := 1024, r := 44 },
            { logN := 13, ell := 64, r := 152 }, { logN := 12, ell := 256, r := 54 },
            { logN := 14, ell := 1024, r := 51 }, { logN := 14, ell := 512, r := 51 },
            { logN := 13, ell := 256, r := 51 }, { logN := 15, ell := 1024, r := 41 },
            { logN := 13, ell := 256, r := 55 }, { logN := 14, ell := 512, r := 55 }] },
    link :=
      { group :=
          { main := { logN := 23, ell := 4194304, r := 219, overE := false },
            mask := { logN := 17, ell := 8192, r := 219, overE := true }, k := 8, h := 0,
            slots := 16, rule := OnBytes.Params.Radius.johnson, m := 258 }, t := 219 },
    last :=
      { group :=
          { main := { logN := 23, ell := 4194304, r := 219, overE := true },
            mask := { logN := 17, ell := 8192, r := 219, overE := true }, k := 1, h := 0,
            slots := 1, rule := OnBytes.Params.Radius.johnson, m := 258 }, t := 219,
        stages :=
          [{ g :=
               { main := { logN := 23, ell := 4194304, r := 219, overE := true },
                 mask := { logN := 17, ell := 8192, r := 219, overE := true }, k := 1, h := 0,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 258 }, t := 219,
             rOod := 0 },
           { g :=
               { main := { logN := 22, ell := 262144, r := 55, overE := true },
                 mask := { logN := 17, ell := 4096, r := 55, overE := true }, k := 4, h := 3,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 158 }, t := 55,
             rOod := 15727 },
           { g :=
               { main := { logN := 19, ell := 32768, r := 55, overE := true },
                 mask := { logN := 16, ell := 2048, r := 55, overE := true }, k := 3, h := 3,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 241 }, t := 55,
             rOod := 8027 },
           { g :=
               { main := { logN := 16, ell := 4096, r := 55, overE := true },
                 mask := { logN := 15, ell := 1024, r := 55, overE := true }, k := 3, h := 3,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 367 }, t := 55,
             rOod := 3931 },
           { g :=
               { main := { logN := 13, ell := 256, r := 46, overE := true },
                 mask := { logN := 13, ell := 256, r := 46, overE := true }, k := 4, h := 4,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 378 }, t := 46,
             rOod := 1883 },
           { g :=
               { main := { logN := 15, ell := 256, r := 44, overE := true },
                 mask := { logN := 15, ell := 1024, r := 44, overE := true }, k := 0, h := 0,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 345 }, t := 44,
             rOod := 374 }] },
    request :=
      { code := 0, maskCode := 0,
        link :=
          [{ plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 106, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 104, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 9, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 1 },
                { shape :=
                    { code := 0, mainRows := 3, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 0,
                  life := 2 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 31, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 0,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 42, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 14, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] },
           { plain := 1,
             messages :=
               [{ shape :=
                    { code := 0, mainRows := 103, mainDeg := 1, maskRows := 1, maskCode := 0,
                      answers := 1 }, leafClass := 0, moment := 0, life := 0 },
                { shape :=
                    { code := 0, mainRows := 1, mainDeg := 3, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 1,
                  life := 0 },
                { shape :=
                    { code := 0, mainRows := 24, mainDeg := 1, maskRows := 0,
                      maskCode := 4294967295, answers := 1 }, leafClass := 0, moment := 2,
                  life := 0 }] }],
        atStart :=
          [{ shape :=
               { code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 12,
                 answers := 1 }, leafClass := 1 }], answers := 1,
        last :=
          [{ code := 0, maskCode := 0, k := 1, h := 0 },
           { code := 1, maskCode := 1, k := 4, h := 3 },
           { code := 2, maskCode := 2, k := 3, h := 3 },
           { code := 3, maskCode := 3, k := 3, h := 3 },
           { code := 4, maskCode := 4, k := 4, h := 4 },
           { code := 5, maskCode := 5, k := 0, h := 0 }], choice := { masksRide := true } },
    batch :=
      { lines :=
          { kLo := 7, matrixRows := 3076096,
            folded :=
              { logN := 24, logL := 22, maskLogN := 13, maskLogL := 6,
                stages :=
                  [{ k := 5, h := 2, logN := 21, maskLogN := 12 },
                   { k := 4, h := 2, logN := 17, maskLogN := 12 },
                   { k := 4, h := 2, logN := 13, maskLogN := 12 },
                   { k := 0, h := 0, logN := 14, maskLogN := 14 }] },
            omega :=
              { logN := 22, logL := 18, maskLogN := 13, maskLogL := 6,
                stages :=
                  [{ k := 4, h := 3, logN := 18, maskLogN := 14 },
                   { k := 4, h := 3, logN := 14, maskLogN := 13 },
                   { k := 0, h := 0, logN := 15, maskLogN := 15 }] },
            own :=
              { logN := 22, logL := 18, maskLogN := 13, maskLogL := 8,
                stages :=
                  [{ k := 4, h := 3, logN := 18, maskLogN := 15 },
                   { k := 3, h := 3, logN := 15, maskLogN := 14 },
                   { k := 3, h := 3, logN := 13, maskLogN := 13 },
                   { k := 0, h := 0, logN := 15, maskLogN := 15 }] }, requests := 64,
            inputMaskRows := 1, oneTime := false },
        shape :=
          { fold :=
              { index :=
                  { code := { logN := 32, ell := 402653184, r := 44040191 }, v := 11,
                    answers := 1, saltBytes := 40 },
                u :=
                  { code := 6, mainRows := 107, mainDeg := 3, maskRows := 0,
                    maskCode := 4294967295, answers := 1 }, rowsHigh := true, leafClass := 0,
                columns := 64 }, kLo := 7, matrixRows := 3076096,
            omega :=
              { code := 11, mainRows := 12, mainDeg := 3, maskRows := 0, maskCode := 4294967295,
                answers := 1 },
            w :=
              { code := 11, mainRows := 1, mainDeg := 3, maskRows := 1, maskCode := 12,
                answers := 1 }, omegaRowsHigh := true, wRowsHigh := true,
            sharedSplit :=
              { code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 6,
                answers := 1 },
            ownSplit :=
              { code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 0,
                maskCode := 4294967295, answers := 1 }, omegaLeafClass := 1,
            sharedSplitLeafClass := 2, wLeafClass := 0, ownSplitLeafClass := 3,
            sharedMaskCode := 6, ownMaskCode := 12, masksAhead := true,
            testU :=
              [{ code := 6, maskCode := 6, k := 7, h := 0 },
               { code := 7, maskCode := 7, k := 5, h := 2 },
               { code := 8, maskCode := 7, k := 4, h := 2 },
               { code := 9, maskCode := 7, k := 4, h := 2 },
               { code := 10, maskCode := 8, k := 0, h := 0 }],
            testOmega :=
              [{ code := 11, maskCode := 6, k := 4, h := 0 },
               { code := 12, maskCode := 9, k := 4, h := 3 },
               { code := 13, maskCode := 10, k := 4, h := 3 },
               { code := 14, maskCode := 11, k := 0, h := 0 }],
            testOwn :=
              [{ code := 11, maskCode := 12, k := 5, h := 1 },
               { code := 15, maskCode := 3, k := 4, h := 3 },
               { code := 16, maskCode := 13, k := 3, h := 3 },
               { code := 4, maskCode := 4, k := 3, h := 3 },
               { code := 5, maskCode := 5, k := 0, h := 0 }], testOwnOmega := [],
            choice := { masksRide := true } },
        input :=
          { shape :=
              { code := 4294967295, mainRows := 0, mainDeg := 1, maskRows := 1, maskCode := 12,
                answers := 1 }, leafClass := 0 },
        table :=
          { code := { logN := 32, ell := 402653184, r := 44040191, overE := false }, v := 11,
            answers := 1,
            distances := { radius := 0, laterRadius := 0, mOnce := 24, mLater := 24 } },
        folded :=
          { group :=
              { main := { logN := 24, ell := 4194304, r := 101, overE := true },
                mask := { logN := 13, ell := 64, r := 152, overE := true }, k := 7, h := 0,
                slots := 1, rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 101,
            stages :=
              [{ g :=
                   { main := { logN := 24, ell := 4194304, r := 101, overE := true },
                     mask := { logN := 13, ell := 64, r := 152, overE := true }, k := 7, h := 0,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 101,
                 rOod := 0 },
               { g :=
                   { main := { logN := 21, ell := 131072, r := 54, overE := true },
                     mask := { logN := 12, ell := 256, r := 54, overE := true }, k := 5, h := 2,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 168 }, t := 54,
                 rOod := 491 },
               { g :=
                   { main := { logN := 17, ell := 8192, r := 54, overE := true },
                     mask := { logN := 12, ell := 256, r := 54, overE := true }, k := 4, h := 2,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 293 }, t := 54,
                 rOod := 350 },
               { g :=
                   { main := { logN := 13, ell := 512, r := 54, overE := true },
                     mask := { logN := 12, ell := 256, r := 54, overE := true }, k := 4, h := 2,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 510 }, t := 54,
                 rOod := 350 },
               { g :=
                   { main := { logN := 14, ell := 512, r := 51, overE := true },
                     mask := { logN := 14, ell := 1024, r := 51, overE := true }, k := 0, h := 0,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 489 }, t := 51,
                 rOod := 350 }] },
        omega :=
          { group :=
              { main := { logN := 22, ell := 262144, r := 3571, overE := true },
                mask := { logN := 13, ell := 64, r := 152, overE := true }, k := 4, h := 0,
                slots := 1, rule := OnBytes.Params.Radius.johnson, m := 159 }, t := 51,
            stages :=
              [{ g :=
                   { main := { logN := 22, ell := 262144, r := 3571, overE := true },
                     mask := { logN := 13, ell := 64, r := 152, overE := true }, k := 4, h := 0,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 159 }, t := 51,
                 rOod := 0 },
               { g :=
                   { main := { logN := 18, ell := 16384, r := 51, overE := true },
                     mask := { logN := 14, ell := 512, r := 51, overE := true }, k := 4, h := 3,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 277 }, t := 51,
                 rOod := 93 },
               { g :=
                   { main := { logN := 14, ell := 1024, r := 51, overE := true },
                     mask := { logN := 13, ell := 256, r := 51, overE := true }, k := 4, h := 3,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 489 }, t := 51,
                 rOod := 871 },
               { g :=
                   { main := { logN := 15, ell := 1024, r := 41, overE := true },
                     mask := { logN := 15, ell := 1024, r := 41, overE := true }, k := 0, h := 0,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 299 }, t := 41,
                 rOod := 359 }] },
        own :=
          { group :=
              { main := { logN := 22, ell := 262144, r := 3571, overE := true },
                mask := { logN := 13, ell := 256, r := 55, overE := true }, k := 5, h := 1,
                slots := 1, rule := OnBytes.Params.Radius.johnson, m := 159 }, t := 55,
            stages :=
              [{ g :=
                   { main := { logN := 22, ell := 262144, r := 3571, overE := true },
                     mask := { logN := 13, ell := 256, r := 55, overE := true }, k := 5, h := 1,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 159 }, t := 55,
                 rOod := 0 },
               { g :=
                   { main := { logN := 18, ell := 16384, r := 55, overE := true },
                     mask := { logN := 15, ell := 1024, r := 55, overE := true }, k := 4, h := 3,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 277 }, t := 55,
                 rOod := 3999 },
               { g :=
                   { main := { logN := 15, ell := 2048, r := 55, overE := true },
                     mask := { logN := 14, ell := 512, r := 55, overE := true }, k := 3, h := 3,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 423 }, t := 55,
                 rOod := 1883 },
               { g :=
                   { main := { logN := 13, ell := 256, r := 46, overE := true },
                     mask := { logN := 13, ell := 256, r := 46, overE := true }, k := 3, h := 3,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 378 }, t := 46,
                 rOod := 859 },
               { g :=
                   { main := { logN := 15, ell := 256, r := 44, overE := true },
                     mask := { logN := 15, ell := 1024, r := 44, overE := true }, k := 0, h := 0,
                     slots := 1, rule := OnBytes.Params.Radius.johnson, m := 345 }, t := 44,
                 rOod := 374 }] }, batches := 688127 } }

/-- The link's sizes at the full size. -/
def linkSizedFull : OnBytes.Params.LinkSized :=
  { shape :=
      { table :=
          { code := { logN := 32, ell := 402653184, r := 44040191 }, v := 11, answers := 1,
            saltBytes := 40 }, columnsFirst := 62, columnsFurther := 62, code := 0, maskCode := 0,
        rows := 107, rowsHigh := true, leafClass := 0, masksAhead := true,
        later :=
          [{ code := 1, maskCode := 1, k := 5, h := 2 },
           { code := 2, maskCode := 1, k := 4, h := 2 },
           { code := 3, maskCode := 2, k := 4, h := 2 },
           { code := 4, maskCode := 3, k := 0, h := 0 }], choice := { masksRide := true } },
    table :=
      { code := { logN := 32, ell := 402653184, r := 44040191, overE := false }, v := 11,
        answers := 1,
        distances := { radius := 0, laterRadius := 0, mOnce := 24, mLater := 24 } },
    linked :=
      { group :=
          { main := { logN := 24, ell := 4194304, r := 97, overE := true },
            mask := { logN := 13, ell := 64, r := 97, overE := true }, k := 8, h := 0, slots := 1,
            rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 97,
        stages :=
          [{ g :=
               { main := { logN := 24, ell := 4194304, r := 97, overE := true },
                 mask := { logN := 13, ell := 64, r := 97, overE := true }, k := 8, h := 0,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 97,
             rOod := 0 },
           { g :=
               { main := { logN := 21, ell := 131072, r := 49, overE := true },
                 mask := { logN := 12, ell := 128, r := 49, overE := true }, k := 5, h := 2,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 182 }, t := 49,
             rOod := 93 },
           { g :=
               { main := { logN := 17, ell := 8192, r := 49, overE := true },
                 mask := { logN := 12, ell := 128, r := 49, overE := true }, k := 4, h := 2,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 318 }, t := 49,
             rOod := 109 },
           { g :=
               { main := { logN := 13, ell := 512, r := 50, overE := true },
                 mask := { logN := 12, ell := 128, r := 50, overE := true }, k := 4, h := 2,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 570 }, t := 50,
             rOod := 109 },
           { g :=
               { main := { logN := 14, ell := 512, r := 40, overE := true },
                 mask := { logN := 14, ell := 512, r := 40, overE := true }, k := 0, h := 0,
                 slots := 1, rule := OnBytes.Params.Radius.johnson, m := 348 }, t := 40,
             rOod := 106 }] } }

/-- A plan's six settings, as a tuple. -/
abbrev SixSet : Type := Fmt.Fld × Nat × Nat × Nat × Nat × Nat

/-- The six settings of the proof file's first, shared and second chain's plan at the full size. -/
def sixFull : SixSet × SixSet × SixSet :=
  ((Fmt.Fld.two, 40, 8, 0, 1, 1), (Fmt.Fld.two, 40, 8, 0, 1, 1), (Fmt.Fld.two, 40, 8, 0, 1, 1))

end VerifiableInference.PlanWritten
