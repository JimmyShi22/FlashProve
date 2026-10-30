-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
`Gl.AgreeJ` (Cb/Gl/GlFinalAg.lean) is stated nowhere in this library as a separate theorem: it
follows, by one application that is written down nowhere, from `Cb.BCHKS46At` (`Cb.Gl.glAg_ofAt`,
same file), which this library proves in Cb/Bridge (bchks46At), from files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15), and applies in second
forms of some of its theorems (files named `…Codes.lean` under
Johnson/; a bound on the entry file's closed check); this file does not apply that proof. Within
half the distance its conclusion is proved (`Cb.Gl.agreeHalf`, Cb/Gl/GlAgreeHalf.lean); at the
numbers of the copy's file the radius lies beyond half the distance (reckoned by hand:
lean/GAPS.md, (61)).






Cb/Gl/GlFullErrSide.lean: this file declares nothing; it imports Cb/Ld/LdHonSide.lean and
Cb/Gl/GlFullErrTow.lean.
























Terms: lean/GLOSSARY.md.



-/
import Cb.Ld.LdHonSide
import Cb.Gl.GlFullErrTow

set_option autoImplicit false
