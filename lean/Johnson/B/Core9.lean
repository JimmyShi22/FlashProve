-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/B/Core9.lean: `cntIx`, the assumed statement's count at the index's code and the
radius 2,852,142,980, rounded down, and `cnt132`: cntIx · 2^132 ≤ q.
The rounds outside the towers are the offline test's, the link's and the session's own rounds, with
the index's four folds in the first regime at that radius.

Work is
counted AT THE
ROUNDS THAT DRAW LOCATIONS alone: 62 locations at the offline test's round (32 bits), 62 and 62 at
the link's (32 bits), 64 at the session's (28 bits).
Hypothesis: none: arithmetic on the FORMULA Cb.bchksBound of the assumed statement; that agreement
holds with that count is not said here.
Not said: that the errors below bound a cheater's chance (that tie is the library's, under PreJ
and FoldErr). Margins, by our own reckoning, X the count cntIx: the link's round that folds both
indices has the error (22 X + 583) q^10 (two folds of 11 X + 286 each, and 11) and clears 2^-128 by
about 0.15 bits; the offline test's has (11 X + 304) q^17 (one fold, and 18) and clears it by about
1.15 bits; the session's likewise.
-/
import Cb.Ld.LdBldObjProofs
import Cb.Ld.LdBldMsgProofs
import Cb.Gl.GlFinalEvProofs
import Cb.Ref.GlRefNum
import Cb.Obj.LdObjectCtb
import Cb.Gl.GlFinalPpP
import Cb.Ld.LdKappaWorkRef
import Cb.Ld.LdKappaList
import Johnson.T2.Idx
import Cb.Obj.LdObjectProofs
import Cb.Obj.LdObjectTermsProofs

set_option autoImplicit false

namespace Cb.Gl.Ref
open Iop Prob Hiop IOR
open scoped ENNReal

/-- the assumed statement's count at the index's code and the radius 2852142980, rounded down -/
noncomputable def cntIx : ℕ := ⌊Cb.bchksBound (2 ^ 32) 446693374 2852142980⌋₊

theorem cnt132 : cntIx * 2 ^ 132 ≤ q := Cb.Gl.Bld.J.cnt_32_446693374_2852142980_132

/-! ### Arithmetic at letters -/

end Cb.Gl.Ref
