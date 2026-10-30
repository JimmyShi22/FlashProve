-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5KvCfg.lean

The two configurations at which the public premises of attention's seam are run, typed ONCE.
They have the numbers of the full-size and of the small example of
OnBytes/Model/TestAttentionShape.lean, but Ty = 2^18, where these examples have 1000, and the usual
call list. (Lane5AttWit.lean types the same two for its own guards.)

Not claimed: that these configurations are those of a parameter file.
-/
import OnBytes.Model.AttentionShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.L5.KvCfg

open OnBytes.Attention (Cfg Line)

/-- The usual call list. -/
def lines0 : List Line :=
  [⟨"KR", .kr, [.rm, .rd]⟩, ⟨"KFD", .kfd, [.fm, .fd]⟩, ⟨"R16", .r16, [.wl, .ix]⟩,
    ⟨"WH", .wh, [.wh]⟩]

/-- The numbers of the full-size example, but Ty = 2^18. -/
def cfFull : Cfg :=
  { lt := 10, lB := 6, lgk := 3, ldh := 7, ll := 2, S := 12, rx := 8, kFD := 16, lmS := 16,
    la := 16, lmb := 14, nmin := 20, H := 40, sh := #[8, 8, 8, 8], wcH := 8, wcO := 64, wcQ := 64,
    NAs := 1, Ty := 2 ^ 18, lines := lines0 }

/-- The numbers of the small example, but Ty = 2^18. -/
def cfSmall : Cfg :=
  { lt := 6, lB := 4, lgk := 1, ldh := 7, ll := 2, S := 12, rx := 8, kFD := 16, lmS := 11, la := 8,
    lmb := 13, nmin := 20, H := 4, sh := #[12, 12, 12, 12], wcH := 64, wcO := 128, wcQ := 128,
    NAs := 1, Ty := 2 ^ 18, lines := lines0 }

end OnBytes.Road.L5.KvCfg
