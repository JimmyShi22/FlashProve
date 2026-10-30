-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypingTWire.lean: the typing of a stretch of rounds (OnBytes/Maker/TypingT.lean) and
the wire records (OnBytes/Maker/Wire.lean) number a round's positions alike.

Both files give, for a position of a round with several trees, the number of its tree among the
round's trees and the number of its leaf. The typing looks an opening up under these two numbers;
the compiled verifier walks the opening's path from the leaf that the wire record names, under the
root that it names. The two descriptions are equal.

  `treeIn_eq`   `treeIn` is `treeT`.
  `leafIn_eq`   `leafIn` is `placeT`.

Not claimed. Nothing else.


-/
import OnBytes.Maker.TypingT
import OnBytes.Maker.Wire

set_option autoImplicit false

namespace OnBytes.Maker

theorem treeIn_eq : ∀ (ts : List Fmt.Shape) (p : PosT ts), treeIn ts p = treeT ts p
  | _ :: _, .inl _ => rfl
  | _ :: ts, .inr p => congrArg (· + 1) (treeIn_eq ts p)

theorem leafIn_eq : ∀ (ts : List Fmt.Shape) (p : PosT ts), leafIn ts p = placeT ts p
  | _ :: _, .inl _ => rfl
  | _ :: ts, .inr p => leafIn_eq ts p

end OnBytes.Maker
