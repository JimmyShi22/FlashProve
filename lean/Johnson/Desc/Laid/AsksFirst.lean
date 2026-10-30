-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Laid/AsksFirst.lean: the first test of a list that says no. One definition.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD

/-- The first test of a list that says no; each test stands with the words under which it refuses.
-/
def firstNo (l : List (String × Bool)) : Option (String × Bool) := l.find? (!·.2)

end LPFD
