-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegRefProofs.lean: the statement of Cb/Req1/LdSegRef.lean, proved.

The proof uses the body (Cb/Req1/LdSegRefBodyProofs.lean), the public supports of its rows
(Cb/Req1/LdSegRefSupp.lean) and the segment with one group (Cb/Req1/LdSegWhole.lean).
What the statement says, and the limits: the head of Cb/Req1/LdSegRef.lean.
-/
import Cb.Req1.LdSegRef
import Cb.Req1.LdSegRefBodyProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

theorem ldSegRef_hyp :
    Spec.ldSegRef_hyp := fun E Kc _ _ _ _ pp _ R tensor hT l Qc hf h hl hten hZ hs hfold hsnd =>
  ldSegWhole_one E Kc R.Y.a R.c1 (R.Y.body R.c1.bat.src tensor) hT l Qc
    (ldSegRef_body_hyp E Kc _ _ pp R.Y R.c1.bat.src tensor hf h hl hten) hZ
    (ldSegRef_supp_grp E Kc _ _ R.Y.G R.grp hs) hfold hsnd

end Cb
