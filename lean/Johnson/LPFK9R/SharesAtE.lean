-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
LPFK9R/SharesAtE.lean: OUR SHARES OF THE JOIN OF «the half of the
table's promise that reads the verifier's state is handed on», AT THE JOIN's OWN WRITTEN LIST AND
NUMBERS, WITH THE SIXTH FIELD («more») PAID: at E := the promise's public test at a border
(`ePubAt`, Johnson/Desc/First/EPubAt.lean) at the composed public tests and the composed filling.
SharesAtW.lean's four, without the premise «more». Theorems, and two evaluations by the kernel.

What is said.
  `EW D base z`: the constant E. `pubFit9_W`, `pubFitE_W`: the two Bools on the tables say yes at
    the join's own list. `batch_E`, `behind_E`, `close0_E`, `close2_E`: **`IM.Hands N linksW placesW
    (EW D base z) ft (14 * l + nAt l + 2 | 3 | 4 | 6) …`.**

Limits. PREMISES THAT STAY: the base's tests answer alike at any two states; the plan's two counts
at the two places; `LinkShare` at the link (the runs' share); behind the frame's sub-protocol «the
one sum can be taken» (by nobody); at the one equation: the table's own test on the plan's numbers,
hg, and «no message of the link's own is the index masks' message» (by nobody). `behind_E` AND
`close0_E` ARE SUPERSEDED: their premises on the state in front (htot; hg, hne) range over EVERY
state at which the promise's public tests say yes, and no public item that is open there reads an
array's number of rows, the seats, the link's group or the link's own messages: IN THAT FORM NOBODY
CAN PAY THEM (a reader of our house, by reading). The forms to count are
SharesPt.lean's `behind_R` and `close0_R`, which ask them only where a fence holds. `batch_E` and
`close2_E` have no such premise and stand. Nothing on soundness.

-/
import Johnson.LPFK9R.SharesAtW
import Johnson.Desc.First.Link.Law.EPubRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9.HandsAt
open VerifiableInference.Desc
open VerifiableInference.Desc.LinkJoin
open VerifiableInference.Desc.K9 (atS Where shut messageNow)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.First (S Numbers Pub PubData pubAll ePubAt rowsAtFit)
open IM (linksW placesW nAt)

set_option maxRecDepth 1000000 in
theorem pubFit9_W : pubFit9 true moreAll linksW placesW = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem pubFitE_W : pubFitE moreAll linksW placesW = true := by decide +kernel

variable {P : Type} (D : PubData) (base : Pub → P × S → Bool) (z : P)

/-- **The constant E**: the promise's public test at border k. -/
def EW (k : ℕ) (s : S) : Bool := ePubAt (pubAll D base) moreAll linksW placesW k (z, s)

variable {N : Numbers} {ft : ℕ} (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s))

include hb

/-- **THE FIELD «batch».** -/
theorem batch_E {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (pp : Where) (h : LinkShare Lk pp)
    (hT : N.treesAt placesW[14 * l + nAt l + 2 + 1]? = N.treesAt placesW[14 * l + nAt l + 2]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 2 + 1]? = N.msgsAt placesW[14 * l + nAt l + 2]?) :
    IM.Hands N linksW placesW (EW D base z) ft (14 * l + nAt l + 2)
      (Lk.batch (claimsInBy Lk.each Lk.hear Lk.order)) := by
  obtain ⟨p, p', h1, _, h3, h4⟩ := place_W (l := l) (i := 0) hl (by omega)
  refine batch_W hl Lk pp h.two hT hM fun s s' hy _ _ hx => ?_
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact e_batch D base linksW placesW z hb _ l p pubFit9_W h1 h3 h4 Lk pp h ft s rs cols s' n hstep
    (IM.xk_parts hx).2.2.2.2

/-- **THE FIELD «behind».** -/
theorem behind_E {l : ℕ} (hl : l < 25) (Lk : Link S ProofFile.Cl) (pp : Where) (h : LinkShare Lk pp)
    (hT : N.treesAt placesW[14 * l + nAt l + 3 + 1]? = N.treesAt placesW[14 * l + nAt l + 3]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 3 + 1]? = N.msgsAt placesW[14 * l + nAt l + 3]?)
    (htot : ∀ s s', IM.Yes ft Lk.behindB s s' →
      IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 3) s = true →
      pubAll D base (.totalIn l) (z, s') = true)
    (b : Block S ProofFile.Cl) (hr : b.rounds = [])
    (hd : ∀ s rs gs, b.decide s rs gs = Lk.runBehind s) :
    IM.Hands N linksW placesW (EW D base z) ft (14 * l + nAt l + 3) b := by
  obtain ⟨p, p', h1, _, h3, h4⟩ := place_W (l := l) (i := 1) hl (by omega)
  refine behind_W hl Lk pp h.two hT hM (fun s s' hy _ _ hx => ?_) b hr hd
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact e_behind D base linksW placesW z hb _ l p pubFit9_W h1 h3 h4 Lk pp h ft s rs cols s' n hstep
    (htot s s' ⟨rs, cols, n, hstep⟩ hx) (IM.xk_parts hx).2.2.2.2

/-- **THE FIELD «close» AT j = 0: THE ONE EQUATION.** -/
theorem close0_E {l : ℕ} (hl : l < 25) (hN : rowsAtFit N 25 = true) (pw : Where)
    (Q : First.Close.Par)
    (hT : N.treesAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.treesAt placesW[14 * l + nAt l + 4 + 0]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 4 + 0 + 1]? =
      N.msgsAt placesW[14 * l + nAt l + 4 + 0]?)
    (hg : ∀ s a, IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 4 + 0) s = true →
      atS.get? s = some a → N.groupAt l = a.L.check.group)
    (hne : ∀ s, IM.XK N linksW placesW (EW D base z) (14 * l + nAt l + 4 + 0) s = true →
      ∀ a, atS.get? s = some a → ∀ m' o,
        messageNow a.L.check.frame a.L.check.frame.link m' = some o → o ≠ s.out.indexMasks)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[0]? = some x) :
    IM.Hands N linksW placesW (EW D base z) ft (14 * l + nAt l + 4 + 0)
      (x.retype : Block S ProofFile.Cl) := by
  obtain ⟨p, p', h1, _, h3, h4⟩ := place_W (l := l) (i := 2) hl (by omega)
  refine close0_W hl hN pw Q hT hM hg (fun s s' hy _ _ hxk => ?_) x hx
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact e_eq D base linksW placesW z hb _ l p pubFitE_W h1 h3 h4 pw _ (fun _ _ _ _ _ e => e) ft s rs
    cols s' n hstep (hne s hxk) (IM.xk_parts hxk).2.2.2.2

/-- **THE FIELD «close» AT j = 2: THE SHUTTING.** -/
theorem close2_E {l : ℕ} (hl : l < 25) (pw : Where) (Q : First.Close.Par)
    (hT : N.treesAt placesW[14 * l + nAt l + 4 + 2 + 1]? =
      N.treesAt placesW[14 * l + nAt l + 4 + 2]?)
    (hM : N.msgsAt placesW[14 * l + nAt l + 4 + 2 + 1]? =
      N.msgsAt placesW[14 * l + nAt l + 4 + 2]?)
    (x : Block S Unit) (hx : (K9.closeOf pw Q : List (Block S Unit))[2]? = some x) :
    IM.Hands N linksW placesW (EW D base z) ft (14 * l + nAt l + 4 + 2)
      (x.retype : Block S ProofFile.Cl) := by
  obtain ⟨p, p', h1, _, h3, h4⟩ := place_W (l := l) (i := 4) hl (by omega)
  refine close2_W hl pw Q hT hM (fun s s' hy _ _ hxk => ?_) x hx
  obtain ⟨rs, cols, n, hstep⟩ := hy
  exact e_shut D base linksW placesW z hb _ l p pubFit9_W h1 h3 h4 pw _ _ (fun _ _ _ _ _ e => e)
    ft s rs cols s' n hstep (IM.xk_parts hxk).2.2.2.2

end LPFK9.HandsAt

#print axioms LPFK9.HandsAt.pubFit9_W
#print axioms LPFK9.HandsAt.pubFitE_W
#print axioms LPFK9.HandsAt.batch_E
#print axioms LPFK9.HandsAt.behind_E
#print axioms LPFK9.HandsAt.close0_E
#print axioms LPFK9.HandsAt.close2_E
