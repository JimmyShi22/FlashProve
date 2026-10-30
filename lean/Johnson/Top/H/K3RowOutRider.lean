-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3RowOutRider.lean: the kind "lookup" (K3): THE ROW OUT's FOURTH ITEM, where another
kind's identity rides on the lookup's key point. A definition, and the theorem that at a written
transcript's own rounds it is the proved block's clause on its riders. NO SOUNDNESS IS CLAIMED.

Why. Behind the proved block with riders (kLookupCRN, Johnson/Top/H/LookupCRideRows.lean) the joint
says, beside the lookup's out-claim, that the multilinear extension of every rider's array is 0 at
the chosen places of THE KEY POINT OF THE OUT-STATEMENT. A relation behind a block cannot name the
transcript; it can name what was heard. So, as for the three items of Johnson/Top/H/K3RowOut.lean:
at all rounds for which the heard record stands.

Main names:
  `keyPt En`: the key point of a record of end values: zx, then zy.
  `K3OutRider r lm first st m g F'`: for all rounds rs for which g and F' stand: every rider's
    extension is 0 at its places of keyPt (endsOf r.c.h lm first rs), at the messages m.
  `out_is_lookOutE`: the statement that the block puts out at a written transcript is lookOutE at
    the transcript's own end values (lookKindR_view), whichever name it was given.
  `tgt_of_rider`: so the fourth item, at the transcript's rounds, is the block's clause.
  `rider_of_point`: for whoever proves the item: it follows from the same sentence at the heard
    record's own zx and zy: no rounds, no ledger: so it crosses later blocks as it is.

Limits. WHO GIVES THE FOURTH ITEM is the riding kind's: that its form at the true reads is worth the
identity, and that the sent reads are the true ones. At a record whose g and F' no rounds could have
left, K3OutRider holds for nothing, as the three items of Johnson/Top/H/K3RowOut.lean do (its
Limits). No theorem here joins the fourth item to these three. A tie: no error term.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.LookupCOutD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- The key point of a record of end values. -/
def keyPt (En : Ends Cb.Gl.E) : ℕ → Cb.Gl.E := fun t => (En.zx ++ En.zy).getD t 0

/-- **The row out's fourth item.** -/
def K3OutRider (r : LookupCRCaller) (lm first : ℕ) (st : r.c.St₀) (m : r.c.Sg.Msg)
    (g : Forest.Heard) (F' : Fork) : Prop :=
  ∀ rs : Rounds Cb.Gl.E, HeardIs Reading.gl g F' (endsOf r.c.h lm first rs) →
    AtCoords r.g r.sel r.f st (keyPt (endsOf r.c.h lm first rs)) m

/-- The statement that the block puts out at a written transcript, by name. -/
theorem out_is_lookOutE (L : List LookupCRCaller) (r : LookupCRCaller)
    (hok : FoNums.ok r.c.h = true) (lm jLK : ℕ) (mk : ℕ → r.c.J₀) (pl : ℕ → ℕ → r.c.J₀)
    (hmk : ∀ t, r.c.L.mkS t = mk (jLK + t))
    (hbc : ∀ t k j, k < r.c.h.NC →
      r.c.L.bc t k j =
        pl (FoNums.cellRC r.c.h lm (t, k, j)).1 (FoNums.cellRC r.c.h lm (t, k, j)).2)
    (ds : List RDT) (hM : List.Forall₂ MeetsT ds (specF r.c.h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (a : (r.c.St₀ × r.c.Sg.Smp) × (r.c.Ex.prod r.c.Sg.ext).Str) (τ : Tr (uLT (ckP .two) ds))
    (x : TX (r.c.St₀ × Cb.Gl.E) Cb.Gl.E (Option r.c.J₀))
    (hx : ((kLookupCRN L).toKind.block r).R.red.out a
        ((mapsT ds _ (specF r.c.h) (rkFor r.c.h r.c.L r.c.Ex).R hM.length_eq).view τ) =
      some ((x, a.1.2), a.2)) :
    x = lookOutE r.c.h lm jLK (placeOf mk pl) a.1.1 (endsOf r.c.h lm jLK (viewRounds ds τ)) := by
  have h1 := lookKindR_view L r hok lm jLK mk pl hmk hbc ds hM hA a τ
  have h2 := Option.some.inj (hx.symm.trans h1)
  exact congrArg (fun y => y.1.1) h2

/-- **At a written transcript's own rounds the fourth item is the block's clause on its riders.** -/
theorem tgt_of_rider (r : LookupCRCaller) (lm jLK : ℕ) (ι : Fo.Pl → Option r.c.J₀) (st : r.c.St₀)
    (m : r.c.Sg.Msg) (g : Forest.Heard) (F' : Fork) (rs : Rounds Cb.Gl.E) (y : r.c.Ex.Str)
    (hI : HeardIs Reading.gl g F' (endsOf r.c.h lm jLK rs))
    (h : K3OutRider r lm jLK st m g F') :
    r.tgt m (lookOutE r.c.h lm jLK ι st (endsOf r.c.h lm jLK rs), y) :=
  (lookRider_at r lm jLK ι st _ y m).2 (h rs hI)

/-- **For whoever proves the fourth item: it needs no rounds and no ledger**: the heard record pins
the key point (HeardIs.zx, HeardIs.zy): it is enough that every rider's extension is 0 at its places
of THE HEARD RECORD's OWN zx, then zy. -/
theorem rider_of_point (r : LookupCRCaller) (lm first : ℕ) (st : r.c.St₀) (m : r.c.Sg.Msg)
    (g : Forest.Heard) (F' : Fork)
    (h : AtCoords r.g r.sel r.f st
      (fun t => (rdA Reading.gl g.zx ++ rdA Reading.gl g.zy).getD t 0) m) :
    K3OutRider r lm first st m g F' := fun rs hI => by
  unfold keyPt
  rw [← hI.zx, ← hI.zy]
  exact h

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.rider_of_point
#print axioms VerifiableInference.OnPublicFiles.out_is_lookOutE
#print axioms VerifiableInference.OnPublicFiles.tgt_of_rider
