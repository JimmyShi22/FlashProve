-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/KeysFit.lean: a third test on the public data of the kind "an
attention segment's own rounds" (K5), beside the two of Honest/K5/Row.lean, and the lot's honest
side with all three asked. Definitions with code; two small theorems: what `seatAtK` yields, and an
equation of two names. Tests: Honest/K5/KeysFitToy.lean.

Why. `Seat5.fits` asks that the verifier's function for the named points returns
(`pointsOf`, Johnson/Desc/First/Att/Points.lean). That function tests the sizes of the points that
it cuts out of three calls' key points, not the key points' own: it takes the last coordinates of a
key point, however long that is. It lays the remainder-table units' points with no test on their
size. So `Seat5.fits` says yes at a key point of the remainder tables'
call of any length, the empty one too, and at any call's key point that is a coordinate too short or
too long (Honest/K5/KeysFitToy.lean evaluates it); the values that the row sends would be made of
it: a drawn value read through a shape that no test refuses. The key points come from `keyAt`, which
is handed in.

  `Seat5.keysFit`   each call's key point has just as many coordinates as the call has bits of keys
  `seatAtK`         the public data at a segment (`seatAt`), and nothing where this test fails
  `k5LotK`          the lot's honest side over `seatAtK`: IT TAKES THE PLACE OF `k5Lot`

No move refuses: the test stands where the public data are made, on public data alone.

Limits. `k5Lot` AND `seatAt` OF Honest/K5/Row.lean STAND AS THEY WERE AND ASK TWO TESTS: nothing
here keeps a list of lots from naming `k5Lot`: it must name `k5LotK`. A half laid by hand at public
data of any make is met by no test. The test is asked at challenges that are all 0; that `keyAt`
yields the same sizes at all challenges of these shapes is a named premise of the laws (`KeySizes`,
Honest/K5/Law/Fits.lean; `KeyWide`, Honest/K5/Law/FitsRun.lean), had where `keyAt` is `keyOfK3`
(`keySizes_K3`, `keyWide_K3`, Honest/K5/Law/KeyOfK3.lean); `KeyWide` at a reader that cuts the
key points out of the first round heard is not shown here.
Key points of the right lengths that are another call's, or in another order, pass. `seatAtK` and
`k5LotK.halves` are evaluated by no test: they want the public files' data.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E)

variable {W₀ Rc Xi Tr X : Type}

/-- **THE PUBLIC DATA FIT, THIRD TEST: each call's key point has just as many coordinates as the
call has bits of keys**, and there are as many key points as calls. front: challenges of the shapes
of the rounds in front of the place. With code, on public data alone. -/
def Seat5.keysFit (Z : Seat5) (front : List Fmt.Drawn) : Bool :=
  (Z.keyAt front).map (·.size) == Z.P.g.calls.map (·.n)

/-- The public data at an attention segment, as `seatAt` makes them; nothing where `seatAt` yields
nothing or where the third test fails at the first chain's declared rounds in front. -/
def seatAtK (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) (G : Ground)
    (l : Nat) (nm : String) (g : Nat) : Option Seat5 :=
  (seatAt keyOf Z G l nm g).bind fun Y =>
    if Y.keysFit (blankDraws (Z.D.1.take Y.base)) then some Y else none

/-- What `seatAtK` yields, `seatAt` yields, and the third test says yes there: so a law on what
`seatAt` yields serves here, with the third test in hand. -/
theorem seatAtK_spec {keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)} {Z : Pub}
    {G : Ground} {l : Nat} {nm : String} {g : Nat} {Y : Seat5}
    (h : seatAtK keyOf Z G l nm g = some Y) :
    seatAt keyOf Z G l nm g = some Y ∧ Y.keysFit (blankDraws (Z.D.1.take Y.base)) = true := by
  unfold seatAtK at h
  cases hs : seatAt keyOf Z G l nm g with
  | none => simp [hs] at h
  | some Y' =>
    simp only [hs, Option.bind_some] at h
    by_cases hk : Y'.keysFit (blankDraws (Z.D.1.take Y'.base)) = true
    · simp only [hk, if_true, Option.some.injEq] at h
      subst h
      exact ⟨rfl, hk⟩
    · simp [hk] at h

/-- **The lot's honest side, with all three tests asked**: a half at every attention segment whose
public data fit. keyOf: the key points' reader at a segment. -/
def k5LotK (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := "K5: the attention segments' own rounds"
    halves := fun Z G => (H2K5.k5Places G).filterMap fun y =>
      (seatAtK keyOf Z G y.1 y.2.1 y.2.2).map (k5Half cells) }

/-- The name is the lot's, letter for letter. -/
theorem k5LotK_name (cells : Tr → Cells)
    (keyOf : Pub → Ground → Nat → List Fmt.Drawn → Array (Array E)) (Z : Pub) :
    (k5LotK (W₀ := W₀) (Rc := Rc) (Xi := Xi) (X := X) cells keyOf).name = (H2K5.lotN Z).name := rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.seatAtK_spec
#print axioms ProofFile.Honest.K5.k5LotK_name
