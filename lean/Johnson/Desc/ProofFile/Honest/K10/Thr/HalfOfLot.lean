-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Thr/HalfOfLot.lean: the closing of a segment (K10): which half a list of halves holds
first at a closing's place, where the list holds the halves of the lot with the closings alone (`seatLotC`,
Honest/K10/SeatLotC.lean). A half is the prover's side of one sub-protocol: a place and a list of parts (`Placed`,
Honest/Frame.lean). The functions that play a chain take, at a sub-protocol's place, the first half of the prover's list
that stands there. No thread is named here. Four definitions, one of them a test with code; eleven theorems. It serves
whoever has to show the field half of `CloseAt` (Honest/K10/Thr/CloseAt.lean) at a prover whose list of halves is made
of lots.

  `lotJob`, `lotHalf`   the lot's job at a place's numbers Q (`seatedJob`, Honest/K10/SimSeat.lean, at what the lot lays
                    off the public part Z and the ground G); and the half at Q's place whose one part is
                    `closePart (foldShellT true (lotJob … Q) foldWords)`: the move for the round "BAT", then the fold's
                    part in the form that refuses at no move (Honest/K10/Half.lean, Sim.lean)
  `lotJob_par`, `lotJob_stAt`   the job's place has the numbers Q; its `stAt` is the lot's third parameter at the
                    input's own instance and Q: both by unfolding
  `lotHalf_mem`     where Q is one of the numbers that the lot reads (`closePars`, Honest/K10/AtLot.lean), `lotHalf` at
                    Q is one of the lot's halves
  **`find_in_lot`**   under `IM.Open` (Johnson/IMR/SeatOpen.lean): among the lot's own halves the first at Q's place is
                    `lotHalf` at Q. The halves differ from place to place, so this needs that no two of them stand at
                    one place: `seatLotC_once` (Honest/K10/LotPlaces.lean), `find_of_nodup` (SimLot.lean)
  `noK10`, `find_front`   a test with code: no half of a list stands at a place of the kind K10; where it says yes,
                    nothing is found in the list at a closing's place (`find_none_of_places`, Honest/FirstFind.lean)
  **`find_closing`**  so in a list A, then the lot's halves, then a list B, where `noK10 A` says yes: the first half at
                    Q's place is `lotHalf` at Q. B is free
  `firstOf_mid`, `firstOf_closeC`   `firstOf` (Honest/Frame.lean) at lots Ls, then a lot, then lots Rs, is what Ls
                    lays, then that lot's halves, then what Rs lays; the same at `seatLotC`
  `ClosingsFirst hs readers rows stAt Z G`   a premise on a list of halves hs, by name: at each Q that the lot reads,
                    the first half of hs at Q's place has the one part that `lotHalf` at Q has
  **`first_of_list`**, **`first_of_lots`**, **`first_of_kinds`**   three ways to that premise, each under `IM.Open`.
                    The first: hs is A, then the lot's halves, then B (hT), and `noK10 A` says yes (hA). The second: hs
                    is `firstOf` at lots Ls, then a lot Lc, then lots Rs (hT); at Z and G the halves of Lc are
                    `seatLotC`'s (hLc); `noK10` says yes of what Ls lays (hA). The third: hs is `firstOf` at a list of
                    lots (hT) that holds such an Lc (hL, hLc), and each lot of the list has no half at a place of the
                    kind K10 or has the halves of Lc (ho): by `firstOf_find_kind` (Honest/FirstFindKind.lean)

Why a lot Lc and not `seatLotC` itself. A lot's halves are a function of the public part and the ground, and of nothing
else. `seatLotC`'s third parameter may name a chain (the filler `stAtZero`, Honest/K10/StAtZero.lean, does). A lot that
first makes the chain out of the public part that it is handed, and lays `seatLotC`'s halves at that chain where the
making returns, is not the lot `seatLotC` at one fixed chain: the two lay the same halves at the public part of which
that chain is made, and need not elsewhere. So hLc asks for the halves at Z and G, not for the lot. At `seatLotC` itself
hLc is `rfl`.

Limits. What a prover's list of halves is, at any filling, is not said here: hs, A, B, Ls, Rs, Lc and the list of lots
are letters, and hT, hA, hL, hLc and ho are premises, shown of no prover. readers, rows, stAt and G are letters too:
nothing of them is read. `noK10` is evaluated by no line. `ClosingsFirst` names the first half's parts alone, and holds
for nothing where `closePars Z` is empty. At every older hash, with no premise on scope; whether `IM.Open` can be had is
no theorem here. No statement here reads the part's moves. No property of the protocol is claimed: nothing is said on
its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.LotPlaces
import Johnson.Desc.ProofFile.Honest.FirstFindKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Chain Place KindName FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (segmentsOf)

variable {W₀ Rc Xi Tr V W X : Type}

/-! ## The lot's job and half at a place -/

/-- **The lot's job at a place's numbers**: the seated job at the layout, the addresses and the segments that the lot
reads off the public part and the ground, and at the list of carried messages of that place. -/
abbrev lotJob (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) : CloseJob (Local W₀ Rc Xi Tr) :=
  seatedJob readers rows G.first.layout (addrsAt Z G) ((segmentsOf Z G).take (Q.link + 1)) stAt ⟨Q, borneAt Z Q⟩

/-- **The half at the place of these numbers**, with one part: the move for "BAT", then the fold's part at that job, in
the form that refuses at no move. -/
abbrev lotHalf (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  ⟨closePlace Q, [closePart (foldShellT true (lotJob readers rows stAt Z G Q) foldWords)]⟩

/-- The job's place has the numbers at which it is laid. -/
theorem lotJob_par (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) : (lotJob readers rows stAt Z G Q).pub.par = Q := rfl

/-- The job's statement is the lot's third parameter at the input's own instance and the place's numbers. -/
theorem lotJob_stAt (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (Q : Par) (v : Local W₀ Rc Xi Tr) (s : Seen) (f : List Fmt.Drawn) :
    (lotJob readers rows stAt Z G Q).stAt v s f = stAt v.x Q s f := rfl

/-- At numbers that the lot reads, that half is one of the lot's halves. -/
theorem lotHalf_mem (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) {Q : Par} (hQ : Q ∈ closePars Z) :
    lotHalf (X := X) readers rows stAt Z G Q ∈ (seatLotC (X := X) readers rows stAt).halves Z G := by
  rw [seatLotC_halves]
  exact List.mem_map.2 ⟨Q, hQ, rfl⟩

/-! ## The first half at a closing's place -/

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

/-- **Among the lot's own halves, the first that stands at a place which the lot reads is the half at that place's
numbers.** -/
theorem find_in_lot (O : IM.Open o pol lay KL F Z Bs base c A' B') (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground) {Q : Par} (hQ : Q ∈ closePars Z) :
    ((seatLotC (X := X) readers rows stAt).halves Z G).find? (fun e => e.place == closePlace Q) =
      some (lotHalf readers rows stAt Z G Q) := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem (lotHalf_mem (X := X) readers rows stAt Z G hQ)
  exact find_of_nodup (fun e : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X => e.place)
    ((seatLotC (X := X) readers rows stAt).halves Z G) i (lotHalf readers rows stAt Z G Q)
    (seatLotC_once readers rows stAt G O) hi

end

/-- **A test with code: no half of the list stands at a place of the kind K10.** -/
def noK10 (A : List (Placed V W X)) : Bool := A.all fun e => e.place.kind != .K10

/-- Where the test says yes, nothing is found in the list at a closing's place. -/
theorem find_front {A : List (Placed V W X)} (hA : noK10 A = true) (Q : Par) :
    A.find? (fun e => e.place == closePlace Q) = none := by
  refine find_none_of_places fun e he hc => ?_
  have hk : (e.place.kind != KindName.K10) = true := List.all_eq_true.1 hA e he
  have e1 : e.place.kind = KindName.K10 := (congrArg Place.kind hc :)
  rw [e1] at hk
  exact absurd hk (by decide)

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

/-- **The first half at a closing's place**, in a list that holds the lot's halves behind halves of other kinds, is the
half at that place's numbers. -/
theorem find_closing (O : IM.Open o pol lay KL F Z Bs base c A' B') (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    {A B : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)} (hA : noK10 A = true) {Q : Par}
    (hQ : Q ∈ closePars Z) :
    (A ++ (seatLotC readers rows stAt).halves Z G ++ B).find? (fun e => e.place == closePlace Q) =
      some (lotHalf readers rows stAt Z G Q) := by
  rw [List.append_assoc, List.find?_append, find_front hA Q, List.find?_append,
    find_in_lot O readers rows stAt G hQ]
  rfl

end

/-- What a list of lots lays is what the lots in front of one of them lay, then that lot's halves, then what the lots
behind it lay. -/
theorem firstOf_mid (Z : ProofFile.Pub) (G : ProofFile.Ground) (Ls Rs : List (HLot V W X)) (Lc : HLot V W X) :
    firstOf Z G (Ls ++ Lc :: Rs) = firstOf Z G Ls ++ Lc.halves Z G ++ firstOf Z G Rs := by
  simp only [firstOf, List.flatMap_append, List.flatMap_cons, List.append_assoc]

/-- The same at the lot with the closings alone. -/
theorem firstOf_closeC (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (Ls Rs : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) :
    firstOf Z G (Ls ++ seatLotC readers rows stAt :: Rs) =
      firstOf Z G Ls ++ (seatLotC readers rows stAt).halves Z G ++ firstOf Z G Rs :=
  firstOf_mid Z G Ls Rs (seatLotC readers rows stAt)

/-! ## The premise on a list of halves, and three ways to it -/

/-- **A premise on a list of halves, by name**: at each place that the lot reads, the first half of the list at that
place has one part: the move for "BAT", then the fold's part at the lot's job of that place. A definition, meant as a
premise; nothing is claimed of it. -/
def ClosingsFirst (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) : Prop :=
  ∀ Q ∈ closePars Z, ∃ g, (hs.find? fun e => e.place == closePlace Q) = some g ∧
    g.parts = [closePart (foldShellT true (lotJob readers rows stAt Z G Q) foldWords)]

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
  {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} {A' : ProofFile.SharedSeat} {B' : ProofFile.SecondSeat}

/-- **The premise holds of a list of this form**: halves of other kinds, then the lot's halves, then any list. -/
theorem first_of_list (O : IM.Open o pol lay KL F Z Bs base c A' B') (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    {hs A B : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    (hT : hs = A ++ (seatLotC readers rows stAt).halves Z G ++ B) (hA : noK10 A = true) :
    ClosingsFirst hs readers rows stAt Z G := by
  intro Q hQ
  subst hT
  exact ⟨lotHalf readers rows stAt Z G Q, find_closing O readers rows stAt G hA hQ, rfl⟩

/-- **The premise holds of what a list of lots lays**, where one of them lays the lot's halves at this public part and
ground, and no lot in front of it lays a half at a place of the kind K10. -/
theorem first_of_lots (O : IM.Open o pol lay KL F Z Bs base c A' B') (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {Ls Rs : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {Lc : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X} (hT : hs = firstOf Z G (Ls ++ Lc :: Rs))
    (hLc : Lc.halves Z G = (seatLotC readers rows stAt).halves Z G) (hA : noK10 (firstOf Z G Ls) = true) :
    ClosingsFirst hs readers rows stAt Z G := by
  refine first_of_list O readers rows stAt G (A := firstOf Z G Ls) (B := firstOf Z G Rs) ?_ hA
  rw [hT, firstOf_mid, hLc]

/-- **The premise holds of what a list of lots lays**, where such a lot is in the list, and each lot of the list has no
half at a place of the kind K10 or has that lot's halves. -/
theorem first_of_kinds (O : IM.Open o pol lay KL F Z Bs base c A' B') (readers : Local W₀ Rc Xi Tr → Readers)
    (rows : RowDataOf Xi) (stAt : StAtOf Xi) (G : ProofFile.Ground)
    {hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {ls : List (HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)}
    {Lc : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X} (hT : hs = firstOf Z G ls) (hL : Lc ∈ ls)
    (hLc : Lc.halves Z G = (seatLotC readers rows stAt).halves Z G)
    (ho : ∀ M ∈ ls, (∀ e ∈ M.halves Z G, e.place.kind ≠ KindName.K10) ∨ M.halves Z G = Lc.halves Z G) :
    ClosingsFirst hs readers rows stAt Z G := by
  intro Q hQ
  subst hT
  have hg : (Lc.halves Z G).find? (fun e => e.place == closePlace Q) = some (lotHalf readers rows stAt Z G Q) := by
    rw [hLc]
    exact find_in_lot O readers rows stAt G hQ
  exact ⟨lotHalf readers rows stAt Z G Q, firstOf_find_kind (p := closePlace Q) hL ho hg, rfl⟩

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.lotJob
#print axioms ProofFile.Honest.K10.lotHalf
#print axioms ProofFile.Honest.K10.lotJob_par
#print axioms ProofFile.Honest.K10.lotJob_stAt
#print axioms ProofFile.Honest.K10.lotHalf_mem
#print axioms ProofFile.Honest.K10.find_in_lot
#print axioms ProofFile.Honest.K10.noK10
#print axioms ProofFile.Honest.K10.find_front
#print axioms ProofFile.Honest.K10.find_closing
#print axioms ProofFile.Honest.K10.firstOf_mid
#print axioms ProofFile.Honest.K10.firstOf_closeC
#print axioms ProofFile.Honest.K10.ClosingsFirst
#print axioms ProofFile.Honest.K10.first_of_list
#print axioms ProofFile.Honest.K10.first_of_lots
#print axioms ProofFile.Honest.K10.first_of_kinds
