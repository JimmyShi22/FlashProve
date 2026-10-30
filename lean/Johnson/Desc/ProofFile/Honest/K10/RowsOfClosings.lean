-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/RowsOfClosings.lean: the closing of a segment (kind K10), in the
form in which the frame takes a lot's rows: each row with its simulator, its condition and its
bound, and `Good` at the side of such a row.

The closing spends a run of 2 k + 1 coins and sends 1 + 2 k field elements. The map from the coins to
what is sent is one to one, up to a shift by values that do not read the run, so the simulator lays
uniform coins of its own in the same shape. That is the spender's half alone: the equation takes the
spent run as uniform and independent of all that it holds fixed, among which are the columns of the
table that is made of these very coins. Whether that is so in a run is the field `fresh` at the part
that owns the run, which is not stated here.

  `closingJob`   the job at a place's numbers, as the lot reads it
  `closingPairs`, `closingRow`   the part with its simulator; the row of one closing
  `closingsSLot`   the lot
  `closingRow_half`, `closingsSLot_toHLot`   the row's half; the lot without its simulators is
                   `seatLotC`
  `closing_good`, `closing_hand`   `Good` at a side of that row; what `file_owed_rows` asks at the laid
                   row

`Good` is stated at A := B := False: the fields `plays` and `acc` are met for nothing. The field
`fresh` is empty here, since the part owns no coin, and it is not the condition on the run's owner.
The premise on the book follows from no test of `ProverCoinCounts.clauses`; `bookWhole_spent_nil`
(Honest/BookOwners.lean) gives it at a whole book.
Simulator, condition and bound read nothing of the request, so no type here shuts out a request on
which the model has no value. But a part is handed an input only through `ready`, which refuses where
the request has no trace: what the honest prover does there is not said here.
-/
import Johnson.Desc.ProofFile.Honest.K10.SeatLotC
import Johnson.Desc.ProofFile.Honest.KindSheet
import Johnson.Desc.ProofFile.Honest.K10.SimSent
import Johnson.Desc.ProofFile.Honest.K10.SimLaws
import Johnson.Desc.ProofFile.Honest.Thread.RowsMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (segmentsOf)

variable {W₀ Rc Xi Tr X : Type}

/-! ## 1 The rows and the lot -/

/-- **The job at a place's numbers**, as the lot reads it off the public part and the ground. -/
abbrev closingJob (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) : CloseJob (Local W₀ Rc Xi Tr) :=
  seatedJob readers rows G.first.layout (addrsAt Z G) ((segmentsOf Z G).take (Q.link + 1)) stAt
    ⟨Q, borneAt Z Q⟩

/-- The cured part with its simulator. -/
def closingPairs {V W Y Pb : Type} (J : CloseJob W) : List (Part V W Y × Sim Pb) :=
  [(closePart (foldShellT true J foldWords), closeSim J.pub.par)]

/-- **The row of one closing**: condition and bound ask nothing at the total form. -/
def closingRow (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par) :
    Unlettered (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  ⟨closePlace Q, closingPairs (closingJob readers rows stAt Z G Q),
    closeOn true (closingJob readers rows stAt Z G Q), closeBud⟩

/-- **The lot**: a row at each place that `seatLotC` lays a half at. -/
def closingsSLot (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi) :
    SLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { name := (seatLotC (X := X) readers rows stAt).name
    rows := fun Z G => (closePars Z).map (closingRow readers rows stAt Z G) }

/-- **The lot without its simulators is `seatLotC`.** -/
theorem closingsSLot_toHLot (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) :
    (closingsSLot (X := X) readers rows stAt).toHLot = seatLotC readers rows stAt := by
  have h : (fun (Z : ProofFile.Pub) (G : ProofFile.Ground) =>
      ((closingsSLot (X := X) readers rows stAt).rows Z G).map (·.half)) =
      (seatLotC (X := X) readers rows stAt).halves := by
    funext Z G
    rw [seatLotC_halves]
    show ((closePars Z).map (closingRow (X := X) readers rows stAt Z G)).map (·.half) = _
    rw [List.map_map]
    rfl
  exact congrArg (HLot.mk (seatLotC (X := X) readers rows stAt).name) h

/-! ## 2 Good -/

section
variable {St Cl V W Y Pb : Type}

/-- **The member shows something**, at every coin. -/
theorem closing_shows_some (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb)
    (chain firstTree : Nat) (J : CloseJob W) {σ : Side St Cl V W Y Pb}
    (hp : closePlan J.pub.par) (hm : σ.members = [closeAt true J]) :
    ShowsSome pre φ σ chain firstTree (closeOn true J) closeBud := by
  intro u hu ca m front ds asks hOn _ _ hd _ _ _ c
  rw [hm] at hu
  obtain rfl := List.mem_singleton.1 hu
  obtain ⟨q, -, hq⟩ := sent_is J hp σ φ ca m front ds asks hOn hd
  rw [hq c]
  exact fun e => by cases e

/-- **`Good` at a side whose one member is the literal member**, at A := B := False, under the
place's test, the side's `fits` and the premise on the book. -/
theorem closing_good (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb) (Bk : ProverCoinCounts)
    (ord : List Place) (chain firstTree : Nat) (J : CloseJob W) {σ : Side St Cl V W Y Pb}
    (hp : closePlan J.pub.par) (hm : σ.members = [closeAt true J]) (hf : σ.fits = true)
    (hk : ∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = []) :
    Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) (fun _ _ _ _ => False)
      (closeOn true J) closeBud := by
  refine
    { fits := hf
      plays := fun _ _ _ _ _ h => h.elim
      acc := fun _ _ _ _ _ h => h.elim
      exact := ?_
      fresh := ?_ }
  · intro u hu ca m front ds asks hOn hs _ hd hb hh hst
    rw [hm] at hu
    obtain rfl := List.mem_singleton.1 hu
    exact close_exact J hp σ φ chain firstTree ca m front ds asks hOn hs hd hb hh hst
  · intro u hu p sp ca m ds asks hd hb hst
    rw [hm] at hu
    obtain rfl := List.mem_singleton.1 hu
    exact close_fresh true J σ φ Bk ord hk p sp ca m ds asks hd hb hst

end

/-- **What the rule `file_owed_rows` asks at the laid row**, from what is known of whichever side
`Side.seated` yields at the place. -/
theorem closing_hand {St Cl : Type} {Bk : ProverCoinCounts} (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (φ : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi) (ord : List Place)
    (chain firstTree : Nat) (bs : List (Block St Cl)) (fs : List (Fall St))
    (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (stAt : StAtOf Xi)
    (Z : ProofFile.Pub) (G : ProofFile.Ground) (Q : Par)
    (T : Local W₀ Rc Xi Tr →
      Thread Bk St Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi)
    (Sd : Local W₀ Rc Xi Tr → Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) X → Prop)
    (hp : closePlan Q)
    (hσ : ∀ σ : Side St Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi,
      Side.seated bs (closePlace Q) (closingPairs (closingJob readers rows stAt Z G Q)) fs = some σ →
        σ.members = [closeAt true (closingJob readers rows stAt Z G Q)] ∧ σ.fits = true ∧
          ∀ q, Bk.spentBy ⟨σ.block.place, 0⟩ q = []) :
    ∀ σ, ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd bs).side bs fs = some σ →
      ∃ A' B', Good pre φ σ Bk ord chain firstTree A' B'
        ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd bs).On
        ((closingRow (X := X) readers rows stAt Z G Q).lay T Sd bs).bud :=
  hand_of_seated (closingRow (X := X) readers rows stAt Z G Q) T Sd bs fun σ h =>
    ⟨_, _, closing_good pre φ Bk ord chain firstTree (closingJob readers rows stAt Z G Q) hp
      (hσ σ h).1 (hσ σ h).2.1 (hσ σ h).2.2⟩

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closingJob
#print axioms ProofFile.Honest.K10.closingPairs
#print axioms ProofFile.Honest.K10.closingRow
#print axioms ProofFile.Honest.K10.closingsSLot
#print axioms ProofFile.Honest.K10.closingsSLot_toHLot
#print axioms ProofFile.Honest.K10.closing_shows_some
#print axioms ProofFile.Honest.K10.closing_good
#print axioms ProofFile.Honest.K10.closing_hand
