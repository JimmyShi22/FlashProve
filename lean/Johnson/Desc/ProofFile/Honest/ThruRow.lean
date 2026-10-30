-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/ThruRow.lean: A ROW READ THROUGH: THE LAW FOR THE SIMULATORS' SLOT. General in the kind: no kind is named.
A row of parts with simulators that meets the fields fits, exact and fresh of `Good` at one input type meets them at another input
type when each part is read through (`Part.thru`, Honest/Thru.lean) and each simulator stays as it is. It serves a kind whose rows are fixed at
an unread input type. A kind whose rows are general in the readers of the index and of the tables' randomness does not need it: its
lifts read through are its lifts at the readers composed (`Part.lift_thru`), as Honest/K14/Sim/Through.lean shows.

  `Member.thru`, `Side.thru`, `members_thru`, `seated_thru`, `fits_thru`, `shows_thru`   **what a member read through shows is what the member shows at the narrowed
                  stand**, by `play_thru` (Honest/ThruThreads.lean), `Step.thru`, `Mid.narrow` (Honest/ThruRun.lean)
  `Faces`, `faces_shared`, `faces_own`   the one premise on the two faces: the public field and what the second stop sees are read
                  through; it holds at the two readers of `OnlineProverParts.through`
  `onRowReadThrough`, `good_thru`   **the law**, at A := False, and at any On that gives the row's own at the narrowed stand; its two fields exact and
                  fresh are proved inside it
  `Unlettered.thru`, `SLot.thru`, `half_thru`, `toHLot_thru`   the row and the lot read through; they have the sides read through

Limits. NOTHING IS SAID OF `plays` AND `acc`: `good_thru` is at A := False, where these two are met for nothing. NOTHING IS SAID OF A RUN: no thread,
no `OnFromS`, no `BudDebts` is carried here: a kind fixed at a closed input type whose On asks something proves these at the term's types, or
the crossing is made once above the rule by `runC_thru` (Honest/ThruRun.lean). `onRowReadThrough` ASKS On AT THE MEMBER THAT THE ROW HOLDS AT THAT NUMBER: so a stranger that reads to the same member is asked nothing. `bud` stays the same letter. Laws over a
random `rc` do not cross by this file: every part is handed `rd rc`. `owed_thru` (Johnson/T3/OwedThru.lean) calls `good_thru`, with its own `onThruRow`, of the same text; `Unlettered.thru`, `SLot.thru` and `toHLot_thru` serve the lot's form alone: K14 does not use them. No property of the protocol is claimed: nothing on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.ThruThreads
import Johnson.Desc.ProofFile.Honest.Side
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place)

variable {S Cl V V' W W' X Pb : Type}

/-- A member read through: its part; its simulator stays. -/
def Member.thru (see : V' → V) (wit : W' → W) (u : Member V W X Pb) : Member V' W' X Pb :=
  ⟨u.number, u.rounds, u.part.thru see wit, u.sim⟩

/-- A row read through. -/
def rowThru (see : V' → V) (wit : W' → W) (row : List (Part V W X × Sim Pb)) :
    List (Part V' W' X × Sim Pb) :=
  row.map fun x => (x.1.thru see wit, x.2)

/-- A side read through: its sub-protocol and its fall stay. -/
def Side.thru (see : V' → V) (wit : W' → W) (σ : Side S Cl V W X Pb) : Side S Cl V' W' X Pb :=
  ⟨σ.block, rowThru see wit σ.row, σ.fall⟩

/-- Its members are the members read through. -/
theorem membersOf_thru (see : V' → V) (wit : W' → W) : ∀ (row : List (Part V W X × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)),
    membersOf (rowThru see wit row) j rs = (membersOf row j rs).map (Member.thru see wit)
  | [], _, _ => rfl
  | x :: l, j, rs => by
    have e : (x.1.thru see wit).moves.length = x.1.moves.length := by
      simp [Part.thru, Part.lift]
    show membersOf ((x.1.thru see wit, x.2) :: rowThru see wit l) j rs = _
    unfold membersOf
    rw [e, membersOf_thru see wit l]
    rfl

theorem members_thru (see : V' → V) (wit : W' → W) (σ : Side S Cl V W X Pb) :
    (σ.thru see wit).members = σ.members.map (Member.thru see wit) :=
  membersOf_thru see wit σ.row 0 _

/-- A seated side read through is the side seated at the row read through. -/
theorem seated_thru (see : V' → V) (wit : W' → W) (bs : List (Block S Cl)) (a : Place)
    (row : List (Part V W X × Sim Pb)) (fs : List (Fall S)) :
    Side.seated bs a (rowThru see wit row) fs = (Side.seated bs a row fs).map (Side.thru see wit) := by
  unfold Side.seated
  cases bs.find? (fun b => b.place == a) <;> rfl

/-- **fits stays.** -/
theorem fits_thru (see : V' → V) (wit : W' → W) (σ : Side S Cl V W X Pb) :
    (σ.thru see wit).fits = σ.fits := by
  unfold Side.fits Side.half Side.thru rowThru Placed.rounds
  simp [List.zipIdx_map, Function.comp_def, Part.thru, Part.lift, List.foldl_map]

/-- **What a member read through shows is what the member shows at the narrowed stand**, where what the second stop is handed is
read through. -/
theorem shows_thru (see : V' → V) (wit : W' → W) {φ' : Face V' W' Pb} {φ : Face V W Pb}
    (hsee : ∀ w, (φ'.sees w).map see = φ.sees (wit w)) (σ : Side S Cl V W X Pb)
    (u : Member V W X Pb) (c : u.part.Coins) (m : Mid W' X) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) :
    (σ.thru see wit).shows φ' (u.thru see wit) c m ds asks = σ.shows φ u c (m.narrow wit) ds asks := by
  unfold Side.shows
  show ((play ((u.part.thru see wit).steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
    (φ'.sees m.st.input) c) ds [] m).toOption.map fun y => shownOf y.1 asks) = _
  rw [Part.steps_thru see wit u.part _ _ _ _ _ (hsee m.st.input)]
  have e := play_thru wit (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
    (φ.sees (wit m.st.input)) c) ds [] m
  show _ = ((play (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
    (φ.sees (wit m.st.input)) c) ds [] (m.narrow wit)).toOption.map fun y => shownOf y.1 asks)
  rw [← e]
  cases play ((u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds
    (φ.sees (wit m.st.input)) c).map (Step.thru wit)) ds [] m <;> rfl

/-- **The one premise on the two faces**: the public field and what the second stop sees are read through. -/
structure Faces (see : V' → V) (wit : W' → W) (φ' : Face V' W' Pb) (φ : Face V W Pb) : Prop where
  pub : ∀ w, φ'.pub w = φ.pub (wit w)
  sees : ∀ w, (φ'.sees w).map see = φ.sees (wit w)

/-- The premise at the shared chain: the key stays; its second stop sees nothing. -/
theorem faces_shared {W₀ W₀' Rc Rc' Ky : Type} (g : W₀' → W₀) (rd : Rc' → Rc) :
    Faces id (Common.thru (Ky := Ky) g rd) .shared .shared :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- The premise at the first and the last chain: the instance stays; the second stop sees the input read through. -/
theorem faces_own {W₀ W₀' Rc Rc' Xi Tr : Type} (g : W₀' → W₀) (rd : Rc' → Rc) :
    Faces (Local.thru (Xi := Xi) (Tr := Tr) g rd) (Local.thru g rd) .own .own :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- **The sentence at entry of a row read through**: the row's own, at the narrowed stand, at the member that the row holds at that number. -/
def onRowReadThrough (see : V' → V) (wit : W' → W) (row : List (Part V W X × Sim Pb))
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop) :
    (u : Member V' W' X Pb) → CsAll u.part.carries → Mid W' X → Before → Prop :=
  fun u' ca m f => ∀ (u : Member V W X Pb) (h : u' = u.thru see wit),
    row[u.number]? = some (u.part, u.sim) → On u (cast (by subst h; rfl) ca) (m.narrow wit) f

section law
variable {see : V' → V} {wit : W' → W} {φ' : Face V' W' Pb} {φ : Face V W Pb}
  {σ : Side S Cl V W X Pb} {Bk : ProverCoinCounts} {ord : List Place} {chain firstTree : Nat}
  {pre : List (Nat × Nat × List Fmt.DeclaredRound)}

/-- **`Good` at a side, at A := False, gives `Good` at the side read through.** `On'`: any sentence at entry that gives the row's own at the
narrowed stand (`onRowReadThrough` is one). -/
theorem good_thru (hF : Faces see wit φ' φ)
    {B : Coins Bk → S → Mid W X → Env → Prop} {B' : Coins Bk → S → Mid W' X → Env → Prop}
    {On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {On' : (u : Member V' W' X Pb) → CsAll u.part.carries → Mid W' X → Before → Prop}
    {bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop}
    (hOn : ∀ u ∈ σ.members, ∀ ca m f, On' (u.thru see wit) ca m f → On u ca (m.narrow wit) f)
    (hG : Good pre φ σ Bk ord chain firstTree (fun _ _ _ _ => False) B On bud) :
    Good pre φ' (σ.thru see wit) Bk ord chain firstTree (fun _ _ _ _ => False) B' On' bud :=
  { fits := (fits_thru see wit σ).trans hG.fits
    plays := fun _ _ _ _ _ h => h.elim
    acc := fun _ _ _ _ _ h => h.elim
    exact := by
      intro u' hu' ca m front ds asks ho hs hp hd hb hh hst
      rw [members_thru] at hu'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
      have hst' : u.part.stopAt (φ.sees (m.narrow wit).st.input) (m.narrow wit).loc ds ≠ some .hid := by
        show u.part.stopAt (φ.sees (wit m.st.input)) m.loc ds ≠ some .hid
        rw [← Part.stopAt_thru see wit u.part _ _ (hF.sees m.st.input)]
        exact hst
      have key := hG.exact u hu ca (m.narrow wit) front ds asks (hOn u hu ca m front ho) hs hp hd hb hh hst'
      have e1 : (fun c : Cs (u.thru see wit).part.takes × CsAll (u.thru see wit).part.spends =>
          (σ.thru see wit).shows φ' (u.thru see wit) (c.1, c.2, ca) m ds asks) =
          fun c => σ.shows φ u (c.1, c.2, ca) (m.narrow wit) ds asks :=
        funext fun c => shows_thru see wit hF.sees σ u (c.1, c.2, ca) m ds asks
      have e2 : (fun c : Cs (u.thru see wit).sim.takes =>
          (u.thru see wit).tells φ' c m.st.input front ds asks) =
          fun c => u.tells φ c (m.narrow wit).st.input front ds asks := by
        funext c
        show u.sim.tell (φ'.pub m.st.input) front ds asks c = u.sim.tell (φ.pub (wit m.st.input)) front ds asks c
        rw [hF.pub]
      rw [e1, e2]
      exact key
    fresh := by
      intro u' hu' p sp ca m ds asks hd hb hst
      rw [members_thru] at hu'
      obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hu'
      have hst' : u.part.stopAt (φ.sees (m.narrow wit).st.input) (m.narrow wit).loc ds ≠ some .hid := by
        show u.part.stopAt (φ.sees (wit m.st.input)) m.loc ds ≠ some .hid
        rw [← Part.stopAt_thru see wit u.part _ _ (hF.sees m.st.input)]
        exact hst
      have key := hG.fresh u hu p sp ca (m.narrow wit) ds asks hd hb hst'
      have e1 : ∀ c : Cs u.part.takes, (σ.thru see wit).shows φ' (u.thru see wit) (c, sp, ca) m ds asks =
          σ.shows φ u (c, sp, ca) (m.narrow wit) ds asks :=
        fun c => shows_thru see wit hF.sees σ u (c, sp, ca) m ds asks
      simp only [e1]
      exact key }

/-- The sentence `onRowReadThrough` gives the row's own, at a member that the row holds. -/
theorem onRowReadThrough_gives (row : List (Part V W X × Sim Pb))
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (u : Member V W X Pb) (ca : CsAll u.part.carries) (m : Mid W' X) (f : Before)
    (hu : row[u.number]? = some (u.part, u.sim))
    (h : onRowReadThrough see wit row On (u.thru see wit) ca m f) : On u ca (m.narrow wit) f :=
  h u rfl hu

end law

/-- **A row without letters read through.** -/
def Unlettered.thru (see : V' → V) (wit : W' → W) (r : Unlettered V W X Pb) : Unlettered V' W' X Pb :=
  ⟨r.place, rowThru see wit r.row, onRowReadThrough see wit r.row r.On, r.bud⟩

/-- Its half is the half read through. -/
theorem half_thru (see : V' → V) (wit : W' → W) (r : Unlettered V W X Pb) :
    (r.thru see wit).half = r.half.thru see wit := by
  unfold Unlettered.thru Unlettered.half Placed.thru rowThru
  simp

/-- **A lot with simulators read through.** -/
def SLot.thru (see : V' → V) (wit : W' → W) (l : SLot V W X Pb) : SLot V' W' X Pb :=
  ⟨l.name, fun Z G => (l.rows Z G).map (Unlettered.thru see wit)⟩

/-- Its honest side is the lot's read through. -/
theorem toHLot_thru (see : V' → V) (wit : W' → W) (l : SLot V W X Pb) :
    (l.thru see wit).toHLot = l.toHLot.thru see wit := by
  refine HLot.ext' rfl ?_
  funext Z G
  show ((l.rows Z G).map (Unlettered.thru see wit)).map (·.half) =
    ((l.rows Z G).map (·.half)).map (Placed.thru see wit)
  simp only [List.map_map]
  exact List.map_congr_left fun r _ => half_thru see wit r

end ProofFile.Honest

#print axioms ProofFile.Honest.members_thru
#print axioms ProofFile.Honest.seated_thru
#print axioms ProofFile.Honest.fits_thru
#print axioms ProofFile.Honest.shows_thru
#print axioms ProofFile.Honest.faces_shared
#print axioms ProofFile.Honest.faces_own
#print axioms ProofFile.Honest.good_thru
#print axioms ProofFile.Honest.onRowReadThrough_gives
#print axioms ProofFile.Honest.half_thru
#print axioms ProofFile.Honest.toHLot_thru
