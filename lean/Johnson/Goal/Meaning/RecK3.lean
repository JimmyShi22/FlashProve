-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK3.lean: kind K3's blocks at the first chain's record write neither the
statement nor a copy of the frame of the links: they are Quiet (Johnson/Goal/Meaning/RecQuiet.lean).

  quiet_mark, quiet_putFork, quiet_putTl, quiet_hearLook: four writers of
  Johnson/Desc/First/State.lean are Quiet. k3_block_whole: A GENERAL RULE, at any record and seat: a
    reflexive relation that the seat's two layings (put, mark) keep is kept by the kind's block
    (Johnson/Desc/First/Look/K3Lookup.lean): by its decide and by its two runs of claims ("objects",
    "guests"); it has no run behind the batching.
  seatCalls_put, seatCalls_mark, seatDigits_put, seatDigits_mark: the two seats at the record
  (K3Seat.lean) lay Quietly. quietLook_quiet, quietDigits_quiet, quietHead_quiet, quietAt_quiet: so
  are the steps without a round behind the kind's block (K3Whole.lean).
THE FORM OVER THE VARIANT's GROUND (N): theOwn_quiet and theWhole_quiet | _rec | _grows stand in
Johnson/Goal/Meaning/RecK3More.lean there: K3Own.lean's theOwn is made of K3.Law.blockVia on that
ground, whose rule blockVia_whole lies in that file.
Not claimed: anything on a block of the kind with guests at the record (theOwn hands in none), or on
the second form of the kind (Johnson/Desc/First/Look/K3LookupGeneral.lean, Via/Rounds.lean).
OBJECT: the makers' blocks and steps that are named above. USERS: through whole_rec |
recRel_of_quiet the walk (Johnson/Goal/Meaning/RecWalk.lean: recAll_border, at the letters cs and
sh); through whole_grows | groundKeeps_grows the owed premise of Johnson/Desc/StatementGrows.lean
(ChainKeeps (GrowsBy st) c). Neither calls them yet. Which maker stands at which place of a seated
text is not said here.
-/
import Johnson.Goal.Meaning.RecQuiet
import Johnson.Desc.First.Look.K3Whole
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Fn)

/-! ## Four writers -/

theorem quiet_mark (s : S) (name : String) : Quiet s (s.mark name) := by
  unfold S.mark
  split
  · exact quiet_refl s
  · rename_i hn
    exact ⟨⟨rfl, fun _ h => h, rfl, rfl⟩, rfl, fun w => w, fun _ e => by rw [hn] at e; cases e⟩

theorem mark_stays (s : S) (name : String) {e : String} (h : s.failed = some e) :
    (s.mark name).failed = some e := (quiet_mark s name).failed h

theorem mark_waits (s : S) (name : String) : (s.mark name).noneWaits = s.noneWaits := by
  unfold S.mark
  split <;> rfl

/-- A tactic for a writer that leaves the statement, every copy, the book, the count of roots and
the link's name. -/
local macro "still" d:ident : tactic =>
  `(tactic| (refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> unfold $d <;> repeat' split) <;>
    first
    | (intro w; first | exact w | exact (mark_waits _ _).trans w)
    | (intro e h; first | exact h | exact mark_stays _ _ h)
    | (simp_all [framesIn, ctxW, ctxOf, openOf, armOf, S.link?, S.mark] <;> (repeat' split) <;>
        simp_all))

theorem quiet_putFork (s : S) (F : Fork) : Quiet s (s.putFork F) := by
  still S.putFork

theorem quiet_putTl (s : S) (tl : HTailF2) : Quiet s (s.putTl tl) := by
  still S.putTl

theorem quiet_hearLook (s : S) (g : Forest.Heard) : Quiet s (s.hearLook g) := by
  unfold S.hearLook
  split
  · rename_i a ha
    split
    · exact quiet_mark s _
    · refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
        by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
  · rename_i a ha
    split
    · exact quiet_mark s _
    · refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
        by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
      unfold framesIn at hf ⊢
      rw [ha]
      exact hf
  · rename_i a ha
    split
    · exact quiet_mark s _
    · split
      · exact quiet_mark s _
      · refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
          by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
        unfold framesIn at hf ⊢
        rw [ha]
        exact hf
  · exact quiet_mark s _

/-! ## The kind's block, at any seat -/

/-- **A reflexive relation that the seat's two layings keep is kept by the kind's block.** -/
theorem k3_block_whole {T Cl : Type} (R : T → T → Prop) (hr : ∀ s, R s s) (seat : K3.Seat T Cl)
    (hput : ∀ s g G, R s (seat.put s g G)) (hmark : ∀ s G, R s (seat.mark s G)) (piece : Nat)
    (laid : Array Nat) (before : List (Nat × Nat)) (p : First.Look.P)
    (guests : List (First.Look.Guest T Cl)) :
    Whole R (K3.block seat piece laid before p guests) := by
  refine ⟨fun s rs gs s' h => ?_, fun c hc n s y h => ?_, (fun _ hc => nomatch hc)⟩
  · obtain ⟨F, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨x, _, h⟩ := bindE h
    cases h
    exact hput _ _ _
  · rcases List.mem_cons.1 hc with rfl | hc
    · obtain ⟨F, _, h⟩ := bindE h
      obtain ⟨g, _, h⟩ := bindE h
      cases h
      exact hmark _ _
    · rcases List.mem_cons.1 hc with rfl | hc
      · have h' := Keeps.named_ok h
        obtain ⟨l, _, e⟩ := Option.map_eq_some_iff.1 h'
        rw [← e]
        exact hr _
      · cases hc

/-! ## The two seats at the record -/

variable {Cl : Type}

theorem seatCalls_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    Quiet s ((K3.seatCalls claim).put s g G) :=
  quiet_trans _ _ _ (quiet_putFork s G) (quiet_hearLook _ g)

theorem seatCalls_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    Quiet s ((K3.seatCalls claim).mark s G) := quiet_putFork s G

theorem seatDigits_put (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork) :
    Quiet s ((K3.seatDigits claim).put s g G) := by
  show Quiet s (match s.tl?, s.fork? with
    | some tl, some F =>
      (s.putTl { tl with
        foldDrawn := tl.foldDrawn + 1, slotA := F.next, slotB := G.next,
        heard := some g }).putFork G
    | _, _ => s.mark "K3 seat: no record of the smallness test")
  split
  · exact quiet_trans _ _ _ (quiet_putTl s _) (quiet_putFork _ G)
  · exact quiet_mark s _

theorem seatDigits_mark (claim : Aff → Cl) (s : S) (G : Fork) :
    Quiet s ((K3.seatDigits claim).mark s G) := quiet_putFork s G

/-- Whole reads a block through decide, claims and after alone. -/
theorem whole_same {T : Type} {R : T → T → Prop} {b c : Block T Cl} (W : Whole R b)
    (e1 : c.decide = b.decide) (e2 : ∀ x ∈ c.claims, x ∈ b.claims) (e3 : c.after = b.after) :
    Whole R c :=
  ⟨fun s rs gs s' h => W.1 s rs gs s' (e1 ▸ h), fun x hx => W.2.1 x (e2 x hx),
    fun x hx => W.2.2 x (e3 ▸ hx)⟩

/-! ## The steps without a round -/

theorem quietLook_quiet (fs : Forest.Shape) : Fn Quiet (K3.quietLook fs) := fun s s' h => by
  unfold K3.quietLook at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  cases h
  exact quiet_refl s

theorem quietDigits_quiet (used claims : Nat) : Fn Quiet (K3.quietDigits used claims) :=
  fun s s' h => by
  unfold K3.quietDigits at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  cases h
  exact quiet_putFork s G

theorem quietHead_quiet (X : Verify.Public) : Fn Quiet (K3.quietHead X) := fun s s' h => by
  unfold K3.quietHead at h
  split at h
  · rename_i a ha
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    obtain ⟨_, _, h⟩ := bindE h
    cases h
    refine ⟨⟨rfl, fun f hf => ?_, rfl, rfl⟩,
      by first | rfl | simp [ctxW, ctxOf, openOf, armOf, S.link?, *], fun w => w, fun _ e => e⟩
    unfold framesIn at hf ⊢
    rw [ha]
    exact hf
  · cases h

theorem quietAt_quiet (X : Verify.Public) (i : Nat) (digits : Bool)
    {f : S → Except String S} (h : K3.quietAt X i digits = some f) : Fn Quiet f := by
  unfold K3.quietAt at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact quietHead_quiet X)
    | (cases h; exact quietLook_quiet _)
    | (obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.1 h; exact quietDigits_quiet _ _)
    | cases h

#print axioms k3_block_whole
#print axioms quietAt_quiet

end Meaning.K2
