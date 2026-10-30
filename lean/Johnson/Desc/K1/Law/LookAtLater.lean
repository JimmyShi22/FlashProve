-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LookAtLater.lean: the lookups' public
items (lookIn, lookOut, linkFresh, left, leftOn) over an accept of K1's two sorts of later
sub-protocol, at the composed test `pubAll D base`. An arm of hrest_plus13.
WHENCE. It is the file PubAtLaterLookAll.lean [not in this library], cut by
program: THE NAME "frame.liveIs" IS STRUCK: it has left the composed meaning's list of extra public
tests: the clause on it in `LaterLook`, its arm in `lookPaid` and in `pub_look_later`, and the two
steps of proof that served it. Nothing else turns. New: section 4.
IT CALLS five files (among them PubAtLaterLook.lean, PubAtQuietLook.lean, QuietLook.lean): linkFresh_at_later | lookOut_at_later |
lookIn_at_later · linkFresh_quiet | lookOut_quiet | lookIn_quiet · lookSame_layers | _head | _att.
  `lookSame_k1Quiet` · `HeardNone s` · `LaterLook B dgs HH` with its four members · `lookPaid D dgs`
  `pub_look_later`   **the items at pubAll**
  `dgsL`, `hhL`, `laterLook_blkL`   the sub-protocol at (l, d) is a member: at the digits at both
                     lookups, with nothing asked behind; at the reads at the lookup on the calls
                     alone, and HeardNone is asked of the state behind
What is not claimed. lookIn | lookOut at a piece that is neither of the segment's two lookups'
(k3SortAt = none). HeardNone at any state. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K1.Law.PubAtLaterLook
import Johnson.Desc.K1.Law.PubAtQuietLook
import Johnson.Desc.K1.Law.QuietLook
import Johnson.Desc.K1.Law.PileAtLater
import Johnson.Desc.K1.Law.LaterOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S Pub PubData pubAll)
open VerifiableInference.Desc.First.Look (K3Data linkFreshC lookInC lookOutC k3SortAt)
open VerifiableInference.Desc.Keeps (Decides)
open OnBytes.Model.Stages (LinkH)

variable {Cl Pp : Type}

/-! ## 1 The quiet sub-protocol behind the reads' sending -/

/-- It leaves the four readers of the state: by k1Quiet_decides (PileAtLater.lean). -/
theorem lookSame_k1Quiet (G : ProofFile.Ground) (l : Nat) (X : LinkH) :
    Decides LookSame (IM.k1Quiet G l X) :=
  k1Quiet_decides LookSame (fun _ _ _ _ _ h => lookSame_layers h)
    (fun _ _ _ _ _ h => lookSame_head h) (fun _ _ _ h => lookSame_att h) G l X

/-! ## 2 The lookups' three tests over a later sending -/

/-- Nothing is heard at the digits' seat. -/
def HeardNone (s : S) : Prop := (s.tl?.bind (·.heard)).isNone = true

/-- **What a yes of B on two rounds does to the lookups' three tests.** dgs: at which of a segment's
two lookups "lookOut" is left; HH: what is asked of the state behind. -/
def LaterLook (B : Block S Cl) (dgs : Bool → Bool) (HH : S → Prop) : Prop :=
  ∀ (d : K3Data) (s s' : S) rs gs, rs.length = 2 → B.decide s rs gs = .ok s' → HH s' →
    (∀ m, linkFreshC d m s = true → linkFreshC d m s' = true) ∧
      (∀ m dg, dgs dg = true → lookOutC d m dg s' = lookOutC d m dg s) ∧
      ∀ m dg, lookInC d m dg s = true → lookInC d m dg s' = true

/-- The sending alone: at both lookups; nothing is asked behind. -/
theorem laterLook_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterLook (commitAtS P link moment arrays : Block S Cl) (fun _ => true) fun _ => True := by
  intro d s s' rs gs h2 h _
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  exact ⟨fun m h0 => by rw [linkFresh_at_later d m P link moment arrays s s' r₁ r₂ gs h]; exact h0,
    fun m dg _ => lookOut_at_later d m dg P link moment arrays s s' _ gs h,
    fun m dg h0 => lookIn_at_later d m dg P link moment arrays s s' r₁ r₂ gs h h0⟩

/-- The first member: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterLook_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    LaterLook (laterAt q gp link piece moment arrays : Block S Cl) (fun _ => true) fun _ => True :=
  laterLook_commitAtS _ _ _ _

/-- The sending with a quiet sub-protocol joined behind it: at the lookup on the calls; behind,
nothing is heard at the digits' seat. -/
theorem laterLook_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : Decides LookSame q) :
    LaterLook (Block.andThen nm (commitAtS P link moment arrays) q) (fun dg => !dg) HeardNone := by
  intro d s s' rs gs h2 h hh
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  have hL := hq _ _ _ _ h3
  obtain ⟨a2, a3, a4⟩ := laterLook_commitAtS P link moment arrays d s s₁ _ gs₁ rfl h1 trivial
  refine ⟨fun m h0 => linkFresh_quiet d m hL hh (a2 m h0), fun m dg hdg => ?_,
    fun m dg h0 => lookIn_quiet d m dg hL hh (a4 m dg h0)⟩
  cases dg with
  | true => cases hdg
  | false => exact (lookOut_quiet d m hL).trans (a3 m false rfl)

/-- The second member: the reads' place's joined sub-protocol. -/
theorem laterLook_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) :
    LaterLook (IM.k1Reads Z G l X pr reads) (fun dg => !dg) HeardNone :=
  laterLook_joined _ _ _ _ _ _ (lookSame_k1Quiet G l X)

/-! ## 3 The layer's public items at the composed Bool -/

/-- The lookups' layer's public items that are paid here. -/
def lookPaid (D : PubData) (dgs : Bool → Bool) : Pub → Bool
  | .lookIn m pc => (k3SortAt D.d3.X m pc).isSome
  | .lookOut m pc => (k3SortAt D.d3.X m pc).any dgs
  | .linkFresh _ => true
  | .left _ => true
  | .leftOn _ => true
  | _ => false

/-- **The lookups' items over the sub-protocol's own yes.** -/
theorem pub_look_later {B : Block S Cl} {dgs : Bool → Bool} {HH : S → Prop}
    (hB : LaterLook B dgs HH) (D : PubData) (base : Pub → Pp × S → Bool) (x x' : Pp × S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : B.decide x.2 rs gs = .ok x'.2) (hh : HH x'.2) (q : Pub) (hq : lookPaid D dgs q = true)
    (h0 : pubAll D base q x = true) : pubAll D base q x' = true := by
  obtain ⟨a2, a3, a4⟩ := hB D.d3 _ _ _ _ h2 h hh
  cases q with
  | lookIn m pc =>
    obtain ⟨dg, e⟩ := Option.isSome_iff_exists.1 hq
    have h0' : (match k3SortAt D.d3.X m pc with
      | some dg => lookInC D.d3 m dg x.2
      | none => _) = true := h0
    show (match k3SortAt D.d3.X m pc with
      | some dg => lookInC D.d3 m dg x'.2
      | none => _) = true
    rw [e] at h0' ⊢
    exact a4 m dg h0'
  | lookOut m pc =>
    have hq' : (k3SortAt D.d3.X m pc).any dgs = true := hq
    cases e : k3SortAt D.d3.X m pc with
    | none =>
      rw [e] at hq'
      cases hq'
    | some dg =>
      rw [e] at hq'
      have h0' : (match k3SortAt D.d3.X m pc with
        | some dg => lookOutC D.d3 m dg x.2
        | none => _) = true := h0
      show (match k3SortAt D.d3.X m pc with
        | some dg => lookOutC D.d3 m dg x'.2
        | none => _) = true
      rw [e] at h0' ⊢
      show lookOutC D.d3 m dg x'.2 = true
      rw [a3 m dg hq']
      exact h0'
  | linkFresh m => exact a2 m h0
  | left m => rfl
  | leftOn m => rfl
  | _ => cases hq

/-! ## 4 The sub-protocol at (l, d) -/

/-- At which of a segment's two lookups "lookOut" is left: at the digits' place at both, at the
reads' place at the lookup on the calls alone. -/
def dgsL : Bool → Bool → Bool
  | true => fun _ => true
  | false => fun dg => !dg

/-- What is asked of the state behind: at the digits' place nothing, at the reads' `HeardNone`. -/
def hhL : Bool → S → Prop
  | true => fun _ => True
  | false => HeardNone

theorem laterLook_blkL (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : ℕ) (d : Bool) (X : LinkH)
    (arrs : Option (List ℕ)) : LaterLook (blkL Z G l d X arrs) (dgsL d) (hhL d) := by
  cases d with
  | true => exact laterLook_laterAt _ _ _ _ _ _
  | false => exact laterLook_k1Reads _ _ _ _ _ _

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pub_look_later
#print axioms VerifiableInference.Desc.K1.laterLook_blkL
