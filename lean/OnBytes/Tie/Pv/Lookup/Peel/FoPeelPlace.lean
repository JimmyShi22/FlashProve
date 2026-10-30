-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPeelPlace.lean: the law at a lookup's place: where the byte-level
lookup routine returns, the written stretch that it has heard has an image, the typed lookup's
verifier puts out on it a statement that is fixed by the view, and the routine has left the rest of
the view.

A chain's soundness is carried from the typed blocks to a file's written rounds place by place. At
each place one law is wanted, of one form: for every written transcript τ of the place's rounds that
passes its tests of work, if the rounds of the view still to be taken before the place begin with
τ's reading, then τ has an image under the place's maps, the block's verifier puts out on the image
the statement that the next block starts from, and the rounds still to be taken behind the place are
the rest. This file states it for the lookup of a sub-proof, written out.

What the file states.
 - lookImgP h L Ex ds p: the typed transcript made of the first rounds of the list p of a view's
   rounds, as many as ds has, read as plain data. A term of p.
 - lookImgT_eq: the image of a written transcript τ is lookImgP at every list that begins with τ's
   reading.
 - look_place: for a run of Forest.pad from c to c' that returns, from a state whose arrays have
   their sizes and a context on a view with no message open, h being the record of public numbers
   that the byte-level verifier's own routines make of the calls (ShapeOf):
   for every written transcript τ of ds and every list rest: if τ passes its tests of work and
   c.ch.left = rvT (ckP .two) ds τ ++ rest, then τ has an image under Fo.Peel.lookCarryT; on it the
   typed verifier puts out a', where a' is what it puts out at lookImgP h L Ex ds c.ch.left; and
   c'.ch.left = rest.
 - look_place_some: such an a' there is, for every typed statement a before the place, with a's
   state and oracles in it.

So p := c.ch.left, p' := c'.ch.left, V := rvT (ckP .two) ds, ok τ := the tests of work pass, F :=
lookCarryT, and a' does not read τ.

Under: each written round meets its place in the lookup's list of rounds (MeetsT); no item of a
message is an answer to a sample.

Limits. The typed block is Cb.Fo.forB at the base, not yet lifted over a caller's signature. That
the context at the door is as asked is a premise. Nothing here ties ds to a description's rounds at
the place: of ds the statement asks MeetsT and NoAns alone. Of the routine's run the law uses one
fact: what it leaves of the view. It counts rounds and fixes a'; what a' says of the routine's
record (the flat function's end values at the same plain data) is
OnBytes/Tie/Pv/Lookup/Forest/FoPeelT.lean's look_yesT, at the same typed statement (lookImgT_eq).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelPort
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelT
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelJoinT

set_option autoImplicit false

namespace Fo
open Iop Prob IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp TWhole TwV OnBytes.Slice OnBytes.Flat Run
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Maker Fo.Peel

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay Cb.Gl.E St₀ J₀)
  (Ex : ExtSpec) (ds : List RDT)

/-- The typed transcript made of the first rounds of a view's rounds. -/
noncomputable def lookImgP (p : List Fmt.RoundView) : Tr (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape :=
  img _ (specF h) (rkFor h L Ex).R ((p.take ds.length).map (rdRV Reading.gl))

/-- The image of a written transcript is a term of the view's rounds. -/
theorem lookImgT_eq (hA : ∀ d ∈ ds, NoAns d.items) (τ : Tr (uLT (ckP .two) ds))
    (rest : List Fmt.RoundView) :
    lookImgT h L Ex ds τ = lookImgP h L Ex ds (rvT (ckP .two) ds τ ++ rest) := by
  unfold lookImgT lookImgP
  rw [← rvT_length (C := ckP .two) ds τ, List.take_left, flWsT_view ds τ hA]

/-- **The law at a lookup's place.** -/
theorem look_place {calls : Array Call} {pub : Array Nat} {lid : ℕ} {Fk F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} (hr : Forest.pad calls pub lid Fk c = .ok ((g, F'), c'))
    (hS : ShapeOf calls pub lid h) (hF : Sized Fk) (hc : Clean c)
    (hM : List.Forall₂ MeetsT ds (specF h)) (hA : ∀ d ∈ ds, NoAns d.items) (a : St₀ × Ex.Str)
    (a' : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) × Ex.Str)
    (ha : (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a (lookImgP h L Ex ds c.ch.left) =
      some a') :
    ∀ (τ : Tr (uLT (ckP .two) ds)) (rest : List Fmt.RoundView),
      passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = true →
      c.ch.left = rvT (ckP .two) ds τ ++ rest →
      ∃ τ', (lookCarryT h L Ex ds hM.length_eq).tr τ = some τ' ∧
        (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a τ' = some a' ∧ c'.ch.left = rest := by
  intro τ rest hp hl
  have H : FoNums.ok h = true := by
    obtain ⟨h0, hs0, hp0, he⟩ := hS
    rw [he]
    exact shape_ok hs0 hp0
  have hv : 1 ≤ h.v := by
    have := ok_v H
    omega
  obtain ⟨_, _, h3, _, _⟩ := look_leaf_at hS hr hF hc hl (rvT_len h ds hv hM hA τ) 0
  refine ⟨lookImgT h L Ex ds τ, lookCarryT_pass h L Ex ds hM.length_eq τ hp, ?_, h3⟩
  rw [lookImgT_eq h L Ex ds hA τ rest, ← hl]
  exact ha

/-- There is such a statement behind the place, with the caller's state and the oracles in it. -/
theorem look_place_some (p : List Fmt.RoundView) (a : St₀ × Ex.Str) :
    ∃ x : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀),
      (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.red.out a (lookImgP h L Ex ds p) = some (x, a.2) ∧
        x.1.1 = a.1 :=
  lookOut_total h L a _

end
end Fo
