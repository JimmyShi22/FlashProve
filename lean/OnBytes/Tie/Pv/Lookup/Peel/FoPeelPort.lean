-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPeelPort.lean: the tie that the maps of a lookup's written rounds must
hand on,
and what the byte-level routine's run gives where a goal is unfolded at a whole written transcript.

OnBytes/Tie/Pv/Lookup/Peel/FoPeelLook.lean takes the lookup off the front in the flat function's
words: what is left to show
speaks of
plain data alone. The context in which the byte-level verifier calls Forest.pad holds the whole
file's
rounds, those behind the lookup too; so no run of the routine is named in the peel's statement. It
is
named where the goal is unfolded, at a whole transcript. This file has the tools for that place.

What the file states.
 - shapeOf_unique: the record of public numbers that Forest.shape and Forest.pubAsk make of the
   calls is
   one.
 - ImageReads h L F view: the tie that the maps must hand on beside their error counts: the image of
   a
   written transcript τ, read as plain data, is the list of rounds view τ, read as plain data.
 - look_leaf_at: Fo.look_leaf (OnBytes/Tie/Pv/Lookup/Forest/FoPeelLeaf.lean) where the record of
   public numbers h is known
   beforehand: if the routine returns from a context on a view with no message open, whose rounds
   not yet taken are rv followed by rest, and rv has as many rounds as the lookup's list of rounds
   at h, then the record's shape is h, the routine has taken exactly rv, the context behind has rest
   left, the state is left as PadLeft says, and the record holds the flat function's end values at
   rv read as plain data (HeardIs): the plain data of which NoClaims
     (OnBytes/Tie/Pv/Lookup/Peel/FoPeelLook.lean) speaks, if rv
   is the view of the lookup's written rounds.

Limits. ImageReads is a hypothesis here. That the context at the lookup's door is on a view with no
message open, with the lookup's rounds next, is a premise of look_leaf_at; so is that the state's
arrays have their sizes (Sized).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Peel.FoPeelLook
import OnBytes.Tie.Pv.Lookup.Forest.FoPadAll
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelLeaf

set_option autoImplicit false

namespace Fo
open Iop Prob IOR Cb Cb.Fo Cb.LdLkp Cb.Lkp TWhole TwV OnBytes.Slice
open OnBytes.Flat OnBytes OnBytes.Model OnBytes.PscRun

theorem shapeOf_unique {calls : Array Call} {pub : Array Nat} {lid : ℕ} {h h' : Forest.Shape}
    (a : ShapeOf calls pub lid h) (b : ShapeOf calls pub lid h') : h' = h := by
  obtain ⟨h0, a1, _, rfl⟩ := a
  obtain ⟨h1, b1, _, rfl⟩ := b
  obtain rfl : h0 = h1 := Except.ok.inj (a1.symm.trans b1)
  rfl

/-- The image of a written transcript reads as the rounds of the view as which it is read. -/
def ImageReads {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh)
    (L : Lay Cb.Gl.E St₀ J₀) {Ex : ExtSpec} {s : Shape}
    (F : CarryS s (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape) (view : Tr s → List Fmt.RoundView) :
    Prop :=
  ∀ τ τ', F.tr τ = some τ' → forFl h L Ex τ' = (view τ).map (rdRV Reading.gl)

section
variable {calls : Array Call} {pub : Array Nat} {lid : ℕ} {Fk F' : Fork} {c c' : Ctx}
  {g : Forest.Heard} {rv rest : List Fmt.RoundView}

/-- Fo.look_leaf where the record of public numbers is known beforehand. -/
theorem look_leaf_at {h : Forest.Shape} (hS : ShapeOf calls pub lid h)
    (hr : Forest.pad calls pub lid Fk c = .ok ((g, F'), c')) (hFk : Sized Fk) (hc : Clean c)
    (hl : c.ch.left = rv ++ rest) (hn : rv.length = (planF h).length) (lm : ℕ) :
    g.shape = h ∧ Took c rv c' ∧ c'.ch.left = rest ∧ PadLeft h Fk F' g ∧
      HeardIs Reading.gl g F' (endsOf h lm Fk.next (rv.map (rdRV Reading.gl))) := by
  have hg : g.shape = h :=
    shapeOf_unique hS (hcOut2V Cb.Gl.E Reading.gl calls pub lid lm Fk F' c c' g hr hFk hc).1
  obtain ⟨a1, a2, _, a4, a5⟩ := look_leaf Reading.gl lm hr hFk hc hl (hg.symm ▸ hn)
  rw [hg] at a4 a5
  exact ⟨hg, a1, a2, a4, a5⟩

end

end Fo
