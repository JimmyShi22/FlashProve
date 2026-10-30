-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/RecK10.lean: the closing of a link, which is the step that WRITES the live copy
of the frame, hands RecAll on (Johnson/Goal/Meaning/RecAll.lean; RecRel,
Johnson/Goal/Meaning/RecRel.lean); so does the marking of the segment behind it.

  closeFrame_all: what a yes of closeFrame (Johnson/Desc/First/Close/Closing.lean) says. It writes
    the frame's rows, mask, link and next: shape and groups stay; the link's number goes up by one;
    the next call due is a first message. The statement behind has the codes of the statement in
    front (by the library's closing_inv2, Johnson/Desc/First/Close/Law/Whole.lean). THE CARRIED ROWS
    THAT THE CLOSING LAYS are under the request's two codes and have two mask rows:
    rows.code = f.shape.code, rows.maskCode = f.shape.maskCode, rows.masks = 2.
  closing_rec: Whole (RecRel cs sh) (K9.closing P).
  shut_rec: Whole (RecRel cs sh) (K9.shut p piece).
Not claimed: anything on K9's other blocks (the draw, the one equation, the adding, the batching).
OBJECT: the makers' blocks and steps that are named above. USER: the walk
(Johnson/Goal/Meaning/RecWalk.lean: recAll_border), at the letters cs and sh: it asks
Decides (RecRel cs sh) of every block of a list; that list is not laid yet. Which maker stands
at which place of a seated text is not said here.
-/
import Johnson.Goal.Meaning.RecRel
import Johnson.Desc.First.Batch.Place
import Johnson.Desc.First.Close.Law.Whole
import Johnson.Desc.BlockKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Close (closeFrame closing_inv2)
open VerifiableInference.Desc.Keeps (Whole)

variable {cs : Codes} {sh : ReqShape} {Cl : Type}

/-- What a yes of closeFrame says of the frame, the codes and the carried rows. -/
theorem closeFrame_all {owed : Option Nat} {f f' : ReqFrame} {S S' : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} (h : closeFrame owed f S es rs = .ok (f', S')) :
    f'.shape = f.shape ∧ f'.groups = f.groups ∧ f'.link = f.link + 1 ∧ f'.next = .first ∧
      S'.codes = S.codes ∧ f'.rows.code = f.shape.code ∧ f'.rows.maskCode = f.shape.maskCode ∧
      f'.rows.masks = 2 ∧ f'.rows.d.size = 2 := by
  unfold closeFrame at h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨L, _, h⟩ := bindE h
  obtain ⟨G, _, h⟩ := bindE h
  obtain ⟨_, _, h⟩ := bindE h
  obtain ⟨⟨rows, S1⟩, hc, h⟩ := bindE h
  cases h
  obtain ⟨G', x, row, lay, m, rB, rE, rR, sum, eps, qs, gs, -, -, -, -, -, -, -, -, -, -, -, -, -,
    hcodes, hout⟩ := closing_inv2 hc
  refine ⟨rfl, rfl, rfl, rfl, hcodes, ?_, ?_, ?_, ?_⟩
  · show rows.code = _
    rw [hout]
    rfl
  · show rows.maskCode = _
    rw [hout]
    rfl
  · show rows.masks = _
    rw [hout]
    rfl
  · show rows.d.size = _
    rw [hout]
    rfl

/-- **The closing of a link hands RecAll on.** -/
theorem closing_rec (P : Close.Par) : Whole (RecRel cs sh) (K9.closing (Cl := Cl) P) := by
  refine ⟨fun s rs gs s' h R => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · obtain ⟨r, hr, rfl⟩ := Keeps.emap_ok h
    obtain ⟨x, hx, rfl⟩ := Keeps.emap_ok hr
    obtain ⟨a1, a2, -, -, a5, a6, a7, a8, a9⟩ := closeFrame_all (f' := x.1) (S' := x.2) hx
    have hf : FramePub sh x.1 := ⟨a1.trans R.live.shape, a2.trans R.live.groups, a9.trans a8.symm,
      Or.inr ⟨a6.trans (congrArg (·.code) R.live.shape),
        a7.trans (congrArg (·.maskCode) R.live.shape), a8⟩⟩
    have R1 := recAll_putLive (c := { s.live with frame := x.1 }) R hf
    exact ⟨a5.trans R.codes, R1.frames, R.ok⟩
  · exact nomatch hc
  · exact nomatch hc

/-- **The marking of the segment behind the closing hands RecAll on.** -/
theorem shut_rec (p : K9.Where) (piece : Nat) :
    Whole (RecRel cs sh) (K9.shut (Cl := Cl) p piece) := by
  refine ⟨fun s rs gs s' h R => ?_, (fun _ hc => nomatch hc), (fun _ hc => nomatch hc)⟩
  obtain ⟨L, hL, h⟩ := bindE h
  cases h
  have hl : s.link? = some L := by
    cases e : s.link? with
    | none =>
      rw [e] at hL
      cases hL
    | some L' =>
      rw [e] at hL
      exact congrArg some (Except.ok.inj hL)
  have k := R.live
  unfold S.live at k
  rw [hl] at k
  exact recAll_putLink R (L := K9.closed L L.check.frame) k

#print axioms closeFrame_all
#print axioms closing_rec
#print axioms shut_rec

end Meaning.K2
