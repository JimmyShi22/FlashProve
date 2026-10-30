-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/HeadFreshAt.lean: code switching: IN FRONT OF THE SWITCH AT THE OUTPUT HEAD's
SEGMENT THE GROUP THAT THE HEAD's OWN PART OF THE STATE NAMES IS FRESH (HeadFresh,
K2C/HandsEnds.lean: no row, no member, nothing kept, no proximity test begun). At the level of the
state. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. At a segment's switch the front opens the new group in the switch's own step, at the finish
the way in does. At the head's segment the group is opened ONE SUB-PROTOCOL EARLIER: by the quiet
step headFrontQ (K2C/Head.lean), which stands in front of the round that hears the reply. So
«fresh» in front of that switch is a fact on the state behind the reply's sub-protocol.
  headFresh_front   behind an accept of headFrontQ the group is fresh
  headFresh_same    HeadFresh reads of the state «here» and the statement alone
  guarded_front     the quiet step, guarded on the reply, accepts only where headFrontQ does, with
                    the same state behind
  fresh_behind      an accept of: headFrontQ as a sub-protocol without a round, under whatever
                    place, guarded on the reply; then the reply's sub-protocol: the group is fresh
                    behind it
  fresh_behind_H1   the same at every member of ProofFile.h1Own G (Johnson/Desc/ProofFile/Lots/H1.lean)
CALLED: place_rest (Johnson/Desc/Kinds/Law/ReplyRest.lean: the reply's sub-protocol
turns the field of the heard reply and nothing else).
LIMITS. On the decision of the lot's own sub-protocol. That the sub-protocol which is seated in
front of the switch accepts only where this one does, with the same state behind, and the step to
every reached state, are not here. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.HandsEnds
import Johnson.Top.H0.Tw.K2C.FrontGroup
import Johnson.Desc.ProofFile.Lots.H1
import Johnson.Desc.Kinds.Law.ReplyRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block roundlessBlock Place seatSame)
open VerifiableInference.Desc.Kinds (Reply.blockOf)

/-- **Behind an accept of the head's own first step the group is fresh.** -/
theorem headFresh_front {tl : HTailF2} {s s' : S} (h : headFrontQ tl s = .ok s') :
    HeadFresh s' := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s').1 h
  intro a' ha'
  have hg := (headFrontQ_groups h).2.2.2.2
  rw [k.out] at ha'
  have e2 : (Here.head { a with fr := x.f }) = Here.head a' := ha'
  injection e2 with e3
  refine ⟨freshGroup s.check.frame.shape.code s.check.frame.shape.maskCode, ?_, rfl, rfl, rfl,
    rfl⟩
  rw [← e3]
  show s'.st.groups[x.f.group]? = _
  rw [(firstFront_st k.front).2]
  exact hg

/-- HeadFresh reads «here» and the statement alone. -/
theorem headFresh_same {s s' : S} (h1 : s'.here = s.here) (h2 : s'.st = s.st)
    (h : HeadFresh s) : HeadFresh s' := by
  intro a ha
  rw [h1] at ha
  rw [h2]
  exact h a ha

/-- The guarded quiet step accepts only where headFrontQ does, with the same state behind. -/
theorem guarded_front {tl : HTailF2} {l' : Nat} {pl : Place} {nm : String} {s m : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (Block.guarded ProofFile.sameReply (fun _ => false)
      ({ (roundlessBlock nm 1 (some l') 1 (headFrontQ tl) : Block S Unit) with place := pl })).decide
        s rs gs = .ok m) : headFrontQ tl s = .ok m := by
  have h' : (headFrontQ tl s).bind (seatSame ProofFile.sameReply s) = .ok m := h
  obtain ⟨m₀, h3, h4⟩ := bindOk h'
  unfold seatSame at h4
  split at h4
  · rw [← Except.ok.inj h4]
    exact h3
  · cases h4

/-- **Behind the two steps in a row.** pl: whatever place the first is stamped with. -/
theorem fresh_behind {W : Verify.Public} {tl : HTailF2} {l l' : Nat} {pl : Place} {nm : String}
    {s s' : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (Block.andThen nm (Block.guarded ProofFile.sameReply (fun _ => false)
      ({ (roundlessBlock nm 1 (some l') 1 (headFrontQ tl) : Block S Unit) with place := pl }))
      (Reply.blockOf W l)).decide s rs gs = .ok s') : HeadFresh s' := by
  obtain ⟨s₀, h0, a1, -, -, -, -, -, a7, -⟩ :=
    Kinds.Head.Law.place_rest W l nm _ tl (fun _ _ _ _ e => guarded_front e) s rs gs s' h
  exact headFresh_same (s := s₀) a7 a1 (headFresh_front h0)

/-- **At the lot's own sub-protocol of the head's segment's first place.** -/
theorem fresh_behind_H1 (G : ProofFile.Ground) {b : Block S Unit} (hb : b ∈ ProofFile.h1Own G) {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (h : b.decide s rs gs = .ok s') :
    HeadFresh s' := by
  unfold ProofFile.h1Own at hb
  obtain rfl := List.mem_singleton.1 hb
  exact fresh_behind (W := G.W) (tl := G.W.H.tl) (l := G.built.size - 1)
    (l' := G.built.size - 1) (pl := (P4.k7Core G).place) (nm := "H:1") h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.headFresh_front
#print axioms VerifiableInference.Desc.First.K2.guarded_front
#print axioms VerifiableInference.Desc.First.K2.fresh_behind
#print axioms VerifiableInference.Desc.First.K2.fresh_behind_H1
