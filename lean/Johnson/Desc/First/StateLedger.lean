-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/StateLedger.lean: WHICH FUNCTIONS OF Johnson/Desc/First/State.lean LEAVE THE
LINK's LEDGER (`S.fork?`) AND WHAT THE LOOKUP ON THE CALLS HEARD (`S.lookHeard?`). Small laws with
their proofs, one a function, each by unfolding.

Why. The law of the kind "lookup" speaks of several moments of one link, and asks that what was
heard still stands and that the ledger has only grown (`Carries`, `RanAt`:
Johnson/Desc/Sound/FoldSteps.lean). Each block and each run of the link owes `Block.Steps` |
`Block.RunsStep` at that relation. A block of the first chain is typed over S with the functions of
State.lean: with these laws a kind's files have their share by rewriting, wherever their own text
turns the ledger by `S.putFork` alone, and the ledger that it lays is later than the one in front
and has its sizes IF THE ONE IN FRONT HAS.

The laws.
  `S.fork_‹f›`, `S.look_‹f›`: f leaves both readings, at every record: mark · putLink · putTl ·
    putLook · putLive · owe · back · withReq. `S.here_‹f›`: closed · pay · call · callE leave the
    field `here`, off which both readings are read (`S.fork_of_here`, `S.look_of_here`).
  `S.fork_hearLook`: the hearing leaves the ledger. `S.look_hearLook`: WHAT WAS HEARD ONCE STANDS: a
    second hearing in one link marks the state and lays nothing.
  `S.look_putFork`: `putFork` leaves what was heard. `S.fork_putFork`: where a link is open, the
    ledger behind is the one put.
  `carriesOfSame`: a change that leaves both readings `Carries`, at every reflexive order.
    `carriesPutFork`: `putFork G` carries where, IF THE LEDGER IN FRONT HAS ITS SIZES, G is later
    than it and has its sizes.
NOT AMONG THEM, AND RIGHTLY: the enters, `openHead` and `leaveLink`: they open or end a link's part.

Limits. Laws on State.lean's own functions alone.
A step that lays
`{ s with here := … }` is covered only where the ledger, `lookHeard` (and `opened`) stay
(`S.fork_lay` | `fork_att` | `fork_head`, `S.look_‹…›`); a literal that TURNS the ledger has no law
here. Nothing on soundness. Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.State
import Johnson.Desc.Sound.FoldSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

namespace S

theorem here_mark (s : S) (name : String) : (s.mark name).here = s.here := by
  unfold mark
  split <;> rfl

/-- A change of the record that leaves `here` leaves both readings. -/
theorem fork_of_here (s s' : S) (h : s'.here = s.here) : s'.fork? = s.fork? := by
  unfold fork?
  rw [h]

theorem look_of_here (s s' : S) (h : s'.here = s.here) : s'.lookHeard? = s.lookHeard? := by
  unfold lookHeard?
  rw [h]

theorem fork_mark (s : S) (n : String) : (s.mark n).fork? = s.fork? := fork_of_here _ _
  (here_mark s n)
theorem look_mark (s : S) (n : String) : (s.mark n).lookHeard? = s.lookHeard? :=
  look_of_here _ _ (here_mark s n)

/-- A link's own part laid anew, with the same ledger: the ledger's reading stays. -/
theorem fork_lay (s : S) (a a' : LayOwn) (hh : s.here = .lay a) (hF : a'.F = a.F) :
    ({ s with here := .lay a' } : S).fork? = s.fork? := by
  unfold fork?
  rw [hh]
  exact congrArg some hF

theorem fork_att (s : S) (a a' : AttOwn) (hh : s.here = .att a) (hF : a'.F = a.F) :
    ({ s with here := .att a' } : S).fork? = s.fork? := by
  unfold fork?
  rw [hh]
  exact congrArg some hF

theorem fork_head (s : S) (a a' : HeadOwn) (hh : s.here = .head a) (ho : a'.opened = a.opened)
    (hF : a'.F = a.F) : ({ s with here := .head a' } : S).fork? = s.fork? := by
  unfold fork?
  rw [hh]
  show (if a'.opened then some a'.F else none) = if a.opened then some a.F else none
  rw [ho, hF]

theorem look_lay (s : S) (a a' : LayOwn) (hh : s.here = .lay a)
    (hl : a'.lookHeard = a.lookHeard) : ({ s with here := .lay a' } : S).lookHeard? = s.lookHeard?
      := by
  unfold lookHeard?
  rw [hh]
  exact hl

theorem look_att (s : S) (a a' : AttOwn) (hh : s.here = .att a)
    (hl : a'.lookHeard = a.lookHeard) : ({ s with here := .att a' } : S).lookHeard? = s.lookHeard?
      := by
  unfold lookHeard?
  rw [hh]
  exact hl

theorem look_head (s : S) (a a' : HeadOwn) (hh : s.here = .head a) (ho : a'.opened = a.opened)
    (hl : a'.lookHeard = a.lookHeard) :
    ({ s with here := .head a' } : S).lookHeard? = s.lookHeard? := by
  unfold lookHeard?
  rw [hh]
  show (if a'.opened then a'.lookHeard else none) = if a.opened then a.lookHeard else none
  rw [ho, hl]

theorem fork_putLink (s : S) (L : LinkCtx) : (s.putLink L).fork? = s.fork? := by
  unfold putLink
  split
  · rename_i a hh
    first
      | exact fork_lay s a _ hh rfl
      | (split <;> first | rfl | exact fork_lay s a _ hh rfl)
  · rename_i a hh
    first
      | exact fork_att s a _ hh rfl
      | (split <;> first | rfl | exact fork_att s a _ hh rfl)
  · rename_i a hh
    split <;> first | rfl | exact fork_head s a _ hh rfl rfl
  · rfl

theorem look_putLink (s : S) (L : LinkCtx) : (s.putLink L).lookHeard? = s.lookHeard? := by
  unfold putLink
  split
  · rename_i a hh
    first
      | exact look_lay s a _ hh rfl
      | (split <;> first | rfl | exact look_lay s a _ hh rfl)
  · rename_i a hh
    first
      | exact look_att s a _ hh rfl
      | (split <;> first | rfl | exact look_att s a _ hh rfl)
  · rename_i a hh
    split <;> first | rfl | exact look_head s a _ hh rfl rfl
  · rfl

theorem fork_putTl (s : S) (tl : HTailF2) : (s.putTl tl).fork? = s.fork? := by
  unfold putTl
  split
  · rename_i a hh
    first
      | exact fork_lay s a _ hh rfl
      | (split <;> first | rfl | exact fork_lay s a _ hh rfl)
  · rename_i a hh
    first
      | exact fork_att s a _ hh rfl
      | (split <;> first | rfl | exact fork_att s a _ hh rfl)
  · rename_i a hh
    split <;> first | rfl | exact fork_head s a _ hh rfl rfl
  · rfl

theorem look_putTl (s : S) (tl : HTailF2) : (s.putTl tl).lookHeard? = s.lookHeard? := by
  unfold putTl
  split
  · rename_i a hh
    first
      | exact look_lay s a _ hh rfl
      | (split <;> first | rfl | exact look_lay s a _ hh rfl)
  · rename_i a hh
    first
      | exact look_att s a _ hh rfl
      | (split <;> first | rfl | exact look_att s a _ hh rfl)
  · rename_i a hh
    split <;> first | rfl | exact look_head s a _ hh rfl rfl
  · rfl

theorem fork_putLook (s : S) (g : Forest.Heard) : (s.putLook g).fork? = s.fork? := by
  unfold putLook
  split
  · rename_i a hh
    first
      | exact fork_lay s a _ hh rfl
      | (split <;> first | rfl | exact fork_lay s a _ hh rfl)
  · rename_i a hh
    first
      | exact fork_att s a _ hh rfl
      | (split <;> first | rfl | exact fork_att s a _ hh rfl)
  · rename_i a hh
    split <;> first | rfl | exact fork_head s a _ hh rfl rfl
  · rfl

theorem look_putLook (s : S) (g : Forest.Heard) : (s.putLook g).lookHeard? = s.lookHeard? := by
  unfold putLook
  split
  · rename_i a hh
    first
      | exact look_lay s a _ hh rfl
      | (split <;> first | rfl | exact look_lay s a _ hh rfl)
  · rename_i a hh
    first
      | exact look_att s a _ hh rfl
      | (split <;> first | rfl | exact look_att s a _ hh rfl)
  · rename_i a hh
    split <;> first | rfl | exact look_head s a _ hh rfl rfl
  · rfl

theorem look_putFork (s : S) (F : Fork) : (s.putFork F).lookHeard? = s.lookHeard? := by
  unfold putFork
  split
  · rename_i a hh
    exact look_lay s a _ hh rfl
  · rename_i a hh
    exact look_att s a _ hh rfl
  · rename_i a hh
    split <;> first | rfl | exact look_head s a _ hh rfl rfl
  · rfl

/-- Where a link is open, the ledger behind `putFork` is the one put. -/
theorem fork_putFork (s : S) (F G : Fork) (h : s.fork? = some F) : (s.putFork G).fork? = some G :=
  by
  unfold putFork
  unfold fork? at h
  split
  · simp [fork?]
  · simp [fork?]
  · rename_i a hh
    rw [hh] at h
    split
    · rename_i ho
      simp [fork?, ho]
    · rename_i ho
      simp [ho] at h
  · rename_i h₁ h₂ h₃
    cases hh : s.here <;> simp_all

theorem fork_putLive (s : S) (c : ChainCheck) : (s.putLive c).fork? = s.fork? := by
  unfold putLive
  split <;> first | rfl | exact fork_putLink _ _

theorem look_putLive (s : S) (c : ChainCheck) : (s.putLive c).lookHeard? = s.lookHeard? := by
  unfold putLive
  split <;> first | rfl | exact look_putLink _ _

theorem fork_hearLook (s : S) (g : Forest.Heard) : (s.hearLook g).fork? = s.fork? := by
  unfold hearLook
  split
  · rename_i a hh
    split
    · exact fork_mark _ _
    · simp [fork?, hh]
  · rename_i a hh
    split
    · exact fork_mark _ _
    · simp [fork?, hh]
  · rename_i a hh
    split
    · exact fork_mark _ _
    · split
      · exact fork_mark _ _
      · simp_all [fork?]
  · exact fork_mark _ _

/-- **What was heard once stands.** -/
theorem look_hearLook (s : S) (g g' : Forest.Heard) (h : s.lookHeard? = some g') :
    (s.hearLook g).lookHeard? = some g' := by
  unfold hearLook
  unfold lookHeard? at h
  split
  · rename_i a hh
    rw [hh] at h
    have h' : a.lookHeard = some g' := h
    rw [if_pos (by rw [h']; rfl), look_mark]
    simp [lookHeard?, hh, h']
  · rename_i a hh
    rw [hh] at h
    have h' : a.lookHeard = some g' := h
    rw [if_pos (by rw [h']; rfl), look_mark]
    simp [lookHeard?, hh, h']
  · rename_i a hh
    rw [hh] at h
    split
    · rw [look_mark]
      simp_all
    · split
      · rw [look_mark]
        simp_all [lookHeard?]
      · simp_all
  · rw [look_mark]
    unfold lookHeard?
    exact h

theorem fork_owe (s : S) (rows : Nat) : (s.owe rows).fork? = s.fork? := by
  unfold owe
  split <;> first | rfl | exact fork_mark _ _

theorem look_owe (s : S) (rows : Nat) : (s.owe rows).lookHeard? = s.lookHeard? := by
  unfold owe
  split <;> first | rfl | exact look_mark _ _

theorem fork_back (s : S) (c : Ctx) : (s.back c).fork? = s.fork? := rfl
theorem look_back (s : S) (c : Ctx) : (s.back c).lookHeard? = s.lookHeard? := rfl
theorem fork_withReq (s : S) (req : Array UInt32) : (s.withReq req).fork? = s.fork? := rfl
theorem look_withReq (s : S) (req : Array UInt32) : (s.withReq req).lookHeard? = s.lookHeard? := rfl

theorem here_closed (s s' : S) (rows : Nat) (h : s.closed rows = some s') : s'.here = s.here := by
  unfold closed at h
  split at h
  · rw [← Option.some.inj h]
    unfold owe
    split <;> first | rfl | exact here_mark _ _
  · exact nomatch h

theorem here_pay (s s' : S) (rows : Nat) (h : s.pay rows = some s') : s'.here = s.here := by
  unfold pay at h
  split at h
  · split at h
    · exact (Option.some.inj h) ▸ rfl
    · exact nomatch h
  · exact nomatch h

/-- A call of a routine of `verify-on-bytes` leaves `here`: so both readings. -/
theorem here_callE {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) (a : α) (s' : S) (k : Nat)
    (h : s.callE P es rs cols b = .ok (a, s', k)) : s'.here = s.here := by
  unfold callE at h
  split at h
  · exact nomatch h
  · split at h
    · have e : _ = s' := congrArg (fun x => x.2.1) (Except.ok.inj h)
      rw [← e]
      rfl
    · exact nomatch h

theorem here_call {α : Type} (P : Par) (s : S) (es : List Fmt.Entry) (rs : List Fmt.RoundView)
    (cols : List Col) (b : Blk α) (a : α) (s' : S) (k : Nat)
    (h : s.call P es rs cols b = some (a, s', k)) : s'.here = s.here := by
  unfold call at h
  split at h
  · exact nomatch h
  · split at h
    · have e : _ = s' := congrArg (fun x => x.2.1) (Option.some.inj h)
      rw [← e]
      rfl
    · exact nomatch h

end S

/-- A change that leaves both readings carries, at every reflexive order. -/
theorem carriesOfSame {later : Fork → Fork → Prop} {sized : Fork → Prop} (lr : ∀ F, later F F)
    (s s' : S) (hf : s'.fork? = s.fork?) (hl : s'.lookHeard? = s.lookHeard?) :
    Carries S.fork? S.lookHeard? later sized s s' :=
  ⟨fun _ hg => hl.trans hg, fun F hF hs => ⟨F, hf.trans hF, lr F, hs⟩⟩

/-- `putFork G` carries where, IF THE LEDGER IN FRONT HAS ITS SIZES, G is later than it and has its
sizes. (No real text that we read can pay G's sizes at all
records: the laws on the steps that turn a ledger inside a link (hide, hideRun, paid, owe,
took) give them from the sizes in front.)
-/
theorem carriesPutFork {later : Fork → Fork → Prop} {sized : Fork → Prop} (s : S) (G : Fork)
    (h : ∀ F, s.fork? = some F → sized F → later F G ∧ sized G) :
    Carries S.fork? S.lookHeard? later sized s (s.putFork G) :=
  ⟨fun _ hg => (S.look_putFork s G).trans hg,
    fun F hF hs => ⟨G, S.fork_putFork s F G hF, (h F hF hs).1, (h F hF hs).2⟩⟩

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.S.look_hearLook
#print axioms VerifiableInference.Desc.First.S.fork_putFork
#print axioms VerifiableInference.Desc.First.S.here_callE
#print axioms VerifiableInference.Desc.First.carriesOfSame
#print axioms VerifiableInference.Desc.First.carriesPutFork
