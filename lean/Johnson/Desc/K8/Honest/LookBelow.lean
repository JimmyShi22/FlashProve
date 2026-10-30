-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LookBelow.lean: THE LOOKUP: BEHIND A YES OF ITS BLOCK (`K3.block`,
Johnson/Desc/First/Look/K3Lookup.lean), AT ROUNDS THAT PASS THE LIBRARY's TEST ON WORDS (`okRoundsE`,
Johnson/Top/H/K3LawKind.lean), EVERY COORDINATE OF THE KEY POINT's PART zy, AS WHAT WAS HEARD HOLDS
IT, HAS ITS WORDS BELOW THE PRIME. For the smallness test, whose second computation of the calls'
weights reads zy's words. Lemmas on the verifier's own text; none of the library's goals.

  `walk_lookTie`, `walk_roundsIn` two more of the functions that the messages call, under the
                   library's rule `Walk`
  `mem_toList_of_extract` a member of a cut of an array is a member of the array
  **`walk_messages`** the lookup's messages (`K3.messages`), bind by bind, general in the property
                   D, where 0 has D: zy is a cut of the point that the key side's run of levels
                   leaves
  **`hear_words`**, **`block_words`** at D := «the words lie below the prime»: what the lookup
                   hears; what its block's yes leaves, at a seat that reads what it lays
By: Johnson/Desc/K8/Honest/TapeBelow.lean · the library's `Walk` and its rules
(Johnson/Meaning/HKTDrawn.lean) · `tapeT_ok` (Johnson/Top/H/Keep/CEndTurns.lean: the tape that is
made of such rounds is `AllOk`, which is `Good` at that D by unfolding) · `decide_ok`
(Johnson/Top/H/K3DecideHearsOf.lean).
WRITTEN A FURTHER TIME: `mem_toList_of_extract` is, of lists of members, the library's
`mem_of_extract` (Johnson/P1L20R/RoomKeepK2.lean), which is not imported for three lines' sake.
KIN, AND FIRST: that the words of every coordinate of zy lie below the prime where the rounds'
sampled words do is shown, on another road (the structure that the challenges alone make), behind an
accepting step of the member at the lookup on the digits, at all 25 segments, under the library's
`P5J.AtMgA` and one premise more, in Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DigitsPointsAt.lean
(`digits_points_link`, `ok_zy_at`, `ok_layBack`).
Limits. From a yes alone. ON zy ALONE: nothing on zx, on the table side's points or on what is sent.
At every shape and every seat that reads what it lays.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.TapeBelow
import Johnson.Desc.First.Look.K3Lookup
import Johnson.Top.H.K3DecideHearsOf
import Johnson.Top.H.Keep.CEndTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.K.Kc
open VerifiableInference.Desc.First.Tape (tapeT flRun)
open VerifiableInference.OnPublicFiles (okRoundsE)
open _root_.Fo.Tp (tapeT_ok)
open _root_.Meaning.HKT (Good Walk walk_pure walk_bind walk_mono walk_ask walk_take walk_must
  walk_answer)

variable {D : E → Prop}

theorem walk_lookTie (a : E) : Walk D (K3.tie a) fun _ => True := by
  unfold K3.tie
  refine walk_bind (walk_whole _ _ _ _ _) fun w _ => ?_
  exact walk_bind (walk_foldlM (Q := fun _ => True) (fun s _ _ =>
    walk_bind (walk_whole _ _ _ _ _) fun _ _ => walk_pure _ trivial) _ _ trivial)
    fun _ _ => walk_pure _ trivial

theorem walk_roundsIn (form : RoundForm) (p : Psc) (zs : List (E × Nat)) (hp : PscAll D p) :
    Walk D (Fl.roundsIn form p zs) fun _ => True := by
  unfold Fl.roundsIn
  refine walk_mono (walk_foldlM (Q := fun s : Array E × Psc => PscAll D s.2) (fun s z hs =>
    walk_bind (walk_roundInR form s.2 z.1 z.2 hs) fun y hy => ?_) zs (#[], p) hp)
    fun _ _ => trivial
  obtain ⟨r, q⟩ := y
  exact walk_pure _ hy.2

theorem mem_toList_of_extract {α : Type} {a : Array α} {i j : Nat} {x : α}
    (h : x ∈ (a.extract i j).toList) : x ∈ a.toList := by
  rw [Array.toList_extract, List.extract_eq_take_drop] at h
  exact List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- **THE LOOKUP's MESSAGES: every coordinate of zy has the property.** -/
theorem walk_messages (h0 : D zeroE) (h : Forest.Shape) :
    Walk D (K3.messages h) fun g => ∀ x ∈ g.zy.toList, D x := by
  unfold K3.messages
  dsimp only
  refine walk_bind (walk_ask _) fun slot0 _ => ?_
  refine walk_bind (walk_take _) fun _ _ => ?_
  refine walk_bind (walk_take _) fun _ _ => ?_
  refine walk_bind (walk_take _) fun _ _ => ?_
  refine walk_bind (walk_answer _) fun theta _ => ?_
  refine walk_bind (walk_answer _) fun alpha _ => ?_
  refine walk_bind (walk_lookTie _) fun y _ => ?_
  obtain ⟨rows, sZ, sG⟩ := y
  refine walk_bind (walk_pointAll _ _) fun rho hrho => ?_
  refine walk_bind (walk_run h0 0 _ _ _ (by
    intro x hx
    simp at hx)) fun keys hk => ?_
  refine walk_bind (walk_run h0 5 _ _ _ (by
    intro x hx
    have hx' : x ∈ rho.reverse.toList := hx
    rw [Array.toList_reverse, List.mem_reverse] at hx'
    exact hrho x hx')) fun table _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_pscBeginR _) fun leaves hl => ?_
  refine walk_bind (walk_roundsIn _ _ _ hl) fun y _ => ?_
  obtain ⟨zb0, leaves'⟩ := y
  refine walk_bind (walk_pointAll _ _) fun r5 _ => ?_
  refine walk_bind (walk_whole _ _ _ _ _) fun bits _ => ?_
  refine walk_bind (walk_ask _) fun _ _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_bind (walk_must _) fun _ _ => ?_
  refine walk_pure _ ?_
  intro x hx
  exact hk x (mem_toList_of_extract hx)

/-- **WHAT THE LOOKUP HEARS.** -/
theorem hear_words {p : Look.P} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView}
    {g : Forest.Heard} (h : K3.hear p es F rs = some (g, G)) (hd : okRoundsE rs = true) :
    ∀ x ∈ g.zy.toList, OnBytes.okE x = true := by
  unfold K3.hear at h
  cases hs : p.shape with
  | none => simp [hs] at h
  | some sh =>
    simp only [hs] at h
    split at h
    · unfold flRun at h
      cases ht : tapeT {} rs es with
      | none => simp [ht] at h
      | some t =>
        simp only [ht] at h
        cases hm : K3.messages sh F t with
        | none => simp [hm] at h
        | some y =>
          obtain ⟨g', G', u⟩ := y
          have k := (walk_messages (D := fun e => OnBytes.okE e = true) rfl sh F t g' G' u
            (tapeT_ok {} rs es t ht hd) hm).2
          simp only [hm] at h
          split at h
          · rename_i a b e
            obtain ⟨rfl, -, -⟩ := Prod.mk.inj (Option.some.inj e) |>.imp id Prod.mk.inj
            obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
            exact k
          · cases h
    · cases h

/-- **BEHIND A YES OF THE LOOKUP's BLOCK.** -/
theorem block_words {S Cl : Type} (seat : K3.Seat S Cl) (hr : K3.SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Look.P) (guests : List (Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (K3.block seat piece laid before p guests).decide s rs cols = .ok s')
    (hd : okRoundsE rs = true) :
    ∃ g, seat.heard s' = some g ∧ ∀ x ∈ g.zy.toList, OnBytes.okE x = true := by
  obtain ⟨F, x, hF, hn, hx, rfl⟩ :=
    VerifiableInference.OnPublicFiles.decide_ok seat piece laid before p guests s s' rs cols h
  refine ⟨x.1, hr _ _ _ (by rw [hF]; rfl) hn, ?_⟩
  exact hear_words (g := x.1) (G := x.2) hx hd

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.walk_lookTie
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_roundsIn
#print axioms VerifiableInference.Desc.First.K8.Honest.mem_toList_of_extract
#print axioms VerifiableInference.Desc.First.K8.Honest.walk_messages
#print axioms VerifiableInference.Desc.First.K8.Honest.hear_words
#print axioms VerifiableInference.Desc.First.K8.Honest.block_words
