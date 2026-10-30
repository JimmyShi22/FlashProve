-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/StoredOf.lean: code switching: THE TEST `storedB` (Johnson/G/
SwitchSampleTop.lean: at each kept entry's own number the front's statement has a message of the
typed entry's kept member's shape, with a stored OOD sample row) ACCEPTS AT THE WRITTEN FRAME WITH
THE PLACE's OWN NUMBERS (`placeFrame`, K2Hands/FrontB2.lean), FROM THE SHAPES AND ONE INVARIANT OF
THE VERIFIER's STATE. One theorem with its proof. NO SUB-PROTOCOL IMPORTS THIS FILE.
  storedB_of   hlen: the frame has as many kept entries as the typed entry r has kept members ·
               hl: as many old numbers are given · hsh: at the i-th old number the front's
               statement has a message of the i-th kept member's shape · hA: every message of the
               front's statement whose shape counts an answer has a stored sample row
               (`K2.AnsweredStored`, K2Hands/AnsweredStored.lean) · hs: `keptShapeB r` accepts
               (each kept member's shape counts one answer): `storedB` accepts
LIMITS. hsh and hA are facts on the verifier's state and are premises here. hlen, hl and hs are
facts on public data; nobody shows them here. No soundness is claimed.
-/
import Johnson.G.SwitchSampleTop
import Johnson.Top.H0.K2Hands.CallerRenumber
import Johnson.Top.H0.K2Hands.FrontB2
import Johnson.Top.H0.K2Hands.AnsweredStored

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H Johnson.G
open VerifiableInference.Desc.First VerifiableInference.Desc.First.K2Hands

/-- **The test on the kept old messages accepts at the written frame with the place's own
numbers.** -/
theorem storedB_of {r : SwRow} {W : SwitchFrame} {n0 : ℕ} {olds : List ℕ}
    {fx : _root_.Tw.K2.Front} (hlen : W.kept.length = r.kept.length)
    (hsh : ∀ (i o : ℕ) (y : OracleShape × ℕ), olds[i]? = some o →
      (r.kept[i]?).bind (r.lo[·]?) = some y →
      ∃ x : OnBytes.Oracle, fx.st.oracles[o]? = some x ∧ x.shape = y.1)
    (hl : olds.length = r.kept.length) (hA : K2.AnsweredStored fx.st)
    (hs : keptShapeB r = true) : storedB r (placeFrame W n0 olds) fx = true := by
  unfold storedB
  refine List.all_eq_true.2 fun n hn => ?_
  have hn' : n < r.kept.length := List.mem_range.1 hn
  obtain ⟨k, hk⟩ : ∃ k, W.kept[n]? = some k :=
    ⟨_, List.getElem?_eq_getElem (show n < W.kept.length by omega)⟩
  obtain ⟨i, hi⟩ : ∃ i, r.kept[n]? = some i := ⟨_, List.getElem?_eq_getElem hn'⟩
  obtain ⟨o, ho⟩ : ∃ o, olds[n]? = some o :=
    ⟨_, List.getElem?_eq_getElem (show n < olds.length by omega)⟩
  have e := List.all_eq_true.1 hs i (List.mem_of_getElem? hi)
  obtain ⟨y, hy, ha⟩ : ∃ y, r.lo[i]? = some y ∧ y.1.answers = 1 := by
    cases hy : r.lo[i]? with
    | none => rw [hy] at e; cases e
    | some y =>
      rw [hy] at e
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at e
      exact ⟨y, rfl, e.1⟩
  have hb : (r.kept[n]?).bind (r.lo[·]?) = some y := by
    rw [hi, Option.bind_some]
    exact hy
  obtain ⟨x, hx, hxs⟩ := hsh n o y ho hb
  have hp : (placeFrame W n0 olds).kept[n]? =
      some (reAt olds.toArray (newsAt n0 W.kept.length) n k) := by
    unfold placeFrame
    rw [renumber_kept, hk, Option.map_some]
  have hold : (reAt olds.toArray (newsAt n0 W.kept.length) n k).old = o := by
    show olds.toArray.getD n noId = o
    simp [Array.getD_eq_getD_getElem?, ho]
  simp only [hp, hb, hold, hx, Option.any_some, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne]
  exact ⟨hxs, K2.stored_of_shape hA hx hxs ha⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.storedB_of
