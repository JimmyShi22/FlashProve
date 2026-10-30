-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ReadersAtMg.lean: THE FIELD «readers» OF MgOwes (BlindAtMg.lean) AT THE COMPOSED
MEANING's OWN READERS (MgData.Rd := K9.readersAt 𝔇.lk X (headLink X),
Johnson/Desc/Sound/MgAll.lean), FROM «EACH RUN COMMUTES WITH THE DRAW» (RunBlind,
Johnson/Desc/First/K8/BlindReaders.lean). A joining.
  mg_readers        at a segment l ≤ 24 other than the output head's: every run that sub-protocol number p.1 of the segment's link states under the name p.2 is RunBlind, for every pair p that the table names at a piece in front of the draw's ⟹ MgOwes.readers' clause.
  mg_readers_head   at the output head's segment: the like, with the blindness of the second hole's reader (k6Silent, Johnson/Desc/Kinds/Law/K6SilentCode.lean, through holesAt) as one premise more.
LIMITS. A rule over letters: no run is shown RunBlind. No soundness. Nothing on hiding.
-/
import Johnson.P1K8R.BlindAtMg
import Johnson.Desc.First.K8.BlindReaders

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K8T

open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.K8 (TlBlind RunBlind readersAt_blind readersOfLink_blind)
open VerifiableInference.Desc.K9 (statesOfLink holesAt readersAt_some readersAt_none)
open VerifiableInference.OnPublicFiles (headLink)

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  {𝔇 : MgData Xi P Tok rows cols nR X}

theorem mg_readers {l : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull)
    (hH : (l == headLink X) = false)
    (h : ∀ k r, k < pcOf l → ∀ p ∈ 𝔇.runs l k r, ∀ l', 𝔇.lk l = some l' →
      ∀ ρ ∈ statesOfLink l' p.1, (ρ.1 == p.2) = true → RunBlind (ρ.2 0)) :
    ∀ k r, k < pcOf l → ∀ p ∈ 𝔇.runs l k r, TlBlind ((𝔇.Rd l).forms p.1 p.2) :=
  fun k r hk p hp =>
    readersAt_blind 𝔇.lk X (headLink X) l hH p.1 p.2
      (runs_not_ahead hl k r hk p (by
        have hp' : p ∈ runsAt 𝔇.links l k r := hp
        rw [hL] at hp'
        exact hp'))
      (h k r hk p hp)

theorem mg_readers_head {l : ℕ} (hl : l ≤ 24) (hL : 𝔇.links = linksFull)
    (h : ∀ k r, k < pcOf l → ∀ p ∈ 𝔇.runs l k r, ∀ l', 𝔇.lk l = some l' →
      (∀ ρ ∈ statesOfLink l' p.1, (ρ.1 == p.2) = true → RunBlind (ρ.2 0)) ∧
        TlBlind ((holesAt X (headLink X) l l').silent p.1 p.2)) :
    ∀ k r, k < pcOf l → ∀ p ∈ 𝔇.runs l k r, TlBlind ((𝔇.Rd l).forms p.1 p.2) := by
  intro k r hk p hp
  have hn : (p.2 == "K8.equations") = false := runs_not_ahead hl k r hk p (by
    have hp' : p ∈ runsAt 𝔇.links l k r := hp
    rw [hL] at hp'
    exact hp')
  show TlBlind ((VerifiableInference.Desc.K9.readersAt 𝔇.lk X (headLink X) l).forms p.1 p.2)
  cases hk' : 𝔇.lk l with
  | none =>
    rw [readersAt_none 𝔇.lk X (headLink X) l hk']
    exact fun _ _ _ => rfl
  | some l' =>
    rw [readersAt_some 𝔇.lk X (headLink X) l l' hk']
    exact readersOfLink_blind _ l' p.1 p.2 hn (h k r hk p hp l' hk').1 (h k r hk p hp l' hk').2

end

end P1K8T

#print axioms P1K8T.mg_readers
#print axioms P1K8T.mg_readers_head
