-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K14/MaskAtEnd.lean: WHERE THE MASK OF THE OWN PROXIMITY TEST's FIRST FOLD LIES AT THE
FIRST CHAIN's END, under the library's hypothesis at the full size (P5J.AtMgA,
Johnson/P5J/MgAtAll.lean), at the format's second hash function. The mask goes out with W, as the
last
message of W's sending, which is the last sending of the first chain.

  mask_fresh_atM4   behind the yes of the sub-protocol that sends W and lays the claim's rows: where
                  the shape sends masks ahead, the claim's mask is the last of the messages just
                  sent
  mask_last_of_reach   **at every state reached at the first chain's last border: the claim's mask
                       is
                  the statement's last message**

What is not claimed. That a state is reached. Nothing on completeness, soundness or hiding.
Terms. border: lean/GLOSSARY.md.
-/
import AtFullSide.K14.PadsWAtEnd
import Johnson.Desc.Last.CountAtEnd
import Johnson.Desc.Last.ShapeDoorAhead
import Johnson.P5J.Cols13Paid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K14
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Law (linAt)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA TS)

/-- **The mask's number is that of the last message just sent.** ha: the shape sends masks ahead. -/
theorem mask_fresh_atM4 {Cl : Type} {P : VerifiableInference.Desc.K13.Where}
    {P' : VerifiableInference.Desc.K1.Par} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (VerifiableInference.Desc.K13.atM4 (Cl := Cl) P
      (VerifiableInference.Desc.K1.sendAtS P')).decide s [r₁, r₂] gs = .ok s')
    (ha : P.lin.masksAhead = true) :
    ∀ l', linAt s' = some l' →
      0 < P'.sent.size ∧ l'.mask = some (P'.sent.size - 1 + s.st.oracles.size) := by
  obtain ⟨s₁, g₁, rs₂, g₂, h1, h2⟩ := VerifiableInference.Desc.K13.Law.atM4_mid h
  obtain ⟨a, _, hh, _⟩ := VerifiableInference.Desc.K13.Law.sendAtS_full P' s s₁ r₁ r₂ g₁ h1
  obtain ⟨m₀, l, o, owed, hs, _, hrows, rfl⟩ := VerifiableInference.Desc.K13.Law.rowsB_at h2
  rw [hh] at hs
  obtain rfl : _ = m₀ := by injection hs
  obtain ⟨_, hm, _⟩ := VerifiableInference.Desc.K13.Law.rows_mask _ _ _ _ _ hrows
  intro l' hl'
  obtain rfl : o.1 = l' := Option.some.inj hl'
  rw [if_pos ha] at hm
  have hm' : (((Array.range P'.sent.size).map (· + s.st.oracles.size))[
      ((Array.range P'.sent.size).map (· + s.st.oracles.size)).size - 1]?).map some =
        some o.1.mask := hm
  rw [Array.size_map, Array.size_range, Array.getElem?_map, Array.getElem?_range] at hm'
  split at hm'
  · rename_i hlt
    exact ⟨by omega, (Option.some.inj hm').symm⟩
  · cases hm'

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **At every state reached at the first chain's last border the claim's mask is the statement's
last message.** The border 358 is written 356 + 1 + 1, so that the proof can open the last two
steps. It says nothing where the state holds no claim. -/
theorem mask_last_of_reach (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Pz : Type} {ft : ℕ}
    {start : Pz → TS} {z : Pz} {s : TS} (hr : Reach ft cF.blocksInOrder start (356 + 1 + 1) (z, s)) :
    ∀ l, linAt s = some l → l.mask = some (s.st.oracles.size - 1) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ha : (VerifiableInference.Desc.K13.whereOf Zp).lin.masksAhead = true := by
    show Zp.first.lin.masksAhead = true
    rw [P5J.linOne h.laid]
    exact VerifiableInference.Desc.Last.ahead_at_seat h.laid.pub
  cases hr with
  | succ hr₁ hb₁ hy₁ =>
    cases hr₁ with
    | succ _ hb₀ hy₀ =>
      obtain ⟨_, _, _, e₁⟩ := hy₁
      obtain ⟨_, _, _, e₀⟩ := hy₀
      rw [IM.at_357 h.scope h.reads O hb₁ e₁]
      obtain ⟨w, hw, ⟨rs', gs, hd⟩, -, -⟩ := IM.at_356 h.scope h.reads O hb₀ e₀
      obtain ⟨msg, -, rfl⟩ := (VerifiableInference.Desc.K13.Law.wAt_is _ _ _ w).1 hw
      obtain ⟨q₁, q₂, hd2⟩ := ToldDesc.atM4_two hd
      have e := (VerifiableInference.Desc.K13.Law.atM4_booked hd2).msgs
      intro l hl
      obtain ⟨hpos, hm⟩ := mask_fresh_atM4 hd2 ha l hl
      rw [hm, e]
      exact congrArg some (by omega)

end AtFullSide.K14

#print axioms AtFullSide.K14.mask_fresh_atM4
#print axioms AtFullSide.K14.mask_last_of_reach
